/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0.  If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright 1997 - July 2008 CWI, August 2008 - 2018 MonetDB B.V.
 */

#include "monetdb_config.h"
#include "pyapi.h"
#include "conversion.h"
#include "connection.h"
#include "type_conversion.h"
#include "gdk_interprocess.h"

CREATE_SQL_FUNCTION_PTR(void, SQLdestroyResult);
CREATE_SQL_FUNCTION_PTR(str, SQLstatementIntern);
CREATE_SQL_FUNCTION_PTR(str, create_table_from_emit);

static PyObject *_connection_execute(Py_ConnectionObject *self, PyObject *args)
{
	char *query = NULL;
#ifndef IS_PY3K
	if (PyUnicode_CheckExact(args)) {
		PyObject* str = PyUnicode_AsUTF8String(args);
		if (!str) {
			PyErr_Format(PyExc_Exception, "Unicode failure.");
			return NULL;
		}
		query = GDKstrdup(((PyStringObject *)str)->ob_sval);
		Py_DECREF(str);
	} else
#endif
	if (PyString_CheckExact(args)) {
#ifndef IS_PY3K
		query = GDKstrdup(((PyStringObject *)args)->ob_sval);
#else
		query = GDKstrdup(PyUnicode_AsUTF8(args));
#endif
	} else {
		PyErr_Format(PyExc_TypeError,
					 "expected a query string, but got an object of type %s",
					 Py_TYPE(args)->tp_name);
		return NULL;
	}
	if (!query) {
		PyErr_Format(PyExc_Exception, "%s", MAL_MALLOC_FAIL);
		return NULL;
	}
	if (!self->mapped) {
		// This is not a mapped process, so we can just directly execute the
		// query here
		PyObject *result;
		res_table *output = NULL;
		char *res = NULL;
Py_BEGIN_ALLOW_THREADS;
		res = _connection_query(self->cntxt, query, &output);
Py_END_ALLOW_THREADS;
		GDKfree(query);
		if (res != MAL_SUCCEED) {
			PyErr_Format(PyExc_Exception, "SQL Query Failed: %s",
						 (res ? res : "<no error>"));
			return NULL;
		}

		result = PyDict_New();
		if (output && output->nr_cols > 0) {
			PyInput input;
			PyObject *numpy_array;
			int i;
			for (i = 0; i < output->nr_cols; i++) {
				res_col col = output->cols[i];
				BAT *b = BATdescriptor(col.b);

				if (b == NULL) {
					PyErr_Format(PyExc_Exception, "Internal error: could not retrieve bat");
					return NULL;
				}

				input.bat = b;
				input.count = BATcount(b);
				input.bat_type = getBatType(b->ttype);
				input.scalar = false;
				input.sql_subtype = &col.type;

				numpy_array =
					PyMaskedArray_FromBAT(&input, 0, input.count, &res, true);
				if (!numpy_array) {
					_connection_cleanup_result(output);
					BBPunfix(b->batCacheid);
					PyErr_Format(PyExc_Exception, "SQL Query Failed: %s",
								 (res ? res : "<no error>"));
					return NULL;
				}
				PyDict_SetItem(result,
							   PyString_FromString(output->cols[i].name),
							   numpy_array);
				Py_DECREF(numpy_array);
				BBPunfix(input.bat->batCacheid);
			}
			_connection_cleanup_result(output);
			return result;
		} else {
			Py_RETURN_NONE;
		}
	} else {
		PyErr_Format(PyExc_Exception, "Loopback queries are not supported in parallel.");
		return NULL;
	}
}

regTabList *regTables = NULL;

static int isRegSupportedType(char c) {
	/* FIXME multiple int types */
	switch (c) {
	case 'i':
	case 'l':
		return 1;
	default:
		return 0;
	}
}

static PyObject *_connection_registerTable(Py_ConnectionObject *self, PyObject *args)
{

	PyObject *dict;
	PyObject *key, *value;
	Py_ssize_t pos = 0;
	npy_intp *shape;
	char *name, *tname, *cname;
	regTabList *regTab;
	mvc *sql;
	sql_table *t;
	sql_column *col;
	sql_allocator *sa;
	int i, bat_type, ndims, nrows = -1;
	BAT *b;
	sql_subtype *tpe = NULL;

#ifndef _FDEMOOR_WIP_
	(void) b;
	(void) cname;
	(void) i;
	(void) col;
	(void) bat_type;
	(void) sql;
	(void) tpe;
	(void) t;
#endif

	/* TODO Check that name is not already a table in the database */

	/* Look if there is already a table registered with this name */
	regTab = regTables;
	while (regTab) {
		if (regTab->name && strcmp(name, regTab->name) == 0) {
			PyErr_Format(PyExc_Exception, "There is already a table registered with that name. "
					"Deregister it first or use another name");
			return NULL;
		}
		regTab = regTab->next;
	}

	/* Check arguments */

	if (!PyArg_ParseTuple(args, "Os", &dict, &name)) {
		return NULL;
	}
	if (!PyDict_Check(dict)) {
		PyErr_Format(PyExc_TypeError, "expected a dictionary, but got an object "
				"of type %s", Py_TYPE(dict)->tp_name);
		return NULL;
	}

	while (PyDict_Next(dict, &pos, &key, &value)) {

		if (!PyString_Check(key)) {
			PyErr_Format(PyExc_TypeError, "expected a string as key, but got an object "
							"of type %s", Py_TYPE(key)->tp_name);
			return NULL;
		}
		if (!PyArray_Check(value)) {
			PyErr_Format(PyExc_TypeError, "expected a Numpy array as value, but got "
							"an object of type %s", Py_TYPE(value)->tp_name);
			return NULL;
		}

		ndims = PyArray_NDIM((PyArrayObject *) value);
		if (ndims > 1) {
			PyErr_Format(PyExc_TypeError, "expecting a single dimension Numpy array");
			return NULL;
		}

		shape = PyArray_SHAPE((PyArrayObject *) value);
		if (shape[0] <= 0) {
			PyErr_Format(PyExc_TypeError, "a column cannot be empty ");
			return NULL;
		}

		if (nrows == -1) {
			nrows = shape[0];
		} else {
			if (shape[0] != nrows) {
				PyErr_Format(PyExc_TypeError, "all the columns must have the same "
											  "number of elements");
				return NULL;
			}
		}

		if (!isRegSupportedType(PyArray_DESCR((PyArrayObject *) value)->type)) {
			PyErr_Format(PyExc_TypeError, "Only integers supported in arrays at the moment");
			return NULL;
		}

	}

	if (pos == 0) {
		PyErr_Format(PyExc_TypeError, "empty table not allowed");
		return NULL;
	}

	/* Keep table name */
	tname = (char *) malloc(strlen(name) * sizeof(char));
	if (!tname) {
		PyErr_Format(PyExc_Exception, "Could not allocate space");
		return NULL;
	}
	strcpy(tname, name);

	/* TODO Actually register the table */

	/* Create table descriptor */
	t = (sql_table *) malloc (sizeof(sql_table));
	sa = sa_create();
	t->base.id = 0;
	t->base.wtime = 0;
	t->base.rtime = 0;
	t->base.flag = TR_NEW;
	t->base.refcnt = 1;
	t->base.name = tname;
	t->type = tt_view;
	t->system = 1;
	t->persistence = (temp_t) SQL_PERSIST;
	t->commit_action = (ca_t) CA_PRESERVE;
	t->query = "";
	t->access = 0;
	cs_new(&t->columns, sa, (fdestroy) &column_destroy);
	cs_new(&t->idxs, sa, (fdestroy) &idx_destroy);
	cs_new(&t->keys, sa, (fdestroy) &key_destroy);
	cs_new(&t->members, sa, (fdestroy) NULL);
	t->pkey = NULL;
	t->sz = COLSIZE;
	t->cleared = 0;
	t->s = NULL;

#ifdef _FDEMOOR_WIP_
	while (PyDict_Next(dict, &pos, &key, &value)) {

		switch (PyArray_DESCR((PyArrayObject *) value)->type) {
		case 'i':
			bat_type = TYPE_int;
			sql_find_subtype(tpe, "int", 32, 0);
			break;
		case 'l':
			bat_type = TYPE_lng;
			sql_find_subtype(tpe, "int", 64, 0);
			break;
		default:
			PyErr_Format(PyExc_TypeError, "Only integers supported in arrays at the moment");
			return NULL;
		}

		cname = PyString_AsString(key);
		col = create_sql_column(sql->sa, t, cname, tpe);
		col->data = ZNEW(sql_delta);

		b = PyObject_ConvertArrayToBAT(value, bat_type);
		if (!b) {
			PyErr_Format(PyExc_Exception, "Error during Array -> BAT conversion");
			return NULL;
		}
		((sql_delta *) col->data)->bid = b->batCacheid;
		BBPcacheit(b, 1);
		i++;
	}
#endif

	sql = ((backend *) self->cntxt->sqlcontext)->mvc;
	stack_push_table(sql, tname, NULL, t);/* Keep track of the register */

	/* Keep track of the register */
	regTab = (regTabList *) malloc(sizeof(regTabList));
	if (!regTab) {
		PyErr_Format(PyExc_Exception, "Could not allocate space");
		free(tname);
		return NULL;
	}
	regTab->name = tname;
	regTab->next = regTables;
	regTables = regTab;

	return Py_BuildValue("");
}

static PyObject *_connection_deregisterTable(Py_ConnectionObject *self, PyObject *args)
{

	char *name;
	regTabList *regTab = NULL, *prev = NULL;
	mvc *sql;
	sql_table *t;
	node *cn;
	sql_column *col;
	int i;
	BAT *b;

#ifndef _FDEMOOR_WIP_
	(void) col;
	(void) b;
	(void) i;
	(void) cn;
	(void) t;
	(void) sql;
	(void) self;
#endif

	/* Check argument types */

	if (!PyArg_ParseTuple(args, "s", &name)) {
		return NULL;
	}

	/* Look for the table in the list */
	regTab = regTables;
	while (regTab) {
		if (regTab->name && strcmp(name, regTab->name) == 0) {
			break;
		}
		prev = regTab;
		regTab = regTab->next;
	}
	if (!regTab) {
		PyErr_Format(PyExc_Exception, "There is no table registered with that name");
		return NULL;
	}

	/* TODO Actually deregister the table */
	sql = ((backend *) self->cntxt->sqlcontext)->mvc;
	t = stack_find_table(sql, name);
	if (!t) {
		// TODO Could happen?
		// TODO What happens with a 'DROP TABLE name'?
	}
	for (i = sql->topvars-1; i >= 0; i--) {
		if (!sql->vars[i].frame && strcmp(sql->vars[i].name, name)==0)
		{
			sql->vars[i].t = NULL;
		}
	}
#ifdef _FDEMOOR_WIP_
	for (cn = t->columns.set->h; cn; cn = cn->next) {
		col = (sql_column *) cn->data;
		BBPuncacheit(((sql_delta *) col->data)->bid, 1); // FIXME not sure about the 1, maybe
													     // 0 and manual destroy of BAT
		column_destroy(col);
	}
#endif

	if (--(t->base.refcnt) == 0) {
		cs_destroy(&t->keys);
		cs_destroy(&t->idxs);
		cs_destroy(&t->columns);
		cs_destroy(&t->members);
	}
	free(t);

	t = stack_find_table(sql, name); // Should be null next time ?

	/* Remove the table from the list */
	if (prev) {
		prev->next = regTab->next;
	} else {
		regTables = regTab->next;
	}
	free(regTab->name);
	free(regTab);

	return Py_BuildValue("");
}

static PyMethodDef _connectionObject_methods[] = {
	{"execute", (PyCFunction)_connection_execute, METH_O,
	 "execute(query) -> executes a SQL query on the database in the current "
	 "client context"},
	{"registerTable", (PyCFunction)_connection_registerTable, METH_VARARGS,
	 "registerTable(dict, name) -> registers a table existing through Python "
	 "objects to be able to use it in queries"},
	{"deregisterTable", (PyCFunction)_connection_deregisterTable, METH_VARARGS,
	 "deregisterTable(name) -> deregisters the table 'name' that was previously "
	 "registered"},
	{NULL, NULL, 0, NULL} /* Sentinel */
};

PyTypeObject Py_ConnectionType = {
	_PyObject_EXTRA_INIT
// in python3 they use structs within structs to represent this information, and
// many compilers throw warnings if you don't use separate braces
// to initialize these separate structs. However, in Python2, they use #defines
// to put this information in, so we have these nice #ifdefs
#ifdef IS_PY3K
	{{
#endif
		 1, NULL
#ifdef IS_PY3K
	 }
#endif
	 ,
	 0
#ifdef IS_PY3K
	}
#endif
	,
	"monetdb._connection", sizeof(Py_ConnectionObject), 0, 0, /* tp_dealloc */
	0,														  /* tp_print */
	0,														  /* tp_getattr */
	0,														  /* tp_setattr */
	0,														  /* tp_compare */
	0,														  /* tp_repr */
	0,														  /* tp_as_number */
	0,									   /* tp_as_sequence */
	0,									   /* tp_as_mapping */
	(hashfunc)PyObject_HashNotImplemented, /* tp_hash */
	0,									   /* tp_call */
	0,									   /* tp_str */
	0,									   /* tp_getattro */
	0,									   /* tp_setattro */
	0,									   /* tp_as_buffer */
	Py_TPFLAGS_DEFAULT,					   /* tp_flags */
	"Connection to MonetDB",			   /* tp_doc */
	0,									   /* tp_traverse */
	0,									   /* tp_clear */
	0,									   /* tp_richcompare */
	0,									   /* tp_weaklistoffset */
	0,									   /* tp_iter */
	0,									   /* tp_iternext */
	_connectionObject_methods,			   /* tp_methods */
	0,									   /* tp_members */
	0,									   /* tp_getset */
	0,									   /* tp_base */
	0,									   /* tp_dict */
	0,									   /* tp_descr_get */
	0,									   /* tp_descr_set */
	0,									   /* tp_dictoffset */
	0,									   /* tp_init */
	PyType_GenericAlloc,				   /* tp_alloc */
	PyType_GenericNew,					   /* tp_new */
	PyObject_Del,						   /* tp_free */
	0, 0, 0, 0, 0, 0, 0, 0
#ifdef IS_PY3K
	,
	0
#endif
};

void _connection_cleanup_result(void *output)
{
	(*SQLdestroyResult_ptr)((res_table *)output);
}

str _connection_query(Client cntxt, char *query, res_table **result)
{
	str res = MAL_SUCCEED;
	res = (*SQLstatementIntern_ptr)(cntxt, &query, "name", 1, 0, result);
	return res;
}

str _connection_create_table(Client cntxt, char *sname, char *tname,
							 sql_emit_col *columns, size_t ncols)
{
	return (*create_table_from_emit_ptr)(cntxt, sname, tname, columns, ncols);
}

PyObject *Py_Connection_Create(Client cntxt, bit mapped, QueryStruct *query_ptr,
							   int query_sem)
{
	register Py_ConnectionObject *op;

	op = (Py_ConnectionObject *)PyObject_MALLOC(sizeof(Py_ConnectionObject));
	if (op == NULL)
		return PyErr_NoMemory();
	PyObject_Init((PyObject *)op, &Py_ConnectionType);

	op->cntxt = cntxt;
	op->mapped = mapped;
	op->query_ptr = query_ptr;
	op->query_sem = query_sem;

	return (PyObject *)op;
}

static void _connection_import_array(void) { _import_array(); }

str _connection_init(void)
{
	str msg = MAL_SUCCEED;
	_connection_import_array();

	LOAD_SQL_FUNCTION_PTR(SQLdestroyResult);
	LOAD_SQL_FUNCTION_PTR(SQLstatementIntern);
	LOAD_SQL_FUNCTION_PTR(create_table_from_emit);

	if (msg != MAL_SUCCEED) {
		return msg;
	}

	if (PyType_Ready(&Py_ConnectionType) < 0)
		return createException(MAL, "pyapi.eval",
							   "Failed to initialize connection type.");
	return msg;
}
