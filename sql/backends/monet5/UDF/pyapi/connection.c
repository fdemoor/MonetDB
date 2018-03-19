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


/* Lower all the char in name to be consistent with SQL parser */
#define LOWER_NAME(name)                                                      \
	for (i = 0; (name)[i]; i++) {                                             \
		(name)[i] = tolower((name)[i]);                                       \
	}

#define ASSIGN_TYPE(tpe)                                                      \
	if (!regular) {                                                           \
		PyErr_Format(PyExc_ValueError,                                        \
			"trying to apply option %s to a non-string array for column %s",  \
			#tpe, cname);                                                     \
		goto cleanandfail2;                                                    \
	}                                                                         \
	bat_type = TYPE_##tpe;

#define ASSIGN_BAT_TYPE()                                                     \
	opt = PyDict_GetItem(options, key);                                       \
	if (opt) {                                                                \
		oname = PyString_AsString(opt);                                       \
		if (strcmp(oname, "date") == 0) {                                     \
			ASSIGN_TYPE(date)                                                 \
		} else if (strcmp(oname, "daytime") == 0) {                           \
			ASSIGN_TYPE(daytime)                                              \
		} else if (strcmp(oname, "timestamp") == 0) {                         \
			ASSIGN_TYPE(timestamp)                                            \
		} else {                                                              \
			PyErr_Format(PyExc_ValueError,                                    \
				"unrecognized option for column %s: %s "                      \
				"(available options are: date, daytime, timestamp)",          \
				cname, oname);                                                \
			goto cleanandfail2;                                                \
		}                                                                     \
	} else {                                                                  \
		bat_type = PyType_ToBat(PyArray_TYPE((PyArrayObject *) value));       \
	}

static PyObject *_connection_registerTable(Py_ConnectionObject *self, PyObject *args)
{

	PyObject *dict, *options, *options_default;
	PyObject *key, *value, *mask, *data, *opt;
	Py_ssize_t pos = 0;
	npy_intp *shape;
	char *tname, *cname, *oname;
	char *return_msg = (char *) malloc (1024 * sizeof(char));
	int bat_type, ndims, nrows = -1, i, nptype;
	str msg;
	mvc *sql;
	sql_table *t;
	sql_column *col;
	sql_schema *s;
	sql_subtype *tpe = NULL;
	size_t mem_size;
	BAT *b;

	/* Check arguments */

	options_default = PyDict_New();
	options = NULL;
	if (!options_default) {
		PyErr_Format(PyExc_ValueError, "can't create an empty dictionary for default options");
		goto cleanandfail0;
	}

	if (!PyArg_ParseTuple(args, "Os|O", &dict, &tname, &options)) {
		goto cleanandfail0;
	}
	LOWER_NAME(tname);

	if (!options) {
		options = options_default;
	}

	if (!PyDict_Check(dict)) {
		PyErr_Format(PyExc_TypeError, "expected a dictionary, but got an object "
				"of type %s", Py_TYPE(dict)->tp_name);
		goto cleanandfail0;
	}

	while (PyDict_Next(dict, &pos, &key, &value)) {

		/* Column names should be strings */
		if (!PyString_Check(key)) {
			PyErr_Format(PyExc_TypeError, "expected a string as key, but got an object "
							"of type %s", Py_TYPE(key)->tp_name);
			goto cleanandfail0;
		}

		/* Column values should be single dimension non-empty Numpy arrays
		 * with allowed data types
		 */

		if (!PyArray_Check(value)) {
			PyErr_Format(PyExc_TypeError, "expected a Numpy array as value, but got "
							"an object of type %s", Py_TYPE(value)->tp_name);
			goto cleanandfail0;
		}

		ndims = PyArray_NDIM((PyArrayObject *) value);
		if (ndims > 1) {
			PyErr_Format(PyExc_TypeError, "expecting a single dimension Numpy array");
			goto cleanandfail0;
		}

		shape = PyArray_SHAPE((PyArrayObject *) value);
		if (shape[0] <= 0) {
			PyErr_Format(PyExc_TypeError, "a column cannot be empty ");
			goto cleanandfail0;
		}

		if (nrows == -1) {
			nrows = shape[0];
		} else {
			if (shape[0] != nrows) {
				PyErr_Format(PyExc_TypeError, "all the columns must have the same "
											  "number of elements");
				goto cleanandfail0;
			}
		}

		nptype = PyArray_TYPE((PyArrayObject *) value);
		if (!PyType_IsInteger(nptype) && !PyType_IsFloat(nptype)
					&& !PyType_IsDouble(nptype) && !PyType_IsString(nptype)) {
			PyErr_Format(PyExc_TypeError, "array values type: unsupported Numpy type: %s", PyType_Format(nptype));
			goto cleanandfail0;
		}

	}

	if (pos == 0) { /* Empty table not allowed */
		PyErr_Format(PyExc_ValueError, "empty table not allowed");
		goto cleanandfail0;
	}

	pos = 0;
	while (PyDict_Next(options, &pos, &key, &value)) {

			/* Column names should be strings */
			if (!PyString_Check(key)) {
				PyErr_Format(PyExc_TypeError, "expected a string as key, but got an object "
								"of type %s", Py_TYPE(key)->tp_name);
				goto cleanandfail0;
			}

			/* Column values should be strings */
			if (!PyString_Check(value)) {
				PyErr_Format(PyExc_TypeError, "expected a string as option, but got an object "
								"of type %s", Py_TYPE(key)->tp_name);
				goto cleanandfail0;
			}

	}

	/* Register the table */

	sql = ((backend *) self->cntxt->sqlcontext)->mvc;
	sql->sa = sa_create();
	if(!sql->sa) {
		PyErr_Format(PyExc_RuntimeError, "could not create allocator");
		goto cleanandfail0;
	}
	if (!(s = mvc_bind_schema(sql, "sys"))) {
		PyErr_Format(PyExc_RuntimeError, "could not bind schema");
		goto cleanandfail1;
	}
	if (!(t = mvc_create_table(sql, s, tname, tt_table, 0, SQL_DECLARED_TABLE, CA_ABORT, -1))) {
		PyErr_Format(PyExc_RuntimeError, "could not create table");
		goto cleanandfail1;
	}
	t->base.allocated = 1;
	t->base.flag = 1;
	pos = 0;
	while (PyDict_Next(dict, &pos, &key, &value)) {

		int regular;
		nptype = PyArray_TYPE((PyArrayObject *) value);
		regular = (PyType_IsString(nptype) == true);
		cname = PyString_AsString(key);
		LOWER_NAME(cname);
		ASSIGN_BAT_TYPE()
		tpe = sql_bind_localtype(ATOMname(bat_type));

		if (!tpe) {
			PyErr_Format(PyExc_Exception, "could not find type for the table");
			goto cleanandfail2;
		}

		col = mvc_create_column(sql, t, cname, tpe);
		if (!col) {
			PyErr_Format(PyExc_Exception, "could not create column");
			goto cleanandfail2;
		}

	}
	msg = create_table_or_view(sql, "sys", t->base.name, t, 0);
	if (msg != MAL_SUCCEED) {
		PyErr_Format(PyExc_RuntimeError, "%s", msg);
		freeException(msg);
		goto cleanandfail2;
	}
	t = mvc_bind_table(sql, s, tname);
	if (!t) {
		PyErr_Format(PyExc_RuntimeError, "could not bind table");
		goto cleanandfail2;
	}
	t->access = 1; // Read-only
	pos = 0;
	while (PyDict_Next(dict, &pos, &key, &value)) {

		int regular;
		nptype = PyArray_TYPE((PyArrayObject *) value);
		regular = (PyType_IsString(nptype) == true);
		cname = PyString_AsString(key);
		LOWER_NAME(cname);
		ASSIGN_BAT_TYPE()
		mem_size = PyArray_DESCR((PyArrayObject *) value)->elsize;

		if (PyType_IsNumpyMaskedArray(value)) {
			mask = PyObject_GetAttrString(value, "mask");
			data = PyObject_GetAttrString(value, "data");
		} else {
			mask = NULL;
			data = value;
		}

		col = mvc_bind_column(sql, t, cname);

		if (regular) {
			/* No zero-copy optimization possible, register with a regular
			 * MonetDB column with data copy
			 */

			int unicode = (nptype == NPY_UNICODE);
			bat bid = ((sql_delta *) col->data)->ibid;
			BBPfix(bid);
			b = BBPdescriptor(bid);
			if (!b) {
				PyErr_Format(PyExc_RuntimeError, "could not get BAT", return_msg);
				goto cleanandfail2;
			}

			if (GDKgetenv_istrue("embeddedpy_lazy_virt")) {

				/* Lazy register: conversion price will be paid later, when needed
				 * Hook for conversion is in SQLgetColumnSize function
				 */

				npy_intp *shape = PyArray_SHAPE((PyArrayObject *) data);
				LazyPyBAT *lpb = (LazyPyBAT *) malloc(sizeof(LazyPyBAT));
				LazyVirtual *lv = (LazyVirtual *) malloc(sizeof(LazyVirtual));

				/* Copy the BAT as it is now */
				BAT *bb = COLcopy(b, b->ttype, TRUE, PERSISTENT);

				/* Keep all necessary information */
				lv->data = (PyArrayObject *) data;
				lv->mask = (PyArrayObject *) mask;
				lv->bat_type = bat_type;
				lv->b = bb;
				lv->mem_size = mem_size;
				lv->unicode = unicode;
				lv->backup = b->thash;

				/* Set pointers to the functions to call later */
				lpb->conv_fcn = &PyObject_FillLazyBATFromArray;
				lpb->free_fcn = &FreeLazyVirtual;
				lpb->backup_fcn = &GetBackupLazyVirtual;
				lpb->lv = (void *) lv;

				/* Keep it in the BAT: we use the hash field that is kept in the
				 * structure to be restored later
				 */
				b->thash = (Hash *) lpb;

				/* Make the system believes the BAT is not empty */
				nrows = shape[0];
				b->batCount = nrows;
				b->batCapacity = nrows;

				/* Set a special flag to indicate this is a lazy Python BAT */
				BBPsetlazyBAT(b);

			} else {

				/* Fill immediately, conversion price is paid right now */

				if (PyObject_FillBATFromArray((PyArrayObject *) data, bat_type, mem_size,
						(PyArrayObject *) mask, unicode, b, &return_msg) == false) {
					PyErr_Format(PyExc_RuntimeError, "could not fill BAT from array: %s",
																				return_msg);
					goto cleanandfail2;
				}

			}

		} else {
			/* Numeric data types, zero-copy optimization is possible */

			bat id;
			b = PyObject_ConvertArrayToBAT((PyArrayObject *) data, bat_type, mem_size,
										   (PyArrayObject *) mask, &return_msg);
			if (!b) {
				PyErr_Format(PyExc_RuntimeError, "array->BAT conversion: %s", return_msg);
				goto cleanandfail2;
			}

			id = ((sql_delta *) col->data)->ibid;
			((sql_delta *) col->data)->cnt = b->batCount;

			if (!BBPvirtualBAT(b, id)) {
				PyErr_Format(PyExc_RuntimeError, "could not cache BAT");
				goto cleanandfail2;
			}
		}

	}

	Py_DECREF(options_default);
	free(return_msg);
	sa_destroy(sql->sa);
	sql->sa = NULL;
	return Py_BuildValue("");

cleanandfail2:
	//mvc_drop_table(sql, s, t, DROP_CASCADE);
cleanandfail1:
	sa_destroy(sql->sa);
	sql->sa = NULL;
cleanandfail0:
	Py_XDECREF(options_default);
	free(return_msg);
	return NULL;

}

static PyObject *_connection_persistTable(Py_ConnectionObject *self, PyObject *args)
{
	sql_schema *s;
	sql_table *t;
	sql_column *c;
	sql_delta *d;
	BAT *b;
	mvc *sql;
	node *cn;
	char *tname;

	/* Check arguments */
	if (!PyArg_ParseTuple(args, "s", &tname)) {
		goto cleanandfail0;
	}

	/* Process */
	sql = ((backend *) self->cntxt->sqlcontext)->mvc;
	if (!(s = mvc_bind_schema(sql, "sys"))) {
		PyErr_Format(PyExc_RuntimeError, "could not bind schema");
		goto cleanandfail0;
	}
	t = mvc_bind_table(sql, s, tname);
	if (!t) {
		PyErr_Format(PyExc_RuntimeError, "could not bind table");
		goto cleanandfail0;
	}
	for (cn = t->columns.set->h; cn; cn = cn->next) {
		c = (sql_column *) cn->data;
		d = c ? (sql_delta *) c->data : NULL;
		d = !d ? c->po ? (sql_delta*) c->po->data : NULL : NULL;
		b = d ? BBPdescriptor(d->bid) : NULL;
		if (!b) {
			PyErr_Format(PyExc_RuntimeError, "could not bind column");
			goto cleanandfail0;
		}
		if (BBP_status(b->batCacheid) & BBPPYTHONBAT) {
			if (!BBPpersistBAT(b)) {
				PyErr_Format(PyExc_RuntimeError, "could not persist column");
				goto cleanandfail0;
			}
		}
	}

	return Py_BuildValue("");

cleanandfail0:
	return NULL;
}

static PyMethodDef _connectionObject_methods[] = {
	{"execute", (PyCFunction)_connection_execute, METH_O,
	 "execute(query) -> executes a SQL query on the database in the current "
	 "client context"},
	{"registerTable", (PyCFunction)_connection_registerTable, METH_VARARGS,
	 "registerTable(dict, name) -> registers a table existing through Python "
	 "objects to be able to use it in queries, de-register can be done using "
	 "a 'DROP TABLE name;' statement"},
	{"persistTable", (PyCFunction)_connection_persistTable, METH_VARARGS,
	 "persistTable(name) -> transforms a virtual table into a basetable, "
	 "causing columns to be written to disk if they were not already "
	 "(i.e. the ones with zero-copy optimization)"},
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
