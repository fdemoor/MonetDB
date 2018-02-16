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

static PyObject *_connection_registerTable(Py_ConnectionObject *self, PyObject *args)
{

	PyObject *dict;
	PyObject *key, *value, *mask, *data;
	Py_ssize_t pos = 0;
	npy_intp *shape;
	char *tname, *cname;
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

	if (!PyArg_ParseTuple(args, "Os", &dict, &tname)) {
		return false;
	}
	LOWER_NAME(tname);

	if (!PyDict_Check(dict)) {
		PyErr_Format(PyExc_TypeError, "expected a dictionary, but got an object "
				"of type %s", Py_TYPE(dict)->tp_name);
		return NULL;
	}

	while (PyDict_Next(dict, &pos, &key, &value)) {

		/* Column names should be strings */
		if (!PyString_Check(key)) {
			PyErr_Format(PyExc_TypeError, "expected a string as key, but got an object "
							"of type %s", Py_TYPE(key)->tp_name);
			return NULL;
		}

		/* Column values should be single dimension non-empty Numpy arrays
		 * with allowed data types
		 */

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

		nptype = PyArray_TYPE((PyArrayObject *) value);
		if (!PyType_IsInteger(nptype) && !PyType_IsFloat(nptype)
					&& !PyType_IsDouble(nptype) && !PyType_IsString(nptype)) {
			PyErr_Format(PyExc_TypeError, "array values type: unsupported Numpy type: %s", PyType_Format(nptype));
			return NULL;
		}

	}

	if (pos == 0) { /* Empty table not allowed */
		PyErr_Format(PyExc_ValueError, "empty table not allowed");
		return NULL;
	}

	/* Register the table */

	sql = ((backend *) self->cntxt->sqlcontext)->mvc;
	sql->sa = sa_create();
	if(!sql->sa) {
		PyErr_Format(PyExc_RuntimeError, "Create table failed: could not create allocator");
		goto cleanandfail;
	}
	if (!(s = mvc_bind_schema(sql, "sys"))) {
		PyErr_Format(PyExc_RuntimeError, "Create table failed: could not bind schema");
		goto cleanandfail;
	}
	if (!(t = mvc_create_table(sql, s, tname, tt_table, 0, SQL_DECLARED_TABLE, CA_ABORT, -1))) {
		PyErr_Format(PyExc_RuntimeError, "Create table failed: could not create table");
		goto cleanandfail;
	}
	t->base.allocated = 1;
	t->base.flag = 1;
	pos = 0;
	while (PyDict_Next(dict, &pos, &key, &value)) {

		tpe = sql_bind_localtype(ATOMname(PyType_ToBat(PyArray_TYPE((PyArrayObject *) value))));
		col = NULL;
		cname = PyString_AsString(key);
		LOWER_NAME(cname);

		if (!tpe) {
			PyErr_Format(PyExc_Exception, "Create table failed: could not find type for the table");
			goto cleanandfail;
		}

		col = mvc_create_column(sql, t, cname, tpe);
		if (!col) {
			PyErr_Format(PyExc_Exception, "Create table failed: could not create column");
			goto cleanandfail;
		}

	}
	msg = create_table_or_view(sql, "sys", t->base.name, t, 0);
	if (msg != MAL_SUCCEED) {
		PyErr_Format(PyExc_RuntimeError, "Create table failed: %s", msg);
		freeException(msg);
		goto cleanandfail;
	}
	t = mvc_bind_table(sql, s, tname);
	if (!t) {
		PyErr_Format(PyExc_RuntimeError, "Create table failed: could not bind table");
		goto cleanandfail;
	}
	t->access = 1; // Read-only
	pos = 0;
	while (PyDict_Next(dict, &pos, &key, &value)) {

		int unicode, regular;
		bat oldId;

		nptype = PyArray_TYPE((PyArrayObject *) value);
		unicode = (nptype == NPY_UNICODE);
		regular = (PyType_IsString(nptype) == true);

		bat_type = PyType_ToBat(PyArray_TYPE((PyArrayObject *) value));
		mem_size = PyArray_DESCR((PyArrayObject *) value)->elsize;

		if (PyType_IsNumpyMaskedArray(value)) {
			mask = PyObject_GetAttrString(value, "mask");
			data = PyObject_GetAttrString(value, "data");
		} else {
			mask = NULL;
			data = value;
		}

		b = PyObject_ConvertArrayToBAT((PyArrayObject *) data, bat_type, mem_size,
									   (PyArrayObject *) mask, unicode, &return_msg);
		if (!b) {
			PyErr_Format(PyExc_RuntimeError, "Array->BAT conversion error: %s", return_msg);
			goto cleanandfail;
		}

		col = NULL;
		cname = PyString_AsString(key);
		LOWER_NAME(cname);

		col = mvc_bind_column(sql, t, cname);
		oldId = b->batCacheid;
		b->batCacheid = ((sql_delta *) col->data)->ibid;
		((sql_delta *) col->data)->cnt = b->batCount;
		if (regular && b->tvheap) {
			b->tvheap->parentid = b->batCacheid;
		}

		if (!BBPcacheBAT(b, regular, oldId)) {
			PyErr_Format(PyExc_RuntimeError, "Create table failed: could not cache BAT");
			goto cleanandfail;
		}

	}

	free(return_msg);
	sa_destroy(sql->sa);
	sql->sa = NULL;
	return Py_BuildValue("");

cleanandfail:
	free(return_msg);
	sa_destroy(sql->sa);
	sql->sa = NULL;
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
