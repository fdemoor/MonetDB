/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0.  If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright 2008-2015 MonetDB B.V.
 */

#include "org_monetdb_embedded_MonetDBEmbedded.h"
#include "embedded.h"

#include "res_table.h"
#include "mal_type.h"

jint JNICALL Java_org_monetdb_embedded_MonetDBEmbedded_startupWrapper
(JNIEnv *env, jobject object, jstring directory, jboolean silent) {
	(void)object;
	const char *directory_string_tmp = (*env)->GetStringUTFChars(env, directory, 0);
	char *directory_string = strdup(directory_string_tmp);
	unsigned char silent_char = 'n';

	// Release the directory string
	(*env)->ReleaseStringUTFChars(env, directory, directory_string_tmp);
	// Set the silent flag based on passed boolean value
	if (silent) {
		silent_char = 'y';
	}
	return monetdb_startup(directory_string, silent_char);
}

jobject JNICALL Java_org_monetdb_embedded_MonetDBEmbedded_query
(JNIEnv *env, jobject object, jstring query) {
	(void)object;
	res_table *output = NULL;
	const char *query_string_tmp = (*env)->GetStringUTFChars(env, query, 0);
	char *query_string = strdup(query_string_tmp);
	// Release the query string
	(*env)->ReleaseStringUTFChars(env, query, query_string_tmp);

	jobject result;
	jclass resultClass = (*env)->FindClass(env, "org/monetdb/embedded/result/EmbeddedQueryResult");
	// from Java EmbeddedQueryResult(String[] columnNames, String[] columnTypes, int numberOfColumns, long resultPointer)
	jmethodID resultConstructor = (*env)->GetMethodID(env, resultClass, "<init>", "([Ljava/lang/String;[Ljava/lang/String;IJ)V");
	// column names and types string arrays
	jobjectArray columnNames, columnTypes = NULL;
	jclass stringClass = (*env)->FindClass(env, "java/lang/String");

	// In case we can't find the result object class
	if (resultClass == NULL) {
		return NULL;
	}

	// Execute the query
	char* err = monetdb_query(query_string, (void**)&output);

	// Checking for errors
	if (err != NULL) {
		jclass exClass = (*env)->FindClass(env, "java/sql/SQLException");

		// Clean up the result data
		monetdb_cleanup_result(output);
		if (exClass == NULL) {
			// Cloud not find the exception class, just return empty object
			return NULL;
		}
		(*env)->ThrowNew(env, exClass, err);
		return NULL;
	}

	// Collect result column names and types in string arrays
	// If we have not output, we will return them empty
	columnNames = (*env)->NewObjectArray(env, output->nr_cols, stringClass, 0);
	columnTypes = (*env)->NewObjectArray(env, output->nr_cols, stringClass, 0);
	if (output && output->nr_cols > 0) {
		int i;
		for (i = 0; i < output->nr_cols; i++) {
			res_col col = output->cols[i];
			BAT* b = BATdescriptor(col.b);
			char *type;

			switch (ATOMstorage(getColumnType(b->T->type))) {
			case TYPE_sht:
				type = "short";
				break;
			case TYPE_int:
				type = "integer";
				break;
			case TYPE_lng:
				type = "long";
				break;
			case TYPE_flt:
				type = "float";
				break;
			case TYPE_dbl:
				type = "double";
				break;
			case TYPE_str:
				type = "string";
				break;
#ifdef HAVE_HGE
			case TYPE_hge:
				type = "huge";
				break;
#endif
			default:
				type = "unknown";
			}
			// Set the meta fields in the result object
			(*env)->SetObjectArrayElement(env, columnNames, i, (*env)->NewStringUTF(env, col.name));
			(*env)->SetObjectArrayElement(env, columnTypes, i, (*env)->NewStringUTF(env, type));
		}
	}
	// Also keep a long value with the result pointer in the Java result object
	long resultTablePointer = (long)output;
	// Create the result object
	// from Java EmbeddedQueryResult(String[] columnNames, String[] columnTypes, int numberOfColumns, long resultPointer)
	result = (*env)->NewObject(env, resultClass, resultConstructor, columnNames, columnTypes, output->nr_cols, resultTablePointer);

	return result;
}

jstring JNICALL Java_org_monetdb_embedded_MonetDBEmbedded_append
(JNIEnv *env, jobject object, jstring table, jstring schema, jobject data) {
	(void)object;
	(void)table;
	(void)schema;
	(void)data;

	return (*env)->NewStringUTF(env, "");
}
