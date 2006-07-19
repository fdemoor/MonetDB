/*
 * The contents of this file are subject to the MonetDB Public License
 * Version 1.1 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://monetdb.cwi.nl/Legal/MonetDBLicense-1.1.html
 *
 * Software distributed under the License is distributed on an "AS IS"
 * basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
 * License for the specific language governing rights and limitations
 * under the License.
 *
 * The Original Code is the MonetDB Database System.
 *
 * The Initial Developer of the Original Code is CWI.
 * Portions created by CWI are Copyright (C) 1997-2006 CWI.
 * All Rights Reserved.
 */

/*
 * This code was created by Peter Harvey (mostly during Christmas 98/99).
 * This code is LGPL. Please ensure that this message remains in future
 * distributions and uses of this code (thats about all I get out of it).
 * - Peter Harvey pharvey@codebydesign.com
 * 
 * This file has been modified for the MonetDB project.  See the file
 * Copyright in this directory for more information.
 */

/**********************************************************************
 * SQLConnect()
 * CLI Compliance: ISO 92
 *
 * Author: Martin van Dinther
 * Date  : 30 aug 2002
 *
 **********************************************************************/

#include <monet_options.h>
#include "ODBCGlobal.h"
#include "ODBCDbc.h"
#include "ODBCUtil.h"
#ifdef HAVE_STRINGS_H
#include <strings.h>
#endif

#ifdef NATIVE_WIN32
#include <odbcinst.h>
#define HAVE_SQLGETPRIVATEPROFILESTRING 1
#endif
#ifndef HAVE_SQLGETPRIVATEPROFILESTRING
#define SQLGetPrivateProfileString(section,entry,default,buffer,bufferlen,filename)	(strncpy(buffer,default,bufferlen), buffer[bufferlen-1]=0, strlen(buffer))
#endif

SQLRETURN
SQLConnect_(ODBCDbc *dbc, SQLCHAR *szDataSource, SQLSMALLINT nDataSourceLength, SQLCHAR *szUID, SQLSMALLINT nUIDLength, SQLCHAR *szPWD, SQLSMALLINT nPWDLength, char *host, int port)
{
	SQLRETURN rc = SQL_SUCCESS;
	char *dsn = NULL;
	char uid[32];
	char pwd[32];
	char buf[256];
	char *schema = NULL;
	char *s;
	int n;
	Mapi mid;

	/* check connection state, should not be connected */
	if (dbc->Connected) {
		/* Connection name in use */
		addDbcError(dbc, "08002", NULL, 0);
		return SQL_ERROR;
	}

	/* convert input string parameters to normal null terminated C strings */
	fixODBCstring(szDataSource, nDataSourceLength, addDbcError, dbc);
	if (nDataSourceLength == 0) {
		szDataSource = (SQLCHAR *) "MonetDB";
		nDataSourceLength = strlen((char *) szDataSource);
	}
	dsn = dupODBCstring(szDataSource, (size_t) nDataSourceLength);

	n = SQLGetPrivateProfileString(dsn, "uid", "monetdb", uid, sizeof(uid), "odbc.ini");
	fixODBCstring(szUID, nUIDLength, addDbcError, dbc);
	if (n == 0 && nUIDLength == 0) {
		free(dsn);
		/* Invalid authorization specification */
		addDbcError(dbc, "28000", NULL, 0);
		return SQL_ERROR;
	}
	if (nUIDLength > 0) {
		if (nUIDLength >= sizeof(uid))
			nUIDLength = sizeof(uid) - 1;
		strncpy(uid, szUID, nUIDLength);
		uid[nUIDLength] = 0;
	}
	n = SQLGetPrivateProfileString(dsn, "pwd", "monetdb", pwd, sizeof(pwd), "odbc.ini");
	fixODBCstring(szPWD, nPWDLength, addDbcError, dbc);
	if (n == 0 && nPWDLength == 0) {
		free(dsn);
		/* Invalid authorization specification */
		addDbcError(dbc, "28000", NULL, 0);
		return SQL_ERROR;
	}
	if (nPWDLength > 0) {
		if (nPWDLength >= sizeof(pwd))
			nPWDLength = sizeof(pwd) - 1;
		strncpy(pwd, szPWD, nPWDLength);
		pwd[nPWDLength] = 0;
	}

	if (port == 0 && (s = getenv("MAPIPORT")) != NULL)
		port = atoi(s);
	if (port == 0) {
		n = SQLGetPrivateProfileString(dsn, "port", "50000", buf, sizeof(buf), "odbc.ini");
		port = atoi(buf);
	}
	if (port == 0)
		port = 50000;

	if (host == NULL || *host == 0) {
		n = SQLGetPrivateProfileString(dsn, "host", "localhost", buf, sizeof(buf), "odbc.ini");
		if (n > 0)
			host = buf;
		else
			host = "localhost";
	}

#ifdef ODBCDEBUG
	ODBCLOG("SQLConnect: DSN=%s UID=%s PWD=%s host=%s port=%d\n", dsn, uid, pwd, host, port);
#endif

	/* connect to a server on host via port */
	mid = mapi_connect(host, port, uid, pwd, "sql");
	if (mid == NULL || mapi_error(mid)) {
		/* Client unable to establish connection */
		addDbcError(dbc, "08001", NULL, 0);
		rc = SQL_ERROR;
		/* clean up */
		if (mid)
			mapi_destroy(mid);
		if (dsn != NULL)
			free(dsn);
	} else {
		/* store internal information and clean up buffers */
		dbc->Connected = 1;
		dbc->mid = mid;
		if (dbc->dsn != NULL)
			free(dbc->dsn);
		dbc->dsn = dsn;
		if (dbc->uid != NULL)
			free(dbc->uid);
		dbc->uid = strdup(uid);
		if (dbc->pwd != NULL)
			free(dbc->pwd);
		dbc->pwd = strdup(pwd);
		if (dbc->host)
			free(dbc->host);
		dbc->host = strdup(host);
		if (dbc->DBNAME != NULL)
			free(dbc->DBNAME);
		dbc->DBNAME = schema;
		mapi_setAutocommit(mid, dbc->sql_attr_autocommit == SQL_AUTOCOMMIT_ON);
	}

	return rc;
}

SQLRETURN SQL_API
SQLConnect(SQLHDBC hDbc, SQLCHAR *szDataSource, SQLSMALLINT nDataSourceLength, SQLCHAR *szUID, SQLSMALLINT nUIDLength, SQLCHAR *szPWD, SQLSMALLINT nPWDLength)
{
#ifdef ODBCDEBUG
	ODBCLOG("SQLConnect " PTRFMT "\n", PTRFMTCAST hDbc);
#endif

	if (!isValidDbc((ODBCDbc *) hDbc))
		return SQL_INVALID_HANDLE;

	clearDbcErrors((ODBCDbc *) hDbc);

	return SQLConnect_((ODBCDbc *) hDbc, szDataSource, nDataSourceLength, szUID, nUIDLength, szPWD, nPWDLength, NULL, 0);
}

#ifdef WITH_WCHAR
SQLRETURN SQL_API
SQLConnectA(SQLHDBC hDbc, SQLCHAR *szDataSource, SQLSMALLINT nDataSourceLength, SQLCHAR *szUID, SQLSMALLINT nUIDLength, SQLCHAR *szPWD, SQLSMALLINT nPWDLength)
{
	return SQLConnect(hDbc, szDataSource, nDataSourceLength, szUID, nUIDLength, szPWD, nPWDLength);
}

SQLRETURN SQL_API
SQLConnectW(SQLHDBC hDbc, SQLWCHAR * szDataSource, SQLSMALLINT nDataSourceLength, SQLWCHAR * szUID, SQLSMALLINT nUIDLength, SQLWCHAR * szPWD, SQLSMALLINT nPWDLength)
{
	SQLCHAR *ds = NULL, *uid = NULL, *pwd = NULL;
	SQLRETURN rc = SQL_ERROR;
	ODBCDbc *dbc = (ODBCDbc *) hDbc;

#ifdef ODBCDEBUG
	ODBCLOG("SQLConnectW " PTRFMT "\n", PTRFMTCAST hDbc);
#endif

	if (!isValidDbc(dbc))
		return SQL_INVALID_HANDLE;

	clearDbcErrors(dbc);

	fixWcharIn(szDataSource, nDataSourceLength, SQLCHAR, ds, addDbcError, dbc, goto exit);
	fixWcharIn(szUID, nUIDLength, SQLCHAR, uid, addDbcError, dbc, goto exit);
	fixWcharIn(szPWD, nPWDLength, SQLCHAR, pwd, addDbcError, dbc, goto exit);

	rc = SQLConnect_(dbc, ds, SQL_NTS, uid, SQL_NTS, pwd, SQL_NTS, NULL, 0);

      exit:
	if (ds)
		free(ds);
	if (uid)
		free(uid);
	if (pwd)
		free(pwd);
	return rc;
}
#endif /* WITH_WCHAR */
