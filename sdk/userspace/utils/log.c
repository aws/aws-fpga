/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * @file
 * Log subsystem implementation.
 */

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>

#ifdef CONFIG_ERRORS_FATAL
#ifdef NDEBUG
#error CONFIG_ERRORS_FATAL and NDEBUG cannot co-exist
#endif
#include <assert.h>
#endif

#include <utils/log.h>
#include <utils/macros.h>

/** Log subsystem private data. */
static struct {
	char name[32];
	size_t nr_loggers;
	const struct logger *loggers[8];
} priv = {
	.name = "undefined",
};

/** Per-thread log message prefix. */
static __thread char priv_prefix[32];

int log_init(const char *format, ...)
{
	va_list ap;
	int rc;

	va_start(ap, format);
	rc = vsnprintf(priv.name, sizeof(priv.name), format, ap);
	rc = (size_t)rc >= sizeof(priv.name) ? -ENAMETOOLONG : 0;
	va_end(ap);
	priv.nr_loggers = 0;
	return rc;
}

int log_init_prefix(const char *format, ...)
{
	va_list ap;
	int rc;

	va_start(ap, format);
	rc = vsnprintf(priv_prefix, sizeof(priv_prefix), format, ap);
	rc = (size_t)rc >= sizeof(priv_prefix) ? -ENAMETOOLONG : 0;
	va_end(ap);
	return rc;
}

int log_attach(const struct logger *logger, void *opaque, unsigned int flags)
{
	for (size_t i = 0; i < priv.nr_loggers; i++) {
		if (priv.loggers[i] == logger) {
			if (!priv.loggers[i]->reinit)
				return -ENOTSUP;
			return priv.loggers[i]->reinit(opaque, flags);
		}
	}

	if (priv.nr_loggers >= sizeof_array(priv.loggers))
		return -ENOMEM;

	if (!logger->log)
		return -EINVAL;

	if (logger->init) {
		int rc;

		rc = logger->init(opaque, flags);
		if (rc)
			return rc;
	}

	priv.loggers[priv.nr_loggers++] = logger;

	return 0;
}

/** Stringify a log level. */
static const char *str_log_level(enum log_level level)
{
	static const char * const str[] = {
		[LOG_LEVEL_ERROR] = "ERROR",
		[LOG_LEVEL_WARNING] = "WARNING",
		[LOG_LEVEL_INFO] = "INFO",
		[LOG_LEVEL_DEBUG] = "DEBUG",
		[LOG_LEVEL_END] = "UNKNOWN",
	};

	if (level >= LOG_LEVEL_END)
		level = LOG_LEVEL_END;
	return str[level];
}

/** Stringify an error number. */
static const char *str_error_number(int error_number)
{
	static __thread char buf[64];

	snprintf(buf, sizeof(buf), "error_number=%d", error_number);
	return buf;
}

/** Log on stdout from within the log subsystem. */
static __printf(1, 2) int internal_log(const char *format, ...)
{
	va_list ap;
	int rc;
	char message[LOG_MESSAGE_LENGTH_MAX];

	va_start(ap, format);
	rc = vsnprintf(message, sizeof(message), format, ap);
	va_end(ap);
	printf("%s%s\n",
	       (size_t)rc >= sizeof(message) ? "(TRUNCATED) " : "", message);
	fflush(stdout);
	return 0;
}

/** Log on stdout. */
static int stdout_log(enum log_level level, const char *message)
{
	(void)level;

	printf("%s", message);
	fflush(stdout);
	return 0;
}

/**
 * Generate a log message.
 *
 * Format:
 * \<rfc-3339 datetime\>, \<plugin\>\<plugin-instance\>, \<log level\>,
 * \<file\> +\<line\>: \<function\>(): [\<prefix\>\: ]...[:\<error\>]
 */
static void _log(enum log_level level, const char *file, int line,
		 const char *func, const char *format, va_list ap,
		 int error_number)
{
	struct timespec ts;
	time_t ts_s;
	unsigned long ts_us;
	struct tm tm;
	void *p;
	int rc;
	char message[LOG_MESSAGE_LENGTH_MAX];
	size_t message_length = 0;
	size_t t_len;
	bool logged = false;

	/* time */
	rc = clock_gettime(CLOCK_REALTIME, &ts);
	assert(!rc);
	ts_s = ts.tv_sec;
	p = gmtime_r(&ts_s, &tm);
	assert(p);
	t_len = strftime(&message[message_length],
			 sizeof(message) - message_length, "%Y-%m-%dT%T", &tm);
	if (!t_len) {
		internal_log("strftime() failed");
		rc = 0;
	}
	message_length += t_len;
	ts_us = ts.tv_nsec / 1000;
	rc = snprintf(&message[message_length],
		      sizeof(message) - message_length, ".%06luZ, ", ts_us);
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("snprintf() us failed");
		rc = 0;
	}
	message_length += rc;
	/* name */
	rc = snprintf(&message[message_length],
		      sizeof(message) - message_length, "%s, ", priv.name);
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("snprintf() name failed");
		rc = 0;
	}
	message_length += rc;
	/* log level */
	rc = snprintf(&message[message_length],
		      sizeof(message) - message_length,
		      "%s, ", str_log_level(level));
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("snprintf() log level failed");
		rc = 0;
	}
	message_length += rc;
	/* file, line, func */
	rc = snprintf(&message[message_length],
		      sizeof(message) - message_length,
		      "%s +%d: %s(): ", file, line, func);
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("snprintf() file +line: func() failed");
		rc = 0;
	}
	message_length += rc;
	/* prefix */
	if (priv_prefix[0]) {
		rc = snprintf(&message[message_length],
			      sizeof(message) - message_length,
			      "%s: ", priv_prefix);
		if ((size_t)rc >= sizeof(message) - message_length) {
			internal_log("snprintf() prefix failed");
			rc = 0;
		}
		message_length += rc;
	}
	/* message */
	rc = vsnprintf(&message[message_length],
		       sizeof(message) - message_length, format, ap);
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("vsnprintf() message failed");
		rc = 0;
	}
	message_length += rc;
	/* error message */
	if (error_number) {
		rc = snprintf(&message[message_length],
			      sizeof(message) - message_length, ": %s",
			      str_error_number(error_number));
		if ((size_t)rc >= sizeof(message) - message_length) {
			internal_log("snprintf() error message failed");
			rc = 0;
		}
		message_length += rc;
	}
	/* newline */
	rc = snprintf(&message[message_length],
		      sizeof(message) - message_length,
		      "\n");
	if ((size_t)rc >= sizeof(message) - message_length) {
		internal_log("snprintf() \\n failed");
		rc = 0;
	}
	message_length += rc;

	for (size_t i = 0; i < priv.nr_loggers; i++) {
		int rc;

		rc = priv.loggers[i]->log(level, message);
		if (!rc) {
			logged = true;
			continue;
		}
		internal_log("Could not log a message via the %s logger: %s",
			     priv.loggers[i]->name, str_error_number(-rc));
	}
	if (!logged)
		stdout_log(level, message);
}

void _log_error(const char *file, int line, const char *func,
		const char *format, ...)
{
	va_list ap;
	int error_number = errno;

#ifdef CONFIG_ERRORS_FATAL
	assert(false);
#endif

	va_start(ap, format);
	_log(LOG_LEVEL_ERROR, file, line, func, format, ap, error_number);
	va_end(ap);
	errno = error_number;
}

void _log_warning(const char *file, int line, const char *func,
		  const char *format, ...)
{
	va_list ap;
	int error_number = errno;

	va_start(ap, format);
	_log(LOG_LEVEL_WARNING, file, line, func, format, ap, error_number);
	va_end(ap);
	errno = error_number;
}

void _log_info(const char *file, int line, const char *func,
	       const char *format, ...)
{
	va_list ap;
	int error_number = errno;

	va_start(ap, format);
	_log(LOG_LEVEL_INFO, file, line, func, format, ap, error_number);
	va_end(ap);
	errno = error_number;
}

void _log_debug(const char *file, int line, const char *func,
		const char *format, ...)
{
	va_list ap;
	int error_number = errno;

	va_start(ap, format);
	_log(LOG_LEVEL_DEBUG, file, line, func, format, ap, error_number);
	va_end(ap);
	errno = error_number;
}

/** stdout logger. */
const struct logger logger_stdout = {
	.name = "stdout",
	.log = stdout_log,
};

/** Default logger. */
const struct logger *logger_default = &logger_stdout;
