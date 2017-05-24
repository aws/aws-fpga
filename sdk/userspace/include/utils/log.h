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
 * Log subsystem interface.
 */

#pragma once

#include "compiler.h"

/** Maximum log message length. */
#define LOG_MESSAGE_LENGTH_MAX 512

/** Log levels. */
enum log_level {
	LOG_LEVEL_ERROR,
	LOG_LEVEL_WARNING,
	LOG_LEVEL_INFO,
	LOG_LEVEL_DEBUG,
	LOG_LEVEL_END,
};

/** Logger flags. */
enum {
	/** Change the behavior of a logger to serialize log operations. */
	LOGGER_FLAGS_SERIALIZE = (1u << 0),
};

#ifdef __cplusplus
extern "C" {
#endif

/** Logger. */
struct logger {
	/** Name (for debugging). */
	const char *name;

	/**
	 * Initialization function.
	 *
	 * @param[in]  opaque  Opaque object, need and meaning depend on the
	 *                     logger.
	 * @param[in]  flags   Flags to change the behavior of the logger
	 *                     (e.g., serialize logging operations).
	 *
	 * @returns 0 on success, a negative error number on failure.
	 */
	int (*init)(void *opaque, unsigned int flags);

	/**
	 * Re-initialize function.
	 *
	 * @see logger#init .
	 */
	int (*reinit)(void *opaque, unsigned int flags);

	/**
	 * Log function.
	 *
	 * @param[in]  level    Log level.
	 * @param[in]  message  Log message.
	 *
	 * @returns 0 on success, a negative error number on failure.
	 */
	int (*log)(enum log_level level, const char *message);
};

/**
 * Initialize the log subsystem.
 *
 * @param[in]  format  Entity name format (printf-like).
 *
 * @returns 0 on success, a negative error number on failure.
 */
int log_init(const char *format, ...);

/**
 * Initialize the per-thread log message prefix.
 *
 * @param[in]  format  Message prefix format (printf-like).
 *
 * @returns 0 on success, a negative error number on failure.
 */
__printf(1, 2) int log_init_prefix(const char *format, ...);

/**
 * Attach a logger to the log subsystem.
 *
 * @param[in]  logger  Logger.
 * @param[in]  opaque  Opaque object, @see logger#init .
 * @param[in]  flags   Flags to change the behavior
 *
 * @returns 0 on success, a negative error number on failure.
 */
int log_attach(const struct logger *logger, void *opaque, unsigned int flags);

/** Log an error message (do not call directly!). */
__printf(4, 5) void _log_error(const char *file, int line, const char *func,
			       const char *format, ...);

/** Log a warning message (do not call directly!). */
__printf(4, 5) void _log_warning(const char *file, int line, const char *func,
				 const char *format, ...);

/** Log an info message (do not call directly!). */
__printf(4, 5) void _log_info(const char *file, int line, const char *func,
			      const char *format, ...);

/** Log a debug message (do not call directly!). */
__printf(4, 5) void _log_debug(const char *file, int line, const char *func,
			       const char *format, ...);

/** Dummy log function to discard messages with log level above a threshold. */
static inline __printf(1, 2) void log_dummy(const char *fmt, ...)
{
	(void)fmt;
}

/** Log an error message (doesn't touch errno). */
#if CONFIG_LOGLEVEL >= 1
#define log_error(...) _log_error(__FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define log_error(...) log_dummy(__VA_ARGS__)
#endif

/** Log a warning message (doesn't touch errno). */
#if CONFIG_LOGLEVEL >= 2
#define log_warning(...) _log_warning(__FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define log_warning(...) log_dummy(__VA_ARGS__)
#endif

/** Log an info message (doesn't touch errno). */
#if CONFIG_LOGLEVEL >= 3
#define log_info(...) _log_info(__FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define log_info(...) log_dummy(__VA_ARGS__)
#endif

/** Log a debug message (doesn't touch errno). */
#if CONFIG_LOGLEVEL >= 4
#define log_debug(...) _log_debug(__FILE__, __LINE__, __func__, __VA_ARGS__)
#else
#define log_debug(...) log_dummy(__VA_ARGS__)
#endif

/** Usage: fail_on(condition, label, message format string, [arg1, arg2, ...])*/
#define fail_on(CONDITION, LABEL, ...)          \
	do {                                    \
		if (CONDITION) {                \
			log_error(__VA_ARGS__); \
			goto LABEL;             \
		}                               \
	} while (0)

#define fail_on_quiet(CONDITION, LABEL, ...)          \
    do {                                              \
        if (CONDITION) {                              \
            log_debug(__VA_ARGS__);                   \
            goto LABEL;                               \
        }                                             \
    } while (0)

extern const struct logger logger_stdout;
extern const struct logger logger_kmsg;
extern const struct logger *logger_default;

#ifdef __cplusplus
}
#endif
