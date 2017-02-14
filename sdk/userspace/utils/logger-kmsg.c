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
 * kmsg logger.
 */

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <utils/io.h>
#include <utils/log.h>

/** kmsg logger private data. */
static struct {
	int fd;
} priv;

/**
 * Initialize the kmsg logger.
 *
 * @param[in]  opaque  Unused.
 * @param[in]  flags   Unused.
 *
 * @returns 0 on success, a negative error number on failure.
 */
static int kmsg_init(void *opaque, unsigned int flags)
{
	int fd;

	(void)opaque;
	(void)flags;

	fd = open("/dev/kmsg", O_WRONLY | O_CLOEXEC);
	if (fd == -1)
		return -errno;
	priv.fd = fd;
	return 0;
}

/** Stringify (kmsg prefix) a log level. */
static const char *str_log_level(enum log_level level)
{
	static const char * const str[] = {
		[LOG_LEVEL_ERROR] = "<3>",
		[LOG_LEVEL_WARNING] = "<4>",
		[LOG_LEVEL_INFO] = "<6>",
		[LOG_LEVEL_DEBUG] = "<7>",
		[LOG_LEVEL_END] = "",
	};

	if (level >= LOG_LEVEL_END)
		level = LOG_LEVEL_END;
	return str[level];
}

/**
 * Log a message via the kmsg logger.
 *
 * @see logger#log .
 */
static int kmsg_log(enum log_level level, const char *message)
{
	int rc;
	char prefixed_message[LOG_MESSAGE_LENGTH_MAX + 8];
	size_t prefixed_message_len;

	rc = snprintf(prefixed_message, sizeof(prefixed_message), "%s%s",
		      str_log_level(level), message);
	if ((size_t)rc >= sizeof(prefixed_message))
		return -ENAMETOOLONG;
	prefixed_message_len = rc;
	rc = write_loop(priv.fd, prefixed_message, prefixed_message_len);
	if (rc)
		return -errno;
	return 0;
}

/** kmsg logger. */
const struct logger logger_kmsg = {
	.name = "kmsg",
	.init = kmsg_init,
	.log = kmsg_log,
};
