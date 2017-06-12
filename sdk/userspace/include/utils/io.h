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

/** @file
 * Wrappers for I/O functions
 */

#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Set up epoll.
 *
 * @param[out]	epoll_fd	Memory to write epoll file descriptor to.
 *
 * @returns
 *  0 on success,
 * -1 on failure.
 */
int epoll_init(int *epoll_fd);

/**
 * epoll callback argument.
 * At the moment, users of this type require either an integer or a pointer.
 */
union epoll_cb_arg {
	/** 32-bit signed integer, currently used for the slot number. */
	int i;

	/** Pointer, currently used for struct vcpu. */
	void *ptr;
};

/** epoll callback. */
struct epoll_cb {
	/** Argument of the callback function. */
	union epoll_cb_arg arg;

	/** Callback function. */
	void (*fn)(union epoll_cb_arg *arg);

	/** File descriptor. */
	int fd;
};

/**
 * Add a file descriptor to be polled by epoll.
 *
 * @param[in]	epoll_fd	Epoll file descriptor.
 * @param[in]	cb		Callback function and argument.
 *
 * @returns
 *  0 on success,
 * -1 on failure.
 */
int epoll_add(int epoll_fd, struct epoll_cb *cb);

/**
 * Remove file descriptor so it is not polled anymore by epoll.
 *
 * @param[in]	epoll_fd	Epoll file descriptor.
 * @param[in]	cb		Callback to remove.
 *
 * @returns
 *  0 on success,
 * -1 on failure.
 */
int epoll_remove(int epoll_fd, struct epoll_cb *cb);

/**
 * Read in a loop until a specific number of bytes has been read or a read
 * failed.
 *
 * @param[in]	fd	File descriptor to read from.
 * @param[out]	buffer	Buffer of at least size bytes to copy the read data
 *			into.
 * @param[in]	size	Number of bytes to read.
 * @param[out]	rsize	Number of bytes successfully read.
 *
 * @returns
 *  1	on failure due to EOF,
 *  0	on success,
 * -1	on failures other than EOF.
 */
int sread_loop(int fd, void *buffer, size_t size, size_t *rsize);

/**
 * Read in a loop until a specific number of bytes has been read or a read
 * failed.
 *
 * Same as sread_loop() except the missing rsize parameter.
 */
static inline int
read_loop(int fd, void *buffer, size_t size)
{
	return sread_loop(fd, buffer, size, NULL);
}

/**
 * Write in a loop until a specific number of bytes has been written or a write
 * failed.
 *
 * @param[in]	fd	File descriptor to write to.
 * @param[in]	buffer	Buffer of at least size bytes to data to write.
 * @param[in]	size	Number of bytes to write.
 *
 * @returns
 *  1	on failure due to EOF,
 *  0	on success,
 * -1	on failures other than EOF.
 */
int write_loop(int fd, const void *buffer, size_t size);

struct iovec;

/**
 * Wrap readv in a loop to handle EINTR.
 *
 * @param[in]     fd      The file descriptor.
 * @param[in,out] iov     The I/O vector to scatter input.
 * @param[in]     iov_len The length of the I/O vector.
 *
 * @returns
 *  0 on success,
 * -1 on failure.
 */
int readv_loop(int fd, struct iovec *iov, int iov_len);

/**
 * Wrap writev in a loop to handle EINTR.
 *
 * @param[in] fd      The file descriptor.
 * @param[in] iov     The I/O vector to gather output.
 * @param[in] iov_len The length of the I/O vector.
 *
 * @returns
 *  0 on success,
 * -1 on failure.
 */
int writev_loop(int fd, struct iovec *iov, int iov_len);

/**
 * Convert a string to a 64-bit signed integer.
 *
 * @param[out]	num	The 64-bit signed integer.
 * @param[in]	str	The 64-bit signed integer as a string.
 *
 * @returns	0 on success, -1 on failure.
 */
int string_to_int64(int64_t *num, const char *str);

/**
 * Convert a string to a 64-bit unsigned integer.
 *
 * @param[out]	num	The 64-bit unsigned integer.
 * @param[in]	str	The 64-bit unsigned integer as a string.
 *
 * @returns	0 on success, -1 on failure.
 */
int string_to_uint64(uint64_t *num, const char *str);

/**
 * Convert a string to an integer.
 *
 * @param[out]	num	The buffer where to write the resulting integer.
 * @param[in]	str	The integer as a string.
 *
 * @returns	0 on success, -1 on failure.
 */
int string_to_int(int *num, const char *str);

/**
 * Convert a string to an unsigned integer.
 *
 * @param[out]	num  The buffer where to write the resulting unsigned integer.
 * @param[in]	str  The unsigned integer as a string.
 *
 * @returns	0 on success, -1 on failure.
 */
int string_to_uint(unsigned int *num, const char *str);

/**
 * Get the number of open files.
 *
 * @returns	How many files are open in a given process, -1 on error.
 */
int number_of_open_files(pid_t pid);

#ifdef __cplusplus
}
#endif
