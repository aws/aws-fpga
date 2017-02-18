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

#include <assert.h>
#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/uio.h>
#include <unistd.h>

#include <utils/io.h>
#include <utils/log.h>

int
epoll_init(int *epoll_fd)
{
	int rc;

	/*
	 * Create epoll file descriptor.
	 *
	 * @note The size field of epoll_create is ignored since Linux 2.6.8.
	 * It is initialized to 73 because that is the best number
	 * (there is only one correct answer) according to Dr. Sheldon Cooper.
	 */
	rc = epoll_create(73);
	fail_on(rc == -1, err, "Cannot create epoll");
	*epoll_fd = rc;

	return 0;
err:
	return -1;
}

int
epoll_add(int epoll_fd, struct epoll_cb *cb)
{
	int rc;
	struct epoll_event ev;

	assert(cb && cb->fn);

	memset(&ev, 0, sizeof(ev));
	ev.events = EPOLLIN;
	ev.data.ptr = cb;

	rc = epoll_ctl(epoll_fd, EPOLL_CTL_ADD, cb->fd, &ev);
	if (rc)
		log_error("Cannot add fd %d to epoll fd %d", cb->fd, epoll_fd);

	return rc;
}

int
epoll_remove(int epoll_fd, struct epoll_cb *cb)
{
	fail_on(cb->fd < 0, err, "Invalid fd");

	return epoll_ctl(epoll_fd, EPOLL_CTL_DEL, cb->fd, NULL);
err:
	return -1;
}

int
sread_loop(int fd, void *buffer, size_t size, size_t *rsize)
{
	ssize_t cur = 0;
	uint8_t *buf = buffer;

	for (size_t received = 0; received < size; received += cur) {
		do {
			cur = read(fd, buf + received, size - received);
		} while (cur == -1 && errno == EINTR);

		if (cur < 0) {
			if (rsize)
				*rsize = received;
			return -1;
		}
		if (cur == 0) {
			if (rsize)
				*rsize = received;
			return 1;
		}
	}
	if (rsize)
		*rsize = size;
	return 0;
}

int
write_loop(int fd, const void *buffer, size_t size)
{
	ssize_t cur = 0;
	const uint8_t *buf = buffer;

	/* Catch non-initialized variables */
	assert(fd);

	for (size_t sent = 0; sent < size; sent += cur) {
		do {
			cur = write(fd, buf + sent, size - sent);
		} while (cur == -1 && errno == EINTR);

		if (cur < 0)
			return -1;

		if (cur == 0)
			return 1;
	}

	return 0;
}

int
readv_loop(int fd, struct iovec *iov, int iov_len)
{
	ssize_t rc;
	size_t size;

retry:
	size = 0;
	for (int i = 0; i < iov_len; i++)
		size += iov[i].iov_len;

	do {
		rc = readv(fd, iov, iov_len);
	} while (rc == -1 && errno == EINTR);

	if (rc < 0)
		return -1;

	if ((size_t)rc == size)
		return 0;

	while (1) {
		if ((size_t)rc < iov->iov_len) {
			iov->iov_base = (uint8_t *)iov->iov_base + rc;
			iov->iov_len -= rc;
			break;
		}
		rc -= iov->iov_len;
		iov++;
		iov_len--;
	}
	goto retry;
}

int
writev_loop(int fd, struct iovec *iov, int iov_len)
{
	ssize_t rc;
	size_t size;

	/* Catch non-initialized variables */
	assert(fd);

retry:
	size = 0;
	for (int i = 0; i < iov_len; i++)
		size += iov[i].iov_len;

	do {
		rc = writev(fd, iov, iov_len);
	} while (rc == -1 && errno == EINTR);

	if (rc < 0)
		return -1;

	if ((size_t)rc == size)
		return 0;

	while (1) {
		if ((size_t)rc < iov->iov_len) {
			iov->iov_base = (uint8_t *)iov->iov_base + rc;
			iov->iov_len -= rc;
			break;
		}
		rc -= iov->iov_len;
		iov++;
		iov_len--;
	}
	goto retry;
}

int
string_to_int64(int64_t *num, const char *str)
{
	char *end;
	int64_t val;

	/* NULL pointer or empty string? */
	if (!str || !*str)
		return -1;

	errno = 0;
	val = strtoll(str, &end, 0);	/* Convert string to 64-bit decimal */

	/* Didn't consume whole string? */
	if (*end)
		return -1;

	/* Overflow, underflow, etc? */
	if (errno)
		return -1;

	*num = val;
	return 0;
}

int
string_to_uint64(uint64_t *num, const char *str)
{
	char *end;
	uint64_t val;

	/* NULL pointer or empty string? */
	if (!str || !*str)
		return -1;

	errno = 0;
	val = strtoull(str, &end, 0);	/* Convert string to 64-bit decimal */

	/* Didn't consume whole string? */
	if (*end)
		return -1;

	/* Overflow, underflow, etc? */
	if (errno)
		return -1;

	*num = val;
	return 0;
}

int
string_to_int(int *num, const char *str)
{
	char *end;
	long int val;

	/* NULL pointer or empty string? */
	if (!str || !*str)
		return -1;

	errno = 0;
	val = strtol(str, &end, 0);	/* Convert string to long int        */

	/* Didn't consume whole string? */
	if (*end)
		return -1;

	/* Overflow, underflow, etc? */
	if (errno)
		return -1;
	if (val > INT_MAX || val < INT_MIN)
		return -1;

	*num = (int)val;
	return 0;
}

int
string_to_uint(unsigned int *num, const char *str)
{
	char *end;
	long int val;

	/* NULL pointer or empty string? */
	if (!str || !*str)
		return -1;

	errno = 0;
	val = strtol(str, &end, 0);	/* Convert string to long int        */

	/* Didn't consume whole string? */
	if (*end)
		return -1;

	/* Overflow, underflow, etc? */
	if (errno)
		return -1;
	if (val > UINT_MAX || val < 0)
		return -1;

	*num = (unsigned int)val;
	return 0;
}

/**
 * Counts the number of directory entries.
 *
 * @param[in]	directory_path	The path to a directory.
 *
 * @returns	The number of directory entries in a given path.
 */
static int number_of_directory_entries(const char *directory_path)
{
	int n = 0;
	DIR *dd;

	dd = opendir(directory_path);
	fail_on(!dd, err, "Cannot open %s", directory_path);

	errno = 0;
	while (readdir(dd))
		n++;

	closedir(dd);
	fail_on(errno, err, "Errno is set after readdir loop");

	return n;
err:
	return -1;
}

int number_of_open_files(pid_t pid)
{
	int rc, n;
	char path[sizeof("/proc/-2147483648/fd")];

	rc = snprintf(path, sizeof(path), "/proc/%d/fd", pid);
	fail_on((size_t)rc >= sizeof(path), err, "Cannot make PID path");

	n = number_of_directory_entries(path);
	fail_on(n < 0, err,
		"Cannot get number of directory entries in %s", path);

	/* Account for ".", ".." */
	n -= 2;

	/* Acount for opening "/proc/self/fd" if we're checking ourself. */
	if (getpid() == pid)
		n--;

	return n;
err:
	return -1;
}
