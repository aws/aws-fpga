/*
 * Copyright 2015 Amazon.com, Inc. or its affiliates.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#define CLOCK_PRECISION 1E-9 /* one billion */
#define NANOSECONDS_PER_SECOND 1E9 /* one billion */

#ifndef PAGE_SIZE
#define PAGE_SIZE (1024 *4)
#endif

#ifndef SIZE_OF_DATA
#error "Please define SIZE_OF_DATA"
#endif

#ifndef NUMBER_OF_REPETITIONS
#error "Please define NUMBER_OF_REPETITIONS"
#endif


char* write_buf;
char* read_buf;
long long int write_index;
long long int read_index;

bool read_done = false;

static char *rand_string(char *str, size_t size)
{
	const char charset[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
	int i;

	for(i = 0; i < size; i++){
		int key = rand() % (int) (sizeof charset - 1);
		str[i] = charset[key];
	}

	str[size-1] = '\0';

	return str;
}

int main()
{
	double number_of_succesful_writes = 0;
	struct timespec before, after;
	double global_time = 0;
#ifdef WRITE_PERF
	char transaction_type[] = "Write";
#else
	char transaction_type[] = "Read";

#endif

	int fd, i, ret;
	srand ( time(NULL) );

	write_buf = (char*)malloc(sizeof(char) * SIZE_OF_DATA);
	read_buf = (char*)malloc(sizeof(char) * SIZE_OF_DATA);

	rand_string(write_buf, SIZE_OF_DATA);

	if((fd = open("/dev/edma0_queue_0",O_RDWR)) == -1){
		perror("open failed");
		return -1;
	}

	for( i = 0; i < NUMBER_OF_REPETITIONS; i++)
	{
		ret = lseek(fd, 0x010000000, SEEK_SET);
		if(ret < 0)
			exit(3);

		clock_gettime(CLOCK_REALTIME, &before);
#ifdef WRITE_PERF
		ret = write(fd, write_buf, SIZE_OF_DATA);
#else
		ret = read(fd, read_buf, SIZE_OF_DATA);
#endif
		clock_gettime(CLOCK_REALTIME, &after);

		if(ret == SIZE_OF_DATA) {
			number_of_succesful_writes++;
			if((after.tv_nsec - before.tv_nsec) < 0)
				global_time += (after.tv_sec - before.tv_sec - 1)
						+ (after.tv_nsec - before.tv_nsec
								+ NANOSECONDS_PER_SECOND)
								* CLOCK_PRECISION;
			else
				global_time += (after.tv_sec - before.tv_sec)
						+ (after.tv_nsec - before.tv_nsec)
								* CLOCK_PRECISION;
		}

#if defined(WRITE_PERF_VERIFY) && defined(WRITE_PERF)
		clock_gettime(CLOCK_REALTIME, &before);
		ret = fsync(fd);
		clock_gettime(CLOCK_REALTIME, &after);

		if((after.tv_nsec - before.tv_nsec) < 0)
			global_time += (after.tv_sec - before.tv_sec - 1)
			+ (after.tv_nsec - before.tv_nsec
					+ NANOSECONDS_PER_SECOND)
					* CLOCK_PRECISION;
		else
			global_time += (after.tv_sec - before.tv_sec)
			+ (after.tv_nsec - before.tv_nsec)
			* CLOCK_PRECISION;
#endif

	}

	printf("For block size of %llu and %u repetitions :\n"
		"-----------------------\n", SIZE_OF_DATA, NUMBER_OF_REPETITIONS);
	printf("Average %s Latency is %lf Seconds\n",
			transaction_type,
			(global_time/number_of_succesful_writes));

	printf("%s bandwidth is %lf Mega-Bytes/s\n",
			transaction_type,
			((number_of_succesful_writes * SIZE_OF_DATA)/ global_time)/(1024*1024));

	free(write_buf);
	free(read_buf);

	close(fd);

	return 0;
}


