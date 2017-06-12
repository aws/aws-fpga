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
 * Least Common Denominator library.
 * Include all headers and define inline-functions.
 */

#pragma once

#include <sys/types.h>
#include <time.h>

#include "definitions.h"
#include "io.h"
#include "log.h"
#include "macros.h"

/** PCI device format string */
#define PCI_DEV_FMT "%04x:%02x:%02x.%d"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Sleep for some milliseconds.
 *
 * @param[in]	ms	Milliseconds to sleep
 *
 * @returns
 * whatever clock_nanosleep() returns
 */
static inline int msleep(uint64_t ms)
{
	struct timespec sleep_time = {
		.tv_sec = (time_t)(ms / MS_PER_SECOND),
		.tv_nsec = (long)((ms % MS_PER_SECOND) * NS_PER_MS)
	};

	return clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL);
}

#ifdef __cplusplus
}
#endif
