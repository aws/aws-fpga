/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
		.tv_sec = ms / MS_PER_SECOND,
		.tv_nsec = (ms % MS_PER_SECOND) * NS_PER_MS
	};

	return clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL);
}
