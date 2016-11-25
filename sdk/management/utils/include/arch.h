/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

/** @file
 * x86 architecture macros.
 */

#pragma once

/** x86 page shift. */
#define PAGE_SHIFT 12

/** x86 page size. */
#define PAGE_SIZE (1UL << PAGE_SHIFT)

/** x86 page mask. */
#define PAGE_MASK (~(PAGE_SIZE - 1))

/** Round down to the memory page size. */
#define PAGE_ROUND_DOWN(value) ((value) & PAGE_MASK)

/** Round up to the memory page size. */
#define PAGE_ROUND_UP(value) PAGE_ROUND_DOWN((value) + PAGE_SIZE - 1)
