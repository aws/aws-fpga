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
