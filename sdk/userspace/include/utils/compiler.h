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
 * Compiler macros.
 */

#pragma once

/** Attribute for aligned data structures and variables. */
#define __aligned(size) __attribute__((aligned(size)))

/** Attribute for packed data structures. */
#define __packed __attribute__((packed))

/** Attribute for non-returning functions. */
#define __noreturn __attribute__((noreturn))

/** Attribute for weak functions. */
#define __weak __attribute__((weak))

/** Attribute for printf-like functions. */
#define __printf(a, b) __attribute__((format(printf, a, b)))

/** Attribute for scanf-like functions. */
#define __scanf(a, b) __attribute__((format(scanf, a, b)))

/** Attribute for constructor functions */
#define __constructor __attribute__((constructor))
