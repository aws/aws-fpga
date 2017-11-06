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

#pragma once

/** @file
 * Macros
 */

/*
 * build_assert_or_zero and sizeof_array are slightly adapted, public domain
 * helper macros from
 *	http://ccodearchive.net/info/array_size.html
 */

#define sizeof_array(arr) \
    (sizeof(arr) / sizeof(arr[0]))

/**
 * Return the maximum of two values
 *
 * @param[in]	a	First value
 * @param[in]	b	Second value
 *
 * @returns
 * The maximum of a and b
 */
#define max(a, b)                \
__extension__({                  \
	__typeof__(a) _a = (a); \
	__typeof__(b) _b = (b); \
	_a > _b ? _a : _b;       \
})

/**
 * Return the minimum of two values
 *
 * @param[in]	a	First value
 * @param[in]	b	Second value
 *
 * @returns
 * The minimum of a and b
 */
#define min(a, b)                \
__extension__({                  \
	__typeof__(a) _a = (a); \
	__typeof__(b) _b = (b); \
	_a < _b ? _a : _b;       \
})

/**
 * Swap the content of two variables, a, b = b, a in Python terms, and check
 * that types match.
 *
 * @param[in,out]  a  Pointer to the first variable.
 * @param[in,out]  b  Pointer to the Second variable.
 */
#define swap(a, b) \
	do { \
		(void)((a) == (b)); \
		typeof(*(a)) _tmp = *(a); \
		*(a) = *(b); \
		*(b) = _tmp; \
	} while (0)
