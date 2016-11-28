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
 * Definitions
 */

#pragma once

#define KiB (1024UL)       /**< Kibibytes */
#define MiB (1024UL * KiB) /**< Mebibytes */
#define GiB (1024UL * MiB) /**< Gibibytes */

#define MS_PER_SECOND (1000ULL)                 /**< Milliseconds in a second */
#define US_PER_SECOND (1000ULL * MS_PER_SECOND) /**< Microseconds in a second */
#define NS_PER_SECOND (1000ULL * US_PER_SECOND) /**< Nanoseconds in a second  */

#define US_PER_MS (1000ULL)                 /**< Microseconds in a Millisec   */
#define NS_PER_MS (1000ULL * US_PER_MS)     /**< Nanoseconds in a Millisec    */

#define NS_PER_US (1000ULL)                 /**< Nanoseconds in a Microsecond */
