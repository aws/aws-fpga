/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <errno.h>

#include <fpga_pci.h>

#include <utils/lcd.h>

/** Application PF defines */
#define FPGA_CHECK_APP_PF_DELAY_MSEC		1000
#define FPGA_CHECK_APP_PF_MAX_RETRIES		3
#define FPGA_REMOVE_APP_PF_SHORT_DELAY_MSEC	500
#define FPGA_REMOVE_APP_PF_LONG_DELAY_MSEC	3000
