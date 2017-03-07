/*
 * Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <utils/lcd.h>
#include <fpga_common.h>
#include <hal/fpga_hal_plat.h>
#include <hal/fpga_hal_reg.h>

#include <fpga_pci.h>

/** F1 Mailbox PF defines */
#define F1_MBOX_VENDOR_ID       0x1d0f
#define F1_MBOX_DEVICE_ID       0x1041
#define F1_MBOX_RESOURCE_NUM    0

/** F1 Application PF defines */
#define F1_APP_PF_START         0
#define F1_APP_PF_END           15

/** 
 * Generally, we allow a sanitized first level error to be displayed
 * for the user.  We do not want low-level mailbox related errors
 * to be displayed (since we are abstracting the mailbox interface).
 * The fail_on_quiet define allows the multi-level trace debug info
 * to still be displayed for development if needed, by re-defining
 * fail_on_quiet as fail_on.
 */
#define fail_on_quiet(CONDITION, LABEL, ...)    \
	do {					                    \
		if (CONDITION) {	                    \
			log_info(__VA_ARGS__);             \
			goto LABEL;		                    \
		}					                    \
	} while (0)

/** 
 * This should be used for the sanitized first level errors to be
 * displayed for the user.
 */
#define fail_on_user(CONDITION, LABEL, ...)	\
	do {							\
		if (CONDITION) {			\
			printf(__VA_ARGS__);	\
			printf("\n");			\
			goto LABEL;				\
		}							\
	} while (0)

/** 
 * This should be used for sanitized first level internal errors
 * to be displayed to the user.
 * We're only providing the line number and not the routine name
 * because we're abstracting the mailbox interface and all that
 * goes along with it.
 */
#define CLI_INTERNAL_ERR_STR "Error: Internal error "
#define fail_on_internal(CONDITION, LABEL, ...)	\
	do {										\
		if (CONDITION) {						\
			printf(__VA_ARGS__);				\
			printf("(line %u)\n", __LINE__);	\
			goto LABEL;							\
		}										\
	} while (0)
