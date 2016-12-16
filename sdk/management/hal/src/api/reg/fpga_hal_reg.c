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
 * FPGA HAL register operations.
 */

#include <errno.h>

#include <fpga_hal_reg.h>
#include <fpga_hal_plat.h>
#include <lcd.h>

int 
fpga_hal_reg_read(uint32_t offset, uint32_t *value)
{
	log_debug("enter");
	return fpga_plat_reg_read(offset, value);
}

int 
fpga_hal_reg_write(uint32_t offset, uint32_t value)
{
	log_debug("enter");
	return fpga_plat_reg_write(offset, value);
}
