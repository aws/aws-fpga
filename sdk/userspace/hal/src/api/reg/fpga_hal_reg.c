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

/************************************************************************ 
 * Multi-device use, via the dev_index.
 ************************************************************************/

int 
fpga_hal_dev_reg_read(int dev_index, uint64_t offset, uint32_t *value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_read(dev_index, offset, value);
}

int 
fpga_hal_dev_reg_write(int dev_index, uint64_t offset, uint32_t value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_write(dev_index, offset, value);
}

int
fpga_hal_dev_reg_read64(int dev_index, uint64_t offset, uint64_t *value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_read64(dev_index, offset, value);
}

int
fpga_hal_dev_reg_write64(int dev_index, uint64_t offset, uint64_t value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_write64(dev_index, offset, value);
}

/************************************************************************ 
 * Single device attachment and use.
 * e.g. for applications that only attach to one FPGA at a time,
 * or for applications that separate FPGA access into separate worker
 * processes (e.g. for isolation).
 ************************************************************************/

int 
fpga_hal_reg_read(uint64_t offset, uint32_t *value)
{
	log_debug("enter");
	return fpga_plat_reg_read(offset, value);
}

int 
fpga_hal_reg_write(uint64_t offset, uint32_t value)
{
	log_debug("enter");
	return fpga_plat_reg_write(offset, value);
}
