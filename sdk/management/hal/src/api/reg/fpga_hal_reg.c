/*
 * Copyright 2016-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
