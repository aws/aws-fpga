/*
 * Copyright 2016-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

/** @file
 * FPGA HAL register operations.
 */

#pragma once

#include <stdint.h>

/**
 * FPGA HAL layer register read.
 *
 * @param[in]		offset	the register offset	
 * @param[in,out]	value	the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_reg_read(uint32_t offset, uint32_t *value);

/**
 * FPGA HAL layer register write.
 *
 * @param[in]	offset	the register offset	
 * @param[in]	value	the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_reg_write(uint32_t offset, uint32_t value);
