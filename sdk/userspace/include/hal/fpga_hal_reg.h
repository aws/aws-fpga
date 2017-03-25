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

#pragma once

#include <stdint.h>

/************************************************************************ 
 * Multi-device use, via the dev_index.
 ************************************************************************/

/**
 * FPGA HAL layer register read.
 *
 * @param[in]		dev_index	 the attached fpga device index.
 * @param[in]		offset		the register offset	
 * @param[in,out]	value		the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_dev_reg_read(int dev_index, uint64_t offset, uint32_t *value);

/**
 * FPGA HAL layer register write.
 *
 * @param[in]	dev_index	the attached fpga device index.
 * @param[in]	offset		the register offset	
 * @param[in]	value		the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_dev_reg_write(int dev_index, uint64_t offset, uint32_t value);

/**
 * FPGA HAL layer register read.
 *
 * @param[in]		dev_index	 the attached fpga device index.
 * @param[in]		offset		the register offset
 * @param[in,out]	value		the register value to return
 *
 * @returns
 * 0 on success
 * -1 on failure
 */
int fpga_hal_dev_reg_read64(int dev_index, uint64_t offset, uint64_t *value);

/**
 * FPGA HAL layer register write.
 *
 * @param[in]	dev_index	the attached fpga device index.
 * @param[in]	offset		the register offset
 * @param[in]	value		the register value to write
 *
 * @returns
 * 0 on success
 * -1 on failure
 */
int fpga_hal_dev_reg_write64(int dev_index, uint64_t offset, uint64_t value);

/************************************************************************ 
 * Single device attachment and use.
 * e.g. for applications that only attach to one FPGA at a time,
 * or for applications that separate FPGA access into separate worker
 * processes (e.g. for isolation).
 ************************************************************************/

/**
 * FPGA HAL layer register read.
 *
 * @param[in]		offset		the register offset	
 * @param[in,out]	value		the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_reg_read(uint64_t offset, uint32_t *value);

/**
 * FPGA HAL layer register write.
 *
 * @param[in]	offset		the register offset	
 * @param[in]	value		the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_reg_write(uint64_t offset, uint32_t value);
