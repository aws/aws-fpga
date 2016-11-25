/*
 * Copyright 2016-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

/** @file
 * FPGA HAL register operations.
 */

#pragma once

#include <stdint.h>

#include <fpga_common.h>

/**
 * Initialize the platform.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_init(void);

/**
 * Platform layer attach using the given slot specification.
 *
 * @param[in]	spec	the slot specification to use.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_attach(struct fpga_slot_spec *spec);

/**
 * Platform layer detach using the given slot specification.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_detach(void);

/**
 * Platform layer register read.
 *
 * @param[in]		offset	the register offset	
 * @param[in,out]	value	the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_reg_read(uint32_t offset, uint32_t *value);

/**
 * Platform layer register write.
 *
 * @param[in]	offset	the register offset	
 * @param[in]	value	the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_reg_write(uint32_t offset, uint32_t value);
