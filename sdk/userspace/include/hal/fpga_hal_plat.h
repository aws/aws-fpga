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

#include <fpga_common.h>

/**
 * FPGA_PLAT_DEVS_MAX:
 *  -compile time tunable, defaulted to 1.
 *  -set this to the max number of FPGA BARs that the application plans 
 *   to attach at any one time.
 *  -the upper limit is FPGA_SLOT_MAX * FPGA_BARS_MAX.
 *  -FPGA_SLOT_MAX is driven by the EC2 FPGA system design and instance type.
 *  -FPGA_BARS_MAX is driven by the FPGA Shell release.
 */
#if ! defined(FPGA_PLAT_DEVS_MAX)
#define FPGA_PLAT_DEVS_MAX	1
#endif

/*
 *  Notes on platform vs application locking:
 *
 *  Platform Locking:
 *  -attach/detach are protected via a pthread mutex to allow for use cases
 *   of multi-threaded attach/detach sequences vs calling attach/detach during
 *   one time process init/destroy.
 *
 *  Application Locking:
 *  -a single process may access all of the FPGAs via the dev_index(es) without 
 *   locking.
 *  -a single thread may access a single FPGA via the dev_index without locking.
 *  -multi-threaded access to the same FPGA must be done with locking within 
 *   the application.
 */

/**
 * Initialize the platform.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_init(void);

/************************************************************************ 
 * Multi-device attachment and use, via the dev_index.
 ************************************************************************/

/**
 * Platform layer attach using the given slot specification.
 *
 * @param[in]	spec		the slot specification to use.
 * @param[out]	dev_index	the attached fpga device index.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_dev_attach(struct fpga_slot_spec *spec, int *dev_index);

/**
 * Platform layer detach using the given slot specification.
 *
 * @param[in]	dev_index	the attached fpga device index.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_dev_detach(int dev_index);

/**
 * Platform layer register read.
 *
 * @param[in]		dev_index	the attached fpga device index.
 * @param[in]		offset		the register offset	
 * @param[in,out]	value		the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_dev_reg_read(int dev_index, uint64_t offset, uint32_t *value);

/**
 * Platform layer register write.
 *
 * @param[in]	dev_index	the attached fpga device index.
 * @param[in]	offset		the register offset	
 * @param[in]	value		the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_dev_reg_write(int dev_index, uint64_t offset, uint32_t value);

/**
 * Platform layer get mem base.
 *
 * @param[in]	dev_index	the attached fpga device index.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
void *fpga_plat_dev_get_mem_base(int dev_index);

/************************************************************************ 
 * Single device attachment and use.
 * e.g. for applications that only attach to one FPGA at a time,
 * or for applications that separate FPGA access into separate worker
 * processes (e.g. for isolation).
 ************************************************************************/

/**
 * Platform layer attach using the given slot specification.
 *
 * @param[in]	spec		the slot specification to use.
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
 * @param[in]		offset		the register offset	
 * @param[in,out]	value		the register value to return 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_reg_read(uint64_t offset, uint32_t *value);

/**
 * Platform layer register write.
 *
 * @param[in]	offset		the register offset	
 * @param[in]	value		the register value to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_plat_reg_write(uint64_t offset, uint32_t value);
