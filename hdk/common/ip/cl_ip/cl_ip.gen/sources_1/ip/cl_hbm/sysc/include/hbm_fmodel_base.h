// (c) Copyright 1995-2021, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////

#ifndef HBM_FMODEL_BASE__H 
#define HBM_FMODEL_BASE__H
#include <math.h>
#include <iostream>

#include <string.h> // memcpy
#include <stdlib.h> //realloc
#include <stdint.h>
#include <vector>
#include <map> //realloc
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include "report_handler.h"

#define ONE_KB (0x400)
#define ONE_MB (ONE_KB * ONE_KB)
#define PAGESIZE (ONE_MB)
#define ADDRBITS (20)
#define N_1MBARRAYS 4096

class hbm_fmodel_base {
public:
	virtual unsigned int writeDevMem(uint64_t offset, void* src,
			unsigned int size) = 0;
	virtual unsigned int readDevMem(uint64_t offset, void* dest,
			unsigned int size) = 0;
	virtual bool createMMappedBuffer(uint64_t base_address, uint64_t size,
			std::string& buffer_filename) = 0;
	virtual bool freePage(uint64_t base_address) = 0;
	virtual unsigned char* get_page(uint64_t offset, std::string& p2pFileName,
			uint64_t size = 0) = 0;
	virtual bool copyBO(uint64_t offset, std::string dst_filename,
			uint64_t size, uint64_t src_offset, uint64_t dst_offset) = 0;
	virtual bool importBO(uint64_t offset, std::string dst_filename,
			uint64_t size) = 0;
	hbm_fmodel_base(std::string p_module_name,
			xsc::common_cpp::report_handler* report_handler,
			uint64_t addr_size);
	virtual ~ hbm_fmodel_base();
	void init_fmodel();
	virtual void reset_fmodel() = 0;
	std::string module_name;
};

#endif

