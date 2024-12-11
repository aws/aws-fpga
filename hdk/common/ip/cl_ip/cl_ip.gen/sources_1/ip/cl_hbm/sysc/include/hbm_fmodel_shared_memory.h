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

#ifndef HBM_FMODEL_SHARED_MEMORY__H 
#define HBM_FMODEL_SHARED_MEMORY__H

#include "hbm_fmodel_base.h"
#include "report_handler.h"

class hbm_fmodel_shared_memory: public hbm_fmodel_base {
public:
	unsigned int writeDevMem(uint64_t offset, void* src, unsigned int size);
	unsigned int readDevMem(uint64_t offset, void* dest, unsigned int size);
	bool createMMappedBuffer(uint64_t base_address, uint64_t size,
			std::string& buffer_filename);
	unsigned char* get_page(uint64_t offset, std::string& p2pFileName,
			uint64_t size = 0);
	uint64_t getBaseDdrAddress(uint64_t offset); //get the DDR base address of offset
	bool copyBO(uint64_t offset, std::string dst_filename, uint64_t size,
			uint64_t src_offset, uint64_t dst_offset);
	bool importBO(uint64_t offset, std::string dst_filename, uint64_t size);
	std::string createPage(uint64_t offset, uint64_t size, bool p2p); //create a page of size "size" and add it in mPageCache Map.
	bool freePage(uint64_t offset); //free page and remove it from mPageCache Map.
	std::string get_mem_file_name(uint64_t pageIdx);

public:
	hbm_fmodel_shared_memory(std::string p_module_name,
			xsc::common_cpp::report_handler* report_handler,
			uint64_t addr_size);
	~ hbm_fmodel_shared_memory();
	void reset_fmodel();
private:
	//Paging
	std::map<uint64_t, std::pair<unsigned char*, uint64_t> > mPageCache; // this map is used to store ddrAddress and OsAddress Mapping.
	static std::map<std::string, std::tuple<uint64_t, void*, int> > mFileFdMap; //filename and fd map
	std::map<uint64_t, std::string> mOffsetFileMap; //offset and filename map
	xsc::common_cpp::report_handler *m_report_handler;

};

#endif

