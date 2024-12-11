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

#include "hbm_fmodel_shared_memory.h"
#include <sys/stat.h>
#include <sstream>

std::map<std::string, std::tuple<uint64_t, void*, int> > hbm_fmodel_shared_memory::mFileFdMap;

hbm_fmodel_shared_memory::hbm_fmodel_shared_memory(
		std::string p_module_name,
		xsc::common_cpp::report_handler* report_handler, uint64_t addr_size) : //Mode 0
		hbm_fmodel_base(p_module_name, report_handler, addr_size) {
	m_report_handler = report_handler;
	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		std::stringstream m_ss;
		m_ss.str("");
		m_ss << module_name << std::endl;
		XSC_REPORT_INFO((*m_report_handler), "xtlmmemorymodel_shared_memory",
				m_ss.str().c_str());
	}
}

void hbm_fmodel_shared_memory::reset_fmodel() {
	auto pageIt = mPageCache.begin();
	auto pageEnd = mPageCache.end();
	while (pageIt != pageEnd) {
		uint64_t offset = (*pageIt).first;

		auto itr = mOffsetFileMap.find(offset);
		int fd = -1;
		if (itr != mOffsetFileMap.end()) {
			std::string sFileName = (*itr).second;
			auto itr2 = mFileFdMap.find(sFileName);
			if (itr2 != mFileFdMap.end()) {
				fd = std::get<0>((*itr2).second);
				void* pPtr = std::get<1>((*itr2).second);
				int size = std::get<2>((*itr2).second);
				munmap(pPtr, size);
				mFileFdMap.erase(itr2);
				close(fd);
			}
		}
		pageIt++;
	}

}
hbm_fmodel_shared_memory::~hbm_fmodel_shared_memory() {
}

unsigned int hbm_fmodel_shared_memory::writeDevMem(uint64_t offset,
		void* src, unsigned int size) {

	uint64_t written_bytes = 0;
	uint64_t addr = offset;
	while (written_bytes < size) {
		uint64_t src_offset = written_bytes;

		std::string p2pFileName("");
		unsigned char* page_ptr = get_page(addr, p2pFileName);
		uint64_t ddrAddress = getBaseDdrAddress(addr);
		if (!page_ptr) {
		std::stringstream errMsg;
		errMsg
				<< "Kernel attempting to write to memory which was never allocated ("
				<< std::hex << "0x" << offset << ")" << std::dec;
		XSC_REPORT_INFO((*m_report_handler),
				"xtlmsimplememorymodel_shared_memory",
					errMsg.str().c_str());
		return 0;
		}
		unsigned char* dest_buf_ptr = page_ptr + offset - ddrAddress;
		unsigned char* src_buf_ptr = (unsigned char*) (src) + src_offset;

		uint64_t remaining_bytes_to_write = size - written_bytes;
		//memcpy(dest_buf_ptr,src_buf_ptr,buf_size);
		for (unsigned int i = 0; i < remaining_bytes_to_write; i++) {
			dest_buf_ptr[i] = src_buf_ptr[i];
		}

		written_bytes += remaining_bytes_to_write;
		addr += remaining_bytes_to_write;
	}

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		std::stringstream m_ss;
		m_ss.str("");
		m_ss << "Write Operation size : " << size << std::endl;
		for (int i = 0; i < size; i++) {
			m_ss << std::hex << (unsigned int) (((unsigned char*) src)[i])
					<< " ";
		}
		m_ss << std::endl;
		m_ss << "Write : " << "Offset --> " << offset << std::endl;
		XSC_REPORT_INFO((*m_report_handler), "xtlmmemorymodel_shared_memory",
				m_ss.str().c_str());
	}
	return 0;
}

unsigned int hbm_fmodel_shared_memory::readDevMem(uint64_t offset,
		void* dest, unsigned int size) {
	uint64_t read_bytes = 0;
	uint64_t addr = offset;
	while (read_bytes < size) {
		uint64_t dest_offset = read_bytes;

		std::string p2pFileName("");
		unsigned char* page_ptr = get_page(addr, p2pFileName);
		uint64_t ddrAddress = getBaseDdrAddress(addr);

   if (!page_ptr) {
		if (m_report_handler->get_verbosity_level()
				== xsc::common_cpp::VERBOSITY::DEBUG) {
				std::stringstream errMsg;
				errMsg
						<< "Kernel attempting to read to memory which was never allocated ("
						<< std::hex << "0x" << offset << ")" << std::dec;
				XSC_REPORT_INFO((*m_report_handler),
						"xtlmsimplememorymodel_shared_memory",
						errMsg.str().c_str());
			}
			return 0;
		}

		unsigned char* src_buf_ptr = page_ptr + (offset - ddrAddress);
		unsigned char* dest_buf_ptr = (unsigned char*) (dest) + dest_offset;

		uint64_t remaining_bytes_to_read = size - read_bytes;

		for (uint64_t i = 0; i < remaining_bytes_to_read; i++) {
			dest_buf_ptr[i] = src_buf_ptr[i];
		}

		read_bytes += remaining_bytes_to_read;
		addr += remaining_bytes_to_read;
	}

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		std::stringstream m_ss;
		m_ss.str("");
		m_ss << "Read Operation size : " << size << std::endl;
		for (int i = 0; i < size; i++) {
			m_ss << std::hex << (unsigned int) (((unsigned char*) dest)[i])
					<< " ";
		}
		m_ss << std::endl;
		m_ss << "Read : " << "Offset --> " << offset << std::endl;
		XSC_REPORT_INFO((*m_report_handler),
				"hbm_shared_memory", m_ss.str().c_str());
	}

	return 0;
}

unsigned char* hbm_fmodel_shared_memory::get_page(uint64_t offset,
		std::string& p2pFileName, uint64_t size) {
	auto pageIt = mPageCache.begin();
	auto pageEnd = mPageCache.end();
	while (pageIt != pageEnd) {
		uint64_t startAddress = (*pageIt).first;
		std::pair<unsigned char*, uint64_t> addressSizePair = (*pageIt).second;
		unsigned char* pageStartOSAddress = addressSizePair.first;
		uint64_t pageSize = addressSizePair.second;
		if (offset >= startAddress && offset < startAddress + pageSize) {
			return pageStartOSAddress;
		}
		pageIt++;
	}
	//in partial reconfiguration case, we should read the file which is stored.

	return NULL;

}

uint64_t hbm_fmodel_shared_memory::getBaseDdrAddress(uint64_t offset) {
	auto pageIt = mPageCache.begin();
	auto pageEnd = mPageCache.end();
	while (pageIt != pageEnd) {
		uint64_t startAddress = (*pageIt).first;
		std::pair<unsigned char*, uint64_t> addressSizePair = (*pageIt).second;
		uint64_t pageSize = addressSizePair.second;
		if (offset >= startAddress && offset < startAddress + pageSize) {
			return startAddress;
		}
		pageIt++;
	}

	return 0;
}

bool hbm_fmodel_shared_memory::copyBO(uint64_t offset,
		std::string dst_filename, uint64_t size, uint64_t src_offset,
		uint64_t dst_offset) {
	uint64_t read_bytes = 0;
	uint64_t addr = offset;
	std::string p2pFileName("");
	unsigned char* page_ptr = get_page(addr, p2pFileName);
	uint64_t ddrAddress = getBaseDdrAddress(addr);
	unsigned char* src_buf_ptr = (unsigned char*) (page_ptr
			+ (offset - ddrAddress) + src_offset);
	auto itr = mFileFdMap.find(dst_filename);
	if (itr != mFileFdMap.end()) {
		int dst_fd = std::get<0>((*itr).second);
		if (lseek(dst_fd, dst_offset, SEEK_CUR) < 0)
			return false;
		int bytes_written = write(dst_fd, src_buf_ptr,
				size/*strlen(src_buf_ptr)*/);
		if (bytes_written < 0) {
			std::cout << "Failed to write into file " << dst_fd << std::endl;
		} else {
			std::cout << "bytes_written is " << bytes_written
					<< " is successful " << std::endl;
		}

	}
	return true;
}

bool hbm_fmodel_shared_memory::importBO(uint64_t offset,
		std::string sFileName, uint64_t size) {
	int fd = -1;
	if ((fd = open(sFileName.c_str(), O_CREAT | O_RDWR,
	S_IRWXU | S_IRGRP | S_IROTH)) == -1) {
		printf("Error opening file.\n");
	};
	if (fd < 0)
		return false;
	void* pageStartOSAddressVoid = mmap(0, size,
	PROT_READ | PROT_WRITE | PROT_EXEC, MAP_SHARED, fd,
			0/*sysconf(_SC_PAGESIZE)*/);
	if (ftruncate(fd, size) < 0) {
		close(fd);
		munmap(pageStartOSAddressVoid, size);
		return false;
	}
	mFileFdMap[sFileName] = std::make_tuple(fd, pageStartOSAddressVoid, size);
	mOffsetFileMap[offset] = sFileName;
  return true;
}

//create a page at offset. Return if already exist
std::string hbm_fmodel_shared_memory::createPage(uint64_t offset,
		uint64_t size, bool p2p) {
	std::string sFileName("");
	int fd = -1;
	auto pageIt = mPageCache.begin();
	auto pageEnd = mPageCache.end();
	while (pageIt != pageEnd) {
		uint64_t startAddress = (*pageIt).first;
		std::pair<unsigned char*, uint64_t> addressSizePair = (*pageIt).second;
		uint64_t pageSize = addressSizePair.second;
		if (offset >= startAddress && offset < startAddress + pageSize) {
			freePage(offset);
			//new offset is conflicting old addresses
			//return "";
		}
		pageIt++;
	}

	void* pageStartOSAddressVoid = NULL;
	// TODO:  DDR_BUFFER_ALIGNMENT   0x1000  (4096) this is declared in runtime shim.
	//  below variable is based on it.
	size_t alignmentForBuffer = 4096;  // previously sizeof(double) * 16

	if (!p2p) {
		if (posix_memalign(&pageStartOSAddressVoid, alignmentForBuffer, size)) {
			pageStartOSAddressVoid = NULL;
		}
	} else {
		std::stringstream ssFileName;
		sFileName = get_mem_file_name(offset);
		ssFileName << sFileName << "_shared";
		sFileName = ssFileName.str(); //config::getInstance()->getDeviceDirectory() + "/" + ssFileName.str();
		if ((fd = open(sFileName.c_str(), O_CREAT | O_RDWR,
		S_IRWXU | S_IRGRP | S_IROTH)) == -1) {
			printf("Error opening file.\n");
		}
		pageStartOSAddressVoid = mmap(0, size,
		PROT_READ | PROT_WRITE | PROT_EXEC, MAP_SHARED, fd,
				0/*sysconf(_SC_PAGESIZE)*/);
		if (fd < 0) {
			munmap(pageStartOSAddressVoid, size);
			return sFileName;
		}

		if (ftruncate(fd, size) < 0) {
			close(fd);
			munmap(pageStartOSAddressVoid, size);
			return sFileName;
		}
	}
	if (!pageStartOSAddressVoid) {
		close(fd);
		return sFileName;
	}

	if (!sFileName.empty()) {
		mFileFdMap[sFileName] = std::make_tuple(fd, pageStartOSAddressVoid,
				size);
		mOffsetFileMap[offset] = sFileName;
	}

	unsigned char* pageStartOSAddress = (unsigned char*) pageStartOSAddressVoid;
	mPageCache[offset] = std::make_pair(pageStartOSAddress, size);
	return sFileName;
}
//free page at offset. Return if already exist
bool hbm_fmodel_shared_memory::freePage(uint64_t offset) {
	bool mMappedBuffer = false;
	auto itr = mOffsetFileMap.find(offset);
	int fd = -1;

	if (itr != mOffsetFileMap.end()) {
		mMappedBuffer = true;
		std::string sFileName = (*itr).second;
		auto itr2 = mFileFdMap.find(sFileName);
		if (itr2 != mFileFdMap.end()) {
			fd = std::get<0>((*itr2).second);
			void* pPtr = std::get<1>((*itr2).second);
			int size = std::get<2>((*itr2).second);
			munmap(pPtr, size);
			mFileFdMap.erase(itr2);
		}
	}
	auto pageIt = mPageCache.find(offset);
	if (pageIt != mPageCache.end()) {
		std::pair<unsigned char*, uint64_t> addressSizePair = (*pageIt).second;
		unsigned char* osAddress = addressSizePair.first;
		uint64_t size = addressSizePair.second;
		if (osAddress) {
			if (!mMappedBuffer)
				free((void *) osAddress);
			else {
				munmap(osAddress, size);
				if (fd != -1) {
					close(fd);
				}
			}
		}
		mPageCache.erase(pageIt);
	}

	return true;
}

bool hbm_fmodel_shared_memory::createMMappedBuffer(
		uint64_t base_address, uint64_t size, std::string& buffer_filename) {
	buffer_filename = createPage(base_address, size, true);
	return true;
}

std::string hbm_fmodel_shared_memory::get_mem_file_name(
		uint64_t pageIdx)  //,enum fileType file_type)
		{
	std::string file_name;
	std::string socket_id;
	std::string pid;
	std::string deviceName("");
	std::string user("");
	if (getenv("EMULATION_SOCKETID")) {
		socket_id = getenv("EMULATION_SOCKETID");
		std::size_t foundLast = socket_id.find_last_of("_");
		std::size_t foundFirst = socket_id.find_first_of("_");
		if (foundLast != std::string::npos) {
			pid = socket_id.substr(foundLast + 1);
		}
		if (foundFirst != std::string::npos) {
			deviceName = socket_id.substr(0, foundFirst);
		}
	}

	if (getenv("USER") != NULL) {
		user = getenv("USER");
	}
	std::string file_path("");
	std::string sEmRunDir("");

	if (getenv("EMULATION_RUN_DIR")) {
		sEmRunDir = getenv("EMULATION_RUN_DIR");
	} else {
		sEmRunDir = "/tmp/" + user + "/hw_em/";
	}

	file_path = sEmRunDir + "/" + module_name + "/";
	std::stringstream mkdirCommand;
	mkdirCommand << "mkdir -p " << file_path;
	;
	struct stat statBuf;
	if (stat(file_path.c_str(), &statBuf) == -1) {
		system(mkdirCommand.str().c_str());
	}
	file_name = file_path + module_name + "_" + std::to_string(pageIdx);
	return file_name;
}

