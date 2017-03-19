/*
 * Copyright (C) 2017 Xilinx, Inc
 * Author: Sonal Santan
 * AWS HAL Driver for SDAccel/OpenCL runtime evnrionemnt, for AWS EC2 F1
 *
 * Code copied from SDAccel XDMA based HAL driver
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

#include "shim.h"
#include "memorymanager.h"
#include "datamover.h"
#include <errno.h>
/*
 * Define GCC version macro so we can use newer C++11 features
 * if possible
 */
#define GCC_VERSION (__GNUC__ * 10000 \
                     + __GNUC_MINOR__ * 100 \
                     + __GNUC_PATCHLEVEL__)

//TODO: umang
#ifdef INTERNAL_TESTING
#define ACCELERATOR_BAR        0
#define MMAP_SIZE_USER         0x400000
#endif

/* Aligning access to FPGA DRAM space to 64Byte */
#define DDR_BUFFER_ALIGNMENT   0x40

#include <sys/types.h>
#include <sys/mman.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/file.h>

#include <cstdio>
#include <cstring>
#include <cassert>
#include <algorithm>
#include <stdlib.h>
#include <thread>
#include <chrono>
#include <iostream>
#include <mutex>

#include "xclbin.h"

#ifdef INTERNAL_TESTING
#include "xdma/include/xdma-ioctl.h"
#include "baremetal/mgmt/mgmt-ioctl.h"
#else

#include <fpga_mgmt.h>
#include <fpga_pci.h>

// TODO - define this in a header file
extern char* get_afi_from_xclBin(const xclBin *);

#endif

namespace awsbwhal {
    const unsigned AwsXcl::TAG = 0X586C0C6C; // XL OpenCL X->58(ASCII), L->6C(ASCII), O->0 C->C L->6C(ASCII);

    int AwsXcl::xclLoadXclBin(const xclBin *buffer)
    {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buffer << std::endl;
        }

        if (!mLocked)
            return -EPERM;

#ifdef INTERNAL_TESTING
        const unsigned cmd = AWSMGMT_IOCICAPDOWNLOAD;
        awsmgmt_ioc_bitstream obj = {const_cast<xclBin *>(buffer)};
        return ioctl(mMgtHandle, cmd, &obj);
#else
	char* afi_id = get_afi_from_xclBin(buffer);
	int ret=0;
	return fpga_mgmt_load_local_image(mBoardNumber, afi_id);
	// TODO - add printout and eror case handing
#endif
    }

    /* Accessing F1 FPGA memory space (i.e. OpenCL Global Memory) is mapped through AppPF BAR4
     * all offsets are relative to the base address available in AppPF BAR4
     * SDAcell XCL_ADDR_SPACE_DEVICE_RAM enum maps to AwsXcl::ocl_global_mem_bar, which is the
     * handle for AppPF BAR4
     */
    size_t AwsXcl::xclReadModifyWrite(uint64_t offset, const void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }
#if GCC_VERSION >= 40800
        alignas(DDR_BUFFER_ALIGNMENT) char buffer[DDR_BUFFER_ALIGNMENT];
#else
        AlignedAllocator<char> alignedBuffer(DDR_BUFFER_ALIGNMENT, DDR_BUFFER_ALIGNMENT);
        char* buffer = alignedBuffer.getBuffer();
#endif

        const size_t mod_size = offset % DDR_BUFFER_ALIGNMENT;
        // Read back one full aligned block starting from preceding aligned address
        const uint64_t mod_offset = offset - mod_size;
        if (xclRead(XCL_ADDR_SPACE_DEVICE_RAM, mod_offset, buffer, DDR_BUFFER_ALIGNMENT) != DDR_BUFFER_ALIGNMENT)
            return -1;

        // Update the local copy of buffer with user requested data
        const size_t copy_size = (size + mod_size > DDR_BUFFER_ALIGNMENT) ? DDR_BUFFER_ALIGNMENT - mod_size : size;
        std::memcpy(buffer + mod_size, hostBuf, copy_size);

        // Write back the updated aligned block
        if (xclWrite(XCL_ADDR_SPACE_DEVICE_RAM, mod_offset, buffer, DDR_BUFFER_ALIGNMENT) != DDR_BUFFER_ALIGNMENT)
            return -1;

        // Write any remaining blocks over DDR_BUFFER_ALIGNMENT size
        if (size + mod_size > DDR_BUFFER_ALIGNMENT) {
            size_t write_size = xclWrite(XCL_ADDR_SPACE_DEVICE_RAM, mod_offset + DDR_BUFFER_ALIGNMENT,
                                         (const char *)hostBuf + copy_size, size - copy_size);
            if (write_size != (size - copy_size))
                return -1;
        }
        return size;
    }

    /* Accessing F1 FPGA memory space mapped through AppPF PCIe BARs
    * space = XCL_ADDR_SPACE_DEVICE_RAM maps to AppPF PCIe BAR4, (sh_cl_dma_pcis_ bus), with AwsXcl::ocl_global_mem_bar as handle
    * space = XCL_ADDR_KERNEL_CTRL maps to AppPF PCIe BAR0 (sh_cl_ocl bus), with AwsXcl::ocl_kernel_bar as handle
    * all offsets are relative to the base address available in AppPF
    */
    size_t AwsXcl::xclWrite(xclAddressSpace space, uint64_t offset, const void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << space << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }

        if (!mLocked)
            return -1;

        switch (space) {
        case XCL_ADDR_SPACE_DEVICE_RAM:
        {
            const size_t totalSize = size;
            const size_t mod_size1 = offset % DDR_BUFFER_ALIGNMENT;
            const size_t mod_size2 = size % DDR_BUFFER_ALIGNMENT;
            if (mod_size1) {
                // Buffer not aligned at DDR_BUFFER_ALIGNMENT boundary, need to do Read-Modify-Write
                return xclReadModifyWrite(offset, hostBuf, size);
            }
            else if (mod_size2) {
                // Buffer not a multiple of DDR_BUFFER_ALIGNMENT, write out the initial block and
                // then perform a Read-Modify-Write for the remainder buffer
                const size_t blockSize = size - mod_size2;
                if (xclWrite(space, offset, hostBuf, blockSize) != blockSize)
                    return -1;
                offset += blockSize;
                hostBuf = (const char *)hostBuf + blockSize;
                if (xclReadModifyWrite(offset, hostBuf, mod_size2) != mod_size2)
                    return -1;
                return totalSize;
            }

            const char *curr = static_cast<const char *>(hostBuf);
            while (size > maxDMASize) {
              if (mDataMover->pwrite64(curr,maxDMASize,offset) < 0)
                return -1;
              offset += maxDMASize;
                curr += maxDMASize;
                size -= maxDMASize;
            }
            if (mDataMover->pwrite64(curr,size,offset) < 0)
              return -1;
            return totalSize;
        }

        /* Initial release does not include SDAcce performance monitors */
//        case XCL_ADDR_SPACE_DEVICE_PERFMON:
//        {
//            if (pcieBarWrite(PERFMON_BAR, offset, hostBuf, size) == 0) {
//                return size;
//            }
//            return -1;
//        }
        case XCL_ADDR_KERNEL_CTRL:
        {
            if (mLogStream.is_open()) {
                const unsigned *reg = static_cast<const unsigned *>(hostBuf);
                size_t regSize = size / 4;
                if (regSize > 32)
                    regSize = 32;
                for (unsigned i = 0; i < regSize; i++) {
                    mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << space << ", 0x"
                               << std::hex << offset + i << std::dec << ", 0x" << std::hex << reg[i] << std::dec << std::endl;

                }
            }
#ifdef INTERNAL_TESTING
            if (pcieBarWrite(ACCELERATOR_BAR, offset, hostBuf, size) == 0) {
#else
            if (pcieBarWrite(APP_PF_BAR0, offset, hostBuf, size) == 0) {

#endif
                return size;
            }
            return -1;
        }
        default:
        {
            return -1;
        }
        }
    }


    size_t AwsXcl::xclReadSkipCopy(uint64_t offset, void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }

        const size_t mod_size = offset % DDR_BUFFER_ALIGNMENT;
        // Need to do Read-Modify-Read
// TODO: Windows build support
//    alignas is defined in c++11
#if GCC_VERSION >= 40800
        alignas(DDR_BUFFER_ALIGNMENT) char buffer[DDR_BUFFER_ALIGNMENT];
#else
        AlignedAllocator<char> alignedBuffer(DDR_BUFFER_ALIGNMENT, DDR_BUFFER_ALIGNMENT);
        char* buffer = alignedBuffer.getBuffer();
#endif

        // Read back one full aligned block starting from preceding aligned address
        const uint64_t mod_offset = offset - mod_size;
        if (xclRead(XCL_ADDR_SPACE_DEVICE_RAM, mod_offset, buffer, DDR_BUFFER_ALIGNMENT) != DDR_BUFFER_ALIGNMENT)
            return -1;

        const size_t copy_size = (size + mod_size > DDR_BUFFER_ALIGNMENT) ? DDR_BUFFER_ALIGNMENT - mod_size : size;

        // Update the user buffer with partial read
        std::memcpy(hostBuf, buffer + mod_size, copy_size);

        // Update the remainder of user buffer
        if (size + mod_size > DDR_BUFFER_ALIGNMENT) {
            const size_t read_size = xclRead(XCL_ADDR_SPACE_DEVICE_RAM, mod_offset + DDR_BUFFER_ALIGNMENT,
                                             (char *)hostBuf + copy_size, size - copy_size);
            if (read_size != (size - copy_size))
                return -1;
        }
        return size;
    }

    size_t AwsXcl::xclRead(xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << space << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }

        switch (space) {
        case XCL_ADDR_SPACE_DEVICE_RAM:
        {
            const size_t mod_size1 = offset % DDR_BUFFER_ALIGNMENT;
            const size_t mod_size2 = size % DDR_BUFFER_ALIGNMENT;
            const size_t totalSize = size;

//            if(!mLocked)
//              return -1;

            if (mod_size1) {
                // Buffer not aligned at DDR_BUFFER_ALIGNMENT boundary, need to do Read-Skip-Copy
                return xclReadSkipCopy(offset, hostBuf, size);
            }
            else if (mod_size2) {
                // Buffer not a multiple of DDR_BUFFER_ALIGNMENT, read the initial block and
                // then perform a Read-Skip-Copy for the remainder buffer
                const size_t blockSize = size - mod_size2;
                if (xclRead(space, offset, hostBuf, blockSize) != blockSize)
                    return -1;
                offset += blockSize;
                hostBuf = (char *)hostBuf + blockSize;
                if (xclReadSkipCopy(offset, hostBuf, mod_size2) != mod_size2)
                    return -1;
                return totalSize;
            }

            char *curr = static_cast<char*>(hostBuf);
            while (size > maxDMASize) {
// TODO: Windows build support
              if (mDataMover->pread64(curr,maxDMASize,offset) < 0)
                return -1;
                offset += maxDMASize;
                curr += maxDMASize;
                size -= maxDMASize;
            }

// TODO: Windows build support
            if (mDataMover->pread64(curr,size,offset) < 0)
              return -1;
            return totalSize;
        }
//        case XCL_ADDR_SPACE_DEVICE_PERFMON:
//        {
//            if (pcieBarRead(PERFMON_BAR, offset, hostBuf, size) == 0) {
//                return size;
//            }
//            return -1;
//        }
        case XCL_ADDR_KERNEL_CTRL:
        {
#ifdef	INTERNAL_TESTING
            int result = pcieBarRead(ACCELERATOR_BAR, offset, hostBuf, size);
#else
	    int result = pcieBarRead(APP_PF_BAR0, offset, hostBuf, size);
#endif
            if (mLogStream.is_open()) {
                const unsigned *reg = static_cast<const unsigned *>(hostBuf);
                size_t regSize = size / 4;
                if (regSize > 4)
                    regSize = 4;
                for (unsigned i = 0; i < regSize; i++) {
                    mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << space << ", 0x"
                               << std::hex << offset + i << std::dec << ", 0x" << std::hex << reg[i] << std::dec << std::endl;
                }
            }
            return !result ? size : 0;
        }
        default:
        {
            return -1;
        }
        }
    }

    uint64_t AwsXcl::xclAllocDeviceBuffer(size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << size << std::endl;
        }

        if (size == 0)
            size = DDR_BUFFER_ALIGNMENT;

        uint64_t result = MemoryManager::mNull;
        for (auto i : mDDRMemoryManager) {
            result = i->alloc(size);
            if (result != MemoryManager::mNull)
                break;
        }
        return result;
    }

    uint64_t AwsXcl::xclAllocDeviceBuffer2(size_t size, xclMemoryDomains domain, unsigned flags)
    {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << size << ", "
                       << domain << ", " << flags << std::endl;
        }

        if (domain != XCL_MEM_DEVICE_RAM)
            return MemoryManager::mNull;

        if (size == 0)
            size = DDR_BUFFER_ALIGNMENT;

        if (flags >= mDDRMemoryManager.size()) {
            return MemoryManager::mNull;
        }
        return mDDRMemoryManager[flags]->alloc(size);
    }

    void AwsXcl::xclFreeDeviceBuffer(uint64_t buf) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buf << std::endl;
        }

        uint64_t size = 0;
        for (auto i : mDDRMemoryManager) {
            size += i->size();
            if (buf < size) {
                i->free(buf);
            }
        }
    }


    size_t AwsXcl::xclCopyBufferHost2Device(uint64_t dest, const void *src, size_t size, size_t seek) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << dest << ", "
                       << src << ", " << size << ", " << seek << std::endl;
        }

#ifdef DEBUG
        {
            // Ensure that this buffer was allocated by memory manager before
            const uint64_t v = MemoryManager::mNull;
            std::pair<uint64_t, uint64_t> buf = std::make_pair(v, v);
            uint64_t high = 0;
            for (auto i : mDDRMemoryManager) {
                high += i->size();
                if (dest < high) {
                    buf = i->lookup(dest);
                    break;
                }
            }
            if (MemoryManager::isNullAlloc(buf))
                return -1;

            if (buf.second < (size + seek))
                return -1;
        }
#endif
        dest += seek;
        return xclWrite(XCL_ADDR_SPACE_DEVICE_RAM, dest, src, size);
    }


    size_t AwsXcl::xclCopyBufferDevice2Host(void *dest, uint64_t src, size_t size, size_t skip) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << dest << ", "
                       << src << ", " << size << ", " << skip << std::endl;
        }


#ifdef DEBUG
        {
            // Ensure that this buffer was allocated by memory manager before
            const uint64_t v = MemoryManager::mNull;
            std::pair<uint64_t, uint64_t> buf = std::make_pair(v, v);
            uint64_t high = 0;
            for (auto i : mDDRMemoryManager) {
                high += i->size();
                if (src < high) {
                    buf = i->lookup(src);
                    break;
                }
            }
            if (MemoryManager::isNullAlloc(buf))
                return -1;

            if (buf.second < (size + skip))
                return -1;
        }
#endif
        src += skip;
        return xclRead(XCL_ADDR_SPACE_DEVICE_RAM, src, dest, size);
    }


    AwsXcl *AwsXcl::handleCheck(void *handle) {
        // Sanity checks
        if (!handle)
            return 0;
        if (*(unsigned *)handle != TAG)
            return 0;
        if (!((AwsXcl *)handle)->isGood()) {
            return 0;
        }

        return (AwsXcl *)handle;
    }

    unsigned AwsXcl::xclProbe() {
        char file_name_buf[128];
        unsigned i  = 0;
        for (i = 0; i < 16; i++) {
#ifdef INTERNAL_TESTING
            std::sprintf((char *)&file_name_buf, "/dev/awsmgmt%d", i);
#else
            std::sprintf((char *)&file_name_buf, "/dev/edma%u_queue0", i);
#endif
            int fd = open(file_name_buf, O_RDWR);
            if (fd < 0) {
                return i;
            }
            close(fd);
        }
#ifndef INTERNAL_TESTING
	if (fpga_mgmt_init() || fpga_pci_init() ) {
            std::cout << "xclProbe failed to initialized fpga libraries" << std::endl;
            return 0;
	}
        std::cout << "xclProbe found " << i << "FPGA slots with EDMA driver running" << std::endl;
#else
        std::cout << "xclProbe found " << i << "FPGA slots with baremetal driver running" << std::endl;
#endif
        return i;
    }

    void AwsXcl::initMemoryManager()
    {
        if (!mDeviceInfo.mDDRBankCount)
            return;
        const uint64_t bankSize = mDeviceInfo.mDDRSize / mDeviceInfo.mDDRBankCount;
        uint64_t start = 0x0;
        for (unsigned i = 0; i < mDeviceInfo.mDDRBankCount; i++) {
            mDDRMemoryManager.push_back(new MemoryManager(bankSize, start, DDR_BUFFER_ALIGNMENT));
            start += bankSize;
        }
    }

    AwsXcl::~AwsXcl()
    {
#ifdef INTERNAL_TESTING
        if (mUserMap != MAP_FAILED) {
            munmap(mUserMap, MMAP_SIZE_USER);
        }
        if (mUserHandle > 0) {
            close(mUserHandle);
        }
        if (mMgtHandle > 0)
            close(mMgtHandle);
#else
//#       error "INTERNAL_TESTING macro disabled. AMZN code goes here. "
	if (ocl_kernel_bar >=0)
		fpga_pci_detach(ocl_kernel_bar);
	if (ocl_global_mem_bar>=0)
		fpga_pci_detach(ocl_global_mem_bar);
	if (sda_mgmt_bar>=0)
		fpga_pci_detach(sda_mgmt_bar);

	ocl_kernel_bar = -1;
	ocl_global_mem_bar = -1;
	sda_mgmt_bar = -1;

#endif
	delete mDataMover;

        for (auto i : mDDRMemoryManager) {
            delete i;
        }

        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << std::endl;
            mLogStream.close();
        }
    }

    AwsXcl::AwsXcl(unsigned index, const char *logfileName,
                       xclVerbosityLevel verbosity) : mTag(TAG), mBoardNumber(index),
                                                      maxDMASize(0xfa0000),
                                                      mLocked(false),
                                                      mOffsets{0x0, 0x0, 0x0, 0x0},
                                                      mOclRegionProfilingNumberSlots(XPAR_AXI_PERF_MON_2_NUMBER_SLOTS)
    {
        int slot_id = mBoardNumber;
        mDataMover = new DataMover(mBoardNumber, 1 /* 1 channel each dir */);
// FIXME: need to revisit and change number of channels

#ifdef INTERNAL_TESTING
        char file_name_buf[128];
        std::sprintf((char *)&file_name_buf, "/dev/xdma%d_user", mBoardNumber);
        mUserHandle = open(file_name_buf, O_RDWR | O_SYNC);
        mUserMap = (char *)mmap(0, MMAP_SIZE_USER, PROT_READ | PROT_WRITE, MAP_SHARED, mUserHandle, 0);
        if (mUserMap == MAP_FAILED) {
            close(mUserHandle);
            mUserHandle = -1;
        }

        std::string s = "u.log";
        logfileName = s.c_str();
        if (logfileName && (logfileName[0] != '\0')) {
            mLogStream.open(logfileName);
            mLogStream << "FUNCTION, THREAD ID, ARG..."  << std::endl;
            mLogStream << __func__ << ", " << std::this_thread::get_id() << std::endl;
        }

	std::fill(&file_name_buf[0], &file_name_buf[0] + 128, 0);
        std::sprintf((char *)&file_name_buf, "/dev/awsmgmt%d", mBoardNumber);
        mMgtHandle = open(file_name_buf, O_RDWR | O_SYNC);
        if (xclGetDeviceInfo2(&mDeviceInfo)) {
          close(mUserHandle);
          mUserHandle = -1;
        }
#else
	ocl_kernel_bar = -1;
	ocl_global_mem_bar = -1;
	sda_mgmt_bar = -1;

	if (xclGetDeviceInfo2(&mDeviceInfo)) {
		//	print error;
	}
	else
	if (fpga_pci_attach(slot_id, FPGA_APP_PF, APP_PF_BAR0, 0, &ocl_kernel_bar) ) {
		ocl_kernel_bar = -1;
		// print error
	}
	else
	if (fpga_pci_attach(slot_id, FPGA_APP_PF, APP_PF_BAR4, 0, &ocl_global_mem_bar) ) {
		fpga_pci_detach(ocl_kernel_bar);
		ocl_kernel_bar = -1;
		ocl_global_mem_bar = -1;
		sda_mgmt_bar = -1;
		// print error
	}
	else
	if (fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR4, 0, &sda_mgmt_bar) ) {
		// print error
		fpga_pci_detach(ocl_kernel_bar);
		fpga_pci_detach(ocl_global_mem_bar);
		ocl_kernel_bar = -1;
		ocl_global_mem_bar = -1;
		sda_mgmt_bar = -1;
	}
#endif


        initMemoryManager();
    }

    bool AwsXcl::isGood() const {
        if (!mDataMover)
            return false;
#ifdef INTERNAL_TESTING
        if (mUserHandle < 0)
            return false;
        if (mMgtHandle < 0)
            return false;
#else
	if (ocl_kernel_bar < 0)
	     return false;
	if (ocl_global_mem_bar < 0)
	     return false;
	if (sda_mgmt_bar < 0)
	     return false;
#endif
        return mDataMover->isGood();
        // TODO: Add sanity check for card state
    }


    int AwsXcl::pcieBarRead(int bar_num, unsigned long long offset, void* buffer, unsigned long long length) {
        const char *mem = 0;
        char *qBuf = (char *)buffer;
        switch (bar_num) {
#ifdef INTERNAL_TESTING
		case 0:
		{
            		if ((length + offset) > MMAP_SIZE_USER) {
                		return -1;
            		}
            		mem = mUserMap;
#else
		case APP_PF_BAR0:
		{
#endif
            		break;
        	}
		default:
        	{
            		return -1;
        	}
        }

        while (length >= 4) {
#ifdef INTERNAL_TESTING
            *(unsigned *)qBuf = *(unsigned *)(mem + offset);
#else
	    fpga_pci_peek(ocl_kernel_bar, (uint64_t)offset,(uint32_t*)qBuf);
#endif
            offset += 4;
            qBuf += 4;
            length -= 4;
        }
        while (length) {
#ifdef INTERNAL_TESTING
            *qBuf = *(mem + offset);
#else

	// TODO - add support for sub 4-byte read in AWS platform
#endif
            offset++;
            qBuf++;
            length--;
        }

//        std::memcpy(buffer, mem + offset, length);
        return 0;
    }

    int AwsXcl::pcieBarWrite(int bar_num, unsigned long long offset, const void* buffer, unsigned long long length) {
        char *mem = 0;
        char *qBuf = (char *)buffer;
        switch (bar_num) {
#ifdef INTERNAL_TESTING
        	case 0:
        	{
            		if ((length + offset) > MMAP_SIZE_USER) {
                		return -1;
            		}
            		mem = mUserMap;
#else
		case APP_PF_BAR0:
		{
#endif
            		break;
        	}
        	default:
        	{
            		return -1;
        	}
        }

        while (length >= 4) {
#ifdef INTERNAL_TESTING
            *(unsigned *)(mem + offset) = *(unsigned *)qBuf;
#else
	    fpga_pci_poke(ocl_kernel_bar, uint64_t (offset), *((uint32_t*) qBuf));
#endif
            offset += 4;
            qBuf += 4;
            length -= 4;
        }
        while (length) {
#ifdef INTERNEL_TESTING
            *(mem + offset) = *qBuf;
#else
          std::cout << "xclWrite - unsupported write with length not multiple of 4-bytes" << std::endl;

#endif
            offset++;
            qBuf++;
            length--;
        }

//        std::memcpy(mem + offset, buffer, length);
        return 0;
    }

    bool AwsXcl::zeroOutDDR()
    {
      // Zero out the FPGA external DRAM Content so memory controller
      // will not complain about ECC error from memory regions not
      // initialized before
      // In AWS F1 FPGA, the DRAM is clear before loading new AFI
      // hence this API is redundant and will return false to
      // make sure developers dont assume it works

      //      static const unsigned long long BLOCK_SIZE = 0x4000000;
//      void *buf = 0;
//      if (posix_memalign(&buf, DDR_BUFFER_ALIGNMENT, BLOCK_SIZE))
//          return false;
//      memset(buf, 0, BLOCK_SIZE);
//      mDataMover->pset64(buf, BLOCK_SIZE, 0, mDeviceInfo.mDDRSize/BLOCK_SIZE);
//      free(buf);
      return false;
    }

  /* Locks a given FPGA Slot
   * By levering the available lock infrastrucutre for the DMA
   * Driver associated with the given FPGA slot
   */
    bool AwsXcl::xclLockDevice()
    {
        if (mDataMover->lock() == false)
            return false;
#ifdef INTERNAL_TESTING
        if (flock(mUserHandle, LOCK_EX | LOCK_NB) == -1) {
            mDataMover->unlock();
            return false;
        }
#else
// FIXME: do we need to flock the ocl_kernel interface as well ?
//
#endif
        mLocked = true;

//        return zeroOutDDR();
      return true;
    }

    std::string AwsXcl::getDSAName(unsigned short deviceId, unsigned short subsystemId)
    {
        // Hard coded to AWS DSA name
        std::string dsa("xilinx:minotaur-vu9p-f1:4ddr-xpr:3.3");
        return dsa;
    }

    int AwsXcl::xclGetDeviceInfo2(xclDeviceInfo2 *info)
    {
        std::memset(info, 0, sizeof(xclDeviceInfo2));
        info->mMagic = 0X586C0C6C;
        info->mHALMajorVersion = XCLHAL_MAJOR_VER;
        info->mHALMajorVersion = XCLHAL_MINOR_VER;
        info->mMinTransferSize = DDR_BUFFER_ALIGNMENT;
        info->mDMAThreads = mDataMover->channelCount();

#ifdef INTERNAL_TESTING
        xdma_ioc_info obj = {{0X586C0C6C, XDMA_IOCINFO}};
      /* Calling the underlying DMA driver to extract
       * DMA specific configuration
       * A non-zero value reprent at error
       */
        int ret = ioctl(mUserHandle, XDMA_IOCINFO, &obj);
      // Log the return value for further debug
        if (ret)
            return ret;

        awsmgmt_ioc_info mgmt_info_obj;
        ret = ioctl(mMgtHandle, AWSMGMT_IOCINFO, &mgmt_info_obj);
        if (ret)
            return ret;

        for (int i = 0; i < 4 ; ++i) {
          info->mOCLFrequency[i] = mgmt_info_obj.ocl_frequency[i];
        }
        info->mVendorId = obj.vendor;
        info->mDeviceId = obj.device;
        info->mSubsystemId = obj.subsystem_device;
        info->mSubsystemVendorId = obj.subsystem_vendor;
        info->mDeviceVersion = obj.subsystem_device & 0x00ff;
        info->mPCIeLinkWidth = mgmt_info_obj.pcie_link_width;
        info->mPCIeLinkSpeed = mgmt_info_obj.pcie_link_speed;
#else
	struct fpga_slot_spec slot_info;
	fpga_pci_get_slot_spec(mBoardNumber,  &slot_info);
	info->mVendorId = slot_info.map[FPGA_APP_PF].vendor_id;
	info->mDeviceId = slot_info.map[FPGA_APP_PF].device_id;
// FIXME - update next 3 variables
// info->mSubsystemId = 0;
	info->mSubsystemVendorId = 0;
	info->mDeviceVersion = 0;

	for (int i = 0; i < 4 ; ++i) {
	  info->mOCLFrequency[i] = 0;
	}
        info->mPCIeLinkWidth = 16;// PCIe Gen3 x16 bus
        info->mPCIeLinkSpeed = 8; // 8Gbps Gen3 in AWS F1

#endif


        // F1 has 16 GiB per channel
        info->mDDRSize = 0x400000000;
        info->mDataAlignment = DDR_BUFFER_ALIGNMENT;
        info->mNumClocks = 4;
        // Number of available channels
        // TODO: add support for other FPGA configurations with less
        // than 4 DRAM channels
        info->mDDRBankCount = 4;

        for (auto i : mDDRMemoryManager) {
            info->mDDRFreeSize += i->freeSize();
        }

        const std::string deviceName = getDSAName(info->mDeviceId, info->mSubsystemId);
        if (mLogStream.is_open())
                mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << deviceName << std::endl;

        std::size_t length = deviceName.copy(info->mName, deviceName.length(),0);
        info->mName[length] = '\0';

        if (mLogStream.is_open()) {
          mLogStream << __func__ << ": name=" << deviceName << ", version=0x" << std::hex << info->mDeviceVersion
              << ", clock freq=" << std::dec << info->mOCLFrequency[0]
              << ", clock freq 2=" << std::dec << info->mOCLFrequency[1] << std::endl;
        }

        info->mMigCalib = true;
        for (int i = 0; i < 4; i++) {
#ifdef INTERNAL_TEST
            info->mMigCalib = info->mMigCalib && mgmt_info_obj.mig_calibration[i];
#else
	    info->mMigCalib = 1;
#endif
        }
        //TODO: Umang
        info->mOnChipTemp  = 25;
        info->mFanTemp     = 0;
        info->mVInt        = 0.9;
        info->mVAux        = 0.9;
        info->mVBram       = 0.9;
        return 0;
    }

    int AwsXcl::resetDevice(xclResetKind kind) {
        for (auto i : mDDRMemoryManager) {
            i->reset();
        }

        // Call a new IOCTL to just reset the OCL region
        // TODO : umang
//        if (kind == XCL_RESET_FULL) {
//            xdma_ioc_base obj = {0X586C0C6C, XDMA_IOCHOTRESET};
//            return ioctl(mUserHandle, XDMA_IOCHOTRESET, &obj);
//        }
//        else if (kind == XCL_RESET_KERNEL) {
//            xdma_ioc_base obj = {0X586C0C6C, XDMA_IOCOCLRESET};
//            return ioctl(mUserHandle, XDMA_IOCOCLRESET, &obj);
//        }
//        return -EINVAL;

      // AWS FIXME - add reset
        return 0;
    }

    int AwsXcl::xclReClock2(unsigned short region, const unsigned short *targetFreqMHz)
    {
    #ifdef INTERNAL_TESTING
            awsmgmt_ioc_freqscaling obj = {0, targetFreqMHz[0], targetFreqMHz[1], 0, 0};
            return ioctl(mMgtHandle, AWSMGMT_IOCFREQSCALING, &obj);
    #else
//    #       error "INTERNAL_TESTING macro disabled. AMZN code goes here. "
//    #       This API is not supported in AWS, the frequencies are set per AFI
   	return -1;
    #endif
    }
}


xclDeviceHandle xclOpen(unsigned index, const char *logfileName, xclVerbosityLevel level)
{
    awsbwhal::AwsXcl *handle = new awsbwhal::AwsXcl(index, logfileName, level);
    if (!awsbwhal::AwsXcl::handleCheck(handle)) {
        delete handle;
        handle = 0;
    }

    return (xclDeviceHandle *)handle;
}

void xclClose(xclDeviceHandle handle)
{
    if (awsbwhal::AwsXcl::handleCheck(handle)) {
        delete ((awsbwhal::AwsXcl *)handle);
    }
}

int xclGetDeviceInfo2(xclDeviceHandle handle, xclDeviceInfo2 *info)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclGetDeviceInfo2(info);
}

int xclLoadBitstream(xclDeviceHandle handle, const char *xclBinFileName)
{
    return -ENOSYS;
}

int xclLoadXclBin(xclDeviceHandle handle, const xclBin *buffer)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclLoadXclBin(buffer);
}

size_t xclWrite(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset, const void *hostBuf, size_t size)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclWrite(space, offset, hostBuf, size);
}

size_t xclRead(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclRead(space, offset, hostBuf, size);
}


uint64_t xclAllocDeviceBuffer(xclDeviceHandle handle, size_t size)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclAllocDeviceBuffer(size);
}


uint64_t xclAllocDeviceBuffer2(xclDeviceHandle handle, size_t size, xclMemoryDomains domain,
                               unsigned flags)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclAllocDeviceBuffer2(size, domain, flags);
}


void xclFreeDeviceBuffer(xclDeviceHandle handle, uint64_t buf)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return;
    return drv->xclFreeDeviceBuffer(buf);
}


size_t xclCopyBufferHost2Device(xclDeviceHandle handle, uint64_t dest, const void *src, size_t size, size_t seek)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclCopyBufferHost2Device(dest, src, size, seek);
}


size_t xclCopyBufferDevice2Host(xclDeviceHandle handle, void *dest, uint64_t src, size_t size, size_t skip)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclCopyBufferDevice2Host(dest, src, size, skip);
}


//This will be deprecated.
int xclUpgradeFirmware(xclDeviceHandle handle, const char *fileName)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return xclUpgradeFirmware2(handle, fileName, 0);
}

int xclUpgradeFirmware2(xclDeviceHandle handle, const char *fileName1, const char* fileName2)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return -ENOSYS;
}

int xclBootFPGA(xclDeviceHandle handle)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return -ENOSYS;
}

unsigned xclProbe()
{
    return awsbwhal::AwsXcl::xclProbe();
}

int xclResetDevice(xclDeviceHandle handle, xclResetKind kind)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return -ENOSYS;
}

int xclReClock2(xclDeviceHandle handle, unsigned short region, const unsigned short *targetFreqMHz)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclReClock2(region, targetFreqMHz);
}


int xclLockDevice(xclDeviceHandle handle)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclLockDevice() ? 0 : -1;
}
