/*
 * Copyright (C) 2017-2018 Xilinx, Inc
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
#include <errno.h>
/*
 * Define GCC version macro so we can use newer C++11 features
 * if possible
 */
#define GCC_VERSION (__GNUC__ * 10000 \
                     + __GNUC_MINOR__ * 100 \
                     + __GNUC_PATCHLEVEL__)

#ifdef INTERNAL_TESTING
#define ACCELERATOR_BAR        0
#define MMAP_SIZE_USER         0x400000
#endif

/* Aligning access to FPGA DRAM space to 4096 Byte */
#define DDR_BUFFER_ALIGNMENT   0x1000

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
#include <fstream>
#include <mutex>

#include "xclbin2.h"
#include "xocl/xocl_ioctl.h"
#include "scan.h"
#include "awssak.h"

#ifdef INTERNAL_TESTING
#include "driver/aws/kernel/include/mgmt-ioctl.h"
#else
#define AWSMGMT_NUM_SUPPORTED_CLOCKS 4
#define AWSMGMT_NUM_ACTUAL_CLOCKS    3
// TODO - define this in a header file
extern char* get_afi_from_xclBin(const xclBin *);
extern char* get_afi_from_axlf(const axlf *);
#define DEFAULT_GLOBAL_AFI "agfi-069ddd533a748059b" // 1.4 shell
#endif

namespace awsbwhal {
    // This list will get populated in xclProbe
    // 0 -> /dev/dri/renderD129
    // 1 -> /dev/dri/renderD130
    static std::mutex deviceListMutex;
    //  static std::vector<std::pair<int, int>> deviceList;

    const unsigned AwsXcl::TAG = 0X586C0C6C; // XL OpenCL X->58(ASCII), L->6C(ASCII), O->0 C->C L->6C(ASCII);

#ifdef INTERNAL_TESTING
    int AwsXcl::xclLoadAxlf(const axlf *buffer)
    {
      if ( mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buffer << std::endl;
      }

      if ( !mLocked)
        return -EPERM;

      std::cout << "Downloading xclbin ...\n" << std::endl;
      const unsigned cmd = AWSMGMT_IOCICAPDOWNLOAD_AXLF;
      awsmgmt_ioc_bitstream_axlf obj = { const_cast<axlf *>(buffer) };
      int ret = ioctl(mMgtHandle, cmd, &obj);
      if ( 0 != ret)
        return ret;

      // If it is an XPR DSA, zero out the DDR again as downloading the XCLBIN
      // reinitializes the DDR and results in ECC error.
      if ( isXPR()) {
        if ( mLogStream.is_open()) {
          mLogStream << __func__ << "XPR Device found, zeroing out DDR again.." << std::endl;
        }

        if ( zeroOutDDR() == false) {
          if ( mLogStream.is_open()) {
            mLogStream << __func__ << "zeroing out DDR failed" << std::endl;
          }
          return -EIO;
        }
      }

      drm_xocl_axlf axlf_obj = {const_cast<axlf *>(buffer)};
      ret = ioctl(mUserHandle, DRM_IOCTL_XOCL_READ_AXLF, &axlf_obj);
      return ret;
    }
#endif

    int AwsXcl::xclLoadXclBin(const xclBin *buffer)
    {
      char *xclbininmemory = reinterpret_cast<char*> (const_cast<xclBin*> (buffer));
#ifdef INTERNAL_TESTING
      if (!memcmp(xclbininmemory, "xclbin2", 8)) {
          return xclLoadAxlf(reinterpret_cast<axlf*>(xclbininmemory));
      }

      if (mLogStream.is_open()) {
          mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buffer << std::endl;
      }

      if (!mLocked)
          return -EPERM;

      const unsigned cmd = AWSMGMT_IOCICAPDOWNLOAD;
      awsmgmt_ioc_bitstream obj = {const_cast<xclBin *>(buffer)};
      return ioctl(mMgtHandle, cmd, &obj);
#else
      if (!memcmp(xclbininmemory, "xclbin2", 8)) {   
          int retVal = 0;
          axlf *axlfbuffer = reinterpret_cast<axlf*>(const_cast<xclBin*> (buffer));
          fpga_mgmt_image_info orig_info;
          char* afi_id = get_afi_from_axlf(axlfbuffer);
          std::memset(&orig_info, 0, sizeof(struct fpga_mgmt_image_info));
          fpga_mgmt_describe_local_image(mBoardNumber, &orig_info, 0);
          if (checkAndSkipReload( afi_id, &orig_info )) {
              retVal = fpga_mgmt_load_local_image(mBoardNumber, afi_id);
              if (!retVal) {
                  retVal = sleepUntilLoaded( std::string(afi_id) );
              }
              if (!retVal) {
                  drm_xocl_axlf axlf_obj = { reinterpret_cast<axlf*>(const_cast<xclBin*>(buffer)) };
                  retVal = ioctl(mUserHandle, DRM_IOCTL_XOCL_READ_AXLF, &axlf_obj);
                  if (retVal) {
                      std::cout << "IOCTL DRM_IOCTL_XOCL_READ_AXLF Failed: " << retVal << std::endl;
                  } else {
                      std::cout << "AFI load complete." << std::endl; 
                  }
              }
          } 
          return retVal;
      } else {
          char* afi_id = get_afi_from_xclBin(buffer);
          return fpga_mgmt_load_local_image(mBoardNumber, afi_id);
      }
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

        /* Current release now includes performance monitors */
        case XCL_ADDR_SPACE_DEVICE_PERFMON:
        {
#ifdef INTERNAL_TESTING
            if (pcieBarWrite(ACCELERATOR_BAR, offset, hostBuf, size) == 0) {
                return size;
            }
#else
            if (pcieBarWrite(APP_PF_BAR0, offset, hostBuf, size) == 0) {
                return size;
            }
#endif
            return -1;
        }
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


    size_t AwsXcl::xclRead(xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << space << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }

        switch (space) {
        case XCL_ADDR_SPACE_DEVICE_PERFMON:
        {
#ifdef	INTERNAL_TESTING
            if (pcieBarRead(ACCELERATOR_BAR, offset, hostBuf, size) == 0) {
                return size;
            }
#else
            if (pcieBarRead(APP_PF_BAR0, offset, hostBuf, size) == 0) {
                return size;
            }
#endif
            return -1;
        }
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

    uint64_t AwsXcl::xclAllocDeviceBuffer(size_t size)
    {
      if (mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << size << std::endl;
      }

      uint64_t result = mNullAddr;
      unsigned boHandle = xclAllocBO(size, XCL_BO_DEVICE_RAM, 0x0);
      if (boHandle == mNullBO)
        return result;

      drm_xocl_info_bo boInfo = {boHandle, 0, 0, 0};
      if (ioctl(mUserHandle, DRM_IOCTL_XOCL_INFO_BO, &boInfo))
        return result;

      void *hbuf = xclMapBO(boHandle, true);
      if (hbuf == MAP_FAILED) {
        xclFreeBO(boHandle);
        return mNullAddr;
      }
      mLegacyAddressTable.insert(boInfo.paddr, size, std::make_pair(boHandle, (char *)hbuf));
      return boInfo.paddr;
    }

    uint64_t AwsXcl::xclAllocDeviceBuffer2(size_t size, xclMemoryDomains domain, unsigned flags)
    {
      if (mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << size << ", "
                   << domain << ", " << flags << std::endl;
      }

      uint64_t result = mNullAddr;
      if (domain != XCL_MEM_DEVICE_RAM)
        return result;

      unsigned ddr = 1;
      ddr <<= flags;
      unsigned boHandle = xclAllocBO(size, XCL_BO_DEVICE_RAM, ddr);
      if (boHandle == mNullBO)
        return result;

      drm_xocl_info_bo boInfo = {boHandle, 0, 0, 0};
      if (ioctl(mUserHandle, DRM_IOCTL_XOCL_INFO_BO, &boInfo))
        return result;

      void *hbuf = xclMapBO(boHandle, true);
      if (hbuf == MAP_FAILED) {
        xclFreeBO(boHandle);
        return mNullAddr;
      }
      mLegacyAddressTable.insert(boInfo.paddr, size, std::make_pair(boHandle, (char *)hbuf));
      return boInfo.paddr;
    }

    void AwsXcl::xclFreeDeviceBuffer(uint64_t buf)
    {
      if (mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buf << std::endl;
      }

      std::pair<unsigned, char *> bo = mLegacyAddressTable.erase(buf);
      drm_xocl_info_bo boInfo = {bo.first, 0, 0, 0};
      if (!ioctl(mUserHandle, DRM_IOCTL_XOCL_INFO_BO, &boInfo)) {
        munmap(bo.second, boInfo.size);
      }
      xclFreeBO(bo.first);
    }


    size_t AwsXcl::xclCopyBufferHost2Device(uint64_t dest, const void *src, size_t size, size_t seek)
    {
      if (mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << dest << ", "
                   << src << ", " << size << ", " << seek << std::endl;
      }

      std::pair<unsigned, char *> bo = mLegacyAddressTable.find(dest);
      std::memcpy(bo.second + seek, src, size);
      int result = xclSyncBO(bo.first, XCL_BO_SYNC_BO_TO_DEVICE, size, seek);
      if (result)
        return result;
      return size;
    }


    size_t AwsXcl::xclCopyBufferDevice2Host(void *dest, uint64_t src, size_t size, size_t skip)
    {
      if (mLogStream.is_open()) {
        mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << dest << ", "
                   << src << ", " << size << ", " << skip << std::endl;
      }

      std::pair<unsigned, char *> bo = mLegacyAddressTable.find(src);
      int result = xclSyncBO(bo.first, XCL_BO_SYNC_BO_FROM_DEVICE, size, skip);
      if (result)
        return result;
      std::memcpy(dest, bo.second + skip, size);
      return size;
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
      std::lock_guard<std::mutex> lock(awsbwhal::deviceListMutex);
      if(xcldev::pci_device_scanner::device_list.size() == 0) {
        xcldev::pci_device_scanner devices;
        devices.scan(true);
      }

      unsigned i  = 0;
#ifdef INTERNAL_TESTING
      char file_name_buf[128];
      for (i = 0; i < 16; i++) {
          std::sprintf((char *)&file_name_buf, "/dev/awsmgmt%d", i);
          int fd = open(file_name_buf, O_RDWR);
          if (fd < 0) {
              return i;
          }
          close(fd);
      }
      if (i != xcldev::pci_device_scanner::device_list.size()) {
        std::cout << "ERROR xclProbe: Num of FPGA userPF device do not match num of mgmtPF devices" << std::endl;
        std::cout << "ERROR xclProbe: Num of userPF, mgmtPF devices = " << std::dec << xcldev::pci_device_scanner::device_list.size() << std::dec << i << std::endl;
        return 0;
      }
#endif
      i = xcldev::pci_device_scanner::device_list.size();

#ifndef INTERNAL_TESTING
      std::cout << "xclProbe found " << std::dec << i << " FPGA slots with xocl driver running" << std::endl;
#else
      std::cout << "xclProbe found " << std::dec << i << " FPGA slots with awsmgmt & xocl driver running" << std::endl;
#endif
      return i;
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
#ifndef INTERNAL_TESTING
        loadDefaultAfiIfCleared();
#endif
        const std::string devName = "/dev/dri/renderD" + std::to_string(xcldev::pci_device_scanner::device_list[mBoardNumber].user_instance);
#ifndef INTERNAL_TESTING
        mUserHandle = open(devName.c_str(), O_RDWR);
        if(mUserHandle <= 0) {
            std::cout << "WARNING: AwsXcl - Cannot open userPF: " << devName << std::endl;
        }
#endif

#ifdef INTERNAL_TESTING
        if(mUserHandle > 0) {
            mUserMap = (char *)mmap(0, MMAP_SIZE_USER, PROT_READ | PROT_WRITE, MAP_SHARED, mUserHandle, 0);
            if (mUserMap == MAP_FAILED) {
                std::cout << "Map failed: " << devName << std::endl;
                close(mUserHandle);
                mUserHandle = -1;
            }
        }

        char file_name_buf[128];
        std::fill(&file_name_buf[0], &file_name_buf[0] + 128, 0);
        std::sprintf((char *)&file_name_buf, "/dev/awsmgmt%d", mBoardNumber);
        mMgtHandle = open(file_name_buf, O_RDWR | O_SYNC);
        if(mMgtHandle > 0) {
            if (xclGetDeviceInfo2(&mDeviceInfo)) {
                close(mMgtHandle);
                mMgtHandle = -1;
            }
        } else {
            std::cout << "Cannot open mgmtPF: " << devName << std::endl;
        }
#else
        int slot_id = mBoardNumber;
        ocl_kernel_bar = -1;
        ocl_global_mem_bar = -1;
        sda_mgmt_bar = -1;

        if (xclGetDeviceInfo2(&mDeviceInfo)) {
            std::cout << "ERROR AwsXcl: DeviceInfo failed for slot# " << std::dec << slot_id << std::endl;
        } else if (fpga_pci_attach(slot_id, FPGA_APP_PF, APP_PF_BAR0, 0, &ocl_kernel_bar) ) {
                ocl_kernel_bar = -1;
                std::cout << "ERROR AwsXcl: PCI kernel bar attach failed for slot# " << std::dec << slot_id << std::endl;
        } else if (fpga_pci_attach(slot_id, FPGA_APP_PF, APP_PF_BAR4, 0, &ocl_global_mem_bar) ) {
                    fpga_pci_detach(ocl_kernel_bar);
                    ocl_kernel_bar = -1;
                    ocl_global_mem_bar = -1;
                    sda_mgmt_bar = -1;
                    std::cout << "ERROR AwsXcl: PCI global bar attach failed for slot# " << std::dec << slot_id << std::endl;
        } else if (fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR4, 0, &sda_mgmt_bar) ) {
                        fpga_pci_detach(ocl_kernel_bar);
                        fpga_pci_detach(ocl_global_mem_bar);
                        ocl_kernel_bar = -1;
                        ocl_global_mem_bar = -1;
                        sda_mgmt_bar = -1;
                        std::cout << "ERROR AwsXcl: PCI mgmt bar attach failed for slot# " << std::dec << slot_id << std::endl;
        }
#endif

        //
        // Profiling - defaults
        // Class-level defaults: mIsDebugIpLayoutRead = mIsDeviceProfiling = false
        mDevUserName = xcldev::pci_device_scanner::device_list[mBoardNumber].user_name;
        mMemoryProfilingNumberSlots = 0;
        mPerfMonFifoCtrlBaseAddress = 0x00;
        mPerfMonFifoReadBaseAddress = 0x00;
        //
        // Profiling - defaults
        // Class-level defaults: mIsDebugIpLayoutRead = mIsDeviceProfiling = false
        mDevUserName = xcldev::pci_device_scanner::device_list[mBoardNumber].user_name;
        mMemoryProfilingNumberSlots = 0;
        mPerfMonFifoCtrlBaseAddress = 0x00;
        mPerfMonFifoReadBaseAddress = 0x00;

        //
        // Profiling - defaults
        // Class-level defaults: mIsDebugIpLayoutRead = mIsDeviceProfiling = false
        mDevUserName = xcldev::pci_device_scanner::device_list[mBoardNumber].user_name;
        mMemoryProfilingNumberSlots = 0;
        mPerfMonFifoCtrlBaseAddress = 0x00;
        mPerfMonFifoReadBaseAddress = 0x00;
    }

    bool AwsXcl::isGood() const {
#ifdef INTERNAL_TESTING
        if (mUserHandle < 0) {
            std::cout << "AwsXcl: Bad handle. No userPF Handle" << std::endl;
            return false;
        }
        if (mMgtHandle < 0) {
            std::cout << "AwsXcl: Bad handle. No mgmtPF Handle" << std::endl;
            return false;
        }
#else
        if (ocl_kernel_bar < 0) {
          std::cout << "WARNING: AwsXcl isGood: kernel, global & mgmt bar are: " << std::hex << ocl_kernel_bar << ", " << std::hex << ocl_global_mem_bar << ", " << sda_mgmt_bar << std::endl;
          return false;
        }
        if (ocl_global_mem_bar < 0) {
          std::cout << "WARNING: AwsXcl isGood: kernel, global & mgmt bar are: " << std::hex << ocl_kernel_bar << ", " << std::hex << ocl_global_mem_bar << ", " << sda_mgmt_bar << std::endl;
          return false;
        }
        if (sda_mgmt_bar < 0) {
          std::cout << "WARNING: AwsXcl isGood: kernel, global & mgmt bar are: " << std::hex << ocl_kernel_bar << ", " << std::hex << ocl_global_mem_bar << ", " << sda_mgmt_bar << std::endl;
          return false;
        }
        if (mUserHandle <= 0) {
            std::cout << "WARNING: AwsXcl isGood: invalid user handle." << std::endl;
            return false;
        }
#endif
        return true;
    }


    int AwsXcl::pcieBarRead(int bar_num, unsigned long long offset, void* buffer, unsigned long long length) {
        char *qBuf = (char *)buffer;
        switch (bar_num) {
#ifdef INTERNAL_TESTING
        const char *mem = 0;
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
        char *qBuf = (char *)buffer;
        switch (bar_num) {
#ifdef INTERNAL_TESTING
        char *mem = 0;
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
#ifdef INTERNAL_TESTING
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
        std::string dsa("xilinx_aws-vu9p-f1-04261818_dynamic_5_0");
        return dsa;
    }

    int AwsXcl::xclGetDeviceInfo2(xclDeviceInfo2 *info)
    {
        std::memset(info, 0, sizeof(xclDeviceInfo2));
        info->mMagic = 0X586C0C6C;
        info->mHALMajorVersion = XCLHAL_MAJOR_VER;
        info->mHALMajorVersion = XCLHAL_MINOR_VER;
        info->mMinTransferSize = DDR_BUFFER_ALIGNMENT;
        info->mDMAThreads = 4;//AWS has four threads. Others have only two threads

#ifdef INTERNAL_TESTING
        /* Sarab disabling xdma ioctl
        xdma_ioc_info obj = {{0X586C0C6C, XDMA_IOCINFO}};
      /--* Calling the underlying DMA driver to extract
       * DMA specific configuration
       * A non-zero value reprent at error
       *--/
        int ret = ioctl(mUserHandle, XDMA_IOCINFO, &obj);
      // Log the return value for further debug
        if (ret)
            return ret;
        info->mVendorId = obj.vendor;
        info->mDeviceId = obj.device;
        info->mSubsystemId = obj.subsystem_device;
        info->mSubsystemVendorId = obj.subsystem_vendor;
        info->mDeviceVersion = obj.subsystem_device & 0x00ff;
        */
        awsmgmt_ioc_info mgmt_info_obj;
        int ret = ioctl(mMgtHandle, AWSMGMT_IOCINFO, &mgmt_info_obj);
        if (ret)
            return ret;

        info->mVendorId = mgmt_info_obj.vendor;
        info->mDeviceId = mgmt_info_obj.device;
        info->mSubsystemId = mgmt_info_obj.subsystem_device;
        info->mSubsystemVendorId = mgmt_info_obj.subsystem_vendor;
        info->mDeviceVersion = mgmt_info_obj.subsystem_device & 0x00ff;
        info->mPCIeLinkWidth = mgmt_info_obj.pcie_link_width;
        info->mPCIeLinkSpeed = mgmt_info_obj.pcie_link_speed;
        for (int i = 0; i < AWSMGMT_NUM_SUPPORTED_CLOCKS; ++i) {
          info->mOCLFrequency[i] = mgmt_info_obj.ocl_frequency[i];
        }
        info->mMigCalib = true;
        for (int i = 0; i < 4; i++) {
            info->mMigCalib = info->mMigCalib && mgmt_info_obj.mig_calibration[i];
        }
#else
    struct fpga_slot_spec slot_info;
    //fpga_pci_get_slot_spec(mBoardNumber,FPGA_APP_PF,  &slot_info);
    fpga_pci_get_slot_spec(mBoardNumber, &slot_info);
    info->mVendorId = slot_info.map[0].vendor_id;
    info->mDeviceId = slot_info.map[0].device_id;
    // FIXME - update next 3 variables
    info->mSubsystemId = slot_info.map[0].subsystem_device_id;
    info->mSubsystemVendorId = slot_info.map[0].subsystem_vendor_id;
    info->mDeviceVersion = 0;
    info->mPCIeLinkWidth = 16;
    info->mPCIeLinkSpeed = 8000;
    fpga_mgmt_image_info imageInfo;
    fpga_mgmt_describe_local_image( mBoardNumber, &imageInfo, 0 );
    for (int i = 0; i < AWSMGMT_NUM_SUPPORTED_CLOCKS; ++i) {
      info->mOCLFrequency[i] = imageInfo.metrics.clocks[i].frequency[0] / 1000000;
    }
    info->mMigCalib = true;
#endif

        // F1 has 16 GiB per channel
        info->mDDRSize = 0x400000000 * 4;
        info->mDataAlignment = DDR_BUFFER_ALIGNMENT;
        info->mNumClocks = AWSMGMT_NUM_ACTUAL_CLOCKS;
        // Number of available channels
        // TODO: add support for other FPGA configurations with less
        // than 4 DRAM channels
        info->mDDRBankCount = 4;

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

        info->mOnChipTemp  = 25;
        info->mFanTemp     = 0;
        info->mVInt        = 0.9;
        info->mVAux        = 0.9;
        info->mVBram       = 0.9;
        return 0;
    }

    int AwsXcl::resetDevice(xclResetKind kind) {

        // Call a new IOCTL to just reset the OCL region
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
            awsmgmt_ioc_freqscaling obj = {0, targetFreqMHz[0], targetFreqMHz[1], targetFreqMHz[2], 0};
            return ioctl(mMgtHandle, AWSMGMT_IOCFREQSCALING, &obj);
    #else
//    #       error "INTERNAL_TESTING macro disabled. AMZN code goes here. "
//    #       This API is not supported in AWS, the frequencies are set per AFI
   	return 0;
    #endif
    }

    ssize_t AwsXcl::xclUnmgdPwrite(unsigned flags, const void *buf, size_t count, uint64_t offset)
    {
      if (flags)
        return -EINVAL;
      drm_xocl_pwrite_unmgd unmgd = {0, 0, offset, count, reinterpret_cast<uint64_t>(buf)};
      return ioctl(mUserHandle, DRM_IOCTL_XOCL_PWRITE_UNMGD, &unmgd);
    }

    ssize_t AwsXcl::xclUnmgdPread(unsigned flags, void *buf, size_t count, uint64_t offset)
    {
      if (flags)
        return -EINVAL;
      drm_xocl_pread_unmgd unmgd = {0, 0, offset, count, reinterpret_cast<uint64_t>(buf)};
      return ioctl(mUserHandle, DRM_IOCTL_XOCL_PREAD_UNMGD, &unmgd);
    }

    int AwsXcl::xclExportBO(unsigned int boHandle)
    {
      drm_prime_handle info = {boHandle, 0, -1};
      int result = ioctl(mUserHandle, DRM_IOCTL_PRIME_HANDLE_TO_FD, &info);
      return !result ? info.fd : result;
    }

    unsigned int AwsXcl::xclImportBO(int fd, unsigned flags)
    {

      /*Sarab
      drm_xocl_userptr_bo user = {reinterpret_cast<uint64_t>(userptr), size, mNullBO, flags};
      int result = ioctl(mUserHandle, DRM_IOCTL_XOCL_USERPTR_BO, &user);

       */


      drm_prime_handle info = {mNullBO, flags, fd};
      int result = ioctl(mUserHandle, DRM_IOCTL_PRIME_FD_TO_HANDLE, &info);
      if (result) {
        std::cout << __func__ << " ERROR: FD to handle IOCTL failed" << std::endl;
      }
      return !result ? info.handle : mNullBO;
    }

    int AwsXcl::xclGetBOProperties(unsigned int boHandle, xclBOProperties *properties)
    {
      drm_xocl_info_bo info = {boHandle, 0, 0, 0};
      int result = ioctl(mUserHandle, DRM_IOCTL_XOCL_INFO_BO, &info);
      properties->handle = info.handle;
      properties->flags  = info.flags;
      properties->size   = info.size;
      properties->paddr  = info.paddr;
      properties->domain = XCL_BO_DEVICE_RAM; // currently all BO domains are XCL_BO_DEVICE_RAM
      return result ? mNullBO : 0;
    }

    bool AwsXcl::xclUnlockDevice()
    {
      flock(mUserHandle, LOCK_UN);
      mLocked = false;
      return true;
    }

    // Assume that the memory is always
    // created for the device ddr for now. Ignoring the flags as well.
    unsigned int AwsXcl::xclAllocBO(size_t size, xclBOKind domain, unsigned flags)
    {
      drm_xocl_create_bo info = {size, mNullBO, flags};
      int result = ioctl(mUserHandle, DRM_IOCTL_XOCL_CREATE_BO, &info);
      if (result) {
        std::cout << __func__ << " ERROR: AllocBO IOCTL failed" << std::endl;
      }
      return result ? mNullBO : info.handle;
    }

    unsigned int AwsXcl::xclAllocUserPtrBO(void *userptr, size_t size, unsigned flags)
    {
      drm_xocl_userptr_bo user = {reinterpret_cast<uint64_t>(userptr), size, mNullBO, flags};
      int result = ioctl(mUserHandle, DRM_IOCTL_XOCL_USERPTR_BO, &user);
      return result ? mNullBO : user.handle;
    }

    void AwsXcl::xclFreeBO(unsigned int boHandle)
    {
      drm_gem_close closeInfo = {boHandle, 0};
      ioctl(mUserHandle, DRM_IOCTL_GEM_CLOSE, &closeInfo);
    }

    int AwsXcl::xclWriteBO(unsigned int boHandle, const void *src, size_t size, size_t seek)
    {
      drm_xocl_pwrite_bo pwriteInfo = { boHandle, 0, seek, size, reinterpret_cast<uint64_t>(src) };
      return ioctl(mUserHandle, DRM_IOCTL_XOCL_PWRITE_BO, &pwriteInfo);
    }

    int AwsXcl::xclReadBO(unsigned int boHandle, void *dst, size_t size, size_t skip)
    {
      drm_xocl_pread_bo preadInfo = { boHandle, 0, skip, size, reinterpret_cast<uint64_t>(dst) };
      return ioctl(mUserHandle, DRM_IOCTL_XOCL_PREAD_BO, &preadInfo);
    }

    void *AwsXcl::xclMapBO(unsigned int boHandle, bool write)
    {
      drm_xocl_info_bo info = { boHandle, 0, 0 };
      int result = ioctl(mUserHandle, DRM_IOCTL_XOCL_INFO_BO, &info);
      if (result)
        return nullptr;

      drm_xocl_map_bo mapInfo = { boHandle, 0, 0 };
      result = ioctl(mUserHandle, DRM_IOCTL_XOCL_MAP_BO, &mapInfo);
      if (result)
        return nullptr;

      return mmap(0, info.size, (write ? (PROT_READ|PROT_WRITE) : PROT_READ),
                  MAP_SHARED, mUserHandle, mapInfo.offset);
    }

    int AwsXcl::xclSyncBO(unsigned int boHandle, xclBOSyncDirection dir,
                            size_t size, size_t offset)
    {
      drm_xocl_sync_bo_dir drm_dir = (dir == XCL_BO_SYNC_BO_TO_DEVICE) ?
        DRM_XOCL_SYNC_BO_TO_DEVICE :
        DRM_XOCL_SYNC_BO_FROM_DEVICE;
      drm_xocl_sync_bo syncInfo = {boHandle, 0, size, offset, drm_dir};
      return ioctl(mUserHandle, DRM_IOCTL_XOCL_SYNC_BO, &syncInfo);
    }

#ifndef INTERNAL_TESTING
    int AwsXcl::loadDefaultAfiIfCleared( void )
    {
        int array_len = 16;
        fpga_slot_spec spec_array[ array_len ];
        std::memset( spec_array, mBoardNumber, sizeof(fpga_slot_spec) * array_len );
        fpga_pci_get_all_slot_specs( spec_array, array_len );
        if( spec_array[mBoardNumber].map[FPGA_APP_PF].device_id == AWS_UserPF_DEVICE_ID ) {
            std::string agfi = DEFAULT_GLOBAL_AFI;
            fpga_mgmt_load_local_image( mBoardNumber, const_cast<char*>(agfi.c_str()) );
            if( sleepUntilLoaded( agfi ) ) {
                std::cout << "ERROR: Sleep until load failed." << std::endl;
                return -1;
            }
            fpga_pci_rescan_slot_app_pfs( mBoardNumber );
        }
        return 0;
    }

    int AwsXcl::sleepUntilLoaded( const std::string afi )
    {
        for( int i = 0; i < 20; i++ ) {
            std::this_thread::sleep_for( std::chrono::milliseconds( 100 ) );
            fpga_mgmt_image_info info;
            std::memset( &info, 0, sizeof(struct fpga_mgmt_image_info) );
            int result = fpga_mgmt_describe_local_image( mBoardNumber, &info, 0 );
            if( result ) {
                std::cout << "ERROR: Load image failed." << std::endl;
                return 1;
            }
            if( (info.status == FPGA_STATUS_LOADED) && !std::strcmp(info.ids.afi_id, const_cast<char*>(afi.c_str())) ) {
                break;
            }
        }
        return 0;
    }

    int AwsXcl::checkAndSkipReload( char *afi_id, fpga_mgmt_image_info *orig_info )
    {
        if( (orig_info->status == FPGA_STATUS_LOADED) && !std::strcmp(orig_info->ids.afi_id, afi_id) ) {
            std::cout << "This AFI already loaded. Skip reload!" << std::endl;
            int result = 0;
            //existing afi matched.
            uint16_t status = 0;
            result = fpga_mgmt_get_vDIP_status(mBoardNumber, &status);
            if(result) {
                printf("Error: can not get virtual DIP Switch state\n");
                return result;
            }
            //Set bit 0 to 1
            status |=  (1 << 0);
            result = fpga_mgmt_set_vDIP(mBoardNumber, status);
            if(result) {
                printf("Error trying to set virtual DIP Switch \n");
                return result;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(250));
            //pulse the changes in.
            result = fpga_mgmt_get_vDIP_status(mBoardNumber, &status);
            if(result) {
                printf("Error: can not get virtual DIP Switch state\n");
                return result;
            }
            //Set bit 0 to 0
            status &=  ~(1 << 0);
            result = fpga_mgmt_set_vDIP(mBoardNumber, status);
            if(result) {
                printf("Error trying to set virtual DIP Switch \n");
                return result;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(250));

            printf("Successfully skipped reloading of local image.\n");
            return result;
        } else {
            std::cout << "AFI not yet loaded, proceed to download." << std::endl;
            return 1;
        }
    }
#endif
} /* end namespace awsbmhal */

xclDeviceHandle xclOpen(unsigned deviceIndex, const char *logFileName, xclVerbosityLevel level)
{
    if(xcldev::pci_device_scanner::device_list.size() <= deviceIndex) {
        printf("Cannot find index %d \n", deviceIndex);
        return nullptr;
    }

    awsbwhal::AwsXcl *handle = new awsbwhal::AwsXcl(deviceIndex, logFileName, level);
    if (!awsbwhal::AwsXcl::handleCheck(handle)) {
        printf("WARNING: xclOpen Handle check failed\n");
        delete handle;
        handle = nullptr;
#ifndef INTERNAL_TESTING
        /* workaround necessary to load a default afi and program with xclbin when device is in a cleared state */
        xcldev::pci_device_scanner rescan;
        rescan.clear_device_list();
        rescan.scan( true );
        for (unsigned int i=0; i<rescan.device_list.size(); i++) {
            std::cout << "device[" << i << "].user_instance : " << rescan.device_list[ i ].user_instance << std::endl;
            if (rescan.device_list[i].user_instance == 128) {
                deviceIndex = i;
                break;
            }
        }
        handle = new awsbwhal::AwsXcl(deviceIndex, logFileName, level);
        if (!awsbwhal::AwsXcl::handleCheck(handle)) {
            printf("ERROR: xclOpen Handle check failed\n");
            delete handle;
            handle = nullptr;
        }
#endif
    }
  return static_cast<xclDeviceHandle>(handle);
}

void xclClose(xclDeviceHandle handle) {
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (drv)
    delete drv;
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

/*
 * xclBootFPGA
 *
 * Sequence:
 *   1) call boot ioctl
 *   2) close the device, unload the driver
 *   3) remove and scan
 *   4) rescan pci devices
 *   5) reload the driver (done by the calling function xcldev::boot())
 *
 * Return 0 on success, -1 on failure.
 */
int xclBootFPGA(xclDeviceHandle handle)
{
//    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
//    if (!drv)
//        return -1;
//    return -ENOSYS;
    int retVal = -1;

    //awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
//    retVal = drv->xclBootFPGA(); // boot ioctl
    retVal = 0; // skip boot ioctl since this may not be possible for AWS

    if( retVal == 0 )
    {
        xclClose(handle); // close the device, unload the driver
        retVal = xclRemoveAndScanFPGA(); // remove and scan
    }

    if( retVal == 0 )
    {
        xcldev::pci_device_scanner devScanner;
        devScanner.scan( true ); // rescan pci devices
    }

    return retVal;
}

int xclRemoveAndScanFPGA( void )
{
    const std::string devPath =    "/devices/";
    const std::string removePath = "/remove";
    const std::string pciPath =    "/sys/bus/pci";
    const std::string rescanPath = "/rescan";
    const char *input = "1\n";

    // remove devices "echo 1 > /sys/bus/pci/devices/<deviceHandle>/remove"
    for (unsigned int i = 0; i < xcldev::pci_device_scanner::device_list.size(); i++)
    {
        std::string dev_name_pf_user = pciPath + devPath + xcldev::pci_device_scanner::device_list[i].user_name + removePath;
        std::string dev_name_pf_mgmt = pciPath + devPath + xcldev::pci_device_scanner::device_list[i].mgmt_name + removePath;

        std::ofstream userFile( dev_name_pf_user );
        if( !userFile.is_open() ) {
            perror( dev_name_pf_user.c_str() );
            return errno;
        }
        userFile << input;

        std::ofstream mgmtFile( dev_name_pf_mgmt );
        if( !mgmtFile.is_open() ) {
            perror( dev_name_pf_mgmt.c_str() );
            return errno;
        }
        mgmtFile << input;
    }

    std::this_thread::sleep_for(std::chrono::seconds(1));
    // initiate rescan "echo 1 > /sys/bus/pci/rescan"
    std::ofstream rescanFile( pciPath + rescanPath );
    if( !rescanFile.is_open() ) {
        perror( std::string( pciPath + rescanPath ).c_str() );
        return errno;
    }
    rescanFile << input;

    return 0;
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

//Sarab: Added for HAL2 support with XOCL GEM Driver

int xclExportBO(xclDeviceHandle handle, unsigned int boHandle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclExportBO(boHandle) : -ENODEV;
}


unsigned int xclImportBO(xclDeviceHandle handle, int fd, unsigned flags)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv) {
    std::cout << __func__ << ", " << std::this_thread::get_id() << ", handle & XOCL Device are bad" << std::endl;
  }
  return drv ? drv->xclImportBO(fd, flags) : -ENODEV;
}

ssize_t xclUnmgdPwrite(xclDeviceHandle handle, unsigned flags, const void *buf,
                       size_t count, uint64_t offset)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclUnmgdPwrite(flags, buf, count, offset) : -ENODEV;
}

int xclGetBOProperties(xclDeviceHandle handle, unsigned int boHandle, xclBOProperties *properties)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclGetBOProperties(boHandle, properties) : -ENODEV;
}

ssize_t xclUnmgdPread(xclDeviceHandle handle, unsigned flags, void *buf,
                      size_t count, uint64_t offset)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclUnmgdPread(flags, buf, count, offset) : -ENODEV;
}

int xclUpgradeFirmwareXSpi(xclDeviceHandle handle, const char *fileName, int index)
{
    awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
    if (!drv)
        return -1;
    return -ENOSYS;
    //return drv->xclUpgradeFirmwareXSpi(fileName, index); Not supported by AWS
}

int xclUnlockDevice(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv) {
    std::cout << "xclUnlockDevice returning -ENODEV\n";
    return -ENODEV;
  } else {
    return drv->xclUnlockDevice() ? 0 : 1;
  }
}

unsigned int xclAllocBO(xclDeviceHandle handle, size_t size, xclBOKind domain, unsigned flags)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclAllocBO(size, domain, flags) : -ENODEV;
}

unsigned int xclAllocUserPtrBO(xclDeviceHandle handle, void *userptr, size_t size, unsigned flags)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclAllocUserPtrBO(userptr, size, flags) : -ENODEV;
}

void xclFreeBO(xclDeviceHandle handle, unsigned int boHandle) {
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return;
  drv->xclFreeBO(boHandle);
}

size_t xclWriteBO(xclDeviceHandle handle, unsigned int boHandle, const void *src, size_t size,
                  size_t seek)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclWriteBO(boHandle, src, size, seek) : -ENODEV;
}

size_t xclReadBO(xclDeviceHandle handle, unsigned int boHandle, void *dst, size_t size,
                 size_t skip)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclReadBO(boHandle, dst, size, skip) : -ENODEV;
}

void *xclMapBO(xclDeviceHandle handle, unsigned int boHandle, bool write)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclMapBO(boHandle, write) : nullptr;
}


int xclSyncBO(xclDeviceHandle handle, unsigned int boHandle, xclBOSyncDirection dir,
              size_t size, size_t offset)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  return drv ? drv->xclSyncBO(boHandle, dir, size, offset) : -ENODEV;
}

unsigned int xclVersion () {
  return 2;
}

int xclGetErrorStatus(xclDeviceHandle handle, xclErrorStatus *info)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
      return -1;
  return -ENOSYS;
  //return drv->xclGetErrorStatus(info); Not supported for AWS
}

int xclXbsak(int argc, char *argv[])
{
    return xcldev::xclXbsak(argc, argv);
}

