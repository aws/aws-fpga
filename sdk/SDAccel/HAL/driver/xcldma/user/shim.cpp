/**
 * Copyright (C) 2015-2016 Xilinx, Inc
 * Author: Sonal Santan
 * XDMA HAL Driver layered on top of XDMA kernel driver
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

#include <sys/types.h>

#ifndef _WINDOWS
// TODO: Windows build support
//    sys/mman.h is linux only header file
//    it is included for mmap
#include <sys/mman.h>
#endif

#ifndef _WINDOWS
// TODO: Windows build support
//    unistd.h is linux only header file
//    it is included for read, write, close, lseek64
#include <unistd.h>
#endif

#include <sys/stat.h>
#include <fcntl.h>

#ifndef _WINDOWS
// TODO: Windows build support
//    sys/ioctl.h is linux only header file
//    it is included for ioctl
#include <sys/ioctl.h>
#endif

#ifndef _WINDOWS
// TODO: Windows build support
//    sys/file.h is linux only header file
//    it is included for flock
#include <sys/file.h>
#endif


#include <cstdio>
#include <cstring>
#include <cassert>
#include <algorithm>
#include <stdlib.h>
#include <thread>
#include <chrono>
#include <iostream>
#include <mutex>

#include "driver/include/xclbin.h"
#include "driver/xcldma/include/xdma-ioctl.h"

#ifdef _WINDOWS
#define __func__ __FUNCTION__
#endif

#ifdef _WINDOWS
#define MAP_FAILED (void *)-1
#endif

#if defined(__PPC64__)
#define OSTAG "-ppc64le"
#else
#define OSTAG ""
#endif

namespace xclxdma {
    const unsigned XDMAShim::TAG = 0X586C0C6C; // XL OpenCL X->58(ASCII), L->6C(ASCII), O->0 C->C L->6C(ASCII);

    xclDeviceInfo2 to_info2(const xclDeviceInfo info) {
        xclDeviceInfo2 info2;
        std::memset(&info2, 0, sizeof(info2));
        info2.mMagic = info.mMagic;
        std::memcpy(info2.mName, info.mName, 256);
        info2.mHALMajorVersion = info.mHALMajorVersion;
        info2.mHALMinorVersion = info.mHALMinorVersion;
        info2.mVendorId = info.mVendorId;
        info2.mDeviceId = info.mDeviceId;
        info2.mSubsystemId = info.mSubsystemId;
        info2.mSubsystemVendorId = info.mSubsystemVendorId;
        info2.mDeviceVersion = info.mDeviceVersion;
        info2.mDDRSize = info.mDDRSize;
        info2.mDataAlignment = info.mDataAlignment;
        info2.mDDRFreeSize = info.mDDRFreeSize;
        info2.mMinTransferSize = info.mMinTransferSize;
        info2.mDDRBankCount = info.mDDRBankCount;
        info2.mOCLFrequency[0] = info.mOCLFrequency;
        info2.mPCIeLinkWidth = info.mPCIeLinkWidth;
        info2.mPCIeLinkSpeed = info.mPCIeLinkSpeed;
        info2.mDMAThreads = info.mDMAThreads;
        return info2;
    }

    int XDMAShim::xclLoadBitstream(const char *fileName) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << fileName << std::endl;
        }

        if (!mLocked)
            return -EPERM;

        std::ifstream stream(fileName);
        if (!stream.is_open()) {
            return errno;
        }

        stream.seekg(0, stream.end);
        int length = stream.tellg();
        stream.seekg(0, stream.beg);
        char *buffer = new char[length];
        stream.read(buffer, length);
        stream.close();
        xclBin *header = (xclBin *)buffer;
        if (std::memcmp(header->m_magic, "xclbin0", 8)) {
            return -EINVAL;
        }

        return xclLoadXclBin(header);
    }


    int XDMAShim::xclLoadXclBin(const xclBin *buffer)
    {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", " << buffer << std::endl;
        }

        if (!mLocked)
            return -EPERM;

#ifndef _WINDOWS
        const unsigned cmd = isUltraScale() ? XDMA_IOCMCAPDOWNLOAD : XDMA_IOCICAPDOWNLOAD;
        xdma_ioc_bitstream obj = {{0X586C0C6C, cmd}, const_cast<xclBin *>(buffer)};
        int ret = ioctl(mUserHandle, cmd, &obj);
        if(0 != ret)
          return ret;

        // If it is an XPR DSA, zero out the DDR again as downloading the XCLBIN
        // reinitializes the DDR and results in ECC error.
        if(isXPR()) {
          if (mLogStream.is_open()) {
              mLogStream << __func__ << "XPR Device found, zeroing out DDR again.." << std::endl;
          }

          if (zeroOutDDR() == false){
            if (mLogStream.is_open()) {
                mLogStream <<  __func__ << "zeroing out DDR failed" << std::endl;
            }
            return -EIO;
          }
        }

        return ret;
#endif
    }

    size_t XDMAShim::xclReadModifyWrite(uint64_t offset, const void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }
#ifndef _WINDOWS
// TODO: Windows build support
//    alignas is defined in c++11
#if GCC_VERSION >= 40800
        alignas(DDR_BUFFER_ALIGNMENT) char buffer[DDR_BUFFER_ALIGNMENT];
#else
        AlignedAllocator<char> alignedBuffer(DDR_BUFFER_ALIGNMENT, DDR_BUFFER_ALIGNMENT);
        char* buffer = alignedBuffer.getBuffer();
#endif
#else
        char buffer[DDR_BUFFER_ALIGNMENT];
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

    size_t XDMAShim::xclWrite(xclAddressSpace space, uint64_t offset, const void *hostBuf, size_t size) {
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
#ifndef _WINDOWS
// TODO: Windows build support
              if (mDataMover->pwrite64(curr,maxDMASize,offset) < 0)
                return -1;
#endif
                offset += maxDMASize;
                curr += maxDMASize;
                size -= maxDMASize;
            }
#ifndef _WINDOWS
// TODO: Windows build support
            if (mDataMover->pwrite64(curr,size,offset) < 0)
              return -1;
#endif
            return totalSize;
        }
        case XCL_ADDR_SPACE_DEVICE_PERFMON:
        {
            if (pcieBarWrite(PERFMON_BAR, offset, hostBuf, size) == 0) {
                return size;
            }
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
            if (pcieBarWrite(ACCELERATOR_BAR, offset, hostBuf, size) == 0) {
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


    size_t XDMAShim::xclReadSkipCopy(uint64_t offset, void *hostBuf, size_t size) {
        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
                       << offset << ", " << hostBuf << ", " << size << std::endl;
        }

        const size_t mod_size = offset % DDR_BUFFER_ALIGNMENT;
        // Need to do Read-Modify-Read
#ifndef _WINDOWS
// TODO: Windows build support
//    alignas is defined in c++11
#if GCC_VERSION >= 40800
        alignas(DDR_BUFFER_ALIGNMENT) char buffer[DDR_BUFFER_ALIGNMENT];
#else
        AlignedAllocator<char> alignedBuffer(DDR_BUFFER_ALIGNMENT, DDR_BUFFER_ALIGNMENT);
        char* buffer = alignedBuffer.getBuffer();
#endif
#else
        char buffer[DDR_BUFFER_ALIGNMENT];
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

    size_t XDMAShim::xclRead(xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size) {
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
#ifndef _WINDOWS
// TODO: Windows build support
              if (mDataMover->pread64(curr,maxDMASize,offset) < 0)
                return -1;
#endif
                offset += maxDMASize;
                curr += maxDMASize;
                size -= maxDMASize;
            }

#ifndef _WINDOWS
// TODO: Windows build support
            if (mDataMover->pread64(curr,size,offset) < 0)
              return -1;
#endif
            return totalSize;
        }
        case XCL_ADDR_SPACE_DEVICE_PERFMON:
        {
            if (pcieBarRead(PERFMON_BAR, offset, hostBuf, size) == 0) {
                return size;
            }
            return -1;
        }
        case XCL_ADDR_KERNEL_CTRL:
        {
            int result = pcieBarRead(ACCELERATOR_BAR, offset, hostBuf, size);
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

    uint64_t XDMAShim::xclAllocDeviceBuffer(size_t size) {
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

    uint64_t XDMAShim::xclAllocDeviceBuffer2(size_t size, xclMemoryDomains domain, unsigned flags)
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

    void XDMAShim::xclFreeDeviceBuffer(uint64_t buf) {
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


    size_t XDMAShim::xclCopyBufferHost2Device(uint64_t dest, const void *src, size_t size, size_t seek) {
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


    size_t XDMAShim::xclCopyBufferDevice2Host(void *dest, uint64_t src, size_t size, size_t skip) {
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


    XDMAShim *XDMAShim::handleCheck(void *handle) {
        // Sanity checks
        if (!handle)
            return 0;
        if (*(unsigned *)handle != TAG)
            return 0;
        if (!((XDMAShim *)handle)->isGood()) {
            return 0;
        }

        return (XDMAShim *)handle;
    }

    unsigned XDMAShim::xclProbe() {
        char file_name_buf[128];
        unsigned i  = 0;
        for (i = 0; i < 64; i++) {
            std::sprintf((char *)&file_name_buf, "/dev/xcldma/xcldma%d_user", i);
#ifndef _WINDOWS
// TODO: Windows build support
//    open, close is defined in unistd.h
            int fd = open(file_name_buf, O_RDWR);
            if (fd < 0) {
                return i;
            }
            close(fd);
#endif
        }
        return i;
    }

    void XDMAShim::initMemoryManager()
    {
        if (!mDeviceInfo.mDDRBankCount)
            return;
        const uint64_t bankSize = mDeviceInfo.mDDRSize / mDeviceInfo.mDDRBankCount;
        uint64_t start = 0;
        for (unsigned i = 0; i < mDeviceInfo.mDDRBankCount; i++) {
            mDDRMemoryManager.push_back(new MemoryManager(bankSize, start, DDR_BUFFER_ALIGNMENT));
            start += bankSize;
        }
    }

    XDMAShim::~XDMAShim()
    {
#ifndef _WINDOWS
// TODO: Windows build support
//    munmap is defined in sys/mman.h
//    close is defined in unistd.h
        if (mUserMap != MAP_FAILED) {
            munmap(mUserMap, MMAP_SIZE_USER);
        }
        if (mUserHandle > 0) {
            close(mUserHandle);
        }

        delete mDataMover;
#endif
        for (auto i : mDDRMemoryManager) {
            delete i;
        }

        if (mLogStream.is_open()) {
            mLogStream << __func__ << ", " << std::this_thread::get_id() << std::endl;
            mLogStream.close();
        }
    }

    XDMAShim::XDMAShim(unsigned index, const char *logfileName,
                       xclVerbosityLevel verbosity) : mTag(TAG), mBoardNumber(index),
                                                      maxDMASize(0xfa0000),
                                                      mLocked(false),
                                                      mOffsets{0x0, 0x0, 0x0, 0x0},
                                                      mOclRegionProfilingNumberSlots(XPAR_AXI_PERF_MON_2_NUMBER_SLOTS)
    {
        mDataMover = new DataMover(mBoardNumber, 1 /* 1 channel each dir */);
        char file_name_buf[128];
        std::sprintf((char *)&file_name_buf, "/dev/xcldma/xcldma%d_user", mBoardNumber);
        mUserHandle = open(file_name_buf, O_RDWR | O_SYNC);

        mUserMap = (char *)mmap(0, MMAP_SIZE_USER, PROT_READ | PROT_WRITE, MAP_SHARED, mUserHandle, 0);
        if (mUserMap == MAP_FAILED) {
            close(mUserHandle);
            mUserHandle = -1;
        }

        if (logfileName && (logfileName[0] != '\0')) {
            mLogStream.open(logfileName);
            mLogStream << "FUNCTION, THREAD ID, ARG..."  << std::endl;
            mLogStream << __func__ << ", " << std::this_thread::get_id() << std::endl;
        }

        // First try the new info2 method and if that fails fall back to legacy info
        if (xclGetDeviceInfo2(&mDeviceInfo)) {
            xclDeviceInfo oldInfo;
            if (xclGetDeviceInfo(&oldInfo)) {
                close(mUserHandle);
                mUserHandle = -1;
            }
            else {
                mDeviceInfo = to_info2(oldInfo);
            }
        }
        initMemoryManager();
    }

    bool XDMAShim::isGood() const {
        if (!mDataMover)
            return false;
        if (mUserHandle < 0)
            return false;
        return mDataMover->isGood();
        // TODO: Add sanity check for card state
    }


    int XDMAShim::pcieBarRead(int bar_num, unsigned long long offset, void* buffer, unsigned long long length) {
        const char *mem = 0;
        switch (bar_num) {
        case 0:
        {
            if ((length + offset) > MMAP_SIZE_USER) {
                return -1;
            }
            mem = mUserMap;
            break;
        }
        default:
        {
            return -1;
        }
        }

        char *qBuf = (char *)buffer;
        while (length >= 4) {
            *(unsigned *)qBuf = *(unsigned *)(mem + offset);
            offset += 4;
            qBuf += 4;
            length -= 4;
        }
        while (length) {
            *qBuf = *(mem + offset);
            offset++;
            qBuf++;
            length--;
        }

//        std::memcpy(buffer, mem + offset, length);
        return 0;
    }

    int XDMAShim::pcieBarWrite(int bar_num, unsigned long long offset, const void* buffer, unsigned long long length) {
        char *mem = 0;
        switch (bar_num) {
        case 0:
        {
            if ((length + offset) > MMAP_SIZE_USER) {
                return -1;
            }
            mem = mUserMap;
            break;
        }
        default:
        {
            return -1;
        }
        }

        char *qBuf = (char *)buffer;
        while (length >= 4) {
            *(unsigned *)(mem + offset) = *(unsigned *)qBuf;
            offset += 4;
            qBuf += 4;
            length -= 4;
        }
        while (length) {
            *(mem + offset) = *qBuf;
            offset++;
            qBuf++;
            length--;
        }

//        std::memcpy(mem + offset, buffer, length);
        return 0;
    }

    bool XDMAShim::zeroOutDDR()
    {
      // Zero out the DDR so MIG ECC believes we have touched all the bits
      // and it does not complain when we try to read back without explicit
      // write. The latter usually happens as a result of read-modify-write
      // TODO: Try and speed this up.
      // [1] Possibly move to kernel mode driver.
      // [2] Zero out specific buffers when they are allocated
      static const unsigned long long BLOCK_SIZE = 0x4000000;
      void *buf = 0;
      if (posix_memalign(&buf, DDR_BUFFER_ALIGNMENT, BLOCK_SIZE))
          return false;
      memset(buf, 0, BLOCK_SIZE);
      mDataMover->pset64(buf, BLOCK_SIZE, 0, mDeviceInfo.mDDRSize/BLOCK_SIZE);
      free(buf);
      return true;
    }

    bool XDMAShim::xclLockDevice()
    {
        if (mDataMover->lock() == false)
            return false;

        if (flock(mUserHandle, LOCK_EX | LOCK_NB) == -1) {
            mDataMover->unlock();
            return false;
        }
        mLocked = true;

        return zeroOutDDR();
    }

    std::string XDMAShim::getDSAName(unsigned short deviceId, unsigned short subsystemId)
    {
        std::string dsa("xilinx:?:?:?");
        const unsigned dsaNum = (deviceId << 16) | subsystemId;
        switch(dsaNum)
        {
        case 0x71380121:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":2.1";
            break;
        case 0x71380122:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":2.2";
            break;
        case 0x71380123:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":2.3";
            break;
        case 0x71380130:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":3.0";
            break;
        case 0x71380131:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":3.1";
            break;
        case 0x71380132:
            dsa = "xilinx:adm-pcie-7v3:1ddr" OSTAG ":3.2";
            break;
        case 0x71380221:
            dsa = "xilinx:adm-pcie-7v3:2ddr" OSTAG ":2.1";
            break;
        case 0x81380121:
            dsa = "xilinx:adm-pcie-ku3:1ddr" OSTAG ":2.1";
            break;
        case 0x81380122:
            dsa = "xilinx:adm-pcie-ku3:1ddr" OSTAG ":2.2";
            break;
        case 0x81380130:
            dsa = "xilinx:adm-pcie-ku3:1ddr" OSTAG ":3.0";
            break;
        case 0x81380221:
            dsa = "xilinx:adm-pcie-ku3:2ddr" OSTAG ":2.1";
            break;
        case 0x81380222:
            dsa = "xilinx:adm-pcie-ku3:2ddr" OSTAG ":2.2";
            break;
        case 0x81380230:
            dsa = "xilinx:adm-pcie-ku3:2ddr" OSTAG ":3.0";
            break;
        case 0x81380231:
            dsa = "xilinx:adm-pcie-ku3:2ddr" OSTAG ":3.1";
            break;
        case 0x81380232:
            dsa = "xilinx:adm-pcie-ku3:2ddr" OSTAG ":3.2";
            break;
        case 0x81381231:
            dsa = "xilinx:adm-pcie-ku3:2ddr-40g:3.1";
            break;
        case 0x81381232:
            dsa = "xilinx:adm-pcie-ku3:2ddr-40g:3.2";
            break;
        case 0x81388221:
            dsa = "xilinx:adm-pcie-ku3:tandem-2ddr:2.1";
            break;
        case 0x81388222:
            dsa = "xilinx:adm-pcie-ku3:tandem-2ddr:2.2";
            break;
        case 0x81388230:
            dsa = "xilinx:adm-pcie-ku3:tandem-2ddr:3.0";
            break;
        case 0x81384221:
            dsa = "xilinx:adm-pcie-ku3:exp-pr-2ddr:2.1";
            break;
        case 0x81384222:
            dsa = "xilinx:adm-pcie-ku3:2ddr-xpr:2.2";
            break;
        case 0x81384230:
            dsa = "xilinx:adm-pcie-ku3:2ddr-xpr:3.0";
            break;
        case 0x81384231:
            dsa = "xilinx:adm-pcie-ku3:2ddr-xpr:3.1";
            break;
        case 0x81384232:
            dsa = "xilinx:adm-pcie-ku3:2ddr-xpr:3.2";
            break;
        case 0x82380222:
            dsa = "xilinx:tul-pcie3-ku115:2ddr:2.2";
            break;
        case 0x82380230:
            dsa = "xilinx:tul-pcie3-ku115:2ddr:3.0";
            break;
        case 0x82380231:
            dsa = "xilinx:tul-pcie3-ku115:2ddr:3.1";
            break;
        case 0x82380232:
            dsa = "xilinx:tul-pcie3-ku115:2ddr:3.2";
            break;
        case 0x82384422:
            dsa = "xilinx:tul-pcie3-ku115:4ddr-xpr:2.2";
            break;
        case 0x82384430:
            dsa = "xilinx:tul-pcie3-ku115:4ddr-xpr:3.0";
            break;
        case 0x82384431:
            dsa = "xilinx:tul-pcie3-ku115:4ddr-xpr:3.1";
            break;
        case 0x82384432:
            dsa = "xilinx:xil-accel-rd-ku115:4ddr-xpr:3.2";
            break;
        case 0x83384431:
            dsa = "xilinx:tul-pcie3-vu095:4ddr-xpr:3.1";
            break;
        case 0x83384432:
            dsa = "xilinx:tul-pcie3-vu095:4ddr-xpr:3.2";
            break;
        case 0x84380231:
            dsa = "xilinx:adm-pcie-8k5:2ddr:3.1";
            break;
        case 0x84380232:
            dsa = "xilinx:adm-pcie-8k5:2ddr:3.2";
            break;
        case 0x923F4232:
            dsa = "xilinx:minotaur-pcie-vu9p:2ddr-xpr:3.2";
            break;
        case 0x923F4432:
            dsa = "xilinx:minotaur-pcie-vu9p:4ddr-xpr:3.2";
            break;

        default:
            break;
        }
        return dsa;
    }

    int XDMAShim::xclGetDeviceInfo2(xclDeviceInfo2 *info)
    {
        std::memset(info, 0, sizeof(xclDeviceInfo2));
        info->mMagic = 0X586C0C6C;
        info->mHALMajorVersion = XCLHAL_MAJOR_VER;
        info->mHALMajorVersion = XCLHAL_MINOR_VER;
        info->mMinTransferSize = DDR_BUFFER_ALIGNMENT;
        info->mDMAThreads = mDataMover->channelCount();
#ifndef _WINDOWS
// TODO: Windows build support
//    XDMA_IOCINFO depends on _IOW, which is defined indirectly by <linux/ioctl.h>
//    ioctl is defined in sys/ioctl.h
        xdma_ioc_info2 obj = {{0X586C0C6C, XDMA_IOCINFO2}};
        int ret = ioctl(mUserHandle, XDMA_IOCINFO2, &obj);
        if (ret)
            return ret;
        info->mVendorId = obj.vendor;
        info->mDeviceId = obj.device;
        info->mSubsystemId = obj.subsystem_device;
        info->mSubsystemVendorId = obj.subsystem_vendor;
        info->mDeviceVersion = obj.subsystem_device & 0x00ff;
#endif
        // TUL cards (0x8238) have 4 GB / bank; other cards have 8 GB memory / bank
        info->mDDRSize = (info->mDeviceId == 0x8238) ? 0x100000000 : 0x200000000;
        info->mDataAlignment = DDR_BUFFER_ALIGNMENT;
        info->mNumClocks = obj.num_clocks;
        for (int i = 0; i < obj.num_clocks; ++i) {
          info->mOCLFrequency[i] = obj.ocl_frequency[i];
        }
        info->mPCIeLinkWidth = obj.pcie_link_width;
        info->mPCIeLinkSpeed = obj.pcie_link_speed;
        info->mDDRBankCount = info->mSubsystemId & 0x0f00;
        info->mDDRBankCount >>= 8;
        if (info->mDDRBankCount == 0)
            info->mDDRBankCount = 1;

        info->mDDRSize *= info->mDDRBankCount;
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

        info->mOnChipTemp  = obj.onchip_temp;
        info->mFanTemp     = obj.fan_temp;
        info->mVInt        = obj.vcc_int;
        info->mVAux        = obj.vcc_aux;
        info->mVBram       = obj.vcc_bram;
        info->mMigCalib    = obj.mig_calibration;

        return 0;
    }

    int XDMAShim::xclGetDeviceInfo(xclDeviceInfo *info)
    {
        std::memset(info, 0, sizeof(xclDeviceInfo));
        info->mMagic = 0X586C0C6C;
        info->mHALMajorVersion = XCLHAL_MAJOR_VER;
        info->mHALMajorVersion = XCLHAL_MINOR_VER;
        info->mMinTransferSize = DDR_BUFFER_ALIGNMENT;
        info->mDMAThreads = mDataMover->channelCount();
#ifndef _WINDOWS
// TODO: Windows build support
//    XDMA_IOCINFO depends on _IOW, which is defined indirectly by <linux/ioctl.h>
//    ioctl is defined in sys/ioctl.h
        xdma_ioc_info obj = {{0X586C0C6C, XDMA_IOCINFO}};
        int ret = ioctl(mUserHandle, XDMA_IOCINFO, &obj);
        if (ret)
            return ret;
        info->mVendorId = obj.vendor;
        info->mDeviceId = obj.device;
        info->mSubsystemId = obj.subsystem_device;
        info->mSubsystemVendorId = obj.subsystem_vendor;
        info->mDeviceVersion = obj.subsystem_device & 0x00ff;
#endif
        // TUL cards (0x8238) have 4 GB / bank; other cards have 8 GB memory / bank
        info->mDDRSize = (info->mDeviceId == 0x8238) ? 0x100000000 : 0x200000000;
        info->mDataAlignment = DDR_BUFFER_ALIGNMENT;
        info->mOCLFrequency = obj.ocl_frequency;
        info->mPCIeLinkWidth = obj.pcie_link_width;
        info->mPCIeLinkSpeed = obj.pcie_link_speed;
        info->mDDRBankCount = info->mSubsystemId & 0x0f00;
        info->mDDRBankCount >>= 8;
        if (info->mDDRBankCount == 0)
            info->mDDRBankCount = 1;

        info->mDDRSize *= info->mDDRBankCount;
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
              << ", clock freq=" << std::dec << info->mOCLFrequency << std::endl;
        }
        return 0;
    }

    int XDMAShim::resetDevice(xclResetKind kind) {
#ifndef _WINDOWS
// TODO: Windows build support
//    XDMA_IOCRESET depends on _IOW, which is defined indirectly by <linux/ioctl.h>
//    ioctl is defined in sys/ioctl.h
        for (auto i : mDDRMemoryManager) {
            i->reset();
        }

        // Call a new IOCTL to just reset the OCL region
        if (kind == XCL_RESET_FULL) {
            xdma_ioc_base obj = {0X586C0C6C, XDMA_IOCHOTRESET};
            return ioctl(mUserHandle, XDMA_IOCHOTRESET, &obj);
        }
        else if (kind == XCL_RESET_KERNEL) {
            xdma_ioc_base obj = {0X586C0C6C, XDMA_IOCOCLRESET};
            return ioctl(mUserHandle, XDMA_IOCOCLRESET, &obj);
        }
        return -EINVAL;
#else
        return 0;
#endif
    }

    int XDMAShim::xclReClock(unsigned freqMHz)
    {
        xdma_ioc_freqscaling obj = {{0X586C0C6C, XDMA_IOCFREQSCALING}, freqMHz};
        return ioctl(mUserHandle, XDMA_IOCFREQSCALING, &obj);
    }

    int XDMAShim::xclReClock2(unsigned short region, const unsigned short *targetFreqMHz)
    {
        xdma_ioc_freqscaling2 obj;
        std::memset(&obj, 0, sizeof(xdma_ioc_freqscaling2));
        obj.base= {0X586C0C6C, XDMA_IOCFREQSCALING2};
        obj.ocl_region = region;
        obj.ocl_target_freq[0] = targetFreqMHz[0];
        obj.ocl_target_freq[1] = targetFreqMHz[1];
        return ioctl(mUserHandle, XDMA_IOCFREQSCALING2, &obj);
    }
}


xclDeviceHandle xclOpen(unsigned index, const char *logfileName, xclVerbosityLevel level)
{
    xclxdma::XDMAShim *handle = new xclxdma::XDMAShim(index, logfileName, level);
    if (!xclxdma::XDMAShim::handleCheck(handle)) {
        delete handle;
        handle = 0;
    }

    return (xclDeviceHandle *)handle;
}

void xclClose(xclDeviceHandle handle)
{
    if (xclxdma::XDMAShim::handleCheck(handle)) {
        delete ((xclxdma::XDMAShim *)handle);
    }
}


int xclGetDeviceInfo(xclDeviceHandle handle, xclDeviceInfo *info)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclGetDeviceInfo(info);
}

int xclGetDeviceInfo2(xclDeviceHandle handle, xclDeviceInfo2 *info)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclGetDeviceInfo2(info);
}

int xclLoadBitstream(xclDeviceHandle handle, const char *xclBinFileName)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclLoadBitstream(xclBinFileName);
}

int xclLoadXclBin(xclDeviceHandle handle, const xclBin *buffer)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclLoadXclBin(buffer);
}

size_t xclWrite(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset, const void *hostBuf, size_t size)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclWrite(space, offset, hostBuf, size);
}

size_t xclRead(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclRead(space, offset, hostBuf, size);
}


uint64_t xclAllocDeviceBuffer(xclDeviceHandle handle, size_t size)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclAllocDeviceBuffer(size);
}


uint64_t xclAllocDeviceBuffer2(xclDeviceHandle handle, size_t size, xclMemoryDomains domain,
                               unsigned flags)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclAllocDeviceBuffer2(size, domain, flags);
}


void xclFreeDeviceBuffer(xclDeviceHandle handle, uint64_t buf)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return;
    return drv->xclFreeDeviceBuffer(buf);
}


size_t xclCopyBufferHost2Device(xclDeviceHandle handle, uint64_t dest, const void *src, size_t size, size_t seek)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclCopyBufferHost2Device(dest, src, size, seek);
}


size_t xclCopyBufferDevice2Host(xclDeviceHandle handle, void *dest, uint64_t src, size_t size, size_t skip)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclCopyBufferDevice2Host(dest, src, size, skip);
}


//This will be deprecated.
int xclUpgradeFirmware(xclDeviceHandle handle, const char *fileName)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclUpgradeFirmware(fileName);
}

int xclUpgradeFirmware2(xclDeviceHandle handle, const char *fileName1, const char* fileName2)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;

    if(!fileName2 || std::strlen(fileName2) == 0)
      return drv->xclUpgradeFirmware(fileName1);
    else
      return drv->xclUpgradeFirmware2(fileName1, fileName2);
}

int xclUpgradeFirmwareXSpi(xclDeviceHandle handle, const char *fileName, int index)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclUpgradeFirmwareXSpi(fileName, index);
}

int xclTestXSpi(xclDeviceHandle handle, int index)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclTestXSpi(index);
}

int xclBootFPGA(xclDeviceHandle handle)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclBootFPGA();
}

unsigned xclProbe()
{
    return xclxdma::XDMAShim::xclProbe();
}


int xclResetDevice(xclDeviceHandle handle, xclResetKind kind)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->resetDevice(kind);
}

int xclReClock(xclDeviceHandle handle, unsigned targetFreqMHz)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclReClock(targetFreqMHz);
}


int xclReClock2(xclDeviceHandle handle, unsigned short region, const unsigned short *targetFreqMHz)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclReClock2(region, targetFreqMHz);
}


int xclLockDevice(xclDeviceHandle handle)
{
    xclxdma::XDMAShim *drv = xclxdma::XDMAShim::handleCheck(handle);
    if (!drv)
        return -1;
    return drv->xclLockDevice() ? 0 : -1;
}

// XSIP watermark, do not delete 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
