/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Sonal Santan
 * AWS HAL Driver layered on top of kernel drivers
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

#ifndef _XDMA_SHIM_H_
#define _XDMA_SHIM_H_

#include "xclhal.h"
#include "xclperf.h"
#include <fstream>
#include <list>
#include <vector>
#include <string>
#include <mutex>

#ifndef INTERNAL_TESTING
#include "fpga_pci.h"
#endif

// Work around GCC 4.8 + XDMA BAR implementation bugs
// With -O3 PCIe BAR read/write are not reliable hence force -O2 as max
// optimization level for pcieBarRead() and pcieBarWrite()
#if defined(__GNUC__) && defined(NDEBUG)
#define SHIM_O2 __attribute__ ((optimize("-O2")))
#else
#define SHIM_O2
#endif

namespace awsbwhal {
    // Memory alignment for DDR and AXI-MM trace access
    template <typename T> class AlignedAllocator {
        void *mBuffer;
        size_t mCount;
    public:
        T *getBuffer() {
            return (T *)mBuffer;
        }

        size_t size() const {
            return mCount * sizeof(T);
        }

        AlignedAllocator(size_t alignment, size_t count) : mBuffer(0), mCount(count) {
            if (posix_memalign(&mBuffer, alignment, count * sizeof(T))) {
                mBuffer = 0;
            }
        }
        ~AlignedAllocator() {
            if (mBuffer)
                free(mBuffer);
        }
    };

    class MemoryManager;
    class DataMover;
    // XDMA Shim
    class AwsXcl{

        struct ELARecord {
            unsigned mStartAddress;
            unsigned mEndAddress;
            unsigned mDataCount;

            std::streampos mDataPos;
            ELARecord() : mStartAddress(0), mEndAddress(0),
                          mDataCount(0), mDataPos(0) {}
        };

        typedef std::list<ELARecord> ELARecordList;

        typedef std::list<std::pair<uint64_t, uint64_t> > PairList;

    public:

        // Bitstreams
        int xclLoadXclBin(const xclBin *buffer);
        int xclUpgradeFirmware(const char *fileName);
        int xclUpgradeFirmware2(const char *file1, const char* file2);
        int xclUpgradeFirmwareXSpi(const char *fileName, int device_index=0);
        int xclTestXSpi(int device_index);
        int xclBootFPGA();
        int resetDevice(xclResetKind kind);
        int xclReClock2(unsigned short region, const unsigned short *targetFreqMHz);

        // Raw read/write
        size_t xclWrite(xclAddressSpace space, uint64_t offset, const void *hostBuf, size_t size);
        size_t xclRead(xclAddressSpace space, uint64_t offset, void *hostBuf, size_t size);

        // Buffer management
        uint64_t xclAllocDeviceBuffer(size_t size);
        uint64_t xclAllocDeviceBuffer2(size_t size, xclMemoryDomains domain, unsigned flags);
        void xclFreeDeviceBuffer(uint64_t buf);
        size_t xclCopyBufferHost2Device(uint64_t dest, const void *src, size_t size, size_t seek);
        size_t xclCopyBufferDevice2Host(void *dest, uint64_t src, size_t size, size_t skip);

        // Performance monitoring
        // Control
        double xclGetDeviceClockFreqMHz();
        double xclGetReadMaxBandwidthMBps();
        double xclGetWriteMaxBandwidthMBps();
        void xclSetOclRegionProfilingNumberSlots(uint32_t numSlots);
        size_t xclPerfMonClockTraining(xclPerfMonType type);
        // Counters
        size_t xclPerfMonStartCounters(xclPerfMonType type);
        size_t xclPerfMonStopCounters(xclPerfMonType type);
        size_t xclPerfMonReadCounters(xclPerfMonType type, xclCounterResults& counterResults);
		
        //debug related
        uint64_t getProtocolCheckerBaseAddress(int type);
        uint32_t getCheckerNumberSlots(int type);
        size_t xclDebugReadCounters(xclDebugCountersResults* debugResult);
        size_t xclDebugReadCheckers(xclDebugCheckersResults* checkerResult);

        // Trace
        size_t xclPerfMonStartTrace(xclPerfMonType type, uint32_t startTrigger);
        size_t xclPerfMonStopTrace(xclPerfMonType type);
        uint32_t xclPerfMonGetTraceCount(xclPerfMonType type);
        size_t xclPerfMonReadTrace(xclPerfMonType type, xclTraceResultsVector& traceVector);

        // Sanity checks
        int xclGetDeviceInfo2(xclDeviceInfo2 *info);
        static AwsXcl *handleCheck(void *handle);
        static unsigned xclProbe();
        bool xclLockDevice();
        unsigned getTAG() const {
            return mTag;
        }
        bool isGood() const;
	bool is4DDR() {return m4DDR;}; 

        ~AwsXcl();
        AwsXcl(unsigned index, const char *logfileName, xclVerbosityLevel verbosity);

    private:

        int xclLoadAxlf(const axlf *buffer);
        bool zeroOutDDR();

        bool isXPR() const {
            return true;
        }

        bool isMultipleOCLClockSupported() {
          unsigned dsaNum = ((mDeviceInfo.mDeviceId << 16) | mDeviceInfo.mSubsystemId);
          // 0x82384431 : TUL KU115 4ddr 3.1 DSA
          return ((dsaNum == 0x82384431)  || (dsaNum == 0x82384432))? true : false;
        }

        bool isUltraScale() const {
            return (mDeviceInfo.mDeviceId & 0x8000);
        }
        void initMemoryManager();

        // Core DMA code
        // Upper two bytes denote PF, lower two bytes denote BAR
        // USERPF == 0x0
        // MGTPF == 0x10000
        SHIM_O2 int pcieBarRead(unsigned int pf_bar, unsigned long long offset, void* buffer, unsigned long long length);
        SHIM_O2 int pcieBarWrite(unsigned int pf_bar, unsigned long long offset, const void* buffer, unsigned long long length);
        int freezeAXIGate();
        int freeAXIGate();

        // PROM flashing
        int prepare(unsigned startAddress, unsigned endAddress);
        int program(std::ifstream& mcsStream, const ELARecord& record);
        int program(std::ifstream& mcsStream);
        int waitForReady(unsigned code, bool verbose = true);
        int waitAndFinish(unsigned code, unsigned data, bool verbose = true);

        //XSpi flashing.
        bool prepareXSpi();
        int programXSpi(std::ifstream& mcsStream, const ELARecord& record);
        int programXSpi(std::ifstream& mcsStream);
        bool waitTxEmpty();
        bool isFlashReady();
        //bool windDownWrites();
        bool bulkErase();
        bool sectorErase(unsigned Addr);
        bool writeEnable();
	int setDDRCount(const axlf* buffer);
#if 0
	bool dataTransfer(bool read);
#endif
        bool readPage(unsigned addr, uint8_t readCmd = 0xff);
        bool writePage(unsigned addr, uint8_t writeCmd = 0xff);
        unsigned readReg(unsigned offset);
        int writeReg(unsigned regOffset, unsigned value);
        bool finalTransfer(uint8_t *sendBufPtr, uint8_t *recvBufPtr, int byteCount);
        bool getFlashId();
        //All remaining read /write register commands can be issued through this function.
        bool readRegister(unsigned commandCode, unsigned bytes);
        bool writeRegister(unsigned commandCode, unsigned value, unsigned bytes);
        bool select4ByteAddressMode();
        bool deSelect4ByteAddressMode();


        // Performance monitoring helper functions
        bool isDSAVersion(unsigned majorVersion, unsigned minorVersion, bool onlyThisVersion);
        unsigned getBankCount();
        uint64_t getHostTraceTimeNsec();
        uint64_t getPerfMonBaseAddress(xclPerfMonType type);
        uint64_t getPerfMonFifoBaseAddress(xclPerfMonType type, uint32_t fifonum);
        uint64_t getPerfMonFifoReadBaseAddress(xclPerfMonType type, uint32_t fifonum);
        uint32_t getPerfMonNumberSlots(xclPerfMonType type);
        uint32_t getPerfMonNumberSamples(xclPerfMonType type);
        uint32_t getPerfMonNumberFifos(xclPerfMonType type);
        uint32_t getPerfMonByteScaleFactor(xclPerfMonType type);
        uint8_t  getPerfMonShowIDS(xclPerfMonType type);
        uint8_t  getPerfMonShowLEN(xclPerfMonType type);
        uint32_t getPerfMonSlotStartBit(xclPerfMonType type, uint32_t slotnum);
        uint32_t getPerfMonSlotDataWidth(xclPerfMonType type, uint32_t slotnum);
        size_t resetFifos(xclPerfMonType type);
        uint32_t bin2dec(std::string str, int start, int number);
        uint32_t bin2dec(const char * str, int start, int number);
        std::string dec2bin(uint32_t n);
        std::string dec2bin(uint32_t n, unsigned bits);
        static const std::string getDSAName(unsigned short deviceId, unsigned short subsystemId);

    private:
        // This is a hidden signature of this class and helps in preventing
        // user errors when incorrect pointers are passed in as handles.
        const unsigned mTag;
        const int mBoardNumber;
        const int mDMADeviceNodeNumber;
        const size_t maxDMASize;
        bool mLocked;
        const uint64_t mOffsets[XCL_ADDR_SPACE_MAX];
        DataMover *mDataMover;
#ifdef INTERNAL_TESTING
        int mUserHandle;
        int mMgtHandle;
#else
	pci_bar_handle_t ocl_kernel_bar; // AppPF BAR0 for OpenCL kernels
	pci_bar_handle_t sda_mgmt_bar;; // MgmtPF BAR4, for SDAccel Perf mon etc
	pci_bar_handle_t ocl_global_mem_bar; // AppPF BAR4
#endif
        uint32_t mOclRegionProfilingNumberSlots;

        char *mUserMap;
        std::ofstream mLogStream;
        xclVerbosityLevel mVerbosity;
        std::string mBinfile;
        ELARecordList mRecordList;
        std::vector<MemoryManager *> mDDRMemoryManager;
        xclDeviceInfo2 mDeviceInfo;
	bool m4DDR;

    public:
        static const unsigned TAG;
    };
}

#endif
