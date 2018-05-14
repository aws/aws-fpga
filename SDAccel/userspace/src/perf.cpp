/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Performance Monitoring using PCIe for AWS HAL Driver
 * Author: Paul Schumacher
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
#include "datamover.h"
#include "perfmon_parameters.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <cstdio>
#include <cstring>
#include <cassert>
#include <algorithm>
#include <thread>
#include <vector>
#include <time.h>

#ifdef _WINDOWS
#define __func__ __FUNCTION__
#endif

namespace awsbwhal {
  // ****************
  // Helper functions
  // ****************

  unsigned AwsXcl::getBankCount() {
    return mDeviceInfo.mDDRBankCount;
  }

  void AwsXcl::xclSetOclRegionProfilingNumberSlots(uint32_t numSlots) {
    mOclRegionProfilingNumberSlots = numSlots;
  }

  // Get host timestamp to write to APM
  // IMPORTANT NOTE: this *must* be compatible with the method of generating
  // timestamps as defined in RTProfile::getTraceTime()
  uint64_t AwsXcl::getHostTraceTimeNsec() {
    struct timespec now;
    int err;
    if ((err = clock_gettime(CLOCK_MONOTONIC, &now)) < 0)
      return 0;

    return (uint64_t) now.tv_sec * 1000000000UL + (uint64_t) now.tv_nsec;
  }

  uint64_t AwsXcl::getPerfMonBaseAddress(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY) return PERFMON0_OFFSET;
    if (type == XCL_PERF_MON_HOST_INTERFACE) return PERFMON1_OFFSET;
    if (type == XCL_PERF_MON_OCL_REGION) return PERFMON2_OFFSET;
    return 0;
  }

  uint64_t AwsXcl::getPerfMonFifoBaseAddress(xclPerfMonType type, uint32_t fifonum) {
    if (type == XCL_PERF_MON_MEMORY) {
      return PERFMON0_OFFSET + XPAR_AXI_PERF_MON_0_TRACE_OFFSET_0;
    }
    if (type == XCL_PERF_MON_OCL_REGION) {
      if (fifonum == 0) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_0);
      if (fifonum == 1) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_1);
      if (fifonum == 2) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_2);
      return 0;
    }
    return 0;
  }

  uint64_t AwsXcl::getPerfMonFifoReadBaseAddress(xclPerfMonType type, uint32_t fifonum) {
    if (type == XCL_PERF_MON_MEMORY) {
      // Use AXI-MM to access trace FIFO
      return XPAR_AXI_PERF_MON_0_TRACE_OFFSET_AXI_FULL;
    }
    if (type == XCL_PERF_MON_OCL_REGION) {
      if (fifonum == 0) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_0);
      if (fifonum == 1) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_1);
      if (fifonum == 2) return (PERFMON2_OFFSET + XPAR_AXI_PERF_MON_2_TRACE_OFFSET_2);
      return 0;
    }
    return 0;
  }

  uint32_t AwsXcl::getPerfMonNumberFifos(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY)
      return XPAR_AXI_PERF_MON_0_TRACE_NUMBER_FIFO;
    if (type == XCL_PERF_MON_HOST_INTERFACE)
      return XPAR_AXI_PERF_MON_1_TRACE_NUMBER_FIFO;
    if (type == XCL_PERF_MON_OCL_REGION) {
      if (mOclRegionProfilingNumberSlots > 4)
        return 3;
      else
        return 2;
    }
    return 0;
  }

  uint32_t AwsXcl::getPerfMonNumberSlots(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY) {
      return (getBankCount() + 1);
    }
    if (type == XCL_PERF_MON_HOST_INTERFACE) {
      return XPAR_AXI_PERF_MON_1_NUMBER_SLOTS;
    }
    if (type == XCL_PERF_MON_OCL_REGION) {
      return mOclRegionProfilingNumberSlots;
    }
    return 1;
  }

  uint32_t AwsXcl::getPerfMonNumberSamples(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY) return XPAR_AXI_PERF_MON_0_TRACE_NUMBER_SAMPLES;
    if (type == XCL_PERF_MON_HOST_INTERFACE) return XPAR_AXI_PERF_MON_1_TRACE_NUMBER_SAMPLES;
    if (type == XCL_PERF_MON_OCL_REGION) return XPAR_AXI_PERF_MON_2_TRACE_NUMBER_SAMPLES;
    return 0;
  }

  uint32_t AwsXcl::getPerfMonByteScaleFactor(xclPerfMonType type) {
    return 1;
  }

  uint8_t AwsXcl::getPerfMonShowIDS(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY) {
      if (getBankCount() > 1)
        return XPAR_AXI_PERF_MON_0_SHOW_AXI_IDS_2DDR;
      return XPAR_AXI_PERF_MON_0_SHOW_AXI_IDS;
    }
    if (type == XCL_PERF_MON_HOST_INTERFACE) {
      return XPAR_AXI_PERF_MON_1_SHOW_AXI_IDS;
    }
    if (type == XCL_PERF_MON_OCL_REGION) {
      return XPAR_AXI_PERF_MON_2_SHOW_AXI_IDS;
    }
    return 0;
  }

  uint8_t AwsXcl::getPerfMonShowLEN(xclPerfMonType type) {
    if (type == XCL_PERF_MON_MEMORY) {
      if (getBankCount() > 1)
        return XPAR_AXI_PERF_MON_0_SHOW_AXI_LEN_2DDR;
      return XPAR_AXI_PERF_MON_0_SHOW_AXI_LEN;
    }
    if (type == XCL_PERF_MON_HOST_INTERFACE) {
      return XPAR_AXI_PERF_MON_1_SHOW_AXI_LEN;
    }
    if (type == XCL_PERF_MON_OCL_REGION) {
      return XPAR_AXI_PERF_MON_2_SHOW_AXI_LEN;
    }
    return 0;
  }

  uint32_t AwsXcl::getPerfMonSlotStartBit(xclPerfMonType type, uint32_t slotnum) {
    // NOTE: ID widths also set to 5 in HEAD/data/sdaccel/board_support/alpha_data/common/xclplat/xclplat_ip.tcl
    uint32_t bitsPerID = 5;
    uint8_t showIDs = getPerfMonShowIDS(type);
    uint8_t showLen = getPerfMonShowLEN(type);
    uint32_t bitsPerSlot = 10 + (bitsPerID * 4 * showIDs) + (16 * showLen);
    return (18 + (bitsPerSlot * slotnum));
  }

  uint32_t AwsXcl::getPerfMonSlotDataWidth(xclPerfMonType type, uint32_t slotnum) {
    if (slotnum == 0) return XPAR_AXI_PERF_MON_0_SLOT0_DATA_WIDTH;
    if (slotnum == 1) return XPAR_AXI_PERF_MON_0_SLOT1_DATA_WIDTH;
    if (slotnum == 2) return XPAR_AXI_PERF_MON_0_SLOT2_DATA_WIDTH;
    if (slotnum == 3) return XPAR_AXI_PERF_MON_0_SLOT3_DATA_WIDTH;
    if (slotnum == 4) return XPAR_AXI_PERF_MON_0_SLOT4_DATA_WIDTH;
    if (slotnum == 5) return XPAR_AXI_PERF_MON_0_SLOT5_DATA_WIDTH;
    if (slotnum == 6) return XPAR_AXI_PERF_MON_0_SLOT6_DATA_WIDTH;
    if (slotnum == 7) return XPAR_AXI_PERF_MON_0_SLOT7_DATA_WIDTH;
    return XPAR_AXI_PERF_MON_0_SLOT0_DATA_WIDTH;
  }

  // Get the device clock frequency (in MHz)
  double AwsXcl::xclGetDeviceClockFreqMHz() {
    unsigned clockFreq = mDeviceInfo.mOCLFrequency[0];
    if (clockFreq == 0)
      clockFreq = 200;

    //if (mLogStream.is_open())
    //  mLogStream << __func__ << ": clock freq = " << clockFreq << std::endl;
    return ((double)clockFreq);
  }

  // Get the maximum bandwidth for host reads from the device (in MB/sec)
  // NOTE: for now, set to: (256/8 bytes) * 300 MHz = 9600 MBps
  double AwsXcl::xclGetReadMaxBandwidthMBps() {
    return 9600.0;
  }

  // Get the maximum bandwidth for host writes to the device (in MB/sec)
  // NOTE: for now, set to: (256/8 bytes) * 300 MHz = 9600 MBps
  double AwsXcl::xclGetWriteMaxBandwidthMBps() {
    return 9600.0;
  }

  // Convert binary string to decimal
  uint32_t AwsXcl::bin2dec(std::string str, int start, int number) {
    return bin2dec(str.c_str(), start, number);
  }

  // Convert binary char * to decimal
  uint32_t AwsXcl::bin2dec(const char* ptr, int start, int number) {
    const char* temp_ptr = ptr + start;
    uint32_t value = 0;
    int i = 0;

    do {
      if (*temp_ptr != '0' && *temp_ptr!= '1')
        return value;
      value <<= 1;
      if(*temp_ptr=='1')
        value += 1;
      i++;
      temp_ptr++;
    } while (i < number);

    return value;
  }

  // Convert decimal to binary string
  // NOTE: length of string is always sizeof(uint32_t) * 8
  std::string AwsXcl::dec2bin(uint32_t n) {
    char result[(sizeof(uint32_t) * 8) + 1];
    unsigned index = sizeof(uint32_t) * 8;
    result[index] = '\0';

    do {
      result[ --index ] = '0' + (n & 1);
    } while (n >>= 1);

    for (int i=index-1; i >= 0; --i)
      result[i] = '0';

    return std::string( result );
  }

  // Convert decimal to binary string of length bits
  std::string AwsXcl::dec2bin(uint32_t n, unsigned bits) {
    char result[bits + 1];
    unsigned index = bits;
    result[index] = '\0';

    do result[ --index ] = '0' + (n & 1);
    while (n >>= 1);

    for (int i=index-1; i >= 0; --i)
      result[i] = '0';

    return std::string( result );
  }

  // Reset all APM trace AXI stream FIFOs
  size_t AwsXcl::resetFifos(xclPerfMonType type) {
    uint64_t resetCoreAddress[] = {
        getPerfMonFifoBaseAddress(type, 0) + AXI_FIFO_SRR,
        getPerfMonFifoBaseAddress(type, 1) + AXI_FIFO_SRR,
        getPerfMonFifoBaseAddress(type, 2) + AXI_FIFO_SRR
    };

    uint64_t resetFifoAddress[] = {
        getPerfMonFifoBaseAddress(type, 0) + AXI_FIFO_RDFR,
        getPerfMonFifoBaseAddress(type, 1) + AXI_FIFO_RDFR,
        getPerfMonFifoBaseAddress(type, 2) + AXI_FIFO_RDFR
    };

    size_t size = 0;
    uint32_t regValue = AXI_FIFO_RESET_VALUE;

    for (int f=0; f < XPAR_AXI_PERF_MON_0_TRACE_NUMBER_FIFO; f++) {
      size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, resetCoreAddress[f], &regValue, 4);
      size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, resetFifoAddress[f], &regValue, 4);
    }

    return size;
  }

  // ********
  // Counters
  // ********

  // Start device counters performance monitoring
  size_t AwsXcl::xclPerfMonStartCounters(xclPerfMonType type) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
          << type << ", Start device counters..." << std::endl;
    }

    size_t size = 0;
    uint32_t regValue;
    uint64_t baseAddress = getPerfMonBaseAddress(type);

    // 1. Reset APM metric counters
    size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    regValue = regValue | XAPM_CR_MCNTR_RESET_MASK;
    size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    regValue = regValue & ~(XAPM_CR_MCNTR_RESET_MASK);
    size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    // 2. Start APM metric counters
    regValue = regValue | XAPM_CR_MCNTR_ENABLE_MASK;
    size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    // 3. Specify APM metric counters to _not_ reset after reading
    regValue = 0x0;
    size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_SICR_OFFSET, &regValue, 4);

    // 4. Read from sample register to ensure total time is read again at end
    size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_SR_OFFSET, &regValue, 4);

    return size;
  }

  // Stop both profile and trace performance monitoring
  size_t AwsXcl::xclPerfMonStopCounters(xclPerfMonType type) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
          << type << ", Stop and reset device counters..." << std::endl;
    }

    size_t size = 0;
    uint32_t regValue;
    uint64_t baseAddress = getPerfMonBaseAddress(type);

    // 1. Stop APM metric counters
    size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    regValue = regValue & ~(XAPM_CR_MCNTR_ENABLE_MASK);
    size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_CTL_OFFSET, &regValue, 4);

    return size;
  }

  // Read APM performance counters
  size_t AwsXcl::xclPerfMonReadCounters(xclPerfMonType type, xclCounterResults& counterResults) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << type << ", " << &counterResults
      << ", Read device counters..." << std::endl;
    }

    // Initialize all values in struct to 0
    memset(&counterResults, 0, sizeof(xclCounterResults));

    size_t size = 0;
    uint32_t scaleFactor = getPerfMonByteScaleFactor(type);
    uint64_t baseAddress = getPerfMonBaseAddress(type);

    uint64_t intervalAddress = baseAddress + XAPM_SR_OFFSET;
    uint64_t metricAddress[] = {
        // Slot 0
        baseAddress + XAPM_SMC0_OFFSET,  baseAddress + XAPM_SMC1_OFFSET,
        baseAddress + XAPM_SMC2_OFFSET,  baseAddress + XAPM_SMC3_OFFSET,
        baseAddress + XAPM_SMC4_OFFSET,  baseAddress + XAPM_SMC5_OFFSET,
        baseAddress + XAPM_SMC48_OFFSET, baseAddress + XAPM_SMC49_OFFSET,
        // Slot 1
        baseAddress + XAPM_SMC6_OFFSET,  baseAddress + XAPM_SMC7_OFFSET,
        baseAddress + XAPM_SMC8_OFFSET,  baseAddress + XAPM_SMC9_OFFSET,
        baseAddress + XAPM_SMC10_OFFSET, baseAddress + XAPM_SMC11_OFFSET,
        baseAddress + XAPM_SMC50_OFFSET, baseAddress + XAPM_SMC51_OFFSET,
        // Slot 2
        baseAddress + XAPM_SMC12_OFFSET, baseAddress + XAPM_SMC13_OFFSET,
        baseAddress + XAPM_SMC14_OFFSET, baseAddress + XAPM_SMC15_OFFSET,
        baseAddress + XAPM_SMC16_OFFSET, baseAddress + XAPM_SMC17_OFFSET,
        baseAddress + XAPM_SMC52_OFFSET, baseAddress + XAPM_SMC53_OFFSET,
        // Slot 3
        baseAddress + XAPM_SMC18_OFFSET, baseAddress + XAPM_SMC19_OFFSET,
        baseAddress + XAPM_SMC20_OFFSET, baseAddress + XAPM_SMC21_OFFSET,
        baseAddress + XAPM_SMC22_OFFSET, baseAddress + XAPM_SMC23_OFFSET,
        baseAddress + XAPM_SMC54_OFFSET, baseAddress + XAPM_SMC55_OFFSET,
        // Slot 4
        baseAddress + XAPM_SMC24_OFFSET, baseAddress + XAPM_SMC25_OFFSET,
        baseAddress + XAPM_SMC26_OFFSET, baseAddress + XAPM_SMC27_OFFSET,
        baseAddress + XAPM_SMC28_OFFSET, baseAddress + XAPM_SMC29_OFFSET,
        baseAddress + XAPM_SMC56_OFFSET, baseAddress + XAPM_SMC57_OFFSET,
        // Slot 5
        baseAddress + XAPM_SMC30_OFFSET, baseAddress + XAPM_SMC31_OFFSET,
        baseAddress + XAPM_SMC32_OFFSET, baseAddress + XAPM_SMC33_OFFSET,
        baseAddress + XAPM_SMC34_OFFSET, baseAddress + XAPM_SMC35_OFFSET,
        baseAddress + XAPM_SMC58_OFFSET, baseAddress + XAPM_SMC59_OFFSET,
        // Slot 6
        baseAddress + XAPM_SMC36_OFFSET, baseAddress + XAPM_SMC37_OFFSET,
        baseAddress + XAPM_SMC38_OFFSET, baseAddress + XAPM_SMC39_OFFSET,
        baseAddress + XAPM_SMC40_OFFSET, baseAddress + XAPM_SMC41_OFFSET,
        baseAddress + XAPM_SMC60_OFFSET, baseAddress + XAPM_SMC61_OFFSET,
        // Slot 7
        baseAddress + XAPM_SMC42_OFFSET, baseAddress + XAPM_SMC43_OFFSET,
        baseAddress + XAPM_SMC44_OFFSET, baseAddress + XAPM_SMC45_OFFSET,
        baseAddress + XAPM_SMC46_OFFSET, baseAddress + XAPM_SMC47_OFFSET,
        baseAddress + XAPM_SMC62_OFFSET, baseAddress + XAPM_SMC63_OFFSET
    };

    // Read sample interval register
    // NOTE: this also latches the sampled metric counters
    uint32_t sampleInterval;
    size_t ret = xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, intervalAddress, &sampleInterval, 4);
    if (ret < 0) return ret;
    counterResults.SampleIntervalUsec = sampleInterval / xclGetDeviceClockFreqMHz();

    // Read all sampled metric counters
    uint32_t countnum = 0;
    uint32_t numSlots = getPerfMonNumberSlots(type);
    //counterResults.NumSlots = numSlots;

    uint32_t temp[XAPM_METRIC_COUNTERS_PER_SLOT];

    for (uint32_t s=0; s < numSlots; s++) {
      for (int c=0; c < XAPM_METRIC_COUNTERS_PER_SLOT; c++)
        size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, metricAddress[countnum++], &temp[c], 4);

      counterResults.WriteBytes[s]      = temp[XAPM_METRIC_WRITE_BYTES] * scaleFactor;
      counterResults.WriteTranx[s]      = temp[XAPM_METRIC_WRITE_TRANX];
      counterResults.WriteLatency[s]    = temp[XAPM_METRIC_WRITE_LATENCY];
      counterResults.WriteMinLatency[s] = (temp[XAPM_METRIC_WRITE_MIN_MAX] & XAPM_MIN_LATENCY_MASK) >> XAPM_MIN_LATENCY_SHIFT;
      counterResults.WriteMaxLatency[s] = (temp[XAPM_METRIC_WRITE_MIN_MAX] & XAPM_MAX_LATENCY_MASK) >> XAPM_MAX_LATENCY_SHIFT;

      counterResults.ReadBytes[s]       = temp[XAPM_METRIC_READ_BYTES] * scaleFactor;
      counterResults.ReadTranx[s]       = temp[XAPM_METRIC_READ_TRANX];
      counterResults.ReadLatency[s]     = temp[XAPM_METRIC_READ_LATENCY];
      counterResults.ReadMinLatency[s] = (temp[XAPM_METRIC_READ_MIN_MAX] & XAPM_MIN_LATENCY_MASK) >> XAPM_MIN_LATENCY_SHIFT;
      counterResults.ReadMaxLatency[s] = (temp[XAPM_METRIC_READ_MIN_MAX] & XAPM_MAX_LATENCY_MASK) >> XAPM_MAX_LATENCY_SHIFT;
    }

    return size;
  }

  // *****
  // Trace
  // *****

  // Clock training used in converting device trace timestamps to host domain
  size_t AwsXcl::xclPerfMonClockTraining(xclPerfMonType type) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
          << type << ", Send clock training..." << std::endl;
    }

    size_t size = 0;
    uint64_t baseAddress = getPerfMonBaseAddress(type);

    // Send host timestamps to target device
    // NOTE: this is used for training to interpolate between time domains
    for (int i=0; i < 3; i++) {
#if 1
      uint64_t hostTimeNsec = getHostTraceTimeNsec();

      uint32_t hostTimeHigh = hostTimeNsec >> 32;
      uint32_t hostTimeLow  = hostTimeNsec & 0xffffffff;
#else
      // Test values
      uint32_t hostTimeHigh = 0xf00df00d;
      uint32_t hostTimeLow  = 0xdeadbeef;
#endif

      // Send upper then lower 32 bits of host timestamp to APM SW data register
      size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_SWD_OFFSET, &hostTimeHigh, 4);
      size += xclWrite(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress + XAPM_SWD_OFFSET, &hostTimeLow, 4);

      if (mLogStream.is_open()) {
        mLogStream << "  Host timestamp: 0x" << std::hex << hostTimeHigh
            << " " << hostTimeLow << std::dec << std::endl;
      }
    }

    return size;
  }

  // Start trace performance monitoring
  size_t AwsXcl::xclPerfMonStartTrace(xclPerfMonType type, uint32_t startTrigger) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << type << ", " << startTrigger
      << ", Start device tracing..." << std::endl;
    }

    size_t size = 0;
    uint32_t regValue;
    uint64_t ctrlAddress = getPerfMonBaseAddress(type) + XAPM_CTL_OFFSET;
    xclAddressSpace addressSpace = (type == XCL_PERF_MON_OCL_REGION) ?
        XCL_ADDR_KERNEL_CTRL : XCL_ADDR_SPACE_DEVICE_PERFMON;

    // 1. Reset APM trace stream FIFO
    size += xclRead(addressSpace, ctrlAddress, &regValue, 4);

    regValue = regValue | XAPM_CR_FIFO_RESET_MASK;
    size += xclWrite(addressSpace, ctrlAddress, &regValue, 4);

    regValue = regValue & ~(XAPM_CR_FIFO_RESET_MASK);
    size += xclWrite(addressSpace, ctrlAddress, &regValue, 4);

    // 2. Start APM event log
    regValue = regValue | XAPM_CR_EVENTLOG_ENABLE_MASK;
    size += xclWrite(addressSpace, ctrlAddress, &regValue, 4);

    // 3. Reset trace FIFOs
    size += resetFifos(type);

    // 4. Send host timestamps to target device
    size += xclPerfMonClockTraining(type);

    // 5. Disable host monitoring on slot 1
    // TODO: replace check for value of startTrigger (temp way
    //       of keeping slot 1 enabled in 06_perfmon test)
    if ((type == XCL_PERF_MON_MEMORY) && (startTrigger == 0)) {
      regValue = 0xFFFFFF0F;
      uint64_t enableTraceAddress = getPerfMonBaseAddress(type) + XAPM_ENT_OFFSET;
      size += xclWrite(addressSpace, enableTraceAddress, &regValue, 4);
    }

    // 6. Write to event trace trigger register
    // TODO: add support for triggering in device here
    //size += xclWrite(addressSpace, TBD, &startTrigger, 4);

    return size;
  }

  // Stop trace performance monitoring
  size_t AwsXcl::xclPerfMonStopTrace(xclPerfMonType type) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id() << ", "
          << type << ", Stop and reset device tracing..." << std::endl;
    }

    size_t size = 0;
    uint32_t regValue;
    uint64_t ctrlAddress = getPerfMonBaseAddress(type) + XAPM_CTL_OFFSET;
    xclAddressSpace addressSpace = (type == XCL_PERF_MON_OCL_REGION) ?
        XCL_ADDR_KERNEL_CTRL : XCL_ADDR_SPACE_DEVICE_PERFMON;

    // 1. Stop APM event log and metric counters
    size += xclRead(addressSpace, ctrlAddress, &regValue, 4);

    regValue = regValue & ~(XAPM_CR_EVENTLOG_ENABLE_MASK);
    size += xclWrite(addressSpace, ctrlAddress, &regValue, 4);

    size += resetFifos(type);

    return size;
  }

  // Get trace word count
  uint32_t AwsXcl::xclPerfMonGetTraceCount(xclPerfMonType type) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << type << std::endl;
    }

    xclAddressSpace addressSpace = (type == XCL_PERF_MON_OCL_REGION) ?
        XCL_ADDR_KERNEL_CTRL : XCL_ADDR_SPACE_DEVICE_PERFMON;

    // Only read first FIFO (and assume the others have the same # words)
    // NOTE: we do this for speed improvements
    uint32_t fifoCount;
    xclRead(addressSpace, getPerfMonFifoBaseAddress(type, 0) + AXI_FIFO_RLR, &fifoCount, 4);
    // Read bits 22:0 per AXI-Stream FIFO product guide (PG080, 10/1/14)
    uint32_t numBytes = fifoCount & 0x7FFFFF;

    uint32_t numSamples = 0;
    if (type == XCL_PERF_MON_MEMORY)
      numSamples = numBytes / (XPAR_AXI_PERF_MON_0_TRACE_WORD_WIDTH/8);
    else
      numSamples = numBytes >> 2;

    if (mLogStream.is_open()) {
      mLogStream << "  No. of trace samples = " << std::dec << numSamples
          << " (fifoCount = 0x" << std::hex << fifoCount << ")" << std::dec << std::endl;
    }

    return numSamples;
  }

  // Read all values from APM trace AXI stream FIFOs
  size_t AwsXcl::xclPerfMonReadTrace(xclPerfMonType type, xclTraceResultsVector& traceVector) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << type << ", " << &traceVector
      << ", Reading device trace stream..." << std::endl;
    }

    traceVector.mLength = 0;

    uint32_t numSamples = xclPerfMonGetTraceCount(type);
    if (numSamples == 0)
      return 0;

    uint64_t fifoReadAddress[] = {0, 0, 0};
    if (type == XCL_PERF_MON_MEMORY) {
      fifoReadAddress[0] = getPerfMonFifoReadBaseAddress(type, 0) + AXI_FIFO_RDFD_AXI_FULL;
    }
    else {
      for (int i=0; i < 3; i++)
        fifoReadAddress[i] = getPerfMonFifoReadBaseAddress(type, i) + AXI_FIFO_RDFD;
    }

    xclAddressSpace addressSpace = (type == XCL_PERF_MON_OCL_REGION) ?
        XCL_ADDR_KERNEL_CTRL : XCL_ADDR_SPACE_DEVICE_PERFMON;
    uint32_t numSlots = getPerfMonNumberSlots(type);
    uint32_t numFifos = getPerfMonNumberFifos(type);

    size_t size = 0;
#ifndef _WINDOWS
    // TODO: Windows build support
    //    runtime array size is not supported
    uint32_t temp[numFifos];
    memset(&temp, 0, numFifos*sizeof(uint32_t));
#else
    uint32_t temp[3];
    memset(&temp, 0, 3*sizeof(uint32_t));
#endif

    // Limit to max number of samples so we don't overrun trace buffer on host
    uint32_t maxSamples = getPerfMonNumberSamples(type);
    numSamples = (numSamples > maxSamples) ? maxSamples : numSamples;
    traceVector.mLength = numSamples;

    const uint32_t bytesPerSample = (XPAR_AXI_PERF_MON_0_TRACE_WORD_WIDTH / 8);
    const uint32_t wordsPerSample = (XPAR_AXI_PERF_MON_0_TRACE_WORD_WIDTH / 32);
    //uint32_t numBytes = numSamples * bytesPerSample;
    uint32_t numWords = numSamples * wordsPerSample;

    // Create trace buffer on host (requires alignment)
    const int BUFFER_BYTES = MAX_TRACE_NUMBER_SAMPLES * bytesPerSample;
    const int BUFFER_WORDS = MAX_TRACE_NUMBER_SAMPLES * wordsPerSample;
#ifndef _WINDOWS
// TODO: Windows build support
//    alignas is defined in c++11
#if GCC_VERSION >= 40800
    alignas(AXI_FIFO_RDFD_AXI_FULL) uint32_t hostbuf[BUFFER_WORDS];
#else
    AlignedAllocator<uint32_t> alignedBuffer(AXI_FIFO_RDFD_AXI_FULL, BUFFER_WORDS);
    uint32_t* hostbuf = alignedBuffer.getBuffer();
#endif
#else
    uint32_t hostbuf[BUFFER_WORDS];
#endif

    // ******************************
    // Read all words from trace FIFO
    // ******************************
    if (type == XCL_PERF_MON_MEMORY) {
      memset((void *)hostbuf, 0, BUFFER_BYTES);

      // Iterate over chunks
      // NOTE: AXI limits this to 4K bytes per transfer
      uint32_t chunkSizeWords = 256 * wordsPerSample;
      if (chunkSizeWords > 1024) chunkSizeWords = 1024;
      uint32_t chunkSizeBytes = 4 * chunkSizeWords;
      uint32_t words=0;

      // Read trace a chunk of bytes at a time
      if (numWords > chunkSizeWords) {
        for (; words < (numWords-chunkSizeWords); words += chunkSizeWords) {
          if (mLogStream.is_open()) {
            mLogStream << __func__ << ": reading " << chunkSizeBytes << " bytes from 0x"
                << std::hex << fifoReadAddress[0] << " and writing it to 0x"
                << (void *)(hostbuf + words) << std::dec << std::endl;
          }

          if (mDataMover->pread64((void *)(hostbuf + words), chunkSizeBytes, fifoReadAddress[0]) < 0)
            return 0;

          size += chunkSizeBytes;
        }
      }

      // Read remainder of trace not divisible by chunk size
      if (words < numWords) {
        chunkSizeBytes = 4 * (numWords - words);

        if (mLogStream.is_open()) {
          mLogStream << __func__ << ": reading " << chunkSizeBytes << " bytes from 0x"
              << std::hex << fifoReadAddress[0] << " and writing it to 0x"
              << (void *)(hostbuf + words) << std::dec << std::endl;
        }

        if (mDataMover->pread64((void *)(hostbuf + words), chunkSizeBytes, fifoReadAddress[0]) < 0)
          return 0;

        size += chunkSizeBytes;
      }

      if (mLogStream.is_open()) {
        mLogStream << __func__ << ": done reading " << size << " bytes " << std::endl;
      }
    }

    // ******************************
    // Read & process all trace FIFOs
    // ******************************
    for (uint32_t wordnum=0; wordnum < numSamples; wordnum++) {
      if (type == XCL_PERF_MON_MEMORY) {
        uint32_t index = wordsPerSample * wordnum;
        bool allZeros = true;
        for (uint32_t fifonum=0; fifonum < numFifos; fifonum++) {
          temp[fifonum] = *(hostbuf + index + fifonum);
          allZeros &= (temp[fifonum] == 0);
        }
        if (allZeros)
          continue;
      }
      else {
        // NOTE: Using AXI-Lite so we use the same address with burst length of 1 word
        for (uint32_t fifonum=0; fifonum < numFifos; fifonum++)
          size += xclRead(addressSpace, fifoReadAddress[fifonum], &temp[fifonum], 4);
      }

      xclTraceResults results;
      // Assign to all 0s to avoid uninitialized variables
      memset(&results, 0, sizeof(xclTraceResults));

      uint64_t temp64 = ((uint64_t)temp[1] << 32) | temp[0];
      results.LogID = temp64 & 0x1;
      results.Timestamp = (temp64 >> 1) & 0xFFFF;
      results.Overflow = (temp64 >> 17) & 0x1;
      results.ReadStartEvent = XCL_PERF_MON_START_ADDR;
      results.WriteStartEvent = XCL_PERF_MON_START_ADDR;
      results.WriteEndEvent = XCL_PERF_MON_END_LAST_DATA;

      if (results.LogID != 0) {
        results.HostTimestamp = (temp64 >> 18) & 0xFFFFFFFF;
      }
      else {
        for (uint32_t s=0; s < numSlots; s++) {
          uint32_t b = getPerfMonSlotStartBit(type, s);

          if (b >= 32)
            temp64 = ((((uint64_t)temp[2] << 32) | temp[1]) >> (b-32));
          else
            temp64 = ((((uint64_t)temp[1] << 32) | temp[0]) >> b);

          results.ExtEventFlags[s] = temp64 & 0x7;
          results.EventFlags[s] = (temp64 >> 3) & 0x7F;

          if (getPerfMonShowIDS(type)) {
            if (getPerfMonShowLEN(type)) {
              results.ReadAddrLen[s] = (temp64 >> 10) & 0xFF;
              results.WriteAddrLen[s] = (temp64 >> 18) & 0xFF;

              // TODO: assumes AXI ID width of 5
              results.RID[s] = (temp64 >> 26) & 0x1F;
              results.ARID[s] = (temp64 >> 31) & 0x1F;
              results.BID[s] = (temp64 >> 36) & 0x1F;
              results.AWID[s] = (temp64 >> 41) & 0x1F;
            }
            else {
              // TODO: assumes AXI ID width of 5
              results.RID[s] = (temp64 >> 10) & 0x1F;
              results.ARID[s] = (temp64 >> 15) & 0x1F;
              results.BID[s] = (temp64 >> 20) & 0x1F;
              results.AWID[s] = (temp64 >> 25) & 0x1F;
            }
          }
          else {
            if (getPerfMonShowLEN(type)) {
              results.ReadAddrLen[s] = (temp64 >> 10) & 0xFF;
              results.WriteAddrLen[s] = (temp64 >> 18) & 0xFF;
            }
          }

          // # bytes = burst length * bytes/burst = (addr len + 1) * bytes/burst
          uint32_t dataWidth = getPerfMonSlotDataWidth(type, s);
          results.ReadBytes[s] = (results.ReadAddrLen[s] + 1) * (dataWidth/8);
          results.WriteBytes[s] = (results.WriteAddrLen[s] + 1) * (dataWidth/8);
        } // for slot
      } // if-else logID != 0

      traceVector.mArray[wordnum] = results;

      // Log values (if requested)
#if 1
      if (mLogStream.is_open()) {
        mLogStream << "  Trace sample " << std::dec << wordnum << ": ";
        for (int fifonum=numFifos-1; fifonum >= 0; fifonum--)
          mLogStream << dec2bin(temp[fifonum]) << " ";
        mLogStream << std::endl;

        if (results.LogID == 1) {
          mLogStream << std::hex << "    Host Timestamp: " << results.HostTimestamp << std::endl;
        }
        else {
          if (type == XCL_PERF_MON_OCL_REGION) {
            mLogStream << "    Ext Event flags: ";
            for (int slot=numSlots-1; slot >= 0; slot--)
              mLogStream << dec2bin(results.ExtEventFlags[slot], 3) << " ";
          }
          else {
            mLogStream << "    Event flags: ";
            for (int slot=numSlots-1; slot >= 0; slot--)
              mLogStream << dec2bin(results.EventFlags[slot], 7) << " ";
          }

          mLogStream << "(ReadAddrLen[0] = " << (int)(results.ReadAddrLen[0])
                     << ", WriteAddrLen[0] = " << (int)(results.WriteAddrLen[0])
                     << ", ReadAddrLen[1] = " << (int)(results.ReadAddrLen[1])
                     << ", WriteAddrLen[1] = " << (int)(results.WriteAddrLen[1]);

          if (getPerfMonShowIDS(type)) {
            mLogStream << ", RID: " << (int)results.RID[0] << ", ARID: " << (int)results.ARID[0]
                       << ", BID: " << (int)results.BID[0] << ", AWID: " << (int)results.AWID[0];
          }
          mLogStream << ")" << std::endl;
        }
      }
#endif
    } // for wordnum

    return size;
  } // end xclPerfMonReadTrace

} // namespace awsbwhal


size_t xclPerfMonStartCounters(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonStartCounters(type);
}


size_t xclPerfMonStopCounters(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonStopCounters(type);
}


size_t xclPerfMonReadCounters(xclDeviceHandle handle, xclPerfMonType type, xclCounterResults& counterResults)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonReadCounters(type, counterResults);
}


size_t xclPerfMonClockTraining(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonClockTraining(type);
}


size_t xclPerfMonStartTrace(xclDeviceHandle handle, xclPerfMonType type, uint32_t startTrigger)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonStartTrace(type, startTrigger);
}


size_t xclPerfMonStopTrace(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonStopTrace(type);
}


uint32_t xclPerfMonGetTraceCount(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonGetTraceCount(type);
}


size_t xclPerfMonReadTrace(xclDeviceHandle handle, xclPerfMonType type, xclTraceResultsVector& traceVector)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return drv->xclPerfMonReadTrace(type, traceVector);
}


double xclGetDeviceClockFreqMHz(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return drv->xclGetDeviceClockFreqMHz();
}


double xclGetReadMaxBandwidthMBps(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return drv->xclGetReadMaxBandwidthMBps();
}


double xclGetWriteMaxBandwidthMBps(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return drv->xclGetWriteMaxBandwidthMBps();
}


size_t xclGetDeviceTimestamp(xclDeviceHandle handle)
{
  return 0;
}


void xclSetOclRegionProfilingNumberSlots(xclDeviceHandle handle, uint32_t numSlots)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return;
  return drv->xclSetOclRegionProfilingNumberSlots(numSlots);
}


void xclWriteHostEvent(xclDeviceHandle handle, xclPerfMonEventType type,
                       xclPerfMonEventID id)
{
  // don't do anything
}
