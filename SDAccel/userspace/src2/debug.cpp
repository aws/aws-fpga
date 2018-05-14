/*
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Debug functionality to AWS hal driver
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
#include "perfmon_parameters.h"
#include "xclbin2.h"

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
#include <string>

#ifndef _WINDOWS
// TODO: Windows build support
//    unistd.h is linux only header file
//    it is included for read, write, close, lseek64
#include <unistd.h>
#endif

#ifdef _WINDOWS
#define __func__ __FUNCTION__
#endif

namespace awsbwhal {
  // ****************
  // Helper functions
  // ****************

  void AwsXcl::readDebugIpLayout()
  {
    if (mIsDebugIpLayoutRead)
      return;

    //
    // Profiling - addresses and names
    // Parsed from debug_ip_layout.rtd contained in xclbin
    if (mLogStream.is_open()) {
      mLogStream << "debug_ip_layout: reading profile addresses and names..." << std::endl;
    }
    mMemoryProfilingNumberSlots = getIPCountAddrNames(AXI_MM_MONITOR, mPerfMonBaseAddress, mPerfMonSlotName);
    mIsDeviceProfiling = (mMemoryProfilingNumberSlots > 0);

    std::string fifoName;
    uint64_t fifoCtrlBaseAddr = mOffsets[XCL_ADDR_SPACE_DEVICE_PERFMON];
    getIPCountAddrNames(AXI_MONITOR_FIFO_LITE, &fifoCtrlBaseAddr, &fifoName);
    mPerfMonFifoCtrlBaseAddress = fifoCtrlBaseAddr;

    uint64_t fifoReadBaseAddr = XPAR_AXI_PERF_MON_0_TRACE_OFFSET_AXI_FULL2;
    getIPCountAddrNames(AXI_MONITOR_FIFO_FULL, &fifoReadBaseAddr, &fifoName);
    mPerfMonFifoReadBaseAddress = fifoReadBaseAddr;

    if (mLogStream.is_open()) {
      for (unsigned int i = 0; i < mMemoryProfilingNumberSlots; ++i) {
        mLogStream << "debug_ip_layout: AXI_MM_MONITOR slot " << i << ": "
                   << "base address = 0x" << std::hex << mPerfMonBaseAddress[i]
                   << ", name = " << mPerfMonSlotName[i] << std::endl;
      }
      mLogStream << "debug_ip_layout: AXI_MONITOR_FIFO_LITE: "
                 << "base address = 0x" << std::hex << fifoCtrlBaseAddr << std::endl;
      mLogStream << "debug_ip_layout: AXI_MONITOR_FIFO_FULL: "
                 << "base address = 0x" << std::hex << fifoReadBaseAddr << std::endl;
    }

    // Only need to read it once
    mIsDebugIpLayoutRead = true;
  }

  // Gets the information about the specified IP from the sysfs debug_ip_table.
  // The IP types are defined in xclbin.h
  uint32_t AwsXcl::getIPCountAddrNames(int type, uint64_t *baseAddress, std::string * portNames) {
    debug_ip_layout *map;
    std::string path = "/sys/bus/pci/devices/" + mDevUserName + "/debug_ip_layout";
    std::ifstream ifs(path.c_str(), std::ifstream::binary);
    uint32_t count = 0;
    char buffer[4096];
    if( ifs ) {
      //sysfs max file size is 4096
      ifs.read(buffer, 4096);
      if (ifs.gcount() > 0) {
        map = (debug_ip_layout*)(buffer);
        for( unsigned int i = 0; i < map->m_count; i++ ) {
          if (map->m_debug_ip_data[i].m_type == type) {
            if(baseAddress)baseAddress[count] = map->m_debug_ip_data[i].m_base_address;
            if(portNames) portNames[count] = (char*)map->m_debug_ip_data[i].m_name;
            ++count;
          }
        }
      }
      ifs.close();
    }
    return count;
  }

  // Read APM performance counters
  size_t AwsXcl::xclDebugReadCheckers(xclDebugCheckersResults* aCheckerResults) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << aCheckerResults
      << ", Read protocl checker status..." << std::endl;
    }

    size_t size = 0;

    uint64_t statusRegisters[] = {
        LAPC_OVERALL_STATUS_OFFSET,

        LAPC_CUMULATIVE_STATUS_0_OFFSET, LAPC_CUMULATIVE_STATUS_1_OFFSET,
        LAPC_CUMULATIVE_STATUS_2_OFFSET, LAPC_CUMULATIVE_STATUS_3_OFFSET,

        LAPC_SNAPSHOT_STATUS_0_OFFSET, LAPC_SNAPSHOT_STATUS_1_OFFSET,
        LAPC_SNAPSHOT_STATUS_2_OFFSET, LAPC_SNAPSHOT_STATUS_3_OFFSET
    };

    uint64_t baseAddress[XLAPC_MAX_NUMBER_SLOTS];
    uint32_t numSlots = getIPCountAddrNames(LAPC, baseAddress, nullptr);
    uint32_t temp[XLAPC_STATUS_PER_SLOT];
    aCheckerResults->NumSlots = numSlots;
    snprintf(aCheckerResults->DevUserName, 256, "%s", mDevUserName.c_str());
    for (uint32_t s = 0; s < numSlots; ++s) {
      for (int c=0; c < XLAPC_STATUS_PER_SLOT; c++)
        size += xclRead(XCL_ADDR_SPACE_DEVICE_CHECKER, baseAddress[s]+statusRegisters[c], &temp[c], 4);

      aCheckerResults->OverallStatus[s]      = temp[XLAPC_OVERALL_STATUS];
      std::copy(temp+XLAPC_CUMULATIVE_STATUS_0, temp+XLAPC_SNAPSHOT_STATUS_0, aCheckerResults->CumulativeStatus[s]);
      std::copy(temp+XLAPC_SNAPSHOT_STATUS_0, temp+XLAPC_STATUS_PER_SLOT, aCheckerResults->SnapshotStatus[s]);
    }

    return size;
  }

  // Read APM performance counters
  
  size_t AwsXcl::xclDebugReadCounters(xclDebugCountersResults* aCounterResults) {
    if (mLogStream.is_open()) {
      mLogStream << __func__ << ", " << std::this_thread::get_id()
      << ", " << XCL_PERF_MON_MEMORY << ", " << aCounterResults
      << ", Read device counters..." << std::endl;
    }

    size_t size = 0;

    uint64_t spm_offsets[] = {
        XSPM_SAMPLE_WRITE_BYTES_OFFSET,
        XSPM_SAMPLE_WRITE_TRANX_OFFSET,
        XSPM_SAMPLE_READ_BYTES_OFFSET,
        XSPM_SAMPLE_READ_TRANX_OFFSET,
        XSPM_SAMPLE_OUTSTANDING_COUNTS_OFFSET,
        XSPM_SAMPLE_LAST_WRITE_ADDRESS_OFFSET,
        XSPM_SAMPLE_LAST_WRITE_DATA_OFFSET,
        XSPM_SAMPLE_LAST_READ_ADDRESS_OFFSET,
        XSPM_SAMPLE_LAST_READ_DATA_OFFSET
    };

    // Read all metric counters
    uint64_t baseAddress[XSPM_MAX_NUMBER_SLOTS];
    uint32_t numSlots = getIPCountAddrNames(AXI_MM_MONITOR, baseAddress, nullptr);

    uint32_t temp[XSPM_DEBUG_SAMPLE_COUNTERS_PER_SLOT];

    aCounterResults->NumSlots = numSlots;
    snprintf(aCounterResults->DevUserName, 256, "%s", mDevUserName.c_str());
    for (uint32_t s=0; s < numSlots; s++) {
      uint32_t sampleInterval;
      // Read sample interval register to latch the sampled metric counters
      size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON,
                    baseAddress[s] + XSPM_SAMPLE_OFFSET,
                    &sampleInterval, 4);

      for (int c=0; c < XSPM_DEBUG_SAMPLE_COUNTERS_PER_SLOT; c++)
        size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, baseAddress[s]+spm_offsets[c], &temp[c], 4);

      aCounterResults->WriteBytes[s]      = temp[0];
      aCounterResults->WriteTranx[s]      = temp[1];

      aCounterResults->ReadBytes[s]       = temp[2];
      aCounterResults->ReadTranx[s]       = temp[3];
      aCounterResults->OutStandCnts[s]    = temp[4];
      aCounterResults->LastWriteAddr[s]   = temp[5];
      aCounterResults->LastWriteData[s]   = temp[6];
      aCounterResults->LastReadAddr[s]    = temp[7];
      aCounterResults->LastReadData[s]    = temp[8];
    }
    return size;
  }
} // namespace awsbwhal

size_t xclDebugReadIPStatus(xclDeviceHandle handle, xclDebugReadType type, void* debugResults)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  switch (type) {
    case XCL_DEBUG_READ_TYPE_LAPC :
      return drv->xclDebugReadCheckers(reinterpret_cast<xclDebugCheckersResults*>(debugResults));
    case XCL_DEBUG_READ_TYPE_SPM :
      return drv->xclDebugReadCounters(reinterpret_cast<xclDebugCountersResults*>(debugResults));
    default :
      break;
  };
  return -1;
}
