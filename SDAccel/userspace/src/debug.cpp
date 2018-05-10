/*
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Debug functionality to AWS hal driver
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

  uint64_t AwsXcl::getProtocolCheckerBaseAddress(int type) {
    switch (type) {
    case 0:
      return LAPC0_BASE;
    case 1:
      return LAPC1_BASE;
    case 2:
      return LAPC2_BASE;
    case 3:
      return LAPC3_BASE;
    };
    return 0;
  }

  uint32_t AwsXcl::getCheckerNumberSlots(int type) {
    return getBankCount();
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

    uint32_t numSlots = getCheckerNumberSlots(0);

    uint32_t temp[XLAPC_STATUS_PER_SLOT];
    for (int s = 0; s < numSlots; ++s) {
      uint64_t baseAddress = getProtocolCheckerBaseAddress(s);
      for (int c=0; c < XLAPC_STATUS_PER_SLOT; c++)
        size += xclRead(XCL_ADDR_SPACE_DEVICE_CHECKER, baseAddress+statusRegisters[c], &temp[c], 4);

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
    uint32_t scaleFactor = getPerfMonByteScaleFactor(XCL_PERF_MON_MEMORY);
    uint64_t baseAddress = getPerfMonBaseAddress(XCL_PERF_MON_MEMORY);

    uint64_t metricAddress[] = {
        // Slot 0
        baseAddress + XAPM_MC0_OFFSET,  baseAddress + XAPM_MC1_OFFSET,
        baseAddress + XAPM_MC3_OFFSET,  baseAddress + XAPM_MC4_OFFSET,
        // Slot 1
        baseAddress + XAPM_MC6_OFFSET,  baseAddress + XAPM_MC7_OFFSET,
        baseAddress + XAPM_MC9_OFFSET,  baseAddress + XAPM_MC10_OFFSET,
        // Slot 2
        baseAddress + XAPM_MC12_OFFSET, baseAddress + XAPM_MC13_OFFSET,
        baseAddress + XAPM_MC15_OFFSET, baseAddress + XAPM_MC16_OFFSET,
        // Slot 3
        baseAddress + XAPM_MC18_OFFSET, baseAddress + XAPM_MC19_OFFSET,
        baseAddress + XAPM_MC21_OFFSET, baseAddress + XAPM_MC22_OFFSET,
        // Slot 4
        baseAddress + XAPM_MC24_OFFSET, baseAddress + XAPM_MC25_OFFSET,
        baseAddress + XAPM_MC27_OFFSET, baseAddress + XAPM_MC28_OFFSET,
        // Slot 5
        baseAddress + XAPM_MC30_OFFSET, baseAddress + XAPM_MC31_OFFSET,
        baseAddress + XAPM_MC33_OFFSET, baseAddress + XAPM_MC34_OFFSET,
        // Slot 6
        baseAddress + XAPM_MC36_OFFSET, baseAddress + XAPM_MC37_OFFSET,
        baseAddress + XAPM_MC39_OFFSET, baseAddress + XAPM_MC40_OFFSET,
        // Slot 7
        baseAddress + XAPM_MC42_OFFSET, baseAddress + XAPM_MC43_OFFSET,
        baseAddress + XAPM_MC45_OFFSET, baseAddress + XAPM_MC46_OFFSET,
    };

    // Read all metric counters
    uint32_t countnum = 0;
    uint32_t numSlots = getPerfMonNumberSlots(XCL_PERF_MON_MEMORY);

    uint32_t temp[XAPM_DEBUG_METRIC_COUNTERS_PER_SLOT];

    for (uint32_t s=0; s < numSlots; s++) {
      for (int c=0; c < XAPM_DEBUG_METRIC_COUNTERS_PER_SLOT; c++)
        size += xclRead(XCL_ADDR_SPACE_DEVICE_PERFMON, metricAddress[countnum++], &temp[c], 4);

      aCounterResults->WriteBytes[s]      = temp[0] * scaleFactor;
      aCounterResults->WriteTranx[s]      = temp[1];

      aCounterResults->ReadBytes[s]       = temp[2] * scaleFactor;
      aCounterResults->ReadTranx[s]       = temp[3];
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
    case XCL_DEBUG_READ_TYPE_APM :
      return drv->xclDebugReadCounters(reinterpret_cast<xclDebugCountersResults*>(debugResults));
    case XCL_DEBUG_READ_TYPE_LAPC :
      return drv->xclDebugReadCheckers(reinterpret_cast<xclDebugCheckersResults*>(debugResults));
  };
  return -1;
}
