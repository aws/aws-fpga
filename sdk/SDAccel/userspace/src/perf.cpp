/*
 * Copyright (C) 2015 Xilinx, Inc
 * Author: Paul Schumacher
 * Performance Monitoring using PCIe for XDMA HAL Driver
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

/**
 * Stub implementation of APM for AWS
 */

#include "shim.h"
#include "datamover.h"

size_t xclPerfMonStartCounters(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonStopCounters(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonReadCounters(xclDeviceHandle handle, xclPerfMonType type, xclCounterResults& counterResults)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonClockTraining(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonStartTrace(xclDeviceHandle handle, xclPerfMonType type, uint32_t startTrigger)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonStopTrace(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


uint32_t xclPerfMonGetTraceCount(xclDeviceHandle handle, xclPerfMonType type)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


size_t xclPerfMonReadTrace(xclDeviceHandle handle, xclPerfMonType type, xclTraceResultsVector& traceVector)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return -1;
  return 0;
}


double xclGetDeviceClockFreqMHz(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return 0.0;
}


double xclGetReadMaxBandwidthMBps(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return 0.0;
}


double xclGetWriteMaxBandwidthMBps(xclDeviceHandle handle)
{
  awsbwhal::AwsXcl *drv = awsbwhal::AwsXcl::handleCheck(handle);
  if (!drv)
    return 0.0;
  return 0.0;
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
}
