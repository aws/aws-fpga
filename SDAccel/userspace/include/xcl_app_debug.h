/**
 * Copyright (C) 2015-2018 Xilinx, Inc
 *
 * Xilinx SDAccel HAL userspace driver extension APIs
 * Performance Monitoring Exposed Parameters
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

#ifndef _XCL_DEBUG_H_
#define _XCL_DEBUG_H_

#ifdef __cplusplus
extern "C" {
#endif

/************************ APM Debug Counters ********************************/
#define XAPM_DEBUG_METRIC_COUNTERS_PER_SLOT     4  //debug is only interested in 4 metric counters

/*
 * LAPC related defs here
 */
#define XLAPC_MAX_NUMBER_SLOTS           4
#define XLAPC_STATUS_PER_SLOT            9

/* Metric counters per slot */
#define XLAPC_OVERALL_STATUS                0
#define XLAPC_CUMULATIVE_STATUS_0           1
#define XLAPC_CUMULATIVE_STATUS_1           2
#define XLAPC_CUMULATIVE_STATUS_2           3
#define XLAPC_CUMULATIVE_STATUS_3           4
#define XLAPC_SNAPSHOT_STATUS_0             5
#define XLAPC_SNAPSHOT_STATUS_1             6
#define XLAPC_SNAPSHOT_STATUS_2             7
#define XLAPC_SNAPSHOT_STATUS_3             8

/********************** Definitions: Enums, Structs ***************************/
enum xclDebugReadType {
  XCL_DEBUG_READ_TYPE_APM = 0,
  XCL_DEBUG_READ_TYPE_LAPC = 1
};

/* Debug counter results */
typedef struct {
  unsigned int   WriteBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   WriteTranx[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   ReadBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   ReadTranx[XAPM_MAX_NUMBER_SLOTS];
} xclDebugCountersResults;

enum xclCheckerType {
XCL_CHECKER_MEMORY = 0,
};

/* Debug checker results */
typedef struct {
  unsigned int   OverallStatus[XLAPC_MAX_NUMBER_SLOTS];
  unsigned int   CumulativeStatus[XLAPC_MAX_NUMBER_SLOTS][4];
  unsigned int   SnapshotStatus[XLAPC_MAX_NUMBER_SLOTS][4];
} xclDebugCheckersResults;

#ifdef __cplusplus
}
#endif
#endif
