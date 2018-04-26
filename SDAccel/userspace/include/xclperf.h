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

#ifndef _XCL_PERF_H_
#define _XCL_PERF_H_

// DSA version (e.g., XCL_PLATFORM=xilinx_adm-pcie-7v3_1ddr_1_1)

#define DSA_MAJOR_VERSION 1
#define DSA_MINOR_VERSION 1

/************************ APM 0: Monitor MIG Ports ****************************/

#define XPAR_AXI_PERF_MON_0_NUMBER_SLOTS                2

#define XPAR_AXI_PERF_MON_0_SLOT0_NAME                  "OCL Region"
#define XPAR_AXI_PERF_MON_0_SLOT1_NAME                  "Host"
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT             0
#define XPAR_AXI_PERF_MON_0_HOST_SLOT                   1

#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT2            2
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT3            3
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT4            4
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT5            5
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT6            6
#define XPAR_AXI_PERF_MON_0_OCL_REGION_SLOT7            7

#define XPAR_AXI_PERF_MON_0_SLOT2_NAME                  "OCL Region Master 2"
#define XPAR_AXI_PERF_MON_0_SLOT3_NAME                  "OCL Region Master 3"
#define XPAR_AXI_PERF_MON_0_SLOT4_NAME                  "OCL Region Master 4"
#define XPAR_AXI_PERF_MON_0_SLOT5_NAME                  "OCL Region Master 5"
#define XPAR_AXI_PERF_MON_0_SLOT6_NAME                  "OCL Region Master 6"
#define XPAR_AXI_PERF_MON_0_SLOT7_NAME                  "OCL Region Master 7"

#define XPAR_AXI_PERF_MON_0_SLOT0_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT1_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT2_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT3_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT4_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT5_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT6_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_0_SLOT7_DATA_WIDTH            512

/* Profile */
#define XPAR_AXI_PERF_MON_0_IS_EVENT_COUNT              1
#define XPAR_AXI_PERF_MON_0_HAVE_SAMPLED_COUNTERS       1
#define XPAR_AXI_PERF_MON_0_NUMBER_COUNTERS (XPAR_AXI_PERF_MON_0_NUMBER_SLOTS * XAPM_METRIC_COUNTERS_PER_SLOT)

/* Trace */
#define XPAR_AXI_PERF_MON_0_IS_EVENT_LOG                1
#define XPAR_AXI_PERF_MON_0_SHOW_AXI_IDS                1
#define XPAR_AXI_PERF_MON_0_SHOW_AXI_LEN                1
// 2 DDR platform
#define XPAR_AXI_PERF_MON_0_SHOW_AXI_IDS_2DDR           0
#define XPAR_AXI_PERF_MON_0_SHOW_AXI_LEN_2DDR           1

/* AXI Stream FIFOs */
#define XPAR_AXI_PERF_MON_0_TRACE_NUMBER_FIFO           3
#define XPAR_AXI_PERF_MON_0_TRACE_WORD_WIDTH            128
#define XPAR_AXI_PERF_MON_0_TRACE_NUMBER_SAMPLES        4096
#define MAX_TRACE_NUMBER_SAMPLES                        8192

#define XPAR_AXI_PERF_MON_0_TRACE_OFFSET_0              0x010000
#define XPAR_AXI_PERF_MON_0_TRACE_OFFSET_1              0x011000
#define XPAR_AXI_PERF_MON_0_TRACE_OFFSET_2              0x012000
// CR 877788: the extra 0x80001000 is a bug in Vivado where the AXI4 base address is not set correctly
// TODO: remove it once that bug is fixed!
#define XPAR_AXI_PERF_MON_0_TRACE_OFFSET_AXI_FULL       (0x2000000000 + 0x80001000)

/********************* APM 1: Monitor PCIe DMA Masters ************************/

#define XPAR_AXI_PERF_MON_1_NUMBER_SLOTS                2

#define XPAR_AXI_PERF_MON_1_SLOT0_NAME                  "DMA AXI4 Master"
#define XPAR_AXI_PERF_MON_1_SLOT1_NAME                  "DMA AXI4-Lite Master"
#define XPAR_AXI_PERF_MON_1_SLOT2_NAME                  "Null"
#define XPAR_AXI_PERF_MON_1_SLOT3_NAME                  "Null"
#define XPAR_AXI_PERF_MON_1_SLOT4_NAME                  "Null"
#define XPAR_AXI_PERF_MON_1_SLOT5_NAME                  "Null"
#define XPAR_AXI_PERF_MON_1_SLOT6_NAME                  "Null"
#define XPAR_AXI_PERF_MON_1_SLOT7_NAME                  "Null"

#define XPAR_AXI_PERF_MON_1_SLOT0_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT1_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT2_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT3_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT4_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT5_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT6_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_1_SLOT7_DATA_WIDTH            512

/* Profile */
#define XPAR_AXI_PERF_MON_1_IS_EVENT_COUNT              1
#define XPAR_AXI_PERF_MON_1_HAVE_SAMPLED_COUNTERS       1
#define XPAR_AXI_PERF_MON_1_NUMBER_COUNTERS (XPAR_AXI_PERF_MON_1_NUMBER_SLOTS * XAPM_METRIC_COUNTERS_PER_SLOT)
#define XPAR_AXI_PERF_MON_1_SCALE_FACTOR                1

/* Trace */
#define XPAR_AXI_PERF_MON_1_IS_EVENT_LOG                0
#define XPAR_AXI_PERF_MON_1_SHOW_AXI_IDS                0
#define XPAR_AXI_PERF_MON_1_SHOW_AXI_LEN                0

/* AXI Stream FIFOs */
#define XPAR_AXI_PERF_MON_1_TRACE_NUMBER_FIFO           0
#define XPAR_AXI_PERF_MON_1_TRACE_WORD_WIDTH            0
#define XPAR_AXI_PERF_MON_1_TRACE_NUMBER_SAMPLES        0

/************************ APM 2: Monitor OCL Region ***************************/

#define XPAR_AXI_PERF_MON_2_NUMBER_SLOTS                1

#define XPAR_AXI_PERF_MON_2_SLOT0_NAME                  "Kernel0"
#define XPAR_AXI_PERF_MON_2_SLOT1_NAME                  "Kernel1"
#define XPAR_AXI_PERF_MON_2_SLOT2_NAME                  "Kernel2"
#define XPAR_AXI_PERF_MON_2_SLOT3_NAME                  "Kernel3"
#define XPAR_AXI_PERF_MON_2_SLOT4_NAME                  "Kernel4"
#define XPAR_AXI_PERF_MON_2_SLOT5_NAME                  "Kernel5"
#define XPAR_AXI_PERF_MON_2_SLOT6_NAME                  "Kernel6"
#define XPAR_AXI_PERF_MON_2_SLOT7_NAME                  "Kernel7"

#define XPAR_AXI_PERF_MON_2_SLOT0_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT1_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT2_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT3_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT4_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT5_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT6_DATA_WIDTH            512
#define XPAR_AXI_PERF_MON_2_SLOT7_DATA_WIDTH            512

/* Profile */
#define XPAR_AXI_PERF_MON_2_IS_EVENT_COUNT              0
#define XPAR_AXI_PERF_MON_2_HAVE_SAMPLED_COUNTERS       0
#define XPAR_AXI_PERF_MON_2_NUMBER_COUNTERS             0
#define XPAR_AXI_PERF_MON_2_SCALE_FACTOR                1

/* Trace */
#define XPAR_AXI_PERF_MON_2_IS_EVENT_LOG                1
#define XPAR_AXI_PERF_MON_2_SHOW_AXI_IDS                0
#define XPAR_AXI_PERF_MON_2_SHOW_AXI_LEN                0

/* AXI Stream FIFOs */
/* NOTE: number of FIFOs is dependent upon the number of compute units being monitored */
//#define XPAR_AXI_PERF_MON_2_TRACE_NUMBER_FIFO           2
#define XPAR_AXI_PERF_MON_2_TRACE_WORD_WIDTH            64
#define XPAR_AXI_PERF_MON_2_TRACE_NUMBER_SAMPLES        4096

#define XPAR_AXI_PERF_MON_2_TRACE_OFFSET_0              0x01000
#define XPAR_AXI_PERF_MON_2_TRACE_OFFSET_1              0x02000
#define XPAR_AXI_PERF_MON_2_TRACE_OFFSET_2              0x03000

/************************ APM Profile Counters ********************************/

#define XAPM_MAX_NUMBER_SLOTS             8
#define XAPM_METRIC_COUNTERS_PER_SLOT     8

/* Metric counters per slot */
#define XAPM_METRIC_WRITE_BYTES           0
#define XAPM_METRIC_WRITE_TRANX           1
#define XAPM_METRIC_WRITE_LATENCY         2
#define XAPM_METRIC_READ_BYTES            3
#define XAPM_METRIC_READ_TRANX            4
#define XAPM_METRIC_READ_LATENCY          5
#define XAPM_METRIC_WRITE_MIN_MAX         6
#define XAPM_METRIC_READ_MIN_MAX          7

#define XAPM_METRIC_COUNT0_NAME           "Write Byte Count"
#define XAPM_METRIC_COUNT1_NAME           "Write Transaction Count"
#define XAPM_METRIC_COUNT2_NAME           "Total Write Latency"
#define XAPM_METRIC_COUNT3_NAME           "Read Byte Count"
#define XAPM_METRIC_COUNT4_NAME           "Read Transaction Count"
#define XAPM_METRIC_COUNT5_NAME           "Total Read Latency"
#define XAPM_METRIC_COUNT6_NAME           "Min/Max Write Latency"
#define XAPM_METRIC_COUNT7_NAME           "Min/Max Read Latency"

/************************ APM Debug Counters ********************************/
#define XAPM_DEBUG_METRIC_COUNTERS_PER_SLOT     4  //debug is only interested in 4 metric counters

/************************ APM Trace Stream ************************************/

/* Bit locations of trace flags */
#define XAPM_READ_LAST                   6
#define XAPM_READ_FIRST                  5
#define XAPM_READ_ADDR                   4
#define XAPM_RESPONSE                    3
#define XAPM_WRITE_LAST                  2
#define XAPM_WRITE_FIRST                 1
#define XAPM_WRITE_ADDR                  0

/* Bit locations of external event flags */
#define XAPM_EXT_START                   2
#define XAPM_EXT_STOP                    1
#define XAPM_EXT_EVENT                   0

/* Total number of bits per slot */
#define FLAGS_PER_SLOT                   7
#define EXT_EVENTS_PER_SLOT              3

/* Cycles to add to timestamp if overflow occurs */
#define LOOP_ADD_TIME                    (1<<16)

/********************** Definitions: Enums, Structs ***************************/

/* Performance monitor type or location */
enum xclPerfMonType {
	XCL_PERF_MON_MEMORY = 0,
	XCL_PERF_MON_HOST_INTERFACE = 1,
	XCL_PERF_MON_OCL_REGION = 2,
	XCL_PERF_MON_TOTAL_PROFILE = 3
};

/* Performance monitor start event */
enum xclPerfMonStartEvent {
	XCL_PERF_MON_START_ADDR = 0,
	XCL_PERF_MON_START_FIRST_DATA = 1
};

/* Performance monitor end event */
enum xclPerfMonEndEvent {
	XCL_PERF_MON_END_LAST_DATA = 0,
	XCL_PERF_MON_END_RESPONSE = 1
};

/* Performance monitor counter types */
enum xclPerfMonCounterType {
  XCL_PERF_MON_WRITE_BYTES = 0,
  XCL_PERF_MON_WRITE_TRANX = 1,
  XCL_PERF_MON_WRITE_LATENCY = 2,
  XCL_PERF_MON_READ_BYTES = 3,
  XCL_PERF_MON_READ_TRANX = 4,
  XCL_PERF_MON_READ_LATENCY = 5
};

/*
 * Performance monitor event types
 * NOTE: these are the same values used by SDSoC
 */
enum xclPerfMonEventType {
  XCL_PERF_MON_START_EVENT = 0x4,
  XCL_PERF_MON_END_EVENT = 0x5
};

/*
 * Performance monitor IDs for host SW events
 * NOTE: HW events start at 0, SDSoC SW events start at 4000
 */
enum xclPerfMonEventID {
  XCL_PERF_MON_IGNORE_EVENT = 0,
  XCL_PERF_MON_GENERAL_ID = 3000,
  XCL_PERF_MON_QUEUE_ID = 3001,
  XCL_PERF_MON_READ_ID = 3002,
  XCL_PERF_MON_WRITE_ID = 3003,
  XCL_PERF_MON_API_GET_PLATFORM_ID = 3005,
  XCL_PERF_MON_API_GET_PLATFORM_INFO_ID = 3006,
  XCL_PERF_MON_API_GET_DEVICE_ID = 3007,
  XCL_PERF_MON_API_GET_DEVICE_INFO_ID = 3008,
  XCL_PERF_MON_API_BUILD_PROGRAM_ID = 3009,
  XCL_PERF_MON_API_CREATE_CONTEXT_ID = 3010,
  XCL_PERF_MON_API_CREATE_CONTEXT_TYPE_ID = 3011,
  XCL_PERF_MON_API_CREATE_COMMAND_QUEUE_ID = 3012,
  XCL_PERF_MON_API_CREATE_PROGRAM_BINARY_ID = 3013,
  XCL_PERF_MON_API_CREATE_BUFFER_ID = 3014,
  XCL_PERF_MON_API_CREATE_IMAGE_ID = 3015,
  XCL_PERF_MON_API_CREATE_KERNEL_ID = 3016,
  XCL_PERF_MON_API_KERNEL_ARG_ID = 3017,
  XCL_PERF_MON_API_WAIT_FOR_EVENTS_ID = 3018,
  XCL_PERF_MON_API_READ_BUFFER_ID = 3019,
  XCL_PERF_MON_API_WRITE_BUFFER_ID = 3020,
  XCL_PERF_MON_API_READ_IMAGE_ID = 3021,
  XCL_PERF_MON_API_WRITE_IMAGE_ID = 3022,
  XCL_PERF_MON_API_MIGRATE_MEM_ID = 3023,
  XCL_PERF_MON_API_MIGRATE_MEM_OBJECTS_ID = 3024,
  XCL_PERF_MON_API_MAP_BUFFER_ID = 3025,
  XCL_PERF_MON_API_UNMAP_MEM_OBJECT_ID = 3026,
  XCL_PERF_MON_API_NDRANGE_KERNEL_ID = 3027,
  XCL_PERF_MON_API_TASK_ID = 3028,
  XCL_PERF_MON_KERNEL0_ID = 3100,
  XCL_PERF_MON_KERNEL1_ID = 3101,
  XCL_PERF_MON_KERNEL2_ID = 3102,
  XCL_PERF_MON_KERNEL3_ID = 3103,
  XCL_PERF_MON_KERNEL4_ID = 3104,
  XCL_PERF_MON_KERNEL5_ID = 3105,
  XCL_PERF_MON_KERNEL6_ID = 3106,
  XCL_PERF_MON_KERNEL7_ID = 3107,
  XCL_PERF_MON_CU0_ID = 3200,
  XCL_PERF_MON_CU1_ID = 3201,
  XCL_PERF_MON_CU2_ID = 3202,
  XCL_PERF_MON_CU3_ID = 3203,
  XCL_PERF_MON_CU4_ID = 3204,
  XCL_PERF_MON_CU5_ID = 3205,
  XCL_PERF_MON_CU6_ID = 3206,
  XCL_PERF_MON_CU7_ID = 3207,
  XCL_PERF_MON_PROGRAM_END = 4090
};

/* Performance monitor counter results */
typedef struct {
  //unsigned int   NumSlots;
  float          SampleIntervalUsec;
  unsigned int   WriteBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   WriteTranx[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   WriteLatency[XAPM_MAX_NUMBER_SLOTS];
  unsigned short WriteMinLatency[XAPM_MAX_NUMBER_SLOTS];
  unsigned short WriteMaxLatency[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   ReadBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   ReadTranx[XAPM_MAX_NUMBER_SLOTS];
  unsigned int   ReadLatency[XAPM_MAX_NUMBER_SLOTS];
  unsigned short ReadMinLatency[XAPM_MAX_NUMBER_SLOTS];
  unsigned short ReadMaxLatency[XAPM_MAX_NUMBER_SLOTS];
} xclCounterResults;

/* Performance monitor trace results */
typedef struct {
  unsigned char  LogID; /* 0: event flags, 1: host timestamp */
  unsigned char  Overflow;
  unsigned char  WriteStartEvent;
  unsigned char  WriteEndEvent;
  unsigned char  ReadStartEvent;
  unsigned short Timestamp;
  unsigned int   HostTimestamp;
  unsigned char  RID[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  ARID[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  BID[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  AWID[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  EventFlags[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  ExtEventFlags[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  WriteAddrLen[XAPM_MAX_NUMBER_SLOTS];
  unsigned char  ReadAddrLen[XAPM_MAX_NUMBER_SLOTS];
  unsigned short WriteBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned short ReadBytes[XAPM_MAX_NUMBER_SLOTS];
  unsigned short WriteAddrId[XAPM_MAX_NUMBER_SLOTS];
  unsigned short ReadAddrId[XAPM_MAX_NUMBER_SLOTS];
} xclTraceResults;

typedef struct {
  unsigned int mLength;
  //unsigned int mNumSlots;
  xclTraceResults mArray[MAX_TRACE_NUMBER_SAMPLES];
} xclTraceResultsVector;

#endif
