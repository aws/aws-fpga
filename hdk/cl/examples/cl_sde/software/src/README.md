# Streaming Data Engine (SDE) Library API and Examples

## Overview

This directory contains example applications demonstrating the usage of the Streaming Data Engine (SDE) on AWS FPGA F2 instances. The examples showcase various data transfer scenarios and performance testing methods.

## sde_mgmt Functions

* **`sde_mgmt_init`**
  Initializes the SDE library by allocating DMA buffers and memory structures for subsequent operations.
  - `slot_id` (int): Specifies the FPGA image slot for subsequent SDE library operations.
  - `direction` (enum): Defines the data transfer direction (C2H: Card-to-Host, H2C: Host-to-Card, LOOPBACK). Determines which subsystem buffers are allocated.
  - `packet_size` (size_t): Defines the buffer size in bytes for data transfers with the CL_SDE.
  - `layout` (enum): Defines the DMA Buffers used for DMA (SINGLE: each buffer descriptor represents the same buffer that is repeatedly used, MULTI: each buffer descriptor represents a unique buffer, USER_MANAGED: buffers are allocated and managed by the user and each descriptor points to a unique buffer)
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_init_and_cfg`**
  Comprehensive initialization that allocates DMA buffers, resets the CL_SDE, and configures it in a single function call.
  - `slot_id` (int): Specifies the FPGA image slot for subsequent SDE library operations.
  - `direction` (enum):  Defines the data transfer direction (C2H: Card-to-Host, H2C: Host-to-Card, LOOPBACK). Determines which subsystem buffers are allocated.
  - `packet_size` (size_t): Defines the buffer size in bytes for data transfers with the CL_SDE.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_close`**
  Releases all resources allocated by the SDE library for the specified FPGA image slot.
  - `slot_id` (int): Identifies the FPGA image slot whose resources will be reclaimed.
  - **Returns**: 0 on successful resource release, non-zero value on error.

* **`sde_mgmt_reset`**
  Performs a reset of the CL_SDE in the specified FPGA image slot.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE to be reset.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_check_status`**
  Verifies the error status of a specific subsystem in the CL_SDE.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `subsystem` (enum): Specifies the subsystem to check (C2H: Card-to-Host, H2C: Host-to-Card).
  - **Returns**: 0 if no errors detected, non-zero value indicating specific error condition.

* **`sde_mgmt_set_dma_buffers**
  Sets the DMA buffers to buffers allocated by the user.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `subsystem` (enum): Specifies the subsystem to check (C2H: Card-to-Host, H2C: Host-to-Card).
  - `sde_buffers` (struct sde_buffer*): Specifies the array of user buffers to be used by the CL_SDE.
  - `num_buffers` (size_t): Specifies the number of user buffers passed in.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_cfg`**
  Configures the CL_SDE using parameters established during initialization.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_wait_desc_credit`**
  Blocks until descriptor credits are available for the specified subsystem.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `subsystem` (enum): Specifies the subsystem (C2H: Card-to-Host, H2C: Host-to-Card).
  - `num_desc` (size_t): Number of available descriptor credits to be blocked for.
  - **Returns**: 0 on success, non-zero value on error or timeout.

* **`sde_mgmt_post_desc`**
  Submits descriptors to the specified subsystem to initiate a DMA operation.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `subsystem` (enum): Specifies the target subsystem (C2H: Card-to-Host, H2C: Host-to-Card).
  - `num_desc` (size_t*): Number of descriptors to be posted.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_start_read`**
  Calculates and posts descriptors for a read operation from Card-to-Host.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `size` (size_t): Total number of bytes to be read from the card.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_read_md`**
  Reads the write-back next valid writeback-metadata struct. This struct specifies if status of a Card-to-Host DMA transfer including the size of the transferred data.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `md` (struct sde_md*): Valid pointer that will be populated with the metadata for the Card-to-Host DMA transfer.
  - **Returns**: 0 on success, non-zero value on error or timeout.

* **`sde_mgmt_read_data`**
  Transfers data from internal DMA buffers to the user-provided buffer.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `data` (void*): Destination buffer to receive the transferred data.
  - `size` (size_t): Number of bytes to transfer.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_prepare_write`**
  Copies user-provided data to internal DMA buffers in preparation for a write operation.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `data` (void*): Source buffer containing data to be written.
  - `size` (size_t): Number of bytes to prepare for writing.
  - **Returns**: 0 on success, non-zero value on error.

* **`sde_mgmt_write`**
  Calculates and posts descriptors for a write operation from Host-to-Card.
  - `slot_id` (int): Identifies the FPGA image slot containing the CL_SDE.
  - `size` (size_t): Total number of bytes to be written to the card.
  - **Returns**: 0 on success, non-zero value on error.

## Prerequisites

### Hardware Requirements
- AWS F2 Instance
- FPGA with CL_SDE loaded
- Bus mastering enabled for the FPGA

### Software Requirements
- AWS FPGA SDK
- Sudo access

## Environment Setup

1. Source the SDK:

`source ./sdk_setup.sh`

2. Enable Bus Mastering (if not already enabled):

`sudo setpci -s <Domain:Bus:Device.Function> 4.w=6`

Note: Device:Bus:Device.Function is for the PF0 function of the FPGA.

3. Configure Hugepages so that 128 are available (for packet sizes > 4096):

`sudo sysctl -w vm.nr_hugepages=<number_of_pages>`

4. Pinning Examples to a NUMA Node

For optimal performance on an `F2.48xlarge` instance, follow the [F2 software performance optimization guide](../../../../../../sdk/docs/F2_Software_Performance_Optimization_Guide.md) to detect the best the NUMA node for your FPGA Slot.

### Example Usage

`numactl --localalloc --cpunodebind <numa_node> sudo ./<example> <num_packets> <packet_size> <slot_id>`

## Examples

Build the sde_examples from the $(HDK)/cl/examples/cl_sde/software/runtime directory.

`make sde_examples`

### 1. Card-to-Host (C2H) Simple Transfer
- File: `sde_c2h_simple`
- Demonstrates basic card-to-host data transfer
- Configures SDE for reading data into a user-allocated buffer

#### Usage

- `sudo ./sde_c2h_simple <num_packets> <packet_size> <slot_id>`
- `sudo ./sde_c2h_simple 1 4096 0`

### 2. Host-to-Card (H2C) Simple Transfer
- File: `sde_h2c_simple`
- Demonstrates basic host-to-card data transfer
- Writes data from a user-allocated buffer to the SDE

#### Usage

- `sudo ./sde_h2c_simple <num_packets> <packet_size> <slot_id>`
- `sudo ./sde_h2c_simple 1 4096 0`

### 3. Loopback Transfer
- File: `sde_loopback_simple`
- Demonstrates bidirectional data transfer
- Writes data to SDE and reads it back

#### Usage

- `sudo ./sde_loopback_simple <num_packets> <packet_size> <slot_id>`
- `sudo ./sde_loopback_simple 1 8192 0`

### 4. Card-to-Host Performance Test
- File: `sde_c2h_perf_test`
- Measures maximum performance for card-to-host transfers
- Tests high-throughput data transfer
- Choose large packet sizes for better performance

#### Usage

- `sudo ./sde_c2h_perf_test <num_millions_packets> <packet_size> <slot_id>`
- `sudo ./sde_c2h_perf_test 5 16384 0`

### 5. Host-to-Card Performance Test
- File: `sde_h2c_perf_test`
- Measures maximum performance for host-to-card transfers
- Tests high-throughput data transfer
- Choose large packet sizes for better performance

#### Usage

- `sudo ./sde_h2c_perf_test <num_millions_packets> <packet_size> <slot_id>`
- `sudo ./sde_h2c_perf_test 1 131072 0`

### 6. Card-to-Host Transfer with User Managed Buffers
- File: `sde_c2h_user_buffers`
- Demonstrates basic card-to-host data transfer with user managed buffers
- Configures SDE for reading data into a user-managed DMA buffer

#### Usage

- `sudo ./sde_c2h_user_buffers <num_packets> <packet_size> <slot_id>`
- `sudo ./sde_c2h_user_buffers 1 4096 0`

## Performance Metrics

Each example provides performance metrics:
- Total Run Time
- Number of Packets
- Millions of Packets per Second (MPPS)
- Bandwidth (GB/s)

## Troubleshooting

- Ensure CL_SDE is loaded on the correct FPGA slot
- Verify bus mastering is enabled
- Check hugepages allocation for large packet sizes

## Software Interactions with the SDE

### Memory Mapping and Configuration

#### 1. Status Counter Mapping
SDE application software must map physical memory for status counters to enable:
- Status reporting
- Descriptor credit limit tracking
- Metadata buffer write pointer monitoring

**Reference:** [SDE Hardware Guide - Status Counter Write-Back](../../../../../../sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md#status-counter-write-back)

#### 2. Metadata Length Reporting
Map physical memory to report the length of data DMA-ed for each Card-to-Host descriptor.

**Reference:** [SDE Hardware Guide - C2H Write-Back Metadata](../../../../../../sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md#c2h-write-back-metadata)

#### 3. DMA Buffer Memory Mapping
Proper memory mapping is crucial for DMA operations:
- Buffer sizes: Up to 4k per packet
- Large packet sizes (>4k): Use hugepage memory mapping
- Descriptor generation requires:
  - Physical address of DMA buffer
  - Number of bytes that can be written to the buffer

Descriptor Types:
- [Card-to-Host (C2H) Descriptor](../../../../../../sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md#c2h-descriptor)
- [Host-to-Card (H2C) Descriptor](../../../../../../apps/virtual-ethernet/doc/SDE_HW_Guide.md#h2c-descriptor)

#### 4. Configuration Registers
Use SDE configuration registers to:
- Setup writeback data reporting
- Configure general SDE settings

**Reference:** [sde_hw_ctrl.c](sde_lib/sde_hw_ctrl.c)

### Data Flow Models

#### Card-to-Host (C2H) Data Flow
Follow the recommended [Card-to-Host data flow model](../../../../../../sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md#c2h)

#### Host-to-Card (H2C) Data Flow
Follow the recommended [Host-to-Card data flow model](../../../../../../sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md#h2c)

## Support
For any issues with the devkit documentation or code, please open a [GitHub](https://github.com/aws/aws-fpga/issues) issue with all steps to reproduce.

For questions about F2 instances, please open a [re:Post issue](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development) with the 'FPGA Development' tag.