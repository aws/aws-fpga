# Using Data Retention to Preserve the Contents of DRAM Across AFI Loads

Workloads that require multiple AFIs to process a data set can take advantage of data retention. For example, if a design is too big to fit into a single AFI, then it could be separated into multiple pipeline stages, each with its own AFI. Previously, a customer would have had to transfer important state and data from the DRAM of the FPGA to host memory before loading the next AFI. With data retention, that time consuming step can be eliminated. With each stage of the of the pipeline, the content of DRAM on the FPGA can be preserved such that each stage can pick up where the previous left off, without waiting for data transfers from host memory to complete.

### Requirements

For an AFI to support data retention, the following requirements must be met:

1. The AFI must be built with shell version 1.4 or higher.
2. The AFI must be built with the version of `sh_ddr.sv` shipped with 1.4 or higher.
3. The AFI must use all four DDR controllers. (All of `DDR_A_PRESENT`, `DDR_B_PRESENT`, `DDR_D_PRESENT` must be set. DDRC is part of the shell and is always present.)

To use data retention across AFI loads, the following conditions must be met:

1. The currently loaded AFI must support data retention.
2. The next AFI (the one to be loaded with data retained) must support data retention.
3. The current and next AFIs must use the same shell version.
4. The `-F` flag, to force reload the shell, must not be specified.
5. The FPGA must not be in a load-failed or any other failed state.
6. Traffic to and from the DDR controllers must be stopped. This includes DMA transactions, memory mapped IO to the DRAM, and accesses internal to the customer logic. Failure to stop this traffic can result in the loss of data.

### Example

To use data retention with the FPGA Image Tools, add the `-D`  flag to the load command. The following example uses the public, cl_dram_dma example AFI. To enter a state where all requirements are met, first load an AFI which supports data retention. Now it is possible to load the next AFI and retain the DRAM contents from the currently loaded AFI. Load another AFI (or the same AFI) which also supports data retention.

```
$ sudo fpga-clear-local-image -S 0
$ sudo fpga-load-local-image -H -S 0 -I agfi-0367124aff5e7c5f7
$ sudo fpga-load-local-image -H -S 0 -I agfi-0367124aff5e7c5f7 -D
```

Note that the first load command does not use the `-D` flag. The flag requests that the current contents of DRAM be preserved across the load. When the FPGA is in a cleared state, you cannot preserve the contents of DRAM and passing `-D` will fail.

#### Using the C API to load an AFI with data retention

```C
#include "fpga_mgmt.h"
#include "utils/log.h" /* fail_on macro */

int load_afi(int slot_id, char *afi_id, bool retention)
{
    int rc;
    union fpga_mgmt_load_local_image_options opt;
    static const uint32_t api_request_poll_count    = 50;
    static const uint32_t api_request_delay_ms      = 200;

    fpga_mgmt_init_load_local_image_options(&opt);
    opt.slot_id = slot_id;
    opt.afi_id = afi_id;
    if (retention) {
        opt.flags |= FPGA_CMD_DRAM_DATA_RETENTION;
    }

    rc = fpga_mgmt_load_local_image_sync_with_options(&opt,
        api_request_poll_count, api_request_delay_ms, 0);
    fail_on(rc != 0, out, "err: %d, %s", rc, fpga_mgmt_strerror(rc));

out:
    return rc;
}
```

To see a full implementation of an example using data retention, see [test_dram_dma_retention.c](../cl/examples/cl_dram_dma/software/runtime/test_dram_dma_retention.c).

### Errors
To accommodate data retention, three new error codes have been added to the FPGA Image Tools and mgmt library.

1. `(18) dram-data-retention-not-possible` - This error can occur when an attempt to load an AFI is made but not all conditions for data retention are met. The load is aborted and the FPGA state unchanged. Refer to the requirements listed above. Additional information may be available in the ingestion log for the AFI to explain why it does not support data retention.
2. `(22) dram-data-retention-failed` - When data retention is attempted and fails, this error is returned. Data has been lost in this case. Users should check if traffic to the DDR controllers is still active at the time of load, because active traffic prevents data retention from working correctly.
3. `(23) dram-data-retention-setup-failed` - This indicates that internal setup steps necessary for data retention have failed and data retention will not be possible when it otherwise would have. This error message is displayed when an internal error of the FPGA has occurred. If this happens, retry the load. If it continues to happen, contact AWS support for assistance.

### Clearing Data

To clear the contents of DRAM, simply call `fpga-clear-local-image`. Customer data is always cleared from the FPGA when an instance is terminated.
