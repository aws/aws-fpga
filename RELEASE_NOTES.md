# F2 Developer Kit Release Notes

## v2.0.5

* Releasing instructions for using the Vivado GUI.
* Updating virtual_ethernet_install.py to no longer require sudo when run.
* Updating f2_mgmt_example, load_multiple_fpga.c, to load AFIs in parallel.
* Updated ReadTheDocs theme.
* Added the "F2 Software Performance Optimization Guide" with techniques for f2.48xlarge instances

## v2.0.4

* Release of new F2 instance size, **f2.6xlarge**:

| Instance Name     | FPGAs     | vCPUs     | FPGA Memory HBM / DDR4     | Instance Memory (GB)     | Local Storage (GiB)     | Network Bandwidth (Gbps)     | EBS Bandwidth (Gbps)     |
| :---------------: | :-------: | :-------: | :------------------------: | :----------------------: | :---------------------: | :--------------------------: | :----------------------: |
|  **f2.6xlarge**   |   **1**   |  **24**   |    **16 GiB / 64 GiB**     |         **256**          |       **1 x 950**       |          **12.5**            |         **7.5**          |
|  f2.12xlarge      |   2       |  48       |    32 GiB / 128 GiB        |         512              |       2 x 950           |          25.0                |         15               |
|  f2.48xlarge      |   8       |  192      |    128 GiB / 512 GiB       |         2048             |       8 x 950           |          100                 |         60               |

## v2.0.3

* Releasing fpga_mgmt_examples to demonstrate how the FPGA Management C API is used to perform FPGA image slot load and clear operations.
* Releasing the PacketGen Dual Instance Loopback example to the SDK Virtual Ethernet Application.
* Fixing the clkgen CLIs to prevent the configuration of clock groups that were removed from the AWS_CLK_GEN IP in customer designs.

## v2.0.2

Updates for initial release of ReadTheDocs documentation and to re-enable tests for XSIM.

## v2.0.1

Updates to HDK, SDK, and Vitis documentation. Added check for XRT install to enable Vitis hardware emulation. XRT install can now be performed automatically by running a command presented during `vitis_setup.sh`.

## v2.0.0

Initial release. F2 general-availability companion.
