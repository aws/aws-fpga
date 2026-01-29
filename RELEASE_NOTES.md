# F2 Developer Kit Release Notes

## v2.2.1

* [Release of FPGA Developer AMI 1.18.0 (Rocky Linux 8.10)](http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu) with Vivado/Vitis 2025.1 tools pre-installed
* [Release of Vivado HLx flow](./User_Guide_AWS_EC2_FPGA_Development_Kit.md#development-environments)
* Fixed TCL glob expression to properly read both .sv and .v files. Credit to @pyz-creeper and @dsw for this update!
* Updated error codes in create-fpga-image for unsupported design logic
* Updated the Virtual Ethernet Application to write the DMA buffer descriptors using the byte alignment required by the CL_SDE example, preventing data alignment errors on Rocky
* [Added Amazon FPGA Image (AFI) creation Python script](./hdk/README.md#step-6-submit-generated-dcp-for-afi-creation)
* Updated XRT version which includes stability fixes for Vitis

## v2.2.0

* Release of Vivado/Vitis 2025.1 Tools on [FPGA Developer AMI 1.18.0 (Ubuntu)](http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq)
* Introduced [MSI-X PCIe Interrupts Guided Example](./sdk/apps/msix-interrupts/README.md)
* Added [Loopback performance test for CL_SDE](./hdk/cl/examples/cl_sde/software/src/README.md)
* [ReadTheDocs navigation improvements](https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/)

## v2.1.2

* Introduced Python Bindings to the SDK
* Added [documentation](./sdk/userspace/cython_bindings/README.md) for Python binding usage and setup
* [Examples](./sdk/userspace/cython_bindings/) demonstrating Python-based FPGA control
* Added link to instructions for DCV licensing setup. Credit to @morgnza for this update!
* Added verbiage to DCV setup guide to show where to set virtual display resolution
* Fix to Bandwidth Calculation

## v2.1.1

* Added global register offset for the SDE IP. See [CL_SDE software examples](./hdk/cl/examples/cl_sde/software/src/README.md).
* Added [CL_SDE software exmaple](./hdk/cl/examples/cl_sde/software/src/sde_c2h_user_buffers.c) for a user allocated DMA buffer.
* [Documentation](./hdk/docs/List_AFI_on_Marketplace.md) to assist F2 customers with releasing AFIs and AMIs on the AWS Marketplace.
* [Documentation](./developer_resources/Amazon_DCV_Setup_Guide.md) to assist in creating a virtual desktop based on the FPGA Developer AMI running graphics-intensive applications remotely on Amazon EC2 instances.
* Fixed the BW calculation and tolerance calculation in the test_hbm_perf_random in the [cl_mem_perf](./hdk/cl/examples/cl_mem_perf/verif/README.md#test_hbm_perf_randomsv).

## v2.1.0

* Support for Vivado and Vitis 2024.2 tools.
* [Releasing New Developer AMI for 2024.2 tools.](http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq)
* Updating the asynchronous fpga_mgmt_examples to poll each FPGA once before moving to the next.

## v2.0.7

* Documentation updates to improve [ReadTheDocs](https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/) navigation and inline snippets.
* XSIM template script update to extend the waveform dump time.
* Added section with instructions for assigning custom PCIe IDs to HDK [README](./hdk/README.md).
* Added supplementary XDMA driver installation [guide](./hdk/docs/XDMA_Install.md)
* Updated [ERRATA](./ERRATA.md#hdk) with fix for XSIM when simulating HBM.
* Revised the [Vitis README](./vitis/README.md) with updated code snippets, more detail about the XRT setup, and a new guided example of the Hardware Emulation workflow.
* Fixed HDK DCP Tarball path issue described in [#706](https://github.com/aws/aws-fpga/issues/706).

## v2.0.6

* Releasing [CL_SDE software examples](./hdk/cl/examples/cl_sde/software/src/README.md) to demonstrate how to use the [Streaming Data Engine (SDE)](./sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md) DMA on [small shell](./User_Guide_AWS_EC2_FPGA_Development_Kit.md#aws-shells).
* Fixing the [virtual ethernet](./sdk/apps/virtual-ethernet/doc/Virtual_Ethernet_Application_Guide.md#packetgen-dual-instance-loopback) PacketGen Dual Instance Loopback example to forward packets back to the PacketGen instance.
* Fixing DDR backdoor access in simulation.

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
