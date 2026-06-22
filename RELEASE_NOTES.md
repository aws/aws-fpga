# F2 Developer Kit Release Notes

## v2.3.3

* Migrated FPGA Developer AMI (Ubuntu) - 1.16.2 to Ubuntu 22.04 due to 20.04 EoL
* Added AWS Clock Gen IP toggle/deassert reset SDK API entries, Cython bindings, and updated documentation
* Updated devkit to support Vivado/Vitis tool versions back to 2024.1
* Updated AWS EC2 F2 RAB to use 32GiB of storage for the root volume to simplify building experience

## v2.3.2

* Introducing a new beginner-friendly CL example called [cl_axil_reg_access](./hdk/cl/examples/cl_demo/cl_axil_reg_access/README.md) that demonstrates OCL AXI-Lite interface usage for CL register access
  * [Interactive Jupyter Notebooks](./sdk/notebooks/README.md) provide step-by-step instructions for the software runtime example, guiding developers through loading an AFI and performing register reads and writes on a live F2 instance
* Added IP warning suppression for Vitis builds with compatible XSAs
* General bug fixes

## v2.3.1

* Released FPGA Developer AMIs - 1.19.1: Ubuntu and Rocky Linux with AMD patch [AR000039913](https://adaptivesupport.amd.com/s/article/000039913) pre-installed. This fixes the XSIM compilation bug in Vivado 2025.2, and the double compilation workaround has been removed from `Makefile.common.inc`
* Updated verbiage in [Amazon DCV Setup Guide](./developer_resources/Amazon_DCV_Setup_Guide.md) to improve clarity
* Updated all NPM packages in [package-lock.json](./developer_resources/runtime_ami_builder/package-lock.json) to address security advisories
* Added information about EC2 instance placement groups to maximize throughput and minimize latency when networking between instances in the [Virtual Ethernet Application Guide](./sdk/apps/virtual-ethernet/doc/Virtual_Ethernet_Application_Guide.md)
* Formatted all Python files for style, consistency, and compliance with PEP 8

## v2.3.0

* Vivado/Vitis 2025.2 Support
  * Both the [FPGA Developer AMI (Ubuntu) - 1.19.0](https://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq) and [FPGA Developer AMI (Rocky Linux) - 1.19.0](http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu) are available with 2025.2 tools installed and ready to use
  * [See what's new in Vivado 2025.2 here](https://www.amd.com/en/products/software/adaptive-socs-and-fpgas/vivado/vivado-whats-new.html#tabs-de9b056824-item-d69fba5dd6-tab)
  * [See what's new in Vitis 2025.2 here](https://www.amd.com/en/products/software/adaptive-socs-and-fpgas/vitis/vitis-whats-new.html)
* AWS EC2 F2 Runtime AMI Builder (RAB) Update
    * Added support for [Vivado Lab Edition 2025.2](https://docs.amd.com/r/en-US/ug908-vivado-programming-debugging/Vivado-Lab-Edition)
* Virtual Ethernet Driver
  * Updated to use natively-available kernel modules instead of DPDK ones
* HDK Devkit Updates
  * Cleaned up the legacy code in the [`power_up()` simulation task](./hdk/common/verif/models/sh_bfm/sh_bfm.sv#L1218-L1253) to align with the correct shell clock scheme.
  * Due to a XSIM bug in Vivado 2025.2, a double compilation workaround is added in `Makefile.common.inc` (see [ERRATA](./ERRATA.md#hdk) for more details)
* AFI and AMI Creation Permission Requirements
  * Added [Setting Up IAM Roles for DevKit Use](./developer_resources/Setting_up_IAM_roles_for_devkit_use.md) doc that shows how to set up an IAM role and the minimum permission configurations needed to create each of these artifacts

## v2.2.2

* Introducing the AWS EC2 F2 Runtime AMI Builder (RAB)
  * The RAB is a customizable and extensible tool based on [the AWS CDK](https://docs.aws.amazon.com/cdk/v2/guide/home.html) that easily automates building production-ready AMIs tailored to each accelerator application's needs
  * [To get started building a runtime AMI, see the README here](./developer_resources/runtime_ami_builder/README.md)
  * Default components are provided to modularly install specific features such as Vivado Lab Edition, the AWS CLI, the AWS FPGA SDK, and more
  * [To learn how to integrate the RAB into existing AWS CDK flows, see the code example here](./developer_resources/runtime_ami_builder/lib/exampleLibraryUsage.ts)
* [Updated Rocky FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu) name and description to match Marketplace info
* Added F2 [AFI Manifest specification](./hdk/docs/AFI_Manifest.md) for the version number, ID, and clock parameters
* Added new "--no-encrypt" build option to the HDK flow to facilitate source code debugging
* Updated [fpga_clkgen_util](./sdk/userspace/fpga_libs/fpga_clkgen/fpga_clkgen_utils.c) and [sde_examples](./hdk/cl/examples/cl_sde/software/src/README.md) with better error handling procedures, addressing stability issues found on Rocky Linux.

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
* Added [CL_SDE software example](./hdk/cl/examples/cl_sde/software/src/sde_c2h_user_buffers.c) for a user allocated DMA buffer.
* [Documentation](./hdk/docs/List_AFI_on_Marketplace.md) to assist F2 customers with releasing AFIs and AMIs on the AWS Marketplace.
* [Documentation](./developer_resources/Amazon_DCV_Setup_Guide.md) to assist in creating a virtual desktop based on the FPGA Developer AMI running graphics-intensive applications remotely on Amazon EC2 instances.
* Fixed the BW calculation and tolerance calculation in the test_hbm_perf_random in the [cl_mem_perf](./hdk/cl/examples/cl_mem_perf/verif/README.md#system-verilog-tests).

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
