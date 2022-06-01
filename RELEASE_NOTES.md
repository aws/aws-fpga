# AWS EC2 FPGA HDK+SDK Release Notes

**NOTE:** See [ERRATA](./ERRATA.md) for unsupported features
## Release 1.4.24
* AWS supports [migration](./hdk/docs/U200_to_F1_migration_HDK.md) from U200 Vivado development flow to F1 HDK flow using F1.A.1.4 shell

## Release 1.4.23
* FPGA developer kit now supports Xilinx Vivado/Vitis 2021.2

## Release 1.4.22
* FPGA developer kit update to upgrade Virtual Ethernet to support jumbo frames using newer versions of dpdk/pktgen

## Release 1.4.21
* FPGA developer kit now supports Xilinx Vivado/Vitis 2021.1

## Release 1.4.20
* Bug Fix release to fix XDMA to fix Issue #516
* Miscellaneous documentation updates

## Release 1.4.19
* Bug Fix release

We have identified a bug in the `flop_ccf.sv` module that can potentially impact timing closure of designs.
The module is instantiated in `sh_ddr.sv` and inadvertently introduces a timing path on the reset logic.
Although there is no functional impact, it may increase Vivado tool’s effort in timing closure of design.
There should be no functional impact from this bug if your design has already met timing.

## Release 1.4.18
* FPGA developer kit now supports Xilinx Vivado/Vitis 2020.2

## Release 1.4.17
* Updated XDMA Driver to allow builds on newer kernels
* Updated documentation on Alveo U200 to F1 platform porting
* Added Vitis 2019.2 Patching for AR#73068

## Release 1.4.16
* FPGA developer kit now supports Xilinx Vivado/Vitis 2020.1
    * To upgrade, use [Developer AMI v1.9.0](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on the AWS Marketplace.
* Updated Vitis examples to include usage of Vitis Libraries.
* Added documentation and examples to show Xilinx Alveo design migration to F1.

## Release 1.4.15a
* Fixed Xilinx AR#73068 patching
    * DDR4 IP needs to be regenerated for the patch to take effect.
* Updated cl_dram_dma public AFI.

## Release 1.4.15
* Added Xilinx AR#73068 patching
* Added DMA range error to the interrupt status register metrics
* Enhanced DDR model rebuild qualifiers in hdk_setup.sh 
* Updated Virtual JTAG Documentation

## Release 1.4.14
* Updated Vitis Platform file to fix a DDR bandwidth issue
* Added Vitis Debug Documentation

## Release 1.4.13
* FPGA developer kit now supports Xilinx Vivado/Vitis 2019.2
* To upgrade, use [Developer AMI v1.8.0](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on the AWS Marketplace.
       
## Release 1.4.12
* Added supported versions for BJS AMI's
* Added link to the re:Invent 19 F1 workshop
* Fixed missing extern C declaration by PR #473 
* Documentation Path fixes from PR #466, #468 and #470 

## Release 1.4.11
* FPGA developer kit supports Xilinx SDx/Vivado 2019.1
    * We recommend developers upgrade to v1.4.11 to benefit from the new features, bug fixes, and optimizations. 
    * To upgrade, use [Developer AMI v1.7.0](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on the AWS Marketplace. The Developer Kit scripts (hdk_setup.sh or sdaccel_setup.sh) will detect the tool version and update the environment based on requirements needed for Xilinx 2019.1 tools. 
* New functionality:
    * Added a [developer resources section](./developer_resources/README.md) that provides guides on how to setup your own GUI Desktop and compute cluster environment.
    * Developers can now ask for AFI limit increases via the [AWS Support Center Console](https://console.aws.amazon.com/support/cases#/create).
        * Create a case to increase your `EC2 FPGA` service limit from the console.
    * HLx IPI flow updates
        * HLx support for AXI Fast Memory mode.
        * HLx support for 3rd party simulations.
        * HLx support for changes in shell and AWS IP updates(e.g. sh_ddr).     
* Bug Fixes:
    * Documentation fixes in the [Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)
    * Fixes for forum questions
        * [Unable to compile aws_v1_0_vl_rfs.sv in Synopsys VCS](https://forums.aws.amazon.com/thread.jspa?threadID=308829&tstart=0)
        * [Use fpga_mgmt init in HLx runtime](https://forums.aws.amazon.com/thread.jspa?messageID=912063)
    * New XRT versions added to the [XRT Installation Instructions](./SDAccel/docs/XRT_installation_instructions.md) to fix segmentation faults when using xclbin instead of awsxclbin files.
* Deprecations:
    * Removed GUI Setup scripts from AMI v1.7.0 onwards. See the [developer resources section](./developer_resources/README.md) that provides guides on how to setup your own GUI Desktop and compute cluster environment.
* Package versions used for validation
  
   | Package | AMI 1.7.0 [2019.1] | AMI 1.6.0 [2018.3] |AMI 1.5.0 [2018.2] | AMI 1.4.0 [2017.4] |
   |---------|---|------------------------|------------------------|-----------------------|
   | OS      | Centos 7.6 | Centos 7.6 | Centos 7.5, 7.6 | Centos 7.4 |
   | kernel  | 3.10.0-957.27.2.el7.x86_64 | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64  | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-957.27.2.el7.x86_64 | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7_6.2.x86_64 | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |   

## Release 1.4.10
* New functionality:
    * SDK now sorts the slots in DBDF order. Any scripts or integration maintainers should note that the slot order will be different from previous versions and should make any updates accordingly.
  
* Bug Fixes:
    * Fixes a bug in the [Automatic Traffic Generator (ATG)](./hdk/cl/examples/cl_dram_dma/design/cl_tst.sv). In SYNC mode, the ATG did not wait for write response transaction before issuing read transactions.
    * Released [Xilinx runtime(XRT) version 2018.3.3.2](https://github.com/Xilinx/XRT/releases/tag/2018.3.3.2) to fix the following error:
           `symbol lookup error: /opt/xilinx/xrt/lib/libxrt_aws.so: undefined symbol: uuid_parse!`
    * This release fixes a bug wherein concurrent AFI load requests on two or more slots resulted in a race condition which sometimes resulted in Error: `(20) pci-device-missing`
    * This release fixes a issue with coding style of logic which could infer a latch during synthesis in [sde_ps_acc module](./hdk/cl/examples/cl_sde/design/sde_ps_acc.sv) within cl_sde example 

* Package versions used for validation
  
   | Package | AMI 1.6.0 [2018.3] |AMI 1.5.0 [2018.2] | AMI 1.4.0 [2017.4] |
   |---------|------------------------|------------------------|-----------------------|
   | OS      | Centos 7.6 | Centos 7.5, 7.6 | Centos 7.4 |
   | kernel  | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64  | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |
   

## Release 1.4.9
 * New functionality:
    * Improved AFI load times for pipelined accelerator designs. For more details please see [Amazon FPGA image (AFI) pre-fetch and caching features](./hdk/docs/load_times.md).

 * Ease of Use features:
    * [Improved SDK Error messaging](./sdk/userspace/fpga_libs/fpga_mgmt/fpga_mgmt.c)
    * [Improved documentation](./hdk/docs/IPI_GUI_Vivado_Setup.md#switching-between-hdk-and-hlx-flows) to help with transition from [HLX to HDK command line flows](https://forums.aws.amazon.com/thread.jspa?threadID=302718&tstart=0) and vice versa
    * Incorporates feedback from [aws-fpga Issue 458](https://github.com/aws/aws-fpga/issues/458) by making the ```init_ddr``` function, used in design simulations to initialize DDR, more generic by moving out ATG deselection logic to a new ```deselect_atg_hw``` task 

 * Bug Fixes:
    * Fixed Shell simulation model (sh_bfm) issue on PCIM AXI read data channel back pressure which was described in HDK 1.4.8 Errata.
    * Fixed HDK simulation example which [demonstrates DMA and PCIM traffic in parallel](./hdk/cl/examples/cl_dram_dma/verif/tests/test_dma_pcim_concurrent.sv).

 * Package versions used for validation
  
   | Package | AMI 1.6.0 [2018.3] |AMI 1.5.0 [2018.2] | AMI 1.4.0 [2017.4] |
   |---------|------------------------|------------------------|-----------------------|
   | OS      | Centos 7.6 | Centos 7.5, 7.6 | Centos 7.4 |
   | kernel  | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64  | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |
   
## Release 1.4.8
 * FPGA developer kit supports Xilinx SDx/Vivado 2018.3
    * We recommend developers upgrade to v1.4.8 to benefit from the new features, bug fixes, and optimizations. To upgrade, use [Developer AMI v1.6.0](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on AWS Marketplace.  The Developer Kit scripts (hdk_setup.sh or sdaccel_setup.sh) will detect the tool version and update the environment based on requirements needed for Xilinx 2018.3 tools. 
 * Ease of Use features:
    * Support for importing results into SDx GUI - By importing results from a script-based flow into SDx IDE, developers can leverage the tools for debug/profiling while keeping flexibility of the script-based flow
    * Vivado HLS developers can now import designs into SDAccel environment to leverage emulation, debug and run-time software
 * New functionality:
    * The following HLS Video Processing cores are now license free and come installed with Vivado (VPSS, Video Mixer, Video TPG, Frame Buffer WR/RD, Gamma LUT, Demosaic, VTC) 
    * Improved XCLBIN utilities designed for automating the management of accelerator designs
    * Incremental compile reduces build times
    * [Python bindings for AWS FPGA MGMT Tools](sdk/userspace/python_bindings/README.md)

  * Fixed Issues
    * [Fixes printf in main of fpga_local_cmd](https://github.com/aws/aws-fpga/pull/450)
    * [Fixes SV dma read function to work with unprintable chars](https://github.com/aws/aws-fpga/pull/412)
    * [Fixes Segmentation Fault in cl_sde simulation test](https://forums.aws.amazon.com/thread.jspa?threadID=298946&tstart=0)
    * [Fixes test issues in cl_dram_dma example when using the AXI memory model for faster simulations](./hdk/cl/examples/cl_dram_dma/verif/README.md)
 
  * Deprecated Features
    * As announced in HDK 1.4.6 all EDMA driver code has been removed and deprecated from the developer kit. 
        * AWS recommends using the [XDMA](sdk/linux_kernel_drivers/xdma/README.md) driver for your applications.
   
  * Package versions used for validation
  
   | Package | AMI 1.6.0 [2018.3] |AMI 1.5.0 [2018.2] | AMI 1.4.0 [2017.4] |
   |---------|------------------------|------------------------|-----------------------|
   | OS      | Centos 7.6 | Centos 7.5, 7.6 | Centos 7.4 |
   | kernel  | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64  | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-957.5.1.el7.x86_64 | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |
   

## Release 1.4.7

  * Adds [Xilinx Runtime (XRT)](https://github.com/Xilinx/XRT/releases/tag/2018.2_XDF.RC5) Support for Linux kernel 3.10.0-957.1.3.el7.x86_64 & Centos 7.6
  * Package versions used to validate SDAccel runtime
  
   | Package | AMI 1.5.0 [SDx 2018.2] | AMI 1.4.0 [SDx 2017.4] |
   |---------|------------------------|------------------------|
   | OS      | Centos 7.5, 7.6 | Centos 7.4 |
   | kernel  | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64  | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-862.11.6.el7.x86_64, 3.10.0-957.1.3.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |


## Release 1.4.6

  * Fixes SDx 2018.2 [missing profile report items in SDAccel](https://forums.aws.amazon.com/thread.jspa?threadID=293541&tstart=0)
    * Requires [Xilinx 2018.2 Patch AR71715](hdk/docs/SDxPatch_AR71715_and_XRT_installation_instructions.md#installing-sdx-20182-tool-patch-ar71715)
    * Requires [Xilinx runtime release 2018.2_XDF.RC4](https://github.com/Xilinx/XRT/tree/2018.2_XDF.RC4)
    * Please see patching & XRT installation instructions [here](hdk/docs/SDxPatch_AR71715_and_XRT_installation_instructions.md)
  * Fixes SDx 2018.2 [multithreaded kernel driver scheduling](https://forums.aws.amazon.com/thread.jspa?threadID=293166&tstart=0)
     * Requires [Xilinx runtime release 2018.2_XDF.RC4](https://github.com/Xilinx/XRT/tree/2018.2_XDF.RC4)
     * Please see XRT installation instructions [here](hdk/docs/SDxPatch_AR71715_and_XRT_installation_instructions.md#installing-xilinx-runtime-xrt-20182_xdfrc4)  
  * EDMA Driver is no longer supported. 
      * AWS strongly recommends moving your applications to [XDMA](sdk/linux_kernel_drivers/xdma/README.md).
      * EDMA Driver will be fully removed from Developer kit 1.4.7+.
  * Fixed Issues
    * [NULL definition include in header file](https://github.com/aws/aws-fpga/pull/414)
    * [Improved messaging for AFI builder script](https://github.com/aws/aws-fpga/pull/407)
    * [Fixes address decoding to DDR slaves in cl_dram_dma example](hdk/cl/examples/cl_dram_dma/design)  
  * Improvements
    * [Improves SDK FPGA management tools error messaging](sdk/userspace/fpga_mgmt_tools/README.md)
    * [Enhanced DMA lib for general device number mapping](sdk/userspace/fpga_libs/fpga_dma/fpga_dma_utils.c)
    * [Improved guidelines for AFI power management](hdk/docs/afi_power.md)
    * [Improved Streaming Data Engine IP Integration Documentation](sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md) 
   
  * Package versions used to validate SDAccel runtime
  
   | Package | AMI 1.5.0 [SDx 2018.2] | AMI 1.4.0 [SDx 2017.4] |
   |---------|------------------------|------------------------|
   | kernel  | 3.10.0-862.11.6.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | kernel-devel | 3.10.0-862.11.6.el7.x86_64 | 3.10.0-693.21.1.el7.x86_64 |
   | LIBSTDC++ | libstdc++-4.8.5-36.el7.x86_64 | libstdc++-4.8.5-16.el7_4.2.x86_64 |
   
   
## Release 1.4.5 

* [Documents SDAccel Runtime compatibility](SDAccel/docs/Create_Runtime_AMI.md#runtime-ami-compatibility-table)
* [Enables SDK FPGA Mgmt tool access to Non-root users](sdk/README.md#using-fpga-as-non-root-user)
* Fixed issues
  * [HLX simulation failure](https://forums.aws.amazon.com/thread.jspa?threadID=293313&tstart=0)
  * [Shell BFM  read from C host memory](https://forums.aws.amazon.com/thread.jspa?threadID=288959&tstart=0)
  * [cl_dram_dma example design DDR read issue](https://forums.aws.amazon.com/thread.jspa?threadID=290277&tstart=50)

## Release 1.4.4        
* Fixed compile issues in simulation while using 3rd party simulators (synopsys VCS, Cadence IES and Mentor Questasim).

## Release 1.4.3
* [DRAM Data Retention](hdk/docs/data_retention.md) - With DRAM data retention, developers can simply load a new AFI and continue using the data that is persistently kept in the DRAM attached to the FPGA, eliminating unnecessary data movements and greatly improving the overall application performance.
* [Virtual Ethernet](./sdk/apps/virtual-ethernet/README.md) - Provides a low latency network interface for EC2 F1, that enables high performance hardware acceleration to ethernet based applications on AWS like firewalls, routers and advanced security virtual appliances. With Virtual Ethernet, developers are able to create F1 accelerators that process ethernet packets directly from user-space on the FPGA with high throughput and low-latency. 
* [Developer AMI v1.5](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) with Vivado/SDx 2018.2 tools - New FPGA Developer AMI supporting Vivado 2018.2 for faster compile times, higher frequencies and improved timing closure

## Release 1.4.2
* Fixed SDAccel XOCL driver compile fails that occur on linux kernels greater than 3.10.0-862.3.3.el7.x86_64

## Release 1.4.1
* Simulation performance Improvements
  * DDR Behavioural Model- Hardware simulations use an AXI memory model to run 4X faster by skipping DDR initialization. Please refer to this [README](./hdk/cl/examples/cl_dram_dma/verif/README.md) on how to use this feature in your simulation.
  * DDR Backdoor Loading- Hardware simulation time is reduced by pre-loading data directly into memory models.  Please refer to this [README](./hdk/cl/examples/cl_dram_dma/verif/README.md#ddr-backdoor-loading) for example tests that demonstrate this feature.
* Fixed Issues
  * XOCL Driver update to address synchronization issues.
  * Fixed XOCL driver issues when using ubuntu distribution for Linux OS.
  * Improved Performance for [cl_dram_dma Public AFI](./hdk/cl/examples/cl_dram_dma/README.md#metadata).
  * SDAccel 3rd party examples updated to use Shell V1.4 DSA.
  * Fixed AFI Manifest generation in IPI flow.
  * HLX button fixed in IPI
  * [FPGA Library update](./sdk/userspace/README.md)
  
  
## Release 1.4.0
* [New Shell Stable: v04261818](./hdk/common/shell_stable).  Starting with release v1.4.0, the AWS FPGA shell stable has been updated and only supports Xilinx 2017.4 SDx/Vivado.  All previous versions of tools and shells are not supported with this developer kit shell release. 
  * [Shell Release Notes](./hdk/docs/AWS_Shell_RELEASE_NOTES.md) 

* The previous shell (v071417d3) will be supported until 09/01/2018.  Developers are required to use the [developer kit v1.3.X branch](https://github.com/aws/aws-fpga/tree/REL_v1_3_8) for all shell version v071417d3 development.  

* Release 1.4.0 greatly improves the performance of the DMA (for interrupt driven DMA on the cl\_dram\_dma example design). This is accomplished through a combination of shell changes to relax DMA timeouts and a new XDMA software driver option.  We have ported the relevant HDK examples to the XDMA driver in this release. EDMA is still supported, and developers can freely choose which DMA driver to use as part of their host application.


## Previous release notes
## Release 1.3.X Details

The following major features are included in this HDK release: 

### 1.    New Shell, with modified Shell/CL interface. Changes are covered in: 
* The floorplan has been enhanced to enable more optimal CL designs through better timing closure and reduced congestion at the CL to Shell interface.
* [AWS_Shell_Interface_Specification.md](./hdk/docs/AWS_Shell_Interface_Specification.md) has been updated.  See cl_ports.vh for the updated port list
* AWS Shell DCP is stored in S3 and fetched/verified when `hdk_setup.sh` script is sourced.

### 2.    Integrated DMA 
* DMA functionality has been enhanced to allow DMA transactions of up to 1MB.
* Multi-queue in each direction is now supported
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA (EDMA) driver is provided.
* EDMA Installation Readme provides installation and usage guidelines
* See [Kernel_Drivers_README](./sdk/linux_kernel_drivers/README.md) for more information on restrictions for this release


### 3.    PCI-M
* The PCI-M interface is fully supported for CL generated transactions to the Shell. 

### 4.    URAM 
* Restrictions on URAM have been updated to enable 100% of the URAM with a CL to be utilized.  See documentation on enabling URAM utilization: [URAM_options](./hdk/docs/URAM_Options.md)

### 5.    Vivado IP Integrator (IPI) and GUI Workflow
* Vivado graphical design canvas and project-based flow is now supported.  This flow allows developers to create CL logic as either RTL or complex subsystems based on an IP centric block diagram.  Prior experience in RTL or system block designs is recommended.  The [IP Integrator and GUI Vivado workflow](hdk/docs/IPI_GUI_Vivado_Setup.md) enables a unified graphical environment to guide the developer through the common steps to design, implement, and verify FPGAs. To get started, start with the [README that will take you through getting started steps and documents on IPI](hdk/docs/IPI_GUI_Vivado_Setup.md)
 
### 6.    Build Flow improvments
* See [Build_Scripts](./hdk/common/shell_v04261818/build/scripts)

### 7.    VHDL
* CL designs in VHDL are fully supported.  
See example for more details [CL_HELLO_WORLD_VHDL](./hdk/cl/examples/cl_hello_world_vhdl/README.md)

### 8.    AXI Interface Checking
* Protocol checks have been added to the CL-Shell interface to detect and report CL errors for enhanced CL debugging.
* Transaction timeout values on the CL-Shell interface have been increased to allow for longer CL response times.
* See [Shell_Interface_Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)

### 9.    Support for Vivado 2017.1 SDX Build 

* The FPGA Development AMI includes Vivado 2017.1 SDX
    * Get the 1.3.0+ AMI by selecting the version from the [marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ#). 
* Older Vivado versions will not be supported

### 10.    SDK changes 

* Synchronous (default) mode for fpga-load-local-image and fpga-clear-local-image.  For example, in synchronous mode (default) fpga-load-local-image will wait for the AFI to transition to the "loaded" state, perform a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id, and display the final state for the given FPGA slot number.  Asynchronous operation is preserved with the "-A" option to both fpga-load-local-image and fpga-clear-local-image.
* The corresponding fpga_mgmt_load_local_image_sync and fpga_mgmt_clear_local_image_sync are provided by the fpga_mgmt library for use in C/C++ programs.

### Release 1.3.7
* Support for Xilinx SDx/Vivado 2017.1 and Xilinx [SDx](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1238-sdx-rnil.pdf)/[Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug973-vivado-release-notes-install-license.pdf) 2017.4 .  The HDK and SDAccel setup scripts configure the development environment based on the tool version found in the PATH environment variable.  
* Dynamic Software Acceleration (OpenCL) platform – The AWS platform is dynamically configured during compile time to optimize unused DDR/Debug logic, free up FPGA resources and reduce compile times.  Developers can instantiate up to 60 kernels (up from the max 16 2017.1 supported). [See 2017.4 Migration Document](SDAccel/docs/SDAccel_Migrate_dynamic_DSA.md) and [SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf) 
* OpenCL Kernel profiling – During compile time, profiling logic can be automatically inserted to enable generation of kernel profile data.  Profile data can be viewed using the SDx IDE under profile summary report and timeline trace report. [See chapter 6 within the SDAccel Environment Profiling and Optimization Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf)   
* OpenCL Hardware Emulation Debug – GDB-like debug allows developers a view of what is going on inside the kernel during hardware emulation.  Debug capabilities include start/stop at intermediate points and memory inspection.  [See chapter 6 within the SDAccel Environment Profiling and Optimization Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf)
* Post-synthesis and place/route optimization is now supported in OpenCL development environment.  [New XOCC options: reuse_synth and reuse_impl](https://www.xilinx.com/html_docs/xilinx2018_1/sdsoc_doc/wfq1517252127836.html)
* Customer simulation environment improvements and bug fixes:
  * 8 Additional tests that will help the developer with using the simulation environment and shell simulation model
  * Simulation model support for non DW aligned accesses
  * Co-simulation support
* EDMA Driver fixes:
  * Prevent timeouts due to scanning of the BARs for DMA hardware
  * Driver compilation support for 4.14 Linux kernel
* HDK improvements and fixes: 
  * cl_dram_dma improvements to make enabling/disabling DDRs easier
  * encrypt.tcl now clears out old files
  * URAM example timing improvements
* IPI Improvements:
  * [HLS example](hdk/cl/examples/cl_hls_dds_hlx/README.md) 
  * Script based approach for running the examples

   
### Release 1.3.6
  * Simulation model bug fix for transfer size of 64 bytes.
  * Xilinx 2017.1 Patch AR70350 - fixes report_power hangs.  Patch is automatically applied during setup scripts using MYVIVADO environment variable.
  * Updated synthesis scripts with -sv option when calling read_verilog.
  * Added documentation on us-gov-west-1 (GovCloud US).
  * Minor EDMA driver fixes and improvements.

### Release 1.3.5
  * [Amazon FPGA Images (AFIs) Tagging](hdk/docs/describe_fpga_images.md) - To help with managing AFIs, you can optionally assign your own metadata to each AFI in the form of tags. Tags are managed using the AWS EC2 CLI commands create-tags, describe-tags and delete-tags.  Tags are custom key/value pairs that can be used to identify or group EC2 resources, including AFIs.  Tags can be used as filters in the describe-fpga-images API to search and filter the AFIs based on the tags you add.
  * EDMA driver fixes and improvements, including polled DMA descriptor completion mode which improves performance on smaller IO (<1MB).
  * [AFI Power metrics and warnings](hdk/docs/afi_power.md) – developers can avoid power violations by monitoring metrics that provide recent FPGA power, maximum FPGA power, and average FPGA power. CL designs can use power state pins to help developers throttle CL to avoid power violation. 
  * Improved IPI 3rd party simulator support.
  * Simulation model fixes.
  * SDAccel improvements - Removal of settings64 script from SDAccel setup and switching between DSAs.

### Release 1.3.4
  * EDMA/XDMA Driver improvements
  * Additional SDAccel Platforms
    * 1DDR for faster build times and smaller expanded shell
    * RTL Kernel Debug adds support for virtual jtag debug on RTL kernels
  * IP Integrator GUI (HLx) improvements 
    * CL\_DRAM\_DMA fixes and improvements
      *  Dual master support
  * Simulation environment fixes and improvements
    * AXI/AXIL Protocol checkers
    * Shell model improvements
    * SW co-simulation support on cl\_hello\_world
    * DDR Model patch
  * Updated SH\_DDR module in preparation for upcoming feature release    
   
### Release 1.3.3
  * New FPGA Image APIs for deleting and reading/editing attributes 

### Release 1.3.2
  * SDAccel general availability 

### Release 1.3.1
  * EDMA Driver release 1.0.29 - MSI-X fixes
  * Improved IPI documentation
  * Documentation updates
  * Build flow fixes
  * Public LTX files for use with hdk examples AFIs 

### Release 1.3.0
  * FPGA initiated read/write over PCI (PCI-M)
  * Redesigned Shell - improved the shell design to allow more complex place and route designs to meet timing
  * Expanded DMA support
  * Improved URAM utilization
  * Improved AXI Interface checking
  * New customer examples/workflows:  IP Integrator, VHDL, and GUI
  * SDAccel preview is accepting developers - See [README](sdk/SDAccel/README.md) registration  

### Release 1.2.4
   *    AWS SDK API `aws ec2 describe-fpga-images` released. See [describe-fpga-images](./hdk/docs/describe_fpga_images.md) document for details on how to use this API.  Requires Developer AMI 1.2.4 or awscli upgrade: `pip install --upgrade --user awscli`
   *    Fix cl_dram_dam debug probes (.ltx) generation in build scripts
   *    Fixed bugs with DMA in the simulation model and testbench

### Release 1.2.3
   *    New [Errata](./ERRATA.md) 
   *    Added debug probes (.ltx) generation to build scripts
   *    Fixed a bug with the simulation model that fixed the AXI behavior of wlast on unaligned address
   *    Added [timeout debug documentation](./hdk/docs/HOWTO_detect_shell_timeout.md)
   
### Release 1.2.2
   *    Expanded [clock recipes](./hdk/docs/clock_recipes.csv) 
   *    Virtual JTAG documentation updates
   *    Reduced DCP build times by 13% (34 mins) for cl_dram_dma example by adding an option to disable virtual jtag
   *    Included encryption of .sv files for CL examples

### Release 1.2.1
   *    Updated CL example build scripts with Prohibit URAM sites 
   *    EDMA Performance improvements 
   *    Expanded EC2 Instance type support
   *    CL Examples @250Mhz (Clock recipe A1)
   *    Option to exclude Chipscope (Virtual JTAG) from building CL examples (DISABLE_VJTAG_DEBUG)

### Release 1.2.0 Content Overview and New Features Details
#### 1.    New Shell, with modified Shell/CL interface. Changes are covered in: 

* New Shell Stable: 0x04151701: ./hdk/common/shell_v04151701
* cl_ports.vh have the updated port list 
* [AWS_Shell_Interface_Specification.md](./hdk/docs/AWS_Shell_Interface_Specification.md) has been updated
* Updated the xdc timing constrains under [constraints](./hdk/common/shell_v04261818/build/constraints) to match the new interfaces 
* Updated [CL HELLO WORLD](./hdk/cl/examples/cl_hello_world) example to use the new cl_ports.vh
* DCP for the latest shell v04151701. AWS Shell DCP is stored in S3 and fetched/verified when `hdk_setup.sh` script is sourced.


#### 2.    Integrated DMA in Beta Release. AWS Shell now includes DMA capabilities on behalf of the CL
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA (EDMA) driver is provided.
* EDMA Installation Readme provides installation and usage guidelines
* The initial release supports a single queue in each direction
* DMA support is in Beta stage with a known issue for DMA READ transactions that cross 4K address boundaries.  See [Kernel_Drivers_README](./sdk/linux_kernel_drivers/README.md) for more information on restrictions for this release


#### 3.    CL  User-defined interrupt events.  The CL can now request sending MSI-X to the instance CPU
* * Usage covered in new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma)
* A corresponding AWS EDMA driver is provided under `/sdk/linux_kernel_drivers/edma`
* EDMA Installation Readme provides installation and usage guidelines
* The initial release supports a single user-defined interrupt 

#### 4.    Added a Mandatory Manifest.txt file submitted with each DCP via create-fpga-image API

* File content defined in [AFI Manifest](./hdk/docs/AFI_Manifest.md)
* AFI_Manifest.txt is created automatically if the developer is using the aws_build_dcp_from_cl.sh script
* PCI Vendor ID and Device ID are part of the manifest 
* Shell Version is part of the manifest 
* The Manifest.txt file is required for AFI generation
* All the examples and documentation for build include the description and dependency on the Manifest.txt

    
#### 5.    Decoupling Shell/CL interface clocking from the internal Shell Clock 

* All the Shell/CL interfaces running off clk_main_a0, and no longer required to be 250Mhz. 
* The default frequency using the HDK build flow for `clk_main_a0` is 125Mhz as specified in recipe number A0. Allowing CL designs to have flexible frequency and not be constrained to 250Mhz only. All CL designs must include the recipe number in the manifest.txt file in order to generate an AFI.
* All xdc scripts have been updated to clk_main_a0 and to reference a table with the possible clocks’ frequencies combinations
* Updated CL_HELLO_WORLD and CL_DRAM_DMA examples to use the `clk_main_a0` 

#### 6.    Additional User-defined Auxiliary Clocks
Additional tunable auxiliary clocks are generated by the Shell and fed to the CL. The clocks frequencies are set by choosing a clock recipe per group from a set of predefined frequencies combination in [clock recipes table](./hdk/docs/clock_recipes.csv)

* Clock frequency selection is set during build time and recorded in the manifest.txt (which should include the clock_recipe_a/b/c parameters)
* Clock frequency programming in the FPGA slot itself occurs when the AFI is loaded. The list of supported frequencies is available [here](./hdk/docs/clock_recipes.csv)
* See [AWS_Shell_Interface_Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for details on the clocking to the CL  
* See [AFI Manifest](./hdk/docs/AFI_Manifest.md) for details on the AFI manifest data
* xdc is automatically updated with the target frequency (WIP)

#### 7.    Additional PCIe BARs and update PCIe Physical Function mapping

** The AppPF now has 4 different PCIe BARs:**

* BAR0 and BAR1 support 32-bit access for different memory ranges of the CL through separate AXI-L interfaces 
* BAR2 is used exclusively for the DMA inside the Shell and MSI-X interrupt tables  
* BAR4 expanded to 128GiB to cover all external DRAM memory space


** ManagementPF added additional PCIe BARs:**

* BAR2 is used for Virtual JTAG
* BAR4 is used for SDAccel Management (WIP)
* [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) covers these changes in detail
* [AWS FPGA PCIe Memory Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md) covers the address map details
* The [FPGA PCI library](./sdk/userspace/include/fpga_pci.h) provides simple APIs to take advantage of these BARs


** MgmtPF and AppPF are now represented as different PCIe devices in F1 instances:**
* Each FPGA Slot will occupy two PCIe buses, one for AppPF and one for MgmtPF


#### 8.    Expanded AppPF BAR4 space to 128GiB 

* BAR4 addressing space enables a CL to fully map FPGA card DRAM into the AppPF address space.  AppPF BAR4 is now a 128GB BAR  
* [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) covers these changes in detail
* [AWS FPGA PCIe Memory Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md) covers the address map in detail

  
#### 9.    Added wider access on the Shell to CL AXI4 512-bit bus (sh_cl_dma_pcis)

* Wider access provides higher bandwidth DMA and host to FPGA access
* Instance CPU can now burst full 64-byte write burst to AppPF PCIe BAR4 if mapped as Burstable (a.k.a WC: WriteCombine) (WIP)
* pci_poke_burst() and pci_poke64() calls were added to [fpga_pci library](./sdk/userspace/include/fpga_pci.h) to take advantage of this
* CL_DRAM_DMA and CL_HELLO_WORLD examples support for a wider access was added


#### 10.    Support larger than 32-bit access to PCIe space

* Large inbound transaction going to AppPF PCIe BAR4 will be passed onward to the CL  
* Large inbound transactions going to the other BARs will be split by the Shell to multiple 32-bit accesses, and satisfy AXI-L protocol specification.


#### 11.    Enhanced AXI4 error handling and reporting

* Additional error conditions detected on the CL to Shell Interface and reported through fpga-describe-image tool
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details
* FPGA Management Tool [metrics output](./sdk/userspace/fpga_mgmt_tools/README.md) covers the additional error handling details

#### 12.    Expanded AXI ID space throughout the design

* The AXI buses between Shell and CL support an expanded number of AXI ID bits to allow for bits to be added by AXI fabrics  See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


#### 13.    Shell to CL interface metrics.  

* New metrics for monitoring the Shell to CL are available from the AFI Management Tools. 
* See [fpga mgmt tools readme](./sdk/userspace/fpga_mgmt_tools/README.md) for more details


#### 14.    Virtual LED/DIP Switches.  

* Added CL capability to present virtual LEDs and push virtual DIP switches indications to the CL, set and read by FPGA Management Tools and without involving CL logic, providing the developer an environment similar to developing on local boards with LED and DIP switches
* See new commands in [FPGA Image Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for description of the new functionality
* CL_HELLO_WORLD example includes some logic to set LED and adjust according to vDIP
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


#### 15.    Virtual JTAG

* The Shell has the capability for supporting CL integrated Xilinx debug cores like Virtual I/O (VIO) and Integrated Logic Analyzer (ILA) and includes support for local/remote debug by running XVC  
* [Virtual_JTAG_XVC](./hdk/docs/Virtual_JTAG_XVC.md) describes how to use Virtual JTAG from Linux shell
* cl_debug_bridge module was added to HDK common directory
* Support for generating .ltx files after `create-fpga-image` was added.  .ltx file is required when running interactive ILA/VIO debug (WIP)
* Build tcl and xdc includes the required changes to enable Virtual JTAG 
* See [CL_DRAM_DMA](./hdk/cl/examples/cl_dram_dma) for examples on using Virtual JTAG and XVC for debug

#### 16.    Examples summary table

* [Example Summary Table](./hdk/cl/examples/cl_examples_list.md) covers which CL capabilities is demonstrated in each example


#### 17.    Updated CL_HELLO_WORLD Example

* Matching the new Shell/CL interface 
* Add support for 32-bit peek/poke via ocl\_ AXI-L bus
* Virtual JTAG support with Xilinx ILA and VIO debug cores 
* Demonstrate the use of Virtual LED and Virtual DIPSwitch
* Runtime software examples, leveraging fpga_pci and fpga_mgmt C-libraries
* Updated PCIe Vendor ID and Device ID
* See [CL HELLO WORLD readme](./hdk/cl/examples/cl_hello_world/README.md) for more details


#### 18.    Added CL_DRAM_DMA Example

* Mapping AppPF PCIe BAR4 to DRAM
* Using DMA to access same DRAM
* Using SystemVerilog Bus constructs to simplify the code
* Demonstrate the use of User interrupts
* Demonstrate the use of bar1\_ AXI-L bus
* Includes Runtime C-code application under [CL_DRAM_DMA software](./hdk/cl/examples/cl_dram_dma/software)
* See [CL_DRAM_DMA README](./hdk/cl/examples/cl_dram_dma/README.md)


#### 19.    Software Programmer View document 

* The [Software Programmer View document](./hdk/docs/Programmer_View.md) is added to explain the various ways a Linux user-space application can work with AWS FPGA Slots


#### 20.    Two C-libraries for FPGA PCIe access and for FPGA Management

* The C-libraries are simplifying and adding more protections from developer’s mistakes when writing a runtime C-application
* [Fpga_mgmt.h](./sdk/userspace/include/fpga_mgmt.h) cover the APIs for calling management functions
* [Fpga_pcie.h](./sdk/userspace/include/fpga_pci.h) covers the API for access the various PCI memory spaces of the FPGA
* CL_HELLO_WORLD and CL_DRAM_DMA examples updated to use these libraries.

#### 21.    VHDL support is added

* Included Vivado encryption key file for VHDL
* Added VHDL-specific line in `encrypt.tcl` reference files
* Developer would need to add `read_vhdl` in `create_dcp_from_cl.tcl`

#### 22.    Additional FPGA Management Tools added

*    See [FPGA Management Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for more details

#### 23.    Support for Vivado 2017.1 Build 

* The FPGA Development AMI includes Vivado 2017.1
* Older Vivado versions will not be supported

#### 24.    Embed the HDK version and Shell Version as part of the git tree

* [hdk_version.txt](./hdk/hdk_version.txt)
* [shell_version.txt](./hdk/common/shell_v04261818)

#### 25.    Initial Release of SDAccel and OpenCL Support (NA)

* Updated documentation in /sdk/SDAccel (NA)
* OpenCL runtime HAL for supporting SDAccel and OpenCL ICD in /sdk/userspace (NA)
* SDAccel build post-processing to register SDAccel xcl.bin as AFI. (NA) 

#### 26.    Simplify handling of unused Shell to CL interfaces

* Developers can simply call `include "unused\_**BUS\_NAME**\_template.inc" for every unused interface
* List of potential files to include is available in `$HDK_SHELL_DIR/design/interfaces/unused\*`
* cl_hello_world.sv and cl_dram_dma.sv provide examples (at the each of each file)

#### 27.    Support multiple Vivado versions

* `hdk_setup.sh` compares between the list of Vivado versions supported by the HDK and the installed vivado versions
* `hdk_setup.sh` would automatically choose the Vivado version from the available binaries in AWS FPGA Developer's AMI

#### 28.    Changes in DRAM controller setting to improve bandwidth utilization

* Change address decoding to ROW_COL_INTLV mode
* Enable auto precharge on COL A3
