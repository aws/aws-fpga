
# AWS EC2 FPGA HDK+SDK Release Notes


##  AWS EC2 F1 Platform Features:
   *    1-8 Xilinx UltraScale+ VU9P based FPGA slots
   *    Per FPGA Slot, Interfaces available for Custom Logic(CL):
         *    One x16 PCIe Gen 3 Interface
         *    Four DDR4 RDIMM interfaces (with ECC)
         *    AXI4 protocol support on all interfaces
   *    User-defined clock frequency driving all CL to Shell interfaces
   *	Multiple free running auxiliary clocks
   *    PCIE endpoint presentation to Custom Logic(CL)
         *    Management PF (physical function)
         *    Application PF
   *    Virtual JTAG, Virtual LED, Virtual DIP Switches
   *    PCIE interface between Shell(SH) and Custom Logic(CL).
         *    SH to CL inbound 512-bit AXI4 interface
         *    CL to SH outbound 512-bit AXI4 interface
	 *    Multiple 32-bit AXI-Lite buses for register access, mapped to different PCIe BARs
         *    Maximum payload size set by the Shell
         *    Maximum read request size set by the Shell
         *    AXI4 error handling 
    *    DDR interface between SH and CL
         *    CL to SH 512-bit AXI4 interface
         *    1 DDR controller implemented in the SH (always available)
         *    3 DDR controllers implemented in the CL (configurable number of implemented controllers allowed)

## Release 1.3.7 (See [ERRATA](./ERRATA.md) for unsupported features)
* Support for Xilinx SDx/Vivado 2017.1 and Xilinx [SDx](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1238-sdx-rnil.pdf)/[Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug973-vivado-release-notes-install-license.pdf) 2017.4 .    * This release supports Xilinx SDx 2017.4 and 2017.1.  The HDK and SDAccel setup scripts configure the development environment based on the tool version found in the PATH environment variable.  
   * FPGA developer kit version is listed in [hdk_version.txt](./hdk/hdk_version.txt)
   * FPGA developer kit supported tool versions are listed in [supported_vivado_versions](./supported_vivado_versions.txt)
   * The compatibility table describes the mapping of developer kit version to [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) version:  
   
| Developer Kit Version   | Tool Version Supported     |  Compatible FPGA developer AMI Version     |
|-----------|-----------|------|
| 1.3.0-1.3.6 | 2017.1 | v1.3.5 |
| 1.3.7-1.3.X | 2017.1 | v1.3.5-v1.3.X (Xilinx SDx 2017.1) |
| 1.3.7-1.3.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |

* OpenCL dynamic resource optimization – The developer tools automatically remove unused DDR and debug logic to free up resources and reduce compile times.  [See 2017.4 Migration Document](SDAccel/docs/SDAccel_Migrate_dynamic_DSA.md) and [SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf) 
* Developers can instantiate up to 60 kernels (up from the max 16 2017.1 supported). 
* OpenCL Kernel profiling – During compile time, profiling logic can be automatically inserted to enable generation of kernel profile data.  Profile data can be viewed using the SDx IDE under profile summary report and timeline trace report. [See chapter 6 within the SDAccel Environment Profiling and Optimization Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf)   
* OpenCL Hardware Emulation Debug – GDB-like debug allows developers a view into what is going on inside the kernel during hardware emulation.  Debug capabilities include start/stop at intermediate points and memory inspection.  [See chapter 6 within the SDAccel Environment Profiling and Optimization Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf)
* Post-synthesis and place/route optimization is now supported in OpenCL development environment.  [New XOCC options: reuse_synth and reuse_impl](https://www.xilinx.com/html_docs/xilinx2018_1/sdsoc_doc/wfq1517252127836.html)
* Customer simulation environment improvements and bug fixes:
  * 8 Additional tests that will help developer with using the simulation environment and shell simulation model
  * Simulation model support for non DW aligned accesses
  * Co-simulation support
* EDMA Driver fixes:
  * Prevent timeouts due to scanning of the BARs for DMA hardware
  * Driver compilation support for 4.14 linux kernel
* HDK improvements and fixes: 
  * cl_dram_dma improvements to make enabling/disabling DDRs easier
  * encrypt.tcl now clears out old files
  * URAM example timing improvements
* IPI Improvements:
  * [HLS example](hdk/cl/examples/cl_hls_dds_hlx/README.md) 
  * Script based approach for running the examples

   
## Release 1.3.6 (See [ERRATA](./ERRATA.md) for unsupported features)
  * Simulation model bug fix for transfer size of 64 bytes.
  * Xilinx 2017.1 Patch AR70350 - fixes report_power hangs.  Patch is automatically applied during setup scripts using MYVIVADO environment variable.
  * Updated synthesis scripts with -sv option when calling read_verilog.
  * Added documentation on us-gov-west-1 (GovCloud US).
  * Minor EDMA driver fixes and improvements.

## Release 1.3.5 (See [ERRATA](./ERRATA.md) for unsupported features)
  * [Amazon FPGA Images (AFIs) Tagging](hdk/docs/describe_fpga_images.md) - To help with managing AFIs, you can optionally assign your own metadata to each AFI in the form of tags. Tags are managed using the AWS EC2 CLI commands create-tags, describe-tags and delete-tags.  Tags are custom key/value pairs that can be used to identify or group EC2 resources, including AFIs.  Tags can be used as filters in the describe-fpga-images API to search and filter the AFIs based on the tags you add.
  * [EDMA driver fixes and improvements](sdk/linux_kernel_drivers/edma/README.md), including polled DMA descriptor completion mode which improves performance on smaller IO (<1MB).
  * [AFI Power metrics and warnings](hdk/docs/afi_power.md) – developers can avoid power violations by monitoring metrics that provide recent FPGA power, maximum FPGA power and average FPGA power. CL designs can use power state pins to help developers throttle CL to avoid power violation. 
  * Improved IPI 3rd party simulator support.
  * Simulation model fixes.
  * SDAccel improvements - Removal of settings64 script from SDAccel setup and switching between DSAs.

## Release 1.3.4 (See [ERRATA](./ERRATA.md) for unsupported features)
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
   
## Release 1.3.3 (See [ERRATA](./ERRATA.md) for unsupported features)
  * New FPGA Image APIs for deleting and reading/editing attributes 

## Release 1.3.2 (See [ERRATA](./ERRATA.md) for unsupported features)
  * SDAccel general availability 

## Release 1.3.1 (See [ERRATA](./ERRATA.md) for unsupported features)
  * EDMA Driver release 1.0.29 - MSI-X fixes
  * Improved IPI documentation
  * Documentation updates
  * Build flow fixes
  * Public LTX files for use with hdk examples AFIs 

## Release 1.3.0 (See [ERRATA](./ERRATA.md) for unsupported features)
  * FPGA initiated read/write over PCI (PCI-M)
  * Redesigned Shell - improved the shell design to allow more complex place and route designs to meet timing
  * Expanded DMA support
  * Improved URAM utilization
  * Improved AXI Interface checking
  * New customer examples/workflows:  IP Integrator, VHDL and GUI
  * SDAccel preview is accepting developers - See [README](sdk/SDAccel/README.md) registration  


**During July, All AFIs created with previous HDK versions will no longer correctly load on an F1 instance**, hence a `fpga-load-local-image` command executed with an AFI created prior to 1.3.0 will return an error and not load.  Watch the forum for additional announcements.

## Release 1.3.0 New Features Details

The following major features are included in this HDK release: 

### 1.	New Shell, with modified Shell/CL interface. Changes are covered in: 
* The floorplan has been enhanced to enable more optimal CL designs through better timing closure and reduced congestion at the CL to Shell interface.
* [New Shell Stable: v071417d3](./hdk/common/shell_v071417d3)
* [AWS_Shell_Interface_Specification.md](./hdk/docs/AWS_Shell_Interface_Specification.md) has been updated.  See cl_ports.vh for the updated port list
* DCP for the latest shell v071417d3. AWS Shell DCP is stored in S3 and fetched/verified when `hdk_setup.sh` script is sourced.

### 2.	Integrated DMA 
* DMA functionality has been enhanced to allow DMA transactions of up to 1MB.
* Multi-queue in each direction is now supported
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA ([EDMA](./sdk/linux_kernel_drivers/edma)) driver is provided.
* [EDMA Installation Readme](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidelines
* See [Kernel_Drivers_README](./sdk/linux_kernel_drivers/README.md) for more information on restrictions for this release


### 3.	PCI-M
* The PCI-M interface is fully supported for CL generated transactions to the Shell. 

### 4.	URAM 
* Restrictions on URAM have been updated to enable 100% of the URAM with a CL to be utilized.  See documentation on enabling URAM utilization: [URAM_options](./hdk/docs/URAM_Options.md)

### 5.	Vivado IP Integrator (IPI) and GUI Workflow
* Vivado graphical design canvas and project based flow is now supported.  This flow allows developers to create CL logic as either RTL or complex subsystems based on an IP centric block diagram.  Prior experience in RTL or system block designs is recommended.  The [IP Integrator and GUI Vivado workflow](README.md#ipi) enables a unified graphical environment to guide the developer through the common steps to design, implement, and verify FGPAs.  To get started, start with the [README that will take you through getting started steps and documents on IPI](README.md#ipi)
 
### 6.	Build Flow improvments
* See [Build_Scripts](./hdk/common/shell_v071417d3/build/scripts)

### 7.	VHDL
* CL designs in VHDL are fully supported.  
See example for more details [CL_HELLO_WORLD_VHDL](./hdk/cl/examples/cl_hello_world_vhdl/README.md)

### 8.	AXI Interface Checking
* Protocol checks have been added to the CL-Shell interface to detect and report CL errors for enhanced CL debugging.
* Transaction timeout values on the CL-Shell interface have been increased to allow for longer CL response times.
* See [Shell_Interface_Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)

### 9.	Support for Vivado 2017.1 SDX Build 

* The FPGA Development AMI includes Vivado 2017.1 SDX
    * Get the 1.3.0+ AMI by selecting the version from the [marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ#). 
* Older Vivado versions will not be supported

### 10.	SDK changes 

* Synchronous (default) mode for fpga-load-local-image and fpga-clear-local-image.  For example, in synchronous mode (default) fpga-load-local-image will wait for the AFI to transition to the "loaded" state, perform a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id, and display the final state for the given FPGA slot number.  Asynchronous operation is preserved with the "-A" option to both fpga-load-local-image and fpga-clear-local-image.
* The corresponding fpga_mgmt_load_local_image_sync and fpga_mgmt_clear_local_image_sync are provided by the fpga_mgmt library for use in C/C++ programs.

## Supported Tools and Environment

* The HDK and SDK are designed for **Linux** environment and has not been tested on other platforms
* First installation of AWS FPGA SDK requires having gcc installed in the instance server. If that's not available, try `sudo yum update && sudo yum group install "Development Tools"`
* The HDK build step requires having Xilinx's Vivado tool and Vivado License Management running.  Tools and licenses are provided with AWS FPGA Developer AMI at no additional cost
* This release is tested and validated with Xilinx 2017.1 SDX (Vivado)
* Developers that choose to not use the developer AMI in AWS EC2, need to have Xilinx license 'EF-VIVADO-SDX-VU9P-OP' installed on premises.  For more help, please refer to [On-premise licensing help](./hdk/docs/on_premise_licensing_help.md)
* Vivado XSIM RTL simulator supported by the HDK
* MentorGraphic's Questa RTL simulator supported by the HDK (but requires a purchase of separate license from MentorGraphics)
* Synopsys' VCS RTL simulator supported by the HDK (but requires a purchase of separate license from Synopsys)

## License Requirements

The HDK and SDK in the development kit have different licenses. SDK is licensed under open source Apache license and HDK is licensed under Amazon Software License. Please refer to [HDK License](./hdk/LICENSE.txt) and [SDK License](./sdk/LICENSE.txt).

## Release Notes FAQ
 
**Q: How do I know which HDK version I have on my instance/machine? **

Look for [hdk_version](./hdk/hdk_version.txt) 

**Q: How do I know what my Shell Version is? **

The Shell Version of an instance is available through the FPGA Image Management tools.  See the description of `fpga-describe-local-image` for details on retrieving the shell version from an instance.

**Q: How do I know what version of FPGA Image management tools are running on my instance? **

The FPGA Image management tools version is reported with any command executed to those tools.  See the description of `fpga-describe-local-image` for details on the tools version identification.

**Q: How do I update my design with this release?**

1.	Start by either cloning the entire GitHub structure for the HDK release or downloading new directories that have changed.  AWS recommends an entire GitHub clone to ensure no files are missed
2.	Update the CL design to conform to the new AWS_Shell_Interface_Specification
3.	Follow the process for AFI generation outlined in aws-fpga/hdk/cl/examples/readme.md
4.	Update FPGA Image Management Tools to the version included in aws-fpga/sdk/management

**Q: How do I get support for this release?**

The AWS Forum FPGA Development provides an easy access to Developer support.  The FPGA development user forum is the first place to go to post questions, suggestions and receive important announcements. To gain access to the user forum, please go to https://forums.aws.amazon.com/index.jspa and login. To be notified on important messages, posts you will need to click the “Watch Forum” button on the right side of the screen.

**Q: How do I know which HDK release I am working with? **

See the release notes at the top of the GitHub directory to identify the version of your GitHub clone.  

## Previous release notes

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
   *    EDMA Performance improvments 
   *    Expanded EC2 Instance type support
   *    CL Examples @250Mhz (Clock recipe A1)
   *    Option to exclude Chipscope (Virtual JTAG) from building CL examples (DISABLE_VJTAG_DEBUG)

### Release 1.2.0 Content Overview and New Features Details

The following major features are included in this HDK release: 

#### 1.	New Shell, with modified Shell/CL interface. Changes are covered in: 

* New Shell Stable: 0x04151701: ./hdk/common/shell_v04151701
* cl_ports.vh have the updated port list 
* [AWS_Shell_Interface_Specification.md](./hdk/docs/AWS_Shell_Interface_Specification.md) has been updated
* Updated the xdc timing constrains under [constraints](./hdk/common/shell_v071417d3/build/constraints) to match the new interfaces 
* Updated [CL HELLO WORLD](./hdk/cl/examples/cl_hello_world) example to use the new cl_ports.vh
* DCP for the latest shell v04151701. AWS Shell DCP is stored in S3 and fetched/verified when `hdk_setup.sh` script is sourced.


#### 2.	Integrated DMA in Beta Release. AWS Shell now includes DMA capabilities on behalf of the CL
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA ([EDMA](./sdk/linux_kernel_drivers/edma)) driver is provided.
* [EDMA Installation Readme](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidlines
* The initial release supports a single queue in each direction
* DMA support is in Beta stage with a known issue for DMA READ transactions that cross 4K address boundaries.  See [Kernel_Drivers_README](./sdk/linux_kernel_drivers/README.md) for more information on restrictions for this release


#### 3.	CL  User-defined interrupt events.  The CL can now request sending MSI-X to the instance CPU
* * Usage covered in new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma)
* A corresponding AWS EDMA driver is provided under [/sdk/linux_kernel_drivers/edma](./sdk/linux_kernel_drivers/edma)
* [EDMA Installation](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidlines
* The initial release supports a single user-defined interrupt 

#### 4.	Added a Mandatory Manifest.txt file submitted with each DCP via create-fpga-image API

* File content defined in [AFI Manifest](./hdk/docs/AFI_Manifest.md)
* AFI_Manifest.txt is created automatically if the developer is using the aws_build_dcp_from_cl.sh script
* PCI Vendor ID and Device ID are part of the manifest 
* Shell Version is part of the manifest 
* The Manifest.txt file is required for AFI generation
* All the examples and documentations for build include the description and dependency on the Manifest.txt

	
#### 5.	Decoupling Shell/CL interface clocking from the internal Shell Clock 

* All the Shell/CL interfaces running off clk_main_a0, and no longer required to be 250Mhz. 
* The default frequency using the HDK build flow for `clk_main_a0` is 125Mhz as specified in recipe number A0. Allowing CL designs to have flexible frequency and not be constrained to 250Mhz only. All CL designs must include the recipe number in the manifest.txt file in order to generate an AFI.
* All xdc scripts have been updated to clk_main_a0 and to reference a table with the possible clocks’ frequencies combinations
* Updated CL_HELLO_WORLD and CL_DRAM_DMA examples to use the `clk_main_a0` 

#### 6.	Additional User-defined Auxiliary Clocks
Additional tunable auxiliary clocks are generated by the Shell and fed to the CL. The clocks frequencies are set by choosing a clock recipe per group from a set of predefined frequencies combination in [clock recipes table](./hdk/docs/clock_recipes.csv)

* Clock frequency selection is set during build time, and recorded in the manifest.txt (which should include the clock_recipe_a/b/c parameters)
* Clock frequency programming in the FPGA slot itself occurs when the AFI is loaded. The list of supported frequencies is available [here](./hdk/docs/clock_recipes.csv)
* See [AWS_Shell_Interface_Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for details on the clocking to the CL  
* See [AFI Manifest](./hdk/docs/AFI_Manifest.md) for details on the AFI manifest data
* xdc is automatically updated with the target frequency (WIP)

#### 7.	Additional PCIe BARs and update PCIe Physical Function mapping

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


#### 8.	Expanded AppPF BAR4 space to 128GiB 

* BAR4 addressing space enables a CL to fully map FPGA card DRAM into the AppPF address space.  AppPF BAR4 is now a 128GB BAR  
* [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) covers these changes in detail
* [AWS FPGA PCIe Memory Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md) covers the address map in detail

  
#### 9.	Added wider access on the Shell to CL AXI4 512-bit bus (sh_cl_dma_pcis)

* Wider access provides higher bandwidth DMA and host to FPGA access
* Instance CPU can now burst full 64-byte write burst to AppPF PCIe BAR4 if mapped as Burstable (a.k.a WC: WriteCombine) (WIP)
* pci_poke_burst() and pci_poke64() calls were added to [fpga_pci library](./sdk/userspace/include/fpga_pci.h) to take advantage of this
* CL_DRAM_DMA and CL_HELLO_WORLD examples support for a wider access was added


#### 10.	Support larger than 32-bit access to PCIe space

* Large inbound transaction going to AppPF PCIe BAR4 will be passed onward to the CL  
* Large inbound transactions going to the other BARs will be split by the Shell to multiple 32-bit accesses, and satisfy AXI-L protocol specification.


#### 11.	Enhanced AXI4 error handling and reporting

* Additional error conditions detected on the CL to Shell Interface and reported through fpga-describe-image tool
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details
* FPGA Management Tool [metrics output](./sdk/userspace/fpga_mgmt_tools/README.md) covers the additional error handling details

#### 12.	Expanded AXI ID space throughout the design

* The AXI buses between Shell and CL support an expanded number of AXI ID bits to allow for bits to be added by AXI fabrics  See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


#### 13.	Shell to CL interface metrics.  

* New metrics for monitoring the Shell to CL are available from the AFI Management Tools. 
* See [fpga mgmt tools readme](./sdk/userspace/fpga_mgmt_tools/README.md) for more details


#### 14.	Virtual LED/DIP Switches.  

* Added CL capability to present virtual LEDs and push virtual DIP switches indications to the CL, set and read by FPGA Management Tools and without involving CL logic, providing the developer an environment similar to developing on local boards with LED and DIP switches
* See new commands in [FPGA Image Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for description of the new functionality
* CL_HELLO_WORLD example includes some logic to set LED and adjust according to vDIP
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


#### 15.	Virtual JTAG

* The Shell has the capability for supporting CL integrated Xilinx debug cores like Virtual I/O (VIO) and Integrated Logic Analyzer (ILA) and includes support for local/remote debug by running XVC  
* [Virtual_JTAG_XVC](./hdk/docs/Virtual_JTAG_XVC.md) describes how to use Virtual JTAG from linux shell
* cl_debug_bridge module was added to HDK common directory
* Support for generating .ltx files after `create-fpga-image` was added.  .ltx file is required when running interactive ILA/VIO debug (WIP)
* Build tcl and xdc includes the required changes to enable Virtual JTAG 
* See [CL_DRAM_DMA](./hdk/cl/examples/cl_dram_dma) for examples on using Virtual JTAG and XVC for debug

#### 16.	Examples summary table

* [Example Summary Table](./hdk/cl/examples/cl_examples_list.md) covers which CL capabilities is demonstrated in each example


#### 17.	Updated CL_HELLO_WORLD Example

* Matching the new Shell/CL interface 
* Add support for 32-bit peek/poke via ocl\_ AXI-L bus
* Virtual JTAG support with Xilinx ILA and VIO debug cores 
* Demonstrate the use of Virtual LED and Virtual DIPSwitch
* Runtime software examples, leveraging fpga_pci and fpga_mgmt C-libraries
* Updated PCIe Vendor ID and Device ID
* See [CL HELLO WORLD readme](./hdk/cl/examples/cl_hello_world/README.md) for more details


#### 18.	Added CL_DRAM_DMA Example

* Mapping AppPF PCIe BAR4 to DRAM
* Using DMA to access same DRAM
* Using SystemVerilog Bus constructs to simplify the code
* Demonstrate the use of User interrupts
* Demonstrate the use of bar1\_ AXI-L bus
* Includes Runtime C-code application under [CL_DRAM_DMA software](./hdk/cl/examples/cl_dram_dma/software)
* See [CL_DRAM_DMA README](./hdk/cl/examples/cl_dram_dma/README.md)


#### 19.	Software Programmer View document 

* The [Software Programmer View document](./hdk/docs/Programmer_View.md) is added to explain the various ways a linux user-space application can work with AWS FPGA Slots


#### 20.	Two C-libraries for FPGA PCIe access and for FPGA Management

* The C-libraries are simplifying and adding more protections from developer’s mistakes when writing a runtime C-application
* [Fpga_mgmt.h](./sdk/userspace/include/fpga_mgmt.h) cover the APIs for calling management functions
* [Fpga_pcie.h](./sdk/userspace/include/fpga_pci.h) covers the API for access the various PCI memory spaces of the FPGA
* CL_HELLO_WORLD and CL_DRAM_DMA examples updated to use these libraries.

#### 21.	VHDL support is added

* Included Vivado encryption key file for VHDL
* Added VHDL-specific line in `encrypt.tcl` reference files
* Developer would need to add `read_vhdl` in `create_dcp_from_cl.tcl`

#### 22.	Additional FPGA Management Tools added

*	See [FPGA Management Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for more details

#### 23.	Support for Vivado 2017.1 Build 

* The FPGA Development AMI includes Vivado 2017.1
* Older Vivado versions will not be supported

#### 24.	Embed the HDK version and Shell Version as part of git tree

* [hdk_version.txt](./hdk/hdk_version.txt)
* [shell_version.txt](./hdk/common/shell_v071417d3)

#### 25.	Initial Release of SDAccel and OpenCL Support (NA)

* Updated documentation in /sdk/SDAccel (NA)
* OpenCL runtime HAL for supporting SDAccel and OpenCL ICD in /sdk/userspace (NA)
* SDAccel build post-processing to register SDAccel xcl.bin as AFI. (NA) 

#### 26.	Simplify handling of unused Shell to CL interfaces

* Developers can simply call `include "unused\_**BUS\_NAME**\_template.inc" for every unused interface
* List of potential files to include is available in `$HDK_SHELL_DIR/design/interfaces/unused\*`
* cl_hello_world.sv and cl_dram_dma.sv provide examples (at the each of each file)

#### 27.	Support multiple Vivado versions

* `hdk_setup.sh` compares between the list of Vivado versions supported by the HDK and the installed vivado versions
* `hdk_setup.sh` would automatically choose the Vivado version from the available binaries in AWS FPGA Developer's AMI

#### 28.	Changes in DRAM controller setting to improve bandwidth utilization

* Change address decoding to ROW_COL_INTLV mode
* Enable auto precharge on COL A3
