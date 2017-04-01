
# AWS EC2 FPGA HDK+SDK Release Notes


##  AWS EC2 F1 Platform Features:
   *    1-8 Xilinx UltraScale+ VU9P based FPGA slots
   *    Per FPGA Slot, Interfaces available for Custom Logic(CL):
         *    One x16 PCIe Gen 3 Interface
         *    Four DDR4 RDIMM interfaces (with ECC)
         *    AXI4 protocol support on all interfaces
   *    User-defined clock frequency driving all CL to Shell interfaces
   *	Multiple free running auxilary clocks
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
         *     CL to SH 512-bit AXI4 interface
         *     1 DDR controller implemented in the SH (always available)
         *     3 DDR controllers implemented in the CL (configurable number of implemented controllers allowed)


# Release 1.1.0

## NOTE on Pre-Release Availability
Since F1 announcement at Re:Invent 2016, AWS has been working on the release of the next version of Shell, HDK and SDK.  The upcoming release includes extensive enhancements and capabilities that AWS believes will benefit developers and answers customers’ requests. AWS has put the upcoming version in the prelease GitHub tree for Preview Customers to get ready for the coming changes.

The prelease GitHub tree is providing F1 Preview developers with documentation and tools to start porting their Custom Logic (CL) designs to work with the upcoming HDK release that will include mandatory Shell changes.

Various items of this pre-release are in different maturity stage will marked as WIP (Work-in-progress) or NA (Not avaiable yet) throughout this document.


## Release 1.1.0 Content Overview

This is the first major update release to the AWS EC2 FPGA Development Kit.  Major updates are included for both the HDK and SDK directories.  This is a required update for all Developers running on F1 instances, and prior releases of the FPGA Development Kit will no longer be supported once this release Shell is installed in the F1 fleet. 

**All AFIs created with previous HDK, previous shell or Vivado 2016.3 will no longer correctly load on an F1 instance**, hence a `fpga-load-loca-image` command executed with an AFI created prior to 1.1.0 will return an error and not load.


## Release 1.1.0 New Features Details

The following new features are included in this HDK release: 

### 1.	New Shell, with modified Shell/CL interface. Changes are covered in: 

* [New Shell Stable: 0x032117d7](./hdk/common/shell_v032117d7)
* cl_ports.vh have the updated port list 
* Removed all the `ifdef and `ifndef from the cl_ports.vh
* Added all the interfaces required for SDAccel platform support 
* [AWS_Shell_Interface_Specification.md](./hdk/docs/AWS_Shell_Interface_Specification.md) has been updated
* Updated the xdc timing constrains under [constraints](./hdk/common/shell_v032117d7/build/constraints) to match the new interfaces (WIP)
* Updated [CL HELLO WORLD](./hdk/cl/examples/cl_hello_world) example to use the new cl_ports.vh
* Updated clean_log.pl [scripts](./hdk/common/shell_v032117d7/build/scripts/clean_log.pl) (WIP)
* DCP for the latest shell v032117d7. AWS Shell DCP is now stored in S3 and fetched/verified when `hdk_setup.sh` script is sourced.


### 2.	New Integrated DMA. AWS Shell now includes DMA capabilities on behalf of the CL
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA ([EDMA](./sdk/linux_kernel_drivers/edma)) driver is provided.
* [EDMA Installation Readme](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidlines
* The initial release supports a single queue in each direction
* Renamed sh_cl_pcis to sh_cl_dma_pcis

### 3.	CL  User-defined interrupt events.  The CL can now request sending MSI-X to the instance CPU
* Added new req/ack interface on Shell/CL interface
* Usage covered in new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma): RTL verification/simulation and software (WIP)
* A corresponding AWS EDMA driver is provided under [/sdk/linux_kernel_drivers/edma](./sdk/linux_kernel_drivers/edma)
* [EDMA Installation](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidlines
* The initial release supports a single user-defined interrupt 

### 4.	Added a Mandatory Manifest.txt file submitted with each DCP via create-fpga-image API

* File content defined in [AFI Manifest](./hdk/docs/AFI_Manifest.md)
* AFI_Manifest.txt is created automatically if the developer is using the aws_build_dcp_from_cl.sh script
* PCI Vendor ID and Device ID are now part of the manifest and no longer needed in `create-fpga-image`
* Shell Version is part of the manifest and no longer needed in `create-fpga-image`
* All the examples and documentations for build include the description and dependency on the Manifest.txt
	
### 5.	create-fpga-image `-shell_version` and `--pci*` arguments are obsolete 

* From this version the shell_version, pci_vendor_id, pci_device_id, pci_subsystem_id and pci_subsystem_vendor_id arguments are mandatory parameters in manifest.txt that should be submitted within the tar file

### 6.	Decoupling Shell/CL interface clocking from the internal Shell Clock 

* All the Shell/CL interfaces running off the newly introduced clk_main_a0, and no longer required to be 250Mhz. 
* The default frequency for `clk_main_a0` is 125Mhz. Allowing CL designs to have flexible frequency and not be constrained to 250Mhz only. The default frequency can be overridden by changes in the manifest.txt file
* All xdc scripts have been updated to clk_main_a0 and to reference a table with the possible clocks’ frequencies combinations
* Obsolete the cl_clk interface
* Updated CL_HELLO_WORLD and CL_DRAM_DMA examples to use the `clk_main_a0` 

### 7.	Additional User-defined Auxiliary Clocks
Additional tunable auxiliary clocks are generated by the Shell and fed to the CL. The clocks frequencies are set by choosing a clock recipe per group from a set of predefined frequencies combination in [clock recipes table](./hdk/docs/clock_recipes.cvs)

* Clock frequency selection is set during build time, and recorded in the manifest.txt (which should include the clock_recipe_a/b/c parameters)
* Clock frequency programming in the FPGA slot itself occurs when the AFI is loaded. The list of supported frequencies is available [here](./hdk/docs/clock_recipes.cvs)
* See [AWS_Shell_Interface_Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for details on the clocking to the CL  
* See [AFI Manifest](./hdk/docs/AFI_Manifest.md) for details on the AFI manifest data
* xdc is automatically updated with the target frequency (WIP)

### 8.	Additional PCIe BARs and update PCIe Physical Function mapping

** The AppPF now has 4 different PCIe BARs:**

* BAR0 and BAR1 have been expanded to support 32-bit access for different memory ranges of the CL through separate AXI-L interfaces 
* BAR2 is used exclusively for the DMA inside the Shell and MSI-X interrupt tables  
* BAR4 expanded to 128GiB to cover all external DRAM memory space


** ManagementPF added additional PCIe BARs:**

* BAR2 is used for Virtual JTAG
* BAR4 is used for SDAccel management 
* [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) covers these changes in detail
* [AWS FPGA PCIe Memory Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md) covers the address map details
* The [FPGA PCI library](./sdk/userspace/include/fpga_pci.h) provides simple APIs to take advantage of these BARs


** MgmtPF and AppPF are now represented as different PCIe devices in F1 instances:**
* Each FPGA Slot will now occupy two PCIe buses, one for AppPF and one for MgmtPF
* No change is required on the developer's side as long as the developer is using `fpga-image-tools` linux shell commands and/or `fpgamgmt.lib` C-APIs.


### 9.	Expanded AppPF BAR4 space to 128GiB 

* BAR4 has expanded addressing space to enable a CL to fully map FPGA card DRAM into the AppPF address space.  AppPF BAR4 is now a 128GB BAR  
* [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) covers these changes in detail
* [AWS FPGA PCIe Memory Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md) covers the address map in detail

  
### 10.	Added wider access on the Shell to CL AXI4 512-bit bus (sh_cl_dma_pcis)

* Wider access provides higher bandwidth DMA and host to FPGA access
* Instance CPU can now burst full 64-byte write burst to AppPF PCIe BAR4 if mapped as Burstable (a.k.a WC: WriteCombine) (WIP)
* pci_poke_burst() and pci_poke64() calls were added to [fpga_pci library](./sdk/userspace/include/fpga_pci.h) to take advantage of this
* CL_DRAM_DMA and CL_HELLO_WORLD examples support for a wider access was added


### 11.	Support larger than 32-bit access to PCIe space

* Large inbound transaction going to AppPF PCIe BAR4 will be passed onward to the CL  
* Large inbound transactions going to the other BARs will be split by the Shell to multiple 32-bit accesses, and satisfy AXI-L protocol specification.


### 12.	Enhanced AXI4 error handling and reporting

* Additional error conditions detected on the CL to Shell Interface and reported through fpga-describe-image tool
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details
* FPGA Management Tool [metrics output](./sdk/userspace/fpga_mgmt_tools/README.md) covers the additional error handling details

### 13.	Expanded AXI ID space throughout the design

* The AXI buses between Shell and CL support an expanded number of AXI ID bits to allow for bits to be added by AXI fabrics  See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


### 14.	Shell to CL interface metrics.  

* New metrics for monitoring the Shell to CL are available from the AFI Management Tools. 
* See [fpga mgmt tools readme](./sdk/userspace/fpga_mgmt_tools/README.md) for more details


### 15.	Virtual LED/DIP Switches.  

* Added CL capability to present virtual LEDs and push virtual DIP switches indications to the CL, set and read by FPGA Management Tools and without involving CL logic, providing the developer an environment similar to developing on local boards with LED and DIP switches
* See new commands in [FPGA Image Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for description of the new functionality
* CL_HELLO_WORLD example includes some logic to set LED and adjust according to vDIP
* See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details


### 16.	Virtual JTAG

* The Shell has the capability for supporting CL integrated Xilinx debug cores like Virtual I/O (VIO) and Integrated Logic Analyzer (ILA) and includes support for local/remote debug by running XVC  
* [Virtual_JTAG_XVC](./hdk/docs/Virtual_JTAG_XVC.md) describes how to use Virtual JTAG from linux shell
* cl_debug_bridge module was added to HDK common directory
* Support for generating .ltx files after `create-fpga-image` was added.  .ltx file is required when running interactive ILA/VIO debug (WIP)
* Build tcl and xdc includes the required changes to enable Virtual JTAG 
* See [CL_DRAM_DMA](./hdk/cl/examples/cl_dram_dma) for examples on using Virtual JTAG and XVC for debug

### 17.	Examples summary table

* [Example Summary Table](./hdk/cl/examples/cl_examples_list.md) covers which CL capabilities is demonstrated in each example


### 18.	Updated CL_HELLO_WORLD Example

* Matching the new Shell/CL interface 
* Add support for 32-bit peek/poke via ocl\_ AXI-L bus
* Adding Virtual JTAG support with Xilinx ILA and VIO debug cores (WIP)
* Demonstrate the use of Virtual LED and Virtual DIPSwitch
* Runtime software examples, leveraging fpga_pci and fpga_mgmt C-libraries
* Updated PCIe Vendor ID and Device ID
* See [CL HELLO WORLD readme](./hdk/cl/examples/cl_hello_world/README.md) for more details


### 19.	Added CL_DRAM_DMA Example

* Mapping AppPF PCIe BAR4 to DRAM
* Using DMA to access same DRAM
* Using SystemVerilog Bus constructs to simplify the code
* Demonstrate the use of User interrupts
* Demonstrate the use of bar1\_ AXI-L bus
* Includes Runtime C-code application under [CL_DRAM_DMA software](./hdk/cl/examples/cl_dram_dma/software) (WIP)
* See [CL_DRAM_DMA README](./hdk/cl/examples/cl_dram_dma/README.md)


### 20.	Removed the CL_SIMPLE example

* Moved the main functionality to CL_DRAM_DMA and removed the mapping AppPF PCIe BAR4 to DRAM

### 21.	Software Programmer View document 

* The [Software Programmer View document](./hdk/docs/Programmer_View.md) is added to explain the various ways a linux user-space application can work with AWS FPGA Slots


### 22.	Two C-libraries for FPGA PCIe access and for FPGA Management

* The C-libraries are simplifying and adding more protections from developer’s mistakes when writing a runtime C-application
* [Fpga_mgmt.h](./sdk/userspace/include/fpga_mgmt.h) cover the APIs for calling management functions
* [Fpga_pcie.h](./sdk/userspace/include/fpga_pci.h) covers the API for access the various PCI memory spaces of the FPGA
* CL_HELLO_WORLD and CL_DRAM_DMA examples updated to use these libraries.

### 23.	VHDL support is added

* Included Vivado encryption key file for VHDL
* Added VHDL-specific line in `encrypt.tcl` reference files
* Developer would need to add `read_vhdl` in `create_dcp_from_cl.tcl`

### 24.	Additional FPGA Management Tools added

*	See [FPGA Management Tools](./sdk/userspace/fpga_mgmt_tools/README.md) for more details

### 25.	Upgrade to Vivado 2016.04-SDx Build 

* The FPGA Development AMI includes Vivado 2016.4-SDx
* Older Vivado versions will not be supported

### 26.	Embed the HDK version and Shell Version as part of git tree

* [hdk_version.txt](./hdk/hdk_version.txt)
* [shell_version.txt](./hdk/common/shell_stable/shell_version.txt)

### 27.	Initial Release of SDAccel and OpenCL Support (NA)

* Updated documentation in /sdk/SDAccel (NA)
* OpenCL runtime HAL for supporting SDAccel and OpenCL ICD in /sdk/userspace (NA)
* SDAccel build post-processing to register SDAccel xcl.bin as AFI. (NA) 

### 28.	Updates the `/hdk/common` Directory structures

* To identify the `shell_stable` and `shell_next` directories for stable and work-in-progress shells respectively

### 29.	Simplify `create_dcp_from_cl.tcl` and `encrypt.tcl` scripts

* Reduced script complexity by consolidating CL design files list into one script.
* The list of CL design source files would only need to be updated in `encrypt.tcl` script
* Removed pr_verify stage from `create_dcp_from_cl.tcl`.  PR (Partial Reconfiguration) verification is optional and customers

### 30.	Simplify handling of unused Shell to CL interfaces

* Developers can simply call `include "unused\_**BUS\_NAME**\_template.inc" for every unused interface
* List of potential files to include is available in `$HDK_SHELL_DIR/design/interfaces/unused\*`
* cl_hello_world.sv and cl_dram_dma.sv provide examples (at the each of each file)

### 31.	Support multiple Vivado versions

* `hdk_setup.sh` compares between the list of Vivado versions supported by the HDK and the installed vivado versions
* `hdk_setup.sh` would automatically choose the Vivado version from the available binaries in AWS FPGA Developer's AMI

### 32.	Changes in DRAM controller setting to improve bandwidth utilization

* Change address decoding to ROW_COL_INTLV mode
* Enable auto precharge on COL A3


## Bug Fixes with this release
This release fixes (HDK 1.1.0, Shell 0x032117d7) fixes the following issues in previous HDK and Shell:

* Unaligned 32-bit addressed accesses cause instance crash
   o Shell version 0X11241611 would cause an instance crash with unaligned 32-bit addresses.  This bug is fixed in the current release.  No address restrictions exit
* Application accesses to the CL prior to loading an AFI cause instance crash
   o Shell version 0X11241611 would cause an instance crash when an application accesses memory space in the Application PF mapped to the CL prior to an AFI successfully loading.  This bug is fixed in the current release.  
* 64-bit data accesses cause instance crash
   o Shell version 0X11241611 would cause an instance crash when 64-bit data accesses were attempted.  This bug is fixed in the current release.  No data size restrictions exist


## Implementation Restrictions

*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
    *    All PCIe transactions must adhere to the PCIe Exress base spec
    *    4Kbyte Address boundary for all transactions(PCIe restriction)
    *    Multiple outstanding outbound PCIe Read transactions with same ID not supported
    *    PCIE extended tag not supported, so read-request is limited to 32 outstanding
    *    Address must match DoubleWord(DW) address of the transaction
    *    WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
    *    Only Increment burst type is supported
    *    AXI lock, memory type, protection type, Quality of service and Region identifier are not supported

## Unsupported Features (Planned for future releases)

* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over the 400Gbps Ring for F1.16xl
* Aurora and Reliabile Aurora modules for the FPGA-to-FPGA 
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence RTL simulations tools
* All AXI-4 interfaces (PCIM, DDR4) do not support AxSIZE other than 0b110 (64B)

## Known Bugs/Issues

* The Shell does not meet timing.  There are two failing paths, the worst case fails by 24ps.

## Supported Tools and Environment

* The HDK and SDK are designed for **Linux** environment and has not been tested on other platforms
* First install of AWS FPGA SDK requires having gcc installed in the instance server. If that's not available, try `sudo yum update && sudo yum group install "Development Tools"`
* The HDK build step requires having Xilinx's Vivado tool and Vivado License Management running.  Tools and licenses are provided with AWS FPGA Developer AMI at no additional cost
* Vivado License needs to support VU9p ES2 FPGA
* Vivado License needs to support encryption
* This release is tested and validated with Xilinx 2016.4 SDx Vivado
* Developers that choose to not use the developer AMI in AWS EC2, need to have Xilinx license 'EF-VIVADO-SDX-VU9P-OP' installed on premise.  For more help, please refer to [On-premise licensing help](./hdk/on_premise_licensing_help.md)
* Vivado XSIM RTL simulator supported by the HDK
* MentorGraphic's Questa RTL simulator supported by the HDK (but requires a purchase of separate license from MentorGraphics)
* Synopsys' VCS RTL simulator supported by the HDK (but requires a purchase of separate license from Synopsys)

## License Requirements

The HDK and SDK in the development kit have different licenses. SDK is licensed under open source Apache license and HDK is licensed under Amazon Software License. Please refer to [HDK License](./hdk/LICENSE.txt) and [SDK License](./sdk/LICENSE.txt).


## What's New

### 2016/12/06 
   * Add support for configurable number of DDR controllers in the CL (see ![AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md))
### 2017/01/26
   * Add support for `create-fpga-image` AFI generation AWS API. For more details please read the forum announcement [here](https://forums.aws.amazon.com/forum.jspa?forumID=243&start=0).

### 2017/03/03
   * Major update to content reflecting upcoming HDK/SDK 1.1.0 release and new shell

## Release Notes FAQ

**Q: Is this a required update?**

Yes.  This update is required for all F1 instances. 
 
**Q: How do I know which HDK version I have on my instance/machine? **

Look for [hdk_version](./hdk/hdk_version.txt) 

**Q: How do I know what my Shell Version is? **

The Shell Version of an instance is available through the FPGA Image Management tools.  See the description of `fpga-describe-local-image` for details on retrieving the shell version from an instance.

**Q: How do I know what version of FPGA Image management tools are running on my instance? **

The FPGA Image management tools version is reported with any command executed to those tools.  See the description of `fpga-describe-local-image` for details on the tools version identification.

**Q: When do I need to repeat the AFI ingestion process for my CL design?**

A new AFI ingestion will be needed after instances have been updated with the new AWS Shell.  A notification will be sent prior to an instance terminating for update.  Developers are encouraged to start the build of CLs with the new HDK version prior to an instance update for the new Shell.  New AFI IDs will be created for the CL design built with this Shell version.

**Q: Can I use my existing AFI with the new HDK release?**

No.  Existing AFIs will not load with the new Shell.  

**Q: How do I update my design with this release?**

1.	Start by either cloning the entire GitHub structure for the HDK release or downloading new directories that have changed.  AWS recommends an entire GitHub clone to ensure no files are missed
2.	Update the CL design to conform to the new AWS_Shell_Interface_Specification
3.	Follow the process for AFI generation outlined in aws-fpga/hdk/cl/examples/readme.md
4.	Update FPGA Image Management Tools to the version included in aws-fpga/sdk/management

**Q: How do I get support for this release?**

The AWS Forum FPGA Development provides an easy access to Developer support.  The FPGA development user forum is the first place to go to post questions, suggestions and receive important announcements. To gain access to the user forum, please go to https://forums.aws.amazon.com/index.jspa and login. During the preview, the first time you login, click on "Your Stuff" where you will see your forums username and userID at the end of the URL. Please email these to f1-preview@amazon.com with "FPGA forum access" in the subject line, in order to receive forum access. To be notified on important messages, posts you will need to click the “Watch Forum” button on the right side of the screen.

**Q: Will I need to restart my instance? **

No.  Your instance will be terminated as part of the update, we will coordinate this termination by issuing a warning email 1-day before the upgrade and a follow-on reminder email 2-hours before the upgrade. You need to make sure all your data is backed up before the upgrade. 

**Q: Will there be mixed instances in the fleet with Shell 1.0.0 and 1.1.0?   **

No.  Once you have received notification of your instance termination, you will need to migrate to version 1.1.0.  After your instance is terminated, new instances will be launched with version 1.1.0

**Q: How do I know which HDK release I am working with? **

See the release notes at the top of the GitHub directory to identify the version of your GitHub clone.  

