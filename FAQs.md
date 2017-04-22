# Frequently Asked Questions

* [General](#general)
* [Getting Started](#getting-started)
* [Marketplace](#marketplace)
* [F1 Instance and Tools](#instance)
* [Development Languages](#languages)
* [FPGA Specific](#fpga)
* [General AWS FPGA Shell](#shell)
* [Troubleshooting](#troubleshooting)

## General

**What is included in the HDK?**

The HDK includes the following major components::

1. Documentation for the Shell interface and other Custom Logic implementation guidelines, the Shell code needed for Custom Logic development, simulation models for the Shell, software for exercising.

2. Custom Logic examples, a getting started guide for building your own Custom Logic, and examples for starting a Custom Logic Design.

3. Scripts for building and submitting Amazon FPGA Image (AFI) from a Custom Logic.

4. Reference software drivers to be used in conjunction with the Custom Logic examples.
5. RTL Simulation models and RTL simulation.

**What is in the AWS Shell?**

The AWS Shell is a piece of code provided and managed by AWS, that implements the non-differentiated development heavy lifting tasks like setting up the PCIe interface, FPGA image infrastructure, security and operational isolation, metrics and debug hooks.

Every FPGA deployed in AWS cloud includes an AWS shell, and the developer Custom Logic (CL) interfaces with the available AWS Shell interfaces.

The AWS shell includes the PCIe interface for the FPGA, and necessary FPGA management functionality.  One of the four DRAM interface controllers is included in the Shell, while the three other DRAM interface controllers is expected to be instantiated in the CL code (A design choice that was made to achieve optimal utilization of FPGA resources from placement perspective)

**What is an AFI?**

An AFI stands for Amazon FPGA Image. It is the compiled FPGA code that is loaded into an FPGA in AWS for performing the Custom Logic (CL) function created by the developer. AFIs are maintained by AWS according to the AWS account that created them. An AFI ID is used to reference a particular AFI from an F1 instance.

The developer can create multiple AFIs at no extra cost, up to a defined limited (typically 100 AFIs per AWS account). An AFI can be loaded into as many FPGAs as needed.

**What is the process for creating an AFI?**

The AFI process starts by creating Custom Logic (CL) code that conforms to the [Shell Specification]((./hdk/docs/AWS_Shell_Interface_Specification.md). Then, the CL must be compiled using the HDK scripts which leverages Vivado tools to create a Design Checkpoint (DCP). That DCP is submitted to AWS for generating an AFI using the `aws ec2 create-fpga-image` API.

**Can I bring my own bitstream for loading on an F1 FPGA?**

No. There is no mechanism for loading a bitstream directly onto the FPGAs of an F1 instance. All Custom Logic bitstreams are loaded onto the FPGA by the `aws ec2 fpga-local-load-image` API. Developers create an AFI by creating a Vivado Design Checkpoint (DCP) and submitting that DCP to AWS using `aws ec2 create-fpga-image` API. AWS creates the final AFI and bitstream from that DCP and returns an AFI ID for referencing that AFI.

**Can I generate my bitstream on my own desktop/server (not on AWS cloud)?**

Yes, on-premises tools can be used to develop the Design Checkpoint needed for creating an AFI. The developer needs to download HDK can be downloaded from GitHub and run on any local machine.

If a developer uses local tools and license, please check the [supported versions of Vivado](./hdk/supported_vivado_versions.txt) for the exact Xilinx Vivado tool version supported by the HDK.  Developers have access to Xilinx Vivado running in the AWS by using the [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ)

**Do I need to get a Xilinx license to generate an AFI?**

If the developer uses the [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ), Xilinx licenses for simulation, encryption, SDAccel and Design Checkpoint generation are included.

If the developer want to run using other methods or on a local machine, the developer is responsible for obtaining any necessary licenses.
Developers that choose to not use the developer AMI in AWS EC2, need to have Xilinx license 'EF-VIVADO-SDX-VU9P-OP' installed on premise.  For more help, please refer to [On-premise licensing help](./hdk/docs/on_premise_licensing_help.md)

**Does AWS provide actual FPGA boards for on-premises development?**

No. AWS supports a cloud-only development model and provides the necessary elements for doing 100% cloud development including Virtual JTAG (Vivado ChipScope), Virtual LEDs and Virtual DIP-switch. No development board is provided for on-premises development.

**Do I need to design for a specific power envelope?**

Yes, the design scripts provided in the HDK include checks for power consumption that exceeds the allocated power for the Custom Logic (CL) region. Developers do not need to include design considerations for DRAM, Shell, or Thermal. AWS includes the design considerations for
those as part of providing the power envelop for the CL region.

**What IP blocks are provided in the HDK?**

The HDK includes IP for the Shell and DRAM interface controllers. Inside the Shell there is a PCIe interface, DMA Engine, and one DRAM interface controller. These blocks are only accessible via the AXI interfaces defined by the Shell-Custom Logic interface. The HDK provides additional IP blocks for the other DRAM interfaces, enabling up to 3 additional DRAM interfaces instantiated by the developer in the Custom Logic region.

*Note that future versions of the HDK will include IP for the FPGA Link interface.*

**Can I use other IP blocks from Xilinx or other 3rd parties?**

Yes. Developers are free to use any IP blocks within the Custom Logic region. Those can be 3rd party IP or IP available in the Vivado IP catalog.

*Note that AWS supports only the IP blocks contained in the HDK.*

## Getting Started

**What do I need to get started on building accelerators for FPGA instances?**

Getting started requires downloading the latest HDK and SDK from the AWS FPGA GitHub repository. The HDK and SDK provide the needed code and information for building FPGA code. The HDK provides all the information needed for developing an FPGA image from source code, while the SDK provides all the runtime software for managing the Amazon FPGA Image (AFI) loaded into the F1 instance FPGA.

Typically, FPGA development process requires a simulator to perform functional test on the source code, and a Vivado tool set for synthesis of source code into compiled FPGA code. The FPGA Developer AMI provided by AWS includes the complete Xilinx Vivado tools for simulation (XSIM) and synthesis of FPGA.

**How do I develop accelerator code for an FPGA in an F1 instance?**

Start with the [Shell interface specification](./hdk/docs/AWS_Shell_Interface_Specification.md). This document describes the interface between Custom Logic and the AWS Shell. All Custom Logic for an accelerator resides within the Custom Logic region of the F1 FPGA.

The [HDK README](./hdk/README.md) walks the developer through the steps to build an FPGA image from one of the provided examples as well starting a new code

**Are there examples for getting started on accelerators?**

Yes, examples are in the [examples directory](./hdk/cl/examples):

The [cl_hello_world example](./hdk/cl/examples/cl_hello_world) is an RTL/Verilog simple example to build and test the Custom Logic development process, it does not use any of the external interfaces of the FPGA except the PCIe to "peek" and "poke" registers in the memory space of the CL inside the FPGA.

The [cl_dram_dma example](.hdk/cl/examples/cl_dram_dma) provides expanded features that demonstrates the use and connectivity for many of the Shell/CL interfaces and functionality.

**How do I get access to AWS FPGA Developer AMI?**

[FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ)

**Where do I go for support?**

We encourage you to use the [AWS FPGA Developer Forum](https://forums.aws.amazon.com/forum.jspa?forumID=243) to post questions, suggestions and receive important announcements. To be notified on important messages, posts you will need to click the “Watch Forum" button on the right side of the screen.

**Is there any software I need on my F1 instance that will use the AFI?**

The required AWS software is the [FPGA Management Tool set](./sdk/userspace/fpga_mgmt_tools). This software manages loading and clearing AFIs for FPGAs in the instance. It also allows developers to retrieve status on the FPGAs from within the instance. Users will want to load to F1 AMI the drivers and runtime libraries needed for their application.

Typically, you will not need the HDK nor any Xilinx Vivado tools on an F1 instance that is using prebuilt AFIs; unless, you want to do in-field debug using Vivado's ChipScope.

## Marketplace
**What does publishing my AFI/AMI to AWS Marketplace enables?**

Developers can sell their AFI/AMI combination through the AWS Marketplace to other AWS users. Once in Marketplace, customers can launch an F1 instance with that AFI/AMI combination directly from the marketplace with the 1-click deployment feature. Sellers can take advantage of the Management Portal to better build and analyze their business, using it to drive marketing activities and customer adoption. The metering, billing, collections, and disbursement of payments are managed by AWS, allowing you to focus on marketing and selling your solution. Please check out [AWS Marketplace](https://aws.amazon.com/marketplace/management/tour/) for more details on how to become a seller, how to set price and collect metrics.

**How can I publish my AFI to AWS Marketplace?**

First, you should create an AMI that includes the drivers and runtime libraries needed to use the AFI. Then, follow the standard flow for publish AMI on AWS marketplace, providing your AFI IDs.

In other words, AFIs are not published directly on AWS marketplace, rather AFI(s) should be associated with an AMI that gets published.

**Do AWS Marketplace customers see FPGA source code or a bitstream?**

Neither: AWS Marketplace customers that pick up an AMI with one our more AFIs associated with it will not see any source code nor bitstream. Marketplace customers actually have permission to use the AFI but not permission to see its code. The only reference to the AFI is through its unique AFI ID. The AMI would call `fpga-local-load-image` with the correct AFI ID for that Marketplace offering, which will result in **AWS loading the AFI into the FPGA** in sideband and without sending the AFI code through the customer's instance. No FPGA internal design code is exposed.

## Instance

**What OS can run on the F1 instance?**

Amazon Linux 2016.09 and CentOS 7.3 are supported and tested on AWS EC2 F1 instance. Developers can utilize the source code in the SDK directory to compile other variants of Linux for use on F1. Windows is not supported on F1.

**What support exists for host DMA?**

There are two mechanisms for host DMA between the instance CPU and the FPGA:

The first is the Xilinx XDMA engine. This engine is included in the AWS Shell and programmed through address space in a Physical Function directly mapped to the instance. There are dedicated AXI interfaces for data movement between the Custom Logic (CL) and the XDMA in the Shell.

The second is the capability for developers to create their own DMA engine in the CL region. Developers can create any DMA structure using the CL to Shell AXI master interface. Interrupt support is through MSI-X.

**What are the interfaces between the host CPU and the FPGAs?**

There are two types of interface from the host (instance) CPU to the FPGA:

The first is the FPGA Image Management Tools. These APIs are detailed in the [SDK portion](./sdk/userspace/fpga_mgmt_tools) of the GitHub repository. FPGA Image Management Tools include APIs to load, clear, and get status of the FPGA.

The second type of interface is direct address access to the Application PCIe Physical Functions (PF) of the FPGA. There is no API for this access. Rather, there is direct access to resources in the Custom Logic (CL) region or Shell that can be accessed by software written on the instance. For example, the ChipScope software uses address space in a PF to provide FPGA debug support. Developers can create any API to the resources in their CL. See the [Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details on the address space mapping as seen from the instance.

**Can I integrate the FPGA Image Management Tools in my application?**

Yes, In addition to providing the [FPGA Management Tools](./sdk/userspace/fpga_mgmt_tools) as linux shell commands, the [SDK Userspace](./sdk/userspace) directory includes files in the `include` and `hal` to integrate the FPGA Management Tools into the developer's application(a) and  avoid calling linux shell commands.

**Is the FPGA address space exposed to the instance Linux kernel or userspace?**

Both. The FPGA PCIe memory address space can be mmap() to both kernel and userspace, with userspace being the recommended option for fault isolation.

**How do I change what AFI is loaded in an FPGA?**

Changing the AFI loaded in an FPGA is done using the `fpga-clear-local-image` and `fpga-load-local-image` APIs from the [FPGA Image Management tools](./sdk/userspace/fpga_mgmt_tools). Note that to ensure your AFI is loaded to a consistent state, a loaded FPGA slot must be cleared with `fpga-clear-local-image` before loading another FPGA image.  The `fpga-load-local-image` command takes the AFI ID and requests it to be programmed into the identified FPGA. The AWS infrastructure manages the actual FPGA image and programming of the FPGA using Partial Reconfiguration capabilities of Xilinx FPGA. The AFI image is not stored in the F1 instance nor AMI. The AFI image can’t be read or modified by the instance as there isn't a direct access to programming the FPGA from the instance. A users may call `fpga-load-local-image` at any time during the life of an instance, and may call `fpga-load-local-image` any number of times.

**I can not see the new AFI after `fpga-load-local-image` call returned ?**

The `fpga-load-local-image` call will initiate the loading of the AFI, however a successful return of `fpga-load-local-image` is just an indication that the loading process has started. The developer should poll on the status of the AFI via `fpga-describe-local-image` until the status would show **`loaded`**.

**What will happen to FPGA state after my instance stops/terminates/crashes?**

Yes. The AWS infrastructure scrubs FPGA state on termination of an F1 instance and any reuse of the FPGA hardware. Scrubbing includes both
FPGA internal state and the contents of DRAM attached to the FPGA. Additionally, users can call the `fpga-clear-local-image` command from the FPGA Image Management tools to force a clear of FPGA and DRAM contents while the instance is running.

**How do the FPGAs connect to the x86 CPU?**

Each FPGA in F1 is connected to the instance CPU via a x16 PCIe Gen3 interface. Physical Functions (PF) within the FPGA are directly mapped into the F1 instance. Software on the instance can directly access the address in the PF to take advantage of the high performance PCIe interface.

**Can the FPGAs on F1 directly access Amazon’s network?**

No. The FPGAs do not have direct access to the network. The FPGAs communicate via PCIe to the instance CPU, where the ENA drivers are run. ENA provides a high-performance, low-latency virtualized network interface suitable for data movement to the F1 instance. See the AWS ENA driver documentation for more details.

The developer can take advantage of a userspace polling-mode driver framework like DPDK, to implement fast and low latency copy between network and FPGA, with the data most probably stored in the x86 LastLevelCache (LLC).

**Can the FPGAs on F1 directly access the SSDs in the instance?**

No. The FPGAs do not have direct access to the SSDs on F1. The SSDs on F1 are high-performance, NVMe SSD devices. The developer can take advantage of a userspace polling-mode driver framework like SPDK, to implement fast and low latency copy between the NVMe SSD and the FPGA, with the data most probably stored in the x86 LastLevelCache (LLC).

## Languages

**Which HDL languages are supported?**

For RTL level development: Verilog and VHDL are both supported in the FPGA Developer AMI and in generating a Design Checkpoint. The Xilinx Vivado tools and simulator support mixed mode simulation of Verilog and VHDL. The AWS Shell is written in Verilog. Support for mixed mode simulation may vary if developers use other simulators. Check your simulator documentation for Verilog/VHDL/System Verilog support.

**Is OpenCL and/or SDAccel Supported?**

Yes. OpenCL is supported through either the Xilinx SDAccel environment or any OpenCL tool capable of generating RTL supported by the Xilinx Vivado synthesis tool. There is a branch in the AWS SDK tree for SDAccel.

**Can I use High Level Synthesis(HLS) Tools to generate an AFI?**

Yes. Vivado HLS and SDAccel are directly supported through the FPGA Developer AMI. Any other HLS tool that generates compatible Verilog or VHDL for Vivado input can also be used for writing in HLS.

**What RTL simulators are supported?**

The FPGA Developer AMI has built-in support for the Xilinx XSIM simulator. All licensing and software for XSIM is included in the
FPGA Developer AMI when launched.

Support for other simulators is included through the bring-your-own license in the
FPGA Developer AMI. AWS tests the HDK with Synopsys VCS, Mentor Questa/ModelSim, and Cadence Incisive. Licenses for these simulators must be acquired by the developer and not available with AWS FPGA Developer AMI.

## FPGA

**What FPGA is used in AWS EC2 F1 instance?**

The FPGA for F1 is the Xilinx Ultrascale+ VU9P device with the -2 speed grade. The HDK scripts have the compile scripts needed for the VU9P device.

**What is FPGA Direct and how fast is it?**

FPGA Direct is FPGA to FPGA low latency high throughput peer communication through the PCIe links on each FPGA, where all FPGAs shared the same memory space. The PCIe BAR space in the Application PF (see [Shell Interface specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details) allows the developer to map regions of the Custom Logic (such as external DRAM space) to other FPGAs. The implementation of communication protocol and data transfer engine across the PCIe interface using FPGA direct is left to the developer.

**What is FPGA Link and how fast is it?**

FPGA Link is based on 4x 100Gbps links on each FPGA card. The FPGA Link is organized as a ring, with 2x 100Gbps links to each adjacent card. This enables each FPGA card to send/receive data from an adjacent card at 200Gbps. Details on the FPGA Link interface will be provided in the Shell Interface specification when available.

**What protocol is used for FPGA link?**

There is no transport protocol for the FPGA link. It is a generic raw streaming interface. Details on the Shell Interface to the FPGA Link IP blocks are provided in the [Shell Interface specification](./hdk/docs/AWS_Shell_Interface_Specification.md) when available.

It is expected that developers would take advantage of standard PCIe protocol, Ethernet protocol, or Xilinx's (reliable) Aurora protocol layer on this interface.

**What clock speed does the FPGA utilize?**

The FPGA provides a 250MHz clock from the Shell to the Custom Logic (CL) region. All the AXI interfaces between Shell and CL are synchronous to that clock (with exception of DDR_C interface). Developers can create an asynchronous interface to the AXI buses and run their CL region at any clock frequency needed. Clocks can be created in the CL region using the Xilinx clock generation modules. See the [Shell Interface specification](./hdk/docs/AWS_Shell_Interface_Specification.md) for more details.

**What memory is attached to the FPGA?**

Each FPGA on F1 has 4x DDR4-2133 interfaces, each at 72bits wide (64bit data). Each DRAM interface has 16GiB of RDRAM attached. This yields 64GiB of total DRAM memory local to each FPGA on F1.

**What FPGA debug capabilities are supported?**

There are four debug capabilities supported in F1 for FPGA debug:

* The first is the Virtual JTAG included in the AWS Shell. It provides equivalent function to JTAG debugger with exception that it's an emulated JTAG-over-PCIe.  Based on Xilinx's ChipScope circuit is pre-integrated with AWS Shell and available to the instance over memory-mapped PCIe space. The driver is included with the F1 SDK.
* The second is the usage metrics available through the FPGA Image Management tools. The `fpga-describe-local-image` command allows the F1 instance to query metrics from the Shell and Shell to Custom Logic (CL) interface. See Shell Interface specification and FPGA Image Management tools for more information on supported metrics.
* Virtual LEDs. An emulated LEDs that represents the status of 16 different LEDs (On/Off). The LED status is read through the PCIe management Physical Function (PF).
* Virtual DIP Switch. An emulated DIP Switch represents a generic 16 binary DIP switch that is passed to the CL.

Refer to [Virtual JTAG readme](./hdk/docs/Virtual_JTAG_XVC.md) for more details.


## Shell

**Do I need to interface to the AWS Shell?**

Yes. The only way to interface to PCIe and the instance CPU is using the AWS Shell. The AWS Shell is included with all F1 FPGAs. There is no option to run the F1 FPGA without a Shell. The Shell takes care of the non-differentiating heavy lifting tasks like PCIe tuning, FPGA I/O assignment, power, thermal management, and runtime health monitoring.

**Is a simulation model of the AWS Shell available?**

Yes. The HDK includes a simulation model for the AWS shell. See the [HDK common tree](./hdk/common/verif) for more information on the Shell simulation model.

**What resources within the FPGA does the AWS Shell consume?**

The Shell consumes about 20% of the FPGA resources, and that includes the PCIe Gen3 X16, DMA engine, DRAM controller interface, ChipScope and other health monitoring and image loading logic. No modifications to the Shell or the partition pins between the Shell and the Custom Logic are possible by the developer.

## Troubleshooting

**Why do I see error `vivado not found` while running `hdk_setup.sh`?**

This is an indication that Xilinx Vivado tool set are not installed. Try installing the tool if you are working on your own environment, or alternative use AWS FPGA Development AMI available on AWS Marketplace, which comes with pre-installed Vivado toolset and license.

**Why did my example job run and die without generating a DCP file?**

The error message below indicates that you ran out of memory.  Restart your instance
with a different instance type that has 32GiB or more.

```
Finished applying 'set_property' XDC Constraints : Time (s): cpu = 00:06:26 ;
elapsed = 00:08:59 . Memory (MB): peak = 4032.184 ; gain = 3031.297 ; free physical = 1285 ; free virtual = 1957
/opt/Xilinx/Vivado/2016.3/bin/loader: line 164:  8160 Killed                  "$RDI_PROG" "$@"
Parent process (pid 8160) has died. This helper process will now exit
```
