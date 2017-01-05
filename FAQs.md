#AWS FPGA - Frequently Asked Questions

**Q: What do I need to get started on building accelerators for FPGA
instances?*

Getting started requires downloading the latest HDK and SDK from the AWS FPGA GitHub repository. The HDK and SDK provide the needed code and information for building FPGA code. The HDK provides all the information needed for developing an FPGA image from source code, while the SDK provides all the runtime software for managing Amazon FPGAs image (AFI) on loaded into F1 instance FPGA.

Typically, FPGA development process requires a simulator to perform functional test on the source code,  and a Vivado tool set for synthesis of source code into compiled FPGA code. The FPGA Developer AMI provided by AWS includes the complete Xilinx Vivado tools for simulation (XSMI) and synthesis of FPGA .

**Q: How do I develop accelerator code for an FPGA in an F1 instance?**

Start with the [Shell interface specification](./hdk/docs/AWS_Shell_Interface_Specification.md). This document describes the interface between Custom Logic and the AWS Shell. All Custom Logic for an accelerator resides within the Custom Logic region of the F1 FPGA.

The [HDK README](./hdk/README.md) walks the developer through the steps to build an FPGA image from one of the provided examples as well starting a new code

**Q: What is included in the HDK?**

The HDK includes major portions:
1) Documentation for the Shell interface and other Custom Logic implementation guidelines, the Shell code needed for Custom Logic
development, simulation models for the Shell, software for exercising

2) Custom Logic examples, a getting started guide for building your own Custom Logic, and
examples for starting a Custom Logic Design.

3) Scripts for building and submitting Amazon FPGA Image (AFI) from a Custom Logic

4) Reference software drivers to be used in conjunction with the Custom Logic examples

5) RTL Simulation models and RTL simula

**Q: What is in the AWS Shell?**

The AWS Shell is a piece of code provided and managed by AWS, that does a lot of the non-differentiated heavy lefting like setting up the PCIe interface, and FPGA image loading infrastructure, security and operational isolation, metrics and debug hooks

Every FPGA deployed in AWS cloud includes AWS shell, and the developer Custom Logic (CL) actually interfaces with the available AWS Shell interfaces.

AWS itselfs includes the PCIe interface for the FPGA, and necessary FPGA management functionality.  One of the four DRAM interface controllers is included in the Shell, while the three other DRAM interface controllers is expected to be instanciated in the Custom Logic code (A design choice that was made to achieve optimal utilization of FPGA resources from placement perspective)

**Q: What is an AFI?**

An AFI stands for Amazon FPGA Image. That is the compiled FPGA code that
is loaded into an FPGA for performing the Custom Logic function created
by the developer. AFIs are maintained by AWS according to the AWS
account that created them. An AFI ID is used to reference a particular
AFI from an F1 instance. The AFI ID is used to indicate the AFI that
should be loaded into a specific FPGA within the instance.

**Q: Are there examples for getting started on accelerators?**

Yes, examples are in the [examples directory](./hdk/cl/examples):

The [cl_hello_world example](.hdk/cl/examples/cl_hello_world) is an RTL/Verilog simple example to build and test the CL development process, it does not use any of the external interfaces of the FPGA except the PCIe. 

The [cl_simple example]((.hdk/cl/examples/cl_simple) provides an expanded example for testing access to the DRAM interfaces.

**Q: How do I get access to AWS FPGA Developer AMI?**

Currently, the FPGA Developer AMI is private and you will need to be whitelisted. You will receive permission and notifications via email.  Email aws-fpga-developer-support@amazon.com with any questions.

Once you got access to the FPGA Developer AMI, we suggest you read the the README file within the FPGA Developer for more details.

XXXXX

**What is the process for creating an AFI?**

The AFI process starts by creating Custom Logic code that conforms to
the Shell Specification. Then, the Custom Logic must be compiled using
the Vivado tools to create a Design Checkpoint. That Design Checkpoint
is submitted to AWS for generating an AFI using the API.

See aws-fpga/hdk/cl and aws-fpga/hdk/cl/examples for more detailed
information.

**Is there any software I need on my instance?**

The required AWS software is the FPGA Management Tool set found in the
SDK directory. This software manages loading and clearing AFIs for FPGAs
in the instance. It also allows developers to retrieve status on the
FPGAs from within the instance. See the README in aws-fpga/sdk for more
details.

**Why do I see error “vivado not found” while running hdk\_setup.sh**

This is an indication that Xilinx vivado tool set are not installed. Try
installing the tool, or alternative use AWS FPGA Development AMI
available on AWS Marketplace, which comes with pre-installed Vivado
toolset and license

**Do AWS Marketplace customers see FPGA source code or a bitstream?**

Neither: AWS Marketplace customers that pick up an AMI with with one our
more AFIs associated with it will not see any source code nor bitstream.
Marketplace customers actually have permission to use the AFI but not
permission to see its code. The only reference to the AFI is through the
AFI ID. The Customer would call fpga-local-load-image with the correct
AFI ID for that Marketplace offering, which will result in AWS loading
the AFI into the FPGA. No FPGA internal design code is exposed.

**Why did my example job run and die without generating a DCP file?**

The error message below indicates that you ran out of memory.  Restart your instance
with a different instance type that has 8GiB or more.

Finished applying 'set_property' XDC Constraints : Time (s): cpu = 00:06:26 ; 
elapsed = 00:08:59 . Memory (MB): peak = 4032.184 ; gain = 3031.297 ; free physical = 1285 ; free virtual = 1957
/opt/Xilinx/Vivado/2016.3/bin/loader: line 164:  8160 Killed                  "$RDI_PROG" "$@"
Parent process (pid 8160) has died. This helper process will now exit

**Can I bring my own bitstream for loading on an F1 FPGA?**

No. There is no mechanism for loading a bitstream directly onto the
FPGAs of an F1 instance. All Custom Logic bitstreams are loaded onto the
FPGA by AWS. Developers create an AFI by creating a Vivado Design
Checkpoint (DCP) and submitting that DCP to AWS. AWS creates the final
AFI and bitstream from that DCP and returns an AFI ID for referencing
that AFI.

**Do I need to interface to the AWS Shell?**

Yes. The only interface to PCIe and the instance CPU is through the AWS
shell. The AWS Shell is included in all F1 FPGAs. There is no option to
run the F1 FPGA without the Shell.

**Can I generate my bitstream locally?**

Yes, local tools can be used to develop the DCP needed for creating an
AFI. The HDK can be downloaded from GitHub and run on any local machine.
If a Developer uses local tools, the exact tool version specified in the
HDK and FPGA Developer AMI will need to be used. Note that AWS does not
provide support for generating a bitstream and testing that bitstream.

**Do I need to get a Xilinx license to generate an AFI?**

No, if the Developer uses the FPGA Developer AMI, Xilinx licenses for
simulation and DCP generation are included. Ingestion of a DCP to
generate an AFI is handled by AWS. No license is needed for DCP to AFI
generation. If a local machine is used for development, the Developer is
responsible for obtaining any necessary licenses. AWS only directly
support cloud development using the AWS Developer AMI.

**Does AWS provide local development boards?**

No. AWS supports a cloud-only development model and provides the
necessary elements for doing 100% cloud development. No development
board is provided for on-premise development.

**Which HDL languages are supported?**

Verilog and HVDL are both supported in the FPGA Developer AMI and in
generating a DCP. The Xilinx Vivado tools and simulator support mixed
mode simulation of Verilog and VHDL. The AWS Shell is written in
Verilog. Support for mixed mode simulation may vary if Developers use
other simulators. Check your simulator documentation for
Verilog/VHDL/System Verilog support.

**What simulators are supported?**

The FPGA Developer AMI has built-in support for the Xilinx XSIM
simulator. All licensing and software for XSIM is included in the
Developer AMI when launched. Support for other simulators is included
through the bring-your-own license in the license manager for the
Developer AMI. AWS tests the HDK with Synopsys VCS, Mentor
Questa/ModelSim, and Cadence Incisive. Licenses for these simulators
must be acquired by the Developer.

**Is OpenCL and/or SDAccel Supported?**

Yes. OpenCL is supported through either the Xilinx SDAccel tool or any
SDAccel tool capable of generating RTL supported by the Xilinx Vivado
synthesis tool. There is a branch in the AWS SDK tree for SDAccel. Note
that during the Preview period, SDAccel may not be available.

**Can I use High Level Synthesis (HLS) Tools to generate an AFI?**

Yes. Vivado HLS and SDAccel are directly supported through the FPGA
Developer AMI. Any HLS tool that generates compatible Verilog or VHDL
for Vivado input can also be used for writing in HLS.

**Do I need to design for a specific power envelope?**

Yes, the design scripts provided in the HDK include checks for power
consumption that exceeds the allocated power for the Custom Logic
region. Developers do not need to include design considerations for
DRAM, Shell, or Thermal. AWS includes the design considerations for
those as part of providing the power envelop for the CL region.

**Is a simulation model of the AWS Shell available?**

Yes. The HDK includes a simulation model for the AWS shell. See the
HDK/common tree for more information on the Shell simulation model.

**What example CL designs are provided in the HDK?**

There are two example designs provided in the HDK. There is a
hello\_world example that accepts reads and writes from an F1 instance.
There is a cl\_simple example that expands on hello\_world by adding
traffic generation to DRAM. Both examples are found in the
hdk/cl/examples directory.

**What resources within the FPGA does the AWS Shell consume?**

The Shell consumes 20% of the F1 FPGA resources. The nature of partial
reconfiguration consumes all resources (BRAM, URAM, Logic Elements, DSP,
etc) in the partition allocated for the AWS Shell. No modifications to
the Shell or the partition pins between the Shell and the CL are
possible by the Developer.

**What IP blocks are provided in the HDK?**

The HDK includes IP for the Shell and DDR controllers. Inside the Shell,
there is a PCIe interface, the Xilinx XDMA Engine, and one DDR
controller. These blocks are only accessible via the AXI interfaces
defined by the Shell interface. There are IP blocks for DDR controllers,
enabling up to 3 additional DDR interfaces instantiated by the Developer
in the CL region. Future versions of the HDK will include IP for the
FPGA Link interface.

**Can I use other IP blocks from Xilinx or other 3^rd^ parties?**

Yes. Developers are free to use any IP blocks within the CL region that
can be utilized by Vivado to create a Partial Reconfiguration region.
Note that AWS does not provide direct support for IP blocks not
contained in the HDK.

**What OS can run on the F1 instance?**

Amazon Linux is supported directly on F1. Developers can utilize the
source code in the SDK directory to compile other variants of Linux for
use on F1. Windows is not supported on F1.

**What support exists for host DMA?**

There are two mechanisms for host DMA between the instance CPU and the
FPGA. The first is the Xilinx XDMA engine. This engine is included in
the AWS Shell and programmed through address space in a Physical
Function directly mapped to the instance. There are dedicated AXI
interfaces for data movement between the CL and the XDMA in the Shell.
The second is the capability for Developers to create their own DMA
engine in the CL region. Developers can create any DMA structure using
the CL to Shell AXI master interface. Interrupt support is through
MSI-X. See the Shell\_Interface document in HDK/docs for detailed
information.

**What is the API for the host CPU to the FPGA?**

There are two types of interface from the host (instance) CPU to the
FPGA. The first is the API for FPGA Image Management Tools. This API is
detailed in the SDK portion of the GitHub repository. FPGA Image
Management tools include APIs to load, clear, and get status of the
FPGA. The second type of interface is direct address access to the
Physical Functions (PF) of the FPGA. There is no API for this access.
Rather, there is direct access to resources in the CL region or Shell
that can be accessed by software written on the instance. For example,
the Chipscope software uses address space in a PF to provide debug
support in the FPGA. Developers can create any API to the resources in
their CL that is needed. See the Shell\_Interface specification for more
details on the PF mapping.

**Is the FPGA a kernel or user space interface in the instance?**

The address space in the FPGA can be interfaced via user space.

**How do I change what AFI is loaded in an FPGA?**

Changing the AFI loaded in an FPGA is done using the
fpga-load-local-image API from the FGPA Image Management tools. This
command takes the AFI ID and requests it to be programmed into the
identified FPGA. The AWS infrastructure manages the actual bitstream and
programming of the FPGA using Partial Reconfiguration. The AFI bitstream
is not stored in the F1 instance or AMI. The bitstream can’t be read or
modified within the FPGA by the instance. A users may call
fpga-load-local-image at any time during the life of an instance, and
may call fpga-load-local-image any number of times.

**Will FPGA state be scrubbed?**

Yes. The AWS infrastructure scrubs FPGA state on termination of an F1
instance and any reuse of the FPGA hardware. Scrubbing includes both
FPGA internal state and the contents of DRAM attached to the FPGA.
Additionally, users can call the fpga-clear-local-image command from the
FPGA Image Management tools to force a clear of FPGA and DRAM contents
while the instance is running.

**What does publishing to AWS Marketplace enable?**

Publishing an AFI and AMI for F1 to AWS Marketplace enables Developers
to sell their AFI/AMI combination through the AWS Marketplace. Once in
Marketplace, customers can launch an F1 instance with that AFI/AMI
combination directly and be billed directly for the use of the instance
and AFI/AMI. Contact AWS Marketplace for more details on becoming an AWS
Marketplace seller.

**How do the FPGAs connect to the Xeon CPU?**

Each FPGA in F1 is connected via a x16 Gen3 PCIe interface. Physcial
Functions (PF) within the FPGA are directly mapped into the F1 instance.
Software on the instance can directly access the address in the PF to
take advantage of the high performance PCIe interface.

**What network performance is available on F1?**

F1 supports 20Gbps Networking using the AWS ENA interface.

**Can the FPGAs on F1 directly access Amazon’s network?**

No. The FPGAs do not have direct access to the network. The FPGAs
communicate via PCIe to the host CPU, where the ENA drivers are run. ENA
provides a high-performance, low-latency network interface suitable for
data movement to the F1 instance. See the AWS ENA driver documentation
for more details.

**Can the FPGAs on F1 directly access the disks in the instance?**

No. The FPGAs do not have direct access to the disks on F1. The disks on
F1 are high-performance, NVMe SSD devices. The interface to the host CPU
on the instance is high-performance and low-latency with NVMe.

**What is FPGA direct and how fast is it?**

FPGA direct is FPGA to FPGA peer communication through the PCIe links on
each FPGA. The BAR space in the Application PF (see Shell Interface
specification for more details) allows the Developer to map regions of
the CL (such as DDR space) to other FPGAs. The Developer can create
software to DMA data between FPGAs directly, without using Instance
memory as a buffer. The implementation of communication across the PCIe
interface using FPGA direct is left to the Developer.

**What is FPGA Link and how fast is it?**

FPGA Link is based on 4 x 100Gbps links on each FPGA card. The FPGA Link
is organized as a ring, with 2 x 100Gbps links to each adjacent card.
This enables each FPGA card to send/receive data from an adjacent card
at 200Gbps. Details on the FPGA Link interface are provided in the Shell
Interface specification when available.

**What protocol is used for FPGA link?**

There is no transport protocol for the FPGA link. It is a data streaming
interface. Details on the shell interface to the FPGA Link IP blocks are
provided in the Shell Interface specification when available.

**What clock speed does the FPGA utilize?**

The FPGA provides a 250MHz clock from the Shell to the CL region. The
AXI interfaces to the Shell are synchronous to that clock. Developers
can create an ansynchronous interface to the AXI busses and run their CL
region at any clock frequency needed. Clocks can be created in the CL
region using the Xilinx clock generation modules. See the Shell
Interface specification for more details.

**What FPGA debug capabilities are supported?**

There are two debug capabilities supported in F1 for FPGA debug. The
first is the use of Xilinx Chipscope. Xilinx Chipscope is natively
supported on F1 by running the FPGA Developer AMI on the F1 instance to
be debugged. The Chipscope software is included in the Developer AMI.
Not that Chipscope in the F1 instance uses a memory-mapped interface to
communicate with the FPGA. The JTAG/ICAP interface is not available to
the F1 instance. The second is the use metrics available through the
FPGA Image Management tools. The fpga-describe-local-image command
allows the F1 instance to query metrics from the Shell and Shell to CL
interface. See Shell Interface specification and FPGA Image Management
tools for more information on supported metrics.

**What FPGA is used?**

The FPGA for F1 is the Xilinx Ultrascale+ VU9P device in the -2 speed
grade. The HDK scripts have the compile scripts needed for the VU9P
device.

**What memory is attached to the FPGA?**

Each FPGA on F1 has 4 x DDR4 2400 interfaces at 72bits wide (64bit
data). Each DDR interface has 16GB of DRAM attached. This yields 64GB of
total DDR memory local to each FPGA on F1.
