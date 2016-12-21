**Frequently Asked Questions**

**What do I need to get started on building accelerators for FPGA
instances?**

Getting started requires downloading the latest HDK and SDK from the AWS
FPGA GitHub repository. The HDK and SDK provide the needed code and
information for building FPGA code. The HDK provides all the information
needed on building source code for use within the FPGA. The SDK provides
all the information needed on building software for managing FPGAs on an
F1 instance.

FPGA code requires a simulator to test code and a Vivado tool set for
synthesis of source code into compiled FPGA code. The FPGA Developer AMI
includes the Xilinx Vivado tools for simulation and synthesis of
compiled FPGA code.

**How do I develop accelerator code for an FPGA in an F1 instance?**

Start with the Shell interface specification:
AWS\_Shell\_Interface\_Specification.md. This document describes the
interface between Custom Logic and the AWS Shell. All Custom Logic for
an accelerator resides within the Custom Logic region of the F1 FPGA.

**What are the major areas of the GitHub repository?**

The HDK side of the GitHub repository contains the AWS Shell code, Build
scripts, Documentation, and Examples. Shell code is contained in
aws-fpga/hdk/common. Build scripts are in
aws-fpga/hdk/common/shell\_current/build. Documentation is in
aws-fpga/hdk/docs. Custom Logic examples are in aws-fpga/hdk/cl.

The SDK side of the GitHub repository contains the FPGA Management
Tools, a preview of the AWS CLI for F1, and software for Xilinx XDMA and
SDAccell. The FPGA Management Tools are for loading/clearing AFIs and
getting status of the FPGAs mapped to an instance. FPGA Management Tools
are in aws-fpga/sdk/management. The AWS CLI preview is in
aws-fpga/sdk/aws-cli-preview.

**What is included in the HDK?**

The HDK includes documentation for the Shell interface and other Custom
Logic implementation guidelines, the Shell code needed for Custom Logic
development, simulation models for the Shell, software for exercising
the Custom Logic examples, a getting started guide for Custom Logic, and
examples for starting a Custom Logic Design.

**What is in the AWS Shell?**

The AWS Shell includes the PCIe interface for the FPGA, a single DDR
interface, and necessary FPGA management functionality. Also provided as
part of the Shell code, but implemented within the Custom Logic region
of the FPGA are three DDR interfaces. These interfaces are provided for
implementation within the Custom Logic region to provide maximum
efficiency for the developer.

**Are there examples for getting started on accelerators?**

Yes, examples are in the aws-fpga/hdk/cl/examples directory. The
cl\_hello\_world example is a simple example to build and test the CL
development process. The cl\_simple example provides an expanded example
for testing access to the DDR interfaces.

**How do I get access to the Developer AMI?**

Start with an AWS account and request access to the Developer AMI in AWS
Marketplace. Currently, the FPGA Developer AMI is private. You will
receive permission on the AWS account you submitted for access to the
FPGA Developer AMI. The AMI can be launched directly from AWS
Marketplace on any EC2 instance. See the FPGA Developer AMI README for
more details.

**What is an AFI?**

An AFI stands for Amazon FPGA Image. That is the compiled FPGA code that
is loaded into an FPGA for performing the Custom Logic function created
by the developer. AFIs are maintained by AWS according to the AWS
account that created them. An AFI ID is used to reference a particular
AFI from an F1 instance. The AFI ID is used to indicate the AFI that
should be loaded into a specific FPGA within the instance.

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
