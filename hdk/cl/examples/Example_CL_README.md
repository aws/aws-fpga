**Overview**

Building a Custom Logic (CL) implementation in the AWS FPGA instance
requires an implementation that complies with the CL specification. The
following CL examples are provided to assist developers in creating a
functional Custom Logic implementation. All examples are included in the
hdk/cl/examples directory. Each example includes:
1. the design source code for the example included in the /design/cl directory,
2. constraints and scripts for compiling the example design in the Developer AMI,
3. a design checkpoint that can be submitted for AFI generation,
4. an AFI-ID for a pre-generated AFI that matches the example design,
5. software source code for any software needed in the instance to run the example,
6. software images that can be loaded on an F1 instance to test the AFI on an F1 instance.
An AFI can be creating using the files in sections 1, 2, 3, & 4. The AFI can be used in an F1 instance by using the files in sections 5 & 6. By following the example CLs, a Developer should be understand how to interface to the Shell blocks of the FPGA, compile design source code to create an AFI, and load an AFI from the F1 instance for use.

**cl\_simple Functional Description**

The first CL example is the cl\_simple example. This example contains
the CL template for generating the CL ports and a CL that exercises the
data movement interfaces from the CL to the Shell. In the
hdk/cl/examples/cl\_simple/design directory are all the design source
files for cl\_simple. cl\_ports.vh is the template for generating a CL.
It contains the port interfaces for the AXI interfaces from the Shell to
the CL and including the DDR controller IP blocks. Developers should
start with this file for building their CL design. Cl\_test.vh is a
design built to show developers how to create a CL that moves data
into/out-of DDR and PCIe through the AXI interfaces. Developers should
include cl\_test.vh as a component within the CL to exercise the
interfaces. CL\_test performs Write/Read combinations to all 4 DDR
interfaces and verifies the data. CL\_test also allows software from the
F1 instance to perform CPU-initiated read/write of FPGA memory in the CL
region and verifies the data. This software is included in the HDK
example for CL\_test. CL\_test does not illustrate how to perform DMA
functionality from the instance to the FPGA. CL\_test also does not
illustrate how to create logic operations or instantiate other FPGA IP
blocks within the CL region.

There are three components to the CL\_simple FPGA implementation with
traffic generation: Interface to DDR, Interface to PCIe, and traffic
generation. For the DDR interfaces, CL\_simple instantiates 3 DDR blocks
for the DDR core supplied in the FPGA HDK. These DDR interfaces all use
the same DDR block built 3 times to correspond to the 3 DDR interfaces
contained within the CL region. A developer should not modify the DDR
blocks built within the CL. Functionality of the DDR interface is only
guaranteed when the DDR block is built as delivered in the HDK. The
4^th^ DDR interface is built into the Shell. CL\_test interfaces to the
4^th^ DDR interface using the AXI interface described in the CL
specification. For the PCIe interface, CL\_test uses the AXI interface
described in the CL specification. CL\_test implements an internal
memory that is written/read from the AXI interface. This interface is
mapped to a PCIe Base Address Register of the Application PF so that
instance software can issue reads and writes. No PCIe specific code is
required in the CL\_test to source/sink data from the instance. For
traffic generation, CL\_test creates a data pattern that is written and
read to all 4 DDR banks through the AXI interfaces. The traffic
generation runs all 4 DDR AXI interfaces in parallel, incrementing the
address written/read. The values read are checked against the values
written. An error is indicated if there is a mismatch. The traffic
generation is initiated by a write from the AXI interface, mapped via
PCIe BAR. The status of error conditions can be read through the same
interface.

**Building an AFI from CL\_simple.vh and CL\_test.vh**

To build an AFI that exercises the DDR and PCIe interfaces from
CL\_test, a Developer should first have the AWS FGPA AMI installed on an
instance. See the README for the AWS FPGA AMI in the AWS marketplace for
details on launching the FPGA AMI for development. &lt;Need link for AWS
FPGA AMI&gt;

Once the FPGA AMI is running, download the HDK to the source directory
on the instance. Next prepare a directory for the new example by either
creating directories manually or call source
\$(HDK\_DIR)/cl/developer\_designs/prepare\_new\_cl.sh from within the
directory you want to use for your CL development. A) Set the
environment variable CL\_DIR pointing to directory where the CL is
(export CL\_DIR=Directory\_You\_Want\_For\_Your\_New\_CL) and B) Keep
AWS recommended directory structure for the
'\$(CL\_DIR)/buildand\$(CL\_DIR)/design\` All of the necessary files to
build the cl\_test design are included in the HDK.

Once the design is ready, start the build/create process. Refer to
\$HDK\_DIR/cl/CHECKLIST.txt file to verify all the necessary steps are
set. Once the checklist is complete, run this script to start Vivado and
generate a Design Checkpoint
\$(CL\_DIR)/build/scripts/create\_dcp\_from\_cl.tcl A detailed version
of the Vivado design flow is included in the /build/scripts directory.

Once the Design Checkpoint is ready, submit the cl\_test dcp file to AWS
to generate an AFI. To submit the dcp, create an S3 bucket for
submitting the design and uploads the zipped archive into that bucket.
Then, adds a policy to that bucket allowing our team's account (Account
ID: 682510182675) read/write permissions. A README example of the S3
permissions process is included in the /build/scripts directory. Submit
an email to AWS (email TBD) providing the following information: 1) Name
of the logic design, 2) Generic Desription of the logic design, 3) PCI
IDs (Device, Vendor, Subsystem, SubsystemVendor), 4)Location of the DCP
object (bucket name and key), 4) Location of the directory to write logs
(bucket name and key), and 5) Version of the Shell. After the AFI
generation is complete, AWS will write the logs back into the bucket
locaiton provided by the developer and notify them by email, including
the AFI IDs. These are the IDs used to manage and launch an AFI from
within an Instance. Note that the cl\_test example will always meet
timing constraints.

**Loading and Running cl\_test on an F1 instance**

Once an AFI ID is available, an F1 instance is needed to test the AFI. A
single F1.2XL instance contains 1 FPGA and is enough to utilize the
cl\_test AFI. First, purchase and launch an F1 instance from AWS.
Second, take the FPGA Developer AMI and create a private AMI from the
FPGA Developer AMI. See the FPGA Developer AMI for details on creating a
run-time FGPA AMI. The AMI ID is needed to associate the AFI with the
running instance. Call the AWS CLI associate-fpga-image --fpga-image-id
&lt;AFI ID&gt; \[--image-id &lt;AMI ID&gt;\] This call will associate
the AFI ID with the AMI ID. Once complete, the AFI ID can be loaded on
to any F1 instance running that AMI ID.

To load and run cl\_test from within an instance, start with a launched
F1 instance using the AMI created from the FPGA AMI. Call the FPGA
Management Tools API command load\_afi --afi-id &lt;AFI ID&gt; --
slot&lt;0&gt;. This will load the AFI specified into the only FPGA in
the F1.2XL instance. See the FPGA Management Tools README in /sdk for
more details on the FPGA Management Tools APIs.

The instance software for cl\_test is a single image that issues the
writes and reads to the PCIe address space of the FPGA to start the
test, read/write PCIe space in the FPGA and gather status. This software
is located within the sdk/examples/cl\_simple directory. A single
command to the cl\_test instance software starts the testing within the
FPGA. That command indicates the AFI of the cl\_test and the start of
the testing. The instance software writes to the cl\_test address for
starting the testing. This starts the traffic generation functionality.
The instance software also reads/writes PCIe BAR locations that map to
the cl\_test memory behind the PCIe AXI interface of the FPGA. The
software then reads the status register from the traffic generator to
determine any miscompares from DDR. The software returns a status of
pass/fail and any errors from the failing reads.
