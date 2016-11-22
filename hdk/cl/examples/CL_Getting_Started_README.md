Building a Custom Logic (CL) implementation in the AWS FPGA instance
requires an implementation that complies with the CL specification. The
following CL examples are provided to assist developers in creating a
functional Custom Logic implementation. All examples are included in the
hdk/cl/examples directory. Each example includes 1) the design source
code for the example included in the /design/cl directory, 2)
constraints and scripts for compiling the example design in the
Developer AMI, 3) a design checkpoint that can be submitted for AFI
generation, 4) an AFI-ID for a pre-generated AFI that matches the
example design, 5) software source code for any software needed in the
instance to run the example, and 6) software images that can be loaded
on an F1 instance to test the AFI on an F1 instance. An AFI can be
creating using the files in sections 1, 2, & 3. The AFI can be used in
an F1 instance by using the files in sections 4, 5 & 6. By following the
example CLs, a Developer should be understand how to interface to the
Shell blocks of the FPGA, compile design source code to create an AFI,
and load an AFI from the F1 instance for use.

**Follow these steps to create an AFI from the cl example:**

Have the AWS FGPA AMI installed on an instance. See the README for the
AWS FPGA AMI in the AWS marketplace for details on launching the FPGA
AMI for development. &lt;Need link for AWS FPGA AMI&gt;

Download and configure the HDK to the source directory on the instance.
Prepare a directory for the new example by either creating directories
manually or call source
\$(HDK\_DIR)/cl/developer\_designs/prepare\_new\_cl.sh from within the
directory you want to use for your CL development. A) Set the
environment variable CL\_DIR pointing to directory where the CL is
(export CL\_DIR=Directory\_You\_Want\_For\_Your\_New\_CL) and B) Keep
AWS recommended directory structure for the
'\$(CL\_DIR)/buildand\$(CL\_DIR)/design\` .

Start the build/create process. Run this script to start Vivado and
generate a Design Checkpoint
\$(CL\_DIR)/build/scripts/create\_dcp\_from\_cl.tcl A detailed version
of the Vivado design flow is included in the /build/scripts directory.
Refer to \$HDK\_DIR/cl/CHECKLIST.txt file to see verification steps that
should be performed on any new design. Example cl designs meet the
checklist criteria by default.

Submit the dcp file to AWS to generate an AFI. To submit the dcp, create
an S3 bucket for submitting the design and upload the zipped archive
into that bucket. Then, add a policy to that bucket allowing our team's
account (Account ID: 682510182675) read/write permissions. A README
example of the S3 permissions process is included in the /build/scripts
directory. Submit an email to AWS (email TBD) providing the following
information: 1) Name of the logic design, 2) Generic Desription of the
logic design, 3) PCI IDs (Device, Vendor, Subsystem, SubsystemVendor),
4)Location of the DCP object (bucket name and key), 4) Location of the
directory to write logs (bucket name and key), and 5) Version of the
Shell. After the AFI generation is complete, AWS will write the logs
back into the bucket locaiton provided by the developer and notify them
by email, including the AFI IDs used to manage and launch an AFI from
within an Instance.

**Follow these steps to load and test an AFI from within an F1
instance:**

Take the FPGA Developer AMI and create a private AMI from the FPGA
Developer AMI. See the FPGA Developer AMI for details on creating a
run-time FGPA AMI. The AMI ID is needed to associate the AFI with the
running instance.

Call the AWS CLI associate-fpga-image --fpga-image-id &lt;AFI ID&gt;
\[--image-id &lt;AMI ID&gt;\] This call will associate the AFI ID with
the AMI ID. Once complete, the AFI ID can be loaded on to any F1
instance running that AMI ID.

Purchase and launch an F1 instance with the run-time FPGA AMI. From the
running instance, call the FPGA Management Tools API command load\_afi
--afi-id &lt;AFI ID&gt; -- slot&lt;0&gt;. This will load the AFI
specified into the only FPGA in the F1.2XL instance. See the FPGA
Management Tools README in /sdk for more details on the FPGA Management
Tools APIs.

Load and run the software for the example cl on the running instance
from the sdk/examples directory that matches the example cl AFI that was
loaded.
