Hello\_world is a cl example design that builds on the cl\_simple and
cl\_test example designs. It is built to show a simple logic function
implemented with the cl portion of an AWS FPGA while the cl\_test
functionality runs. Cl\_hello\_world executes a simple byte swap on a 4
byte value written to the FPGA from the F1 instance software. The design
illustrates how to write data to the FPGA from an instance, perform a
logic function within the FPGA, and return data from the FPGA.
cl\_hello\_world allows software to execute the cl\_test functionality
at the same time as the byte swap function.

To start, follow the process illustrated in
hdl/cl/examples/getting\_started.md to build a custom cl directory with
the HDK on a C4 instance running the Developer FPGA AMI. In the
hdk/cl/examples/cl\_hello\_world/design directory are all of the design
source files for cl\_hello\_world.

Once the design is ready, start the Vivado build/create process. Refer
to \$HDK\_DIR/cl/CHECKLIST.txt file to verify all the necessary steps
are set. Once the checklist is complete, run this script to start Vivado
and generate a Design Checkpoint
\$(CL\_DIR)/build/scripts/create\_dcp\_from\_cl.tcl A detailed version
of the Vivado design flow is included in the /build/scripts directory.
Note that cl\_hello\_world is built so that it will always meet timing
constraints in Vivado using the constraints supplied by AWS.

Once the Design Checkpoint is ready, submit the cl\_test dcp file to AWS
to generate an AFI. Follow the steps outline in
hdl/cl/examples/getting\_started.md for details on this process. This
process will create the AFI ID for use in running cl\_hello\_world on an
F1 instance. Create a private AMI from the Developer FPGA AMI using the
process defined in Developer FPGA AMI README. Call the AWS CLI
associate-fpga-image --fpga-image-id &lt;AFI ID&gt; \[--image-id &lt;AMI
ID&gt;\] This call will associate the AFI ID with the newly created AMI
ID.

To load cl\_hello\_world on an F1 instance, launch an F1 instance from
the AWS CLI with the private AMI created for association. When the
instance is ready, call the FPGA Management Tools API command load\_afi
--afi-id &lt;AFI ID&gt; -- slot&lt;0&gt;. This will load the AFI
specified into the only FPGA in the F1.2XL instance. See the FPGA
Management Tools README in /sdk for more details on the FPGA Management
Tools APIs.

To run the cl\_hello\_world functionality, run
cl\_hello\_world\_byte\_swap script in sdk/examples/cl\_hello\_world
with the 4 byte value to swap. This will write the 4 byte value to the
FPGA, where it is swapped. It then reads the FPGA back to retrieve the
new value. The retrieved value is displayed back.

For parallel operation with cl\_test functionality, the script
sdk/examples/cl\_simple cl\_test\_start can be run first. While running,
run cl\_hello\_world\_byte\_swap to see the byte swap function performed
while the interface test is performed.
