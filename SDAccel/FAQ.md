# Frequently Asked Questions (FAQ)


## Q: When I run my application on F1, I see these errors:  ERROR: Failed to load xclbin ERROR: No program executable for device ERROR: buffer (2) is not resident in device (0)", how to debug these errors?
A:  
* Check that your AFI has been generated successfully by reviewing the SDAccel README. 
* Check that you are running your application on F1 as super user(sudo).  
* Lastly, check that your AWS CLI (configure) was configured using output format as json.   

## Q: During AFI generation (create_sdaccel_afi.sh), how do I resolve this error: "An error occurred (AuthFailure) when calling the CreateFpgaImage operation: AWS was not able to validate the provided access credentials"?

A: 

This error message means your AWS credentials or IAM role were not setup correctly to have access to the API (CreateFpgaImage).
AWS Accounts require IAM permissions to access API functions. To test your IAM permissions use [DescribeFpgaImage API](https://github.com/aws/aws-fpga/blob/master/hdk/docs/describe_fpga_images.md)

To setup IAM privileges please check the [EC2 API Permissions documentation](http://docs.aws.amazon.com/AWSEC2/latest/APIReference/ec2-api-permissions.html)


## Q: During AFI generation (create_sdaccel_afi.sh), my AFI failed to generate and I see this error message in the log:  "Provided clocks configuration is illegal. See AWS FPGA HDK documentation for supported clocks configuration. Frequency 0 is lower than minimal supported frequency of 80", how do I debug this message?  

A:  
* Please confirm that you successfully compiled your kernel for HW.  
* For the quick start examples, you will need to have completed the quick start and successfully passed this command:  `make  TARGETS=hw DEVICES=$AWS_PLATFORM all`

## Q: What is a xclbin or binary container on SDAccel? What is an awsxclbin?

A:  The [xclbin](https://www.xilinx.com/html_docs/xilinx2017_2/sdaccel_doc/topics/design-flows/concept-create-compute-unit-binary.html) file or the "Binary Container" is a binary library of kernel compute units that will be loaded together into an OpenCL context for a specific device. 
AWS uses a modified version of the xclbin called awsxclbin. The awsxclbin contains the xclbin metadata and AFI ID.  

## Q: What can we investigate when xocc fails with a path not meeting timing? 
A: An example is WARNING: [XOCC 60-732] Link warning: One or more timing paths failed timing targeting <ORIGINAL_FREQ> MHz for <CLOCK_NAME>. The frequency is being automatically changed to <NEW_SCALED_FREQ> MHz to enable proper functionality.
1. Generally speaking, lowering the clock will make the design functionally operational in terms of operations (since there will not be timing failures) but the design might not operate at the performance needed due this clock frequency change. We can review what can be done.
1. If CLOCK_NAME is `kernel clock 'DATA_CLK'` then this is the clock that drives the kernels. Try reducing the kernel clock frequency see --kernel_frequency option to xocc in the [latest SDAccel Environment User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_1/ug1023-sdaccel-user-guide.pdf).
1. If CLOCK_NAME is `system clock 'clk_main_a0'` then this is the clock clk_main_a0 which drives the AXI interconnect between the AWS Shell and the rest of the platform (SDAccel peripherals and user kernels). Using --kernel_frequency as above does not have any direct effect but might have side effect in changing the topology/placement of the design and improve this issue.
1. If OCL/C/C++ kernels were also used, investigate VHLS reports / correlate with kernel source code to see if there are functions with large number of statements in basic block, examples: might have unrolled loops with large loop-count, might have a 100++ latency; the VHLS runs and log files are located in the directory named `_xocc*compile*`
1. Try `xocc -O3` to run bitstream creation process with higher efforts.
1. Open a Vivado implementation project using ```vivado `find -name ipiimpl.xpr` ``` to analyze the design; needs Vivado knowledge; see [UltraFast Design Methodology Guide for the Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_1/ug949-vivado-design-methodology.pdf)

## Q: xocc issues message WARNING: [XOCC 204-69] Unable to schedule ...due to limited memory ports.
A: This may lower the performance of the implementation.   
Details on this are provided in [the SDAccel HLS Debug document](docs/SDAccel_HLS_Debug.md)

## Q: xocc fails due to routing/resource overflow
A: Examine utilization reports. If OCL/C/C++ kernels were also used, look into the source code for excessive unroll happening.

## Q: How do I open the design as a Vivado project (.xpr)?
A: There are 2 Vivado project files: 
1. CL Design - from command line: ```vivado `find -name ipiprj.xpr\` ``` to see the connectivity of the created design
1. Implementation project - from command line: ```vivado `find -name ipiimpl.xpr\` ``` to analyze the design in the place and routing design phases. 
   1. For an additional Vivado Design reference, see the [UltraFast Design Methodology Guide for the Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_1/ug949-vivado-design-methodology.pdf)

## Q: What should I do if FPGA instance execution gets the wrong results or gets stuck?
A: 
1. Verify hw_emu works as expected
1. See the "Debugging Applications in the SDAccel Environment" chapter in the [latest SDAccel Environment User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_1/ug1023-sdaccel-user-guide.pdf).

## Q: Bitstream creation fails to create design less that 60 MHz?
A: SDAccel flow does not allow clocks running less than 60 MHz kernel clock, therefore, you will need to debug further using [HLS Debug suggestions](./docs/SDAccel_HLS_Debug.md)

## Q: Using the .dcp file generated from xocc results in an error?
A: Directly using the .dcp file without conversion to .awsxclbin file will result in an error - Error: ... invalid binary.  See [Instructions on how to create AFI and subsequent execution process](./README.md#createafi)

## Q: Debugging using gdb in SDX gui is not working? 
A: Please make sure you executed the following commands before launching the SDx gui.
  1.	mv /usr/local/Modules/init init.bak
  2.	unset –f switchml
  3.	unset –f _moduleraw
  4.	unset –f module
  
## Q: How do I debug error: `No current synthesis run set`? 
A: You may have run the previous [HDK IPI examples](../hdk/docs/IPI_GUI_Vivado_Setup.md) and created a `Vivado_init.tcl` file in `~/.Xilinx/Vivado`. It is recommended to remove it before switching from hardware development flow to SDAccel. 

## Q: I am getting an error: `symbol lookup error: /opt/xilinx/xrt/lib/libxrt_aws.so: undefined symbol: uuid_parse` What should I do?
A: This error occured because the XRT RPM was built without linking in a library needed for the uuid symbols.
   To fix it, use the latest XRT RPM's documented in the [XRT installation document](docs/XRT_installation_instructions.md)

## Q: What is the lowest frequency SDAccel design supported on the AWS F1 Platform?
A: We support creating AFI's from CL's that have been built to work at Frequencies no lower than 80MHz.
   Re-clocking/Loading a dynamic clock frequency lower than 80MHz will also result in an error.

# Additional Resources

* The [AWS SDAccel README](README.md).
* Xilinx web portal for [Xilinx SDAccel documentation](https://www.xilinx.com/products/design-tools/legacy-tools/sdaccel.html) 
* [Xilinx SDAccel GitHub repository](https://github.com/Xilinx/SDAccel_Examples)
* [Debug HLS Performance: Limited memory ports](./docs/SDAccel_HLS_Debug.md)
