# Frequently Asked Questions (FAQ)

## Q: When I run my application on F1, I see these errors:  ERROR: Failed to load xclbin ERROR: No program executable for device ERROR: buffer (2) is not resident in device (0)", how to debug these errors?

A:  First double check that your AFI has been generated successfully by reviewing the SDAccel README.  Second, check that you are running your application on F1 using sudo.  Lastly, check that your AWS CLI (configure) was configured using output format as json.   

## Q: During AFI generation (create_sdaccel_afi.sh), how do I resolve this error: "An error occurred (AuthFailure) when calling the CreateFpgaImage operation: AWS was not able to validate the provided access credentials"?

A: The script has output an error, therefore, for AFI generation to complete you will need to resolve this error.
"An error occurred (AuthFailure) when calling the CreateFpgaImage operation: AWS was not able to validate the provided access credentials"

This error message means your AWS credentials were not setup properly or your IAM does not have access to the API (CreateFpgaImage). Here is some additional info on how to setup IAM privileges.
http://docs.aws.amazon.com/AWSEC2/latest/APIReference/ec2-api-permissions.html

You may want to test you IAM policy using DescribeFpgaImage API:
https://github.com/aws/aws-fpga/blob/master/hdk/docs/describe_fpga_images.md

## Q: During AFI generation (create_sdaccel_afi.sh), my AFI failed to generate and I see this error message in the log:  "Provided clocks configuration is illegal. See AWS FPGA HDK documentation for supported clocks configuration. Frequency 0 is lower than minimal supported frequency of 80", how do I debug this message?  

A:  Please confirm that you successfully compiled your kernel for HW.  For the quick start examples, you will need to have completed the quick start and successfully passed this command:  make  TARGETS=hw DEVICES=$AWS_PLATFORM all

## Q: What is a xclbin or binary container on SDAccel?

A:  The [xclbin](https://www.xilinx.com/html_docs/xilinx2017_2/sdaccel_doc/topics/design-flows/concept-create-compute-unit-binary.html) file or the "Binary Container" is a binary library of kernel compute units that will be loaded together into an OpenCL context for a specific device. 
AWS uses a modified version of the xclbin called awsxclbin.  The awsxclbin contains the xclbin metadata and AFI ID.  

## Q: What can we investigate when xocc fails with a path not meeting timing? 
A: An example is WARNING: [XOCC 60-732] Link warning: One or more timing paths failed timing targeting <ORIGINAL_FREQ> MHz for <CLOCK_NAME>. The frequency is being automatically changed to <NEW_SCALED_FREQ> MHz to enable proper functionality.
1. Generally speaking, lowering the clock will make the design functional in terms of operations (since there will not be timing failures) but the design might not operate at the performance needed due this clock frequency change. We can review what can be done.
1. If CLOCK_NAME is `kernel clock 'DATA_CLK'` then this is the clock that drives the kernels. Try reduce kernel clock frequency see --kernel_frequency option to xocc in [2017.4 SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf)
1. If CLOCK_NAME is `system clock 'clk_main_a0'` then this is the clock clk_main_a0 which drives the AXI interconnect between the AWS Shell and the rest of the platform (SDAccel peripherals and user kernels). Using --kernel_frequency as above does not have any direct effect but might have side effect in changing the topology/placement of the design and improve this issue.
1. If OCL/C/C++ kernels were also used, investigate VHLS reports / correlate with kernel source code to see if there are functions with large number of statements in basic block, examples: might have unrolled loops with large loop-count, might have a 100++ latency; the VHLS runs and log files are located in the directory named `_xocc*compile*`
1. Try `xocc -O3` to run bitstream creation process with higher efforts.
1. Open vivado implementation project ```vivado `find -name ipiimpl.xpr` ``` to analyze the design; needs Vivado knowledge; see [UltraFast Design Methodology Guide for the Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug949-vivado-design-methodology.pdf)

## Q: xocc issues message WARNING: [XOCC 204-69] Unable to schedule ...due to limited memory ports.
A: This may lower the performance of the implementation.   
Details on this are provided in [Debug HLS Performance](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1270-vivado-hls-opt-methodology-guide.pdf)

## Q: xocc fails due to routing/resource overflow
A: Examine utilization reports.  If OCL/C/C++ kernels were also used, look into the source code for excessive unroll happening.

## Q: How do I open the design as a Vivado project (.xpr)?
A: There are 2 vivado project files: 
1. CL Design - from command line: ```vivado `find -name ipiprj.xpr\` ``` to see the connectivity of the created design
1. Implementation project - from command line: ```vivado `find -name ipiimpl.xpr\` ``` to analyze the design in the place and routing design phases.  For an additional Vivado Design reference, see [UltraFast Design Methodology Guide for the Vivado](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug949-vivado-design-methodology.pdf)

## Q: What should I do if FPGA instance execution gets the wrong results or gets stuck?
A: 
1. Verify hw_emu works as expected.  Using less data in hw_emu
1. Add assert where run fails and check same conditions for hw_emu
1. See "Chapter 8 - Debugging Applications in the SDAccel Environment" in [2017.4 SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf)

## Q: Bitstream creation fails to create design less that 60 MHz?
A: SDAccel flow does not allow clocks running less that 60 MHz kernel clock, therefore, you will need to debug further using [HLS Debug suggestions](./docs/SDAccel_HLS_Debug.md)

## Q: Using the .xcp file generated from xocc results in an error?
A: Directly using the .xcp file without conversion to .xclbin file will result in an error - Error: ... invalid binary.  See [Instructions on how to create AFI and subsequent execution process](./README.md#createafi)

# Additional Resources
 * [AWS SDAccel Readme](README.md)
 * [Debug HLS Performance: Limited memory ports](./docs/SDAccel_HLS_Debug.md)
 * [Xilinx SDAccel GitHub repository](https://github.com/Xilinx/SDAccel_Examples)
 * [Xilinx SDAccel documentation](https://www.xilinx.com/products/design-tools/software-zone/sdaccel.html#documentation)
 * [Vivado HLS landing page](https://www.xilinx.com/products/design-tools/vivado/integration/esl-design.html)
 * [Vivado landing page](https://www.xilinx.com/products/design-tools/vivado.html)
 * [2017.4 SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf)
 * [2017.4 SDAccel Intro Tutorial](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1021-sdaccel-intro-tutorial.pdf)
 * [2017.1 SDAccel Environment Optimization Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf)

