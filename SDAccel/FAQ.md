# Frequently Asked Questions (FAQ)

This section lists issues/perceived issue and their associated investigations or solutions.

## Q: What can we investigate when xocc fails with a path not meeting timing? 
A: An example is WARNING: [XOCC 60-732] Link warning: One or more timing paths failed timing targeting <ORIGINAL_FREQ> MHz for <CLOCK_NAME>. The frequency is being automatically changed to <NEW_SCALED_FREQ> MHz to enable proper functionality.
1. Generally speaking, lowering the clock will make the design functional in terms of operations (since there will not be timing failures) but the design might not operate at the performance needed due this clock frequency change. We can review what can be done.
1. If CLOCK_NAME is `kernel clock 'DATA_CLK'` then this is the clock that drives the kernels. Try reduce kernel clock frequency see --kernel_frequency option to xocc in [latest SDAccel Environment User Guide]
1. If CLOCK_NAME is `system clock 'clk_main_a0'` then this is the clock clk_main_a0 which drives the AXI interconnect between the AWS Shell and the rest of the platform (SDAccel peripherals and user kernels). Using --kernel_frequency as above does not have any direct effect but might have side effect in changing the topology/placement of the design and improve this issue.
1. If OCL/C/C++ kernels were also used, investigate VHLS reports / correlate with kernel source code to see if there are functions with large number of statements in basic block, examples: might have unrolled loops with large loop-count, might have a 100++ latency; the VHLS runs and log files are located in the directory named `_xocc*compile*`
1. Try `xocc -O3` to run bitstream creation process with higher efforts.
1. Open vivado implementation project ```vivado `find -name ipiimpl.xpr` ``` to analyze the design; needs Vivado knowledge; see [UltraFast Design Methodology Guide for the Vivado][latest UG949]

## Q: xocc issues message WARNING: [XOCC 204-69] Unable to schedule ...due to limited memory ports.
A: This may lower the performance of the implementation.   
Details on this are provided in [Debug HLS Performance: Limited memory ports]

## Q: xocc fails due to routing/resource overflow
A: Examine utilization reports.  If OCL/C/C++ kernels were also used, look into the source code for excessive unroll happening.

## Q: How do I open the design as a Vivado project (.xpr)?
A: There are 2 vivado project files: 
1. CL Design - from command line: ```vivado `find -name ipiprj.xpr\` ``` to see the connectivity of the created design
1. Implementation project - from command line: ```vivado `find -name ipiimpl.xpr\` ``` to analyze the design in the place and routing design phases.  For an additional Vivado Design reference, see [UltraFast Design Methodology Guide for the Vivado][latest UG949]

## Q: What should I do if FPGA instance execution gets the wrong results or gets stuck?
A: 
1. Verify hw_emu works as expected.  Using less data in hw_emu
1. Add assert where run fails and check same conditions for hw_emu
1. See "Chapter 8 - Debugging Applications in the SDAccel Environment" in [latest SDAccel Environment User Guide]

## Q: Host code failed to link?
A:
1. Is the code linking to *.so libs and are they setup correctly on the compiler command line argument
- Note, there has been issues reported where -ldl or -lxilinxopencl needed to be put as the last argument of the comman line for the compiler; try linking on the command line and see if moving the -l options corrects the issue.
1. Check if LD_LIBRARY_PATH is setup correctly

## Q: sw_emu passes but hw_emu fails
A: 
1. arrow down failure: what mismatches, only LSB bits different?
1. Differences due to floating point?
1. Run valgrind on executable to assert no seg faults or out of bounds accesses
1. Have a reduced testcase data size if hw_emu takes too long
1. Have sdaccel.ini configured with [Emulation] section using launch_waveform=gui or batch to generate waveform for analysis; see "Application Timeline" in [latest SDAccel Environment User Guide]

## Q: Bitstream creation fails to create design less that 60 MHz?
A: SDAccel flow does not allow clocks running less that 60 MHz kernel clock, therefore, you will need to debug further using [HLS Debug suggestions](./docs/SDAccel_HLS_Debug.md)

## Q: Using the .xcp file generated from xocc results in an error
A:
1. Raw xclbin (.xcp file) from xocc is not usable
1. Directly using the .xcp file without conversion to .xclbin file will result in an error - Error: ... invalid binary
1. See [Instructions on how to create AFI and subsequent execution process](../README.md#create-an-amazon-fpga-image-afi-for-your-kernel)


# Additional Resources

The [AWS SDAccel README].

Xilinx web portal for [Xilinx SDAccel documentation] and for [Xilinx SDAccel GitHub repository]

Links pointing to **latest** version of the user guides
[UG1023: SDAccel Environment User Guide][latest SDAccel Environment User Guide]
[UG1021: SDAccel Environment Tutorial: Getting Started Guide (including emulation/build/running on H/W flow)][latest UG1021]
[UG1207: SDAccel Environment Optimization Guide][latest SDAccel Environment Optimization Guide]
[UG949: UltraFast Design Methodology Guide for the Vivado Design Suite][latest UG949]

Links pointing to **2017.1** version of the user guides
[UG1023: SDAccel Environment User Guide][UG1023 2017.1]
[UG1021: SDAccel Environment Tutorial: Getting Started Guide (including emulation/build/running on H/W flow)][UG1021 2017.1]
[UG1207: SDAccel Environment Optimization Guide][UG1207 2017.1]
[UG1238: SDx Development Environment Release Notes, Installation, and Licensing Guide][UG1238 2017.1]

[SDAccel_landing_page]: https://www.xilinx.com/products/design-tools/software-zone/sdaccel.html
[VHLS_landing_page]: https://www.xilinx.com/products/design-tools/vivado/integration/esl-design.html
[Vivado_landing_page]: https://www.xilinx.com/products/design-tools/vivado.html

[latest SDAccel Environment User Guide]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1023-sdaccel-user-guide.pdf
[latest UG1021]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1021-sdaccel-intro-tutorial.pdf
[latest SDAccel Environment Optimization Guide]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1207-sdaccel-optimization-guide.pdf
[latest UG949]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug949-vivado-design-methodology.pdf

[UG1023 2017.1]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1023-sdaccel-user-guide.pdf
[UG1021 2017.1]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1021-sdaccel-intro-tutorial.pdf
[UG1207 2017.1]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1207-sdaccel-optimization-guide.pdf
[UG1238 2017.1]:http://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1238-sdx-rnil.pdf
[Xilinx SDAccel documentation]: https://www.xilinx.com/products/design-tools/software-zone/sdaccel.html#documentation
[Xilinx SDAccel GitHub repository]: https://github.com/Xilinx/SDAccel_Examples

[AWS SDAccel Readme]: ../README.md
[Debug HLS Performance: Limited memory ports]: ./docs/SDAccel_HLS_Debug.md
