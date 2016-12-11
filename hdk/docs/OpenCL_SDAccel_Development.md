# Developing using OpenCL on AWS FPGA

** DRAFT ONLY **

OpenCL is a framework for hetrogenous computing, having a goal to enable offload certain workloads to accelerators like FPGA.

Xilinx' SDAccel provides the development environment, compiler and runtime tools to interface with AWS FPGA. 

In addition to OpenCL, SDAccel provides a development flows for development acceleration kernels in RTL (Verilog/VHDL) or C/C++.

## What do I need to start building and running with OpenC ?

The developer should have installed SDAccel environment, including both the compiler and runtime envrionment, and have a valid Vivado license for development. 
AWS FPGA Development AMI comes with with pre-installed SDAccel and license to ease on the developer. (WIP)

In addition to the standard SDAccel tools and license, there are three parts specific to AWS:
a) [AWS-specific Hardware Abstraction Layer (HAL)](../../../sdk/SDAccel/HAL) which links to the OpenCL runtime library
b) DSA - [TBD]
c) An AFI ingestion scripts that will take the OpenCL compiler outcome and register it as AFI.

# Known restrictions

* OpenCL support limited to OpenCL 1.0 core specifications
* On device - only Global memory (i.e. externa DRAM) is supported
* Shared Virtual Memory (SVM) not supported
* Image 2D APIs
* For complete list of the supported OpenCL API, please refer to [Appendix B in Xilinx' UG1023](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1023-sdaccel-user-guide.pdf)

# Additional References

## Introductionary

 # [OpenCL memory model video](https://www.youtube.com/watch?v=c4a8uQ4AnMI)
 # [OpenCL application structure video](https://www.youtube.com/watch?v=hUiX8rBcNzw)
 # Xilinx' [SDAccel Environment tutorial](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1021-sdaccel-intro-tutorial.pdf)

 
## Advanced
1. Xilinx' [SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1023-sdaccel-user-guide.pdf)
3. Xilinx' [SDAccel Environment optimization guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1207-sdaccel-optimization-guide.pdf)
