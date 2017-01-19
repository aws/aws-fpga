# Developing on AWS FPGA with OpenCL and SDAccel

** DRAFT ONLY **

OpenCL is a framework for heterogeneous computing, having a goal to offload certain workloads to accelerators like FPGAs.

Xilinx' SDAccel provides the development environment, compiler and runtime tools to interface with Amazon FPGA instances. 

In addition to OpenCL, SDAccel provides development flows to create accelerated kernels in RTL (Verilog/VHDL) or C/C++.

## What do I need in order to start building and running with OpenCL?

The developer needs to install the SDAccel environment, including both the compiler and runtime envrionment, and have a valid Vivado license for development. 
AWS FPGA Development AMI comes pre-installed with SDAccel and required license. (WIP)

In addition to the standard SDAccel tools and license, there are three parts specific to AWS:
a) [AWS-specific Hardware Abstraction Layer (HAL)](../../sdk/SDAccel/HAL) which links to the OpenCL runtime library
b) DSA - [TBD]
c) AFI ingestion scripts that will take the OpenCL compiler output and register it as an AFI.

# Known Restrictions

* OpenCL support is limited to OpenCL 1.0 core specifications.
* On device - only Global memory (i.e. external DRAM) is supported.
* Shared Virtual Memory (SVM) is not supported.
* Image 2D APIs.
* For complete list of the supported OpenCL APIs, please refer to [Appendix B in Xilinx' UG1023](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1023-sdaccel-user-guide.pdf)

# Additional References

## Introductionary

* [OpenCL memory model video](https://www.youtube.com/watch?v=c4a8uQ4AnMI)

* [OpenCL application structure video](https://www.youtube.com/watch?v=hUiX8rBcNzw)

* Xilinx' [SDAccel Environment tutorial](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1021-sdaccel-intro-tutorial.pdf)

 
## Advanced

* Xilinx' [SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1023-sdaccel-user-guide.pdf)

* Xilinx' [SDAccel Environment optimization guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_3/ug1207-sdaccel-optimization-guide.pdf)
