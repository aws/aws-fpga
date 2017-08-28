# AWS EC2 FPGA SDK Userspace Software

The [Programmer's View](../../hdk/docs/Programmer_View.md) describes all the runtime software components that would be used in an FPGA-enabled EC2 instance like F1. It supports linux operating systems only.

This directory contains the source and build files for the needed components:

1. The [fpga_mgmt_tools directory](./fpga_mgmt_tools) contains  [Amazon FPGA Image (AFI) Management Tools](./fpga_mgmt_tools/README.md): A linux shell commands to manage AFI, Virtual JTAG, Virtual LED and DIPSwitches. Calling [`sdk_setup.sh`](../../sdk_setup.sh) will compile and install the tools.

2. The [Include directory](./include) contains the header files required for integration with a C/C++ application.

3. The [FPGA Libraries](./fpga_libs) contains source files for fpga_pci and fpga_mgmt libraries: libraries used to integrate with C/C++ applications, and need to be compiled and statically linked with the C/C++ applications. The [CL Examples](../../hdk/cl/examples) have example applications builds that use these libraries

4. The [Utility](./utils) contains source files for various utilities used by the fpga_libs and fpga_mgmt_tools, like logging services.





