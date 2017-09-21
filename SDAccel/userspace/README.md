# SDAccel Hardware Abstraction Layer for AWS FPGA

This directory includes the source code and binary files for mapping SDAccel/OpenCL runtime library call to AWS specific hardware. It support the following functionality. The API is documented in [xclhal.h](./include/xclhal.h)

We do NOT expect users to modify the functionality in this directory.

1. Device management APIs which include device discovery:
   - xclProbe()
   - xclOpen()  
   - xclClose()
   - xclGetDeviceInfo()
   - xclLoadXclBin(). 
2. Device memory mamagement including buffer object creation and data migration. The APIs are :
    - xclAllocDeviceBuffer()
    - xclFreeDeviceBuffer()
    - xclCopyBufferHost2Device()
    - xclCopyBufferDevice2Host()
3. Device profiling functionality. 
    - xclPerfMon*()
    



