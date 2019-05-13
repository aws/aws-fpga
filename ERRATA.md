
# AWS EC2 FPGA HDK+SDK Errata

## Shell v1.4 (04261818)
[Shell\_04261818_Errata](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK
* Multiple SDE instances per CL is not supported in this release.  Support planned for future release.
* DRAM Data retention is not supported for CL designs with less than 4 DDRs enabled
* Combinatorial loops in CL designs are not supported.
* [Automatic Traffic Generator (ATG)](./hdk/cl/examples/cl_dram_dma/design/cl_tst.sv) in SYNC mode does not wait for write response transaction before issuing read transactions. The fix for this issue is planned in a future release.

## SDK

## SDAccel (For additional restrictions see [SDAccel ERRATA](./SDAccel/ERRATA.md))
* Virtual Ethernet is not supported when using SDAccel
* DRAM Data retention is not supported for kernels that provision less than 4 DDRs
* Combinatorial loops in CL designs are not supported.
* When using [Xilinx runtime(XRT) version 2018.3.3.1](https://github.com/Xilinx/XRT/releases/tag/2018.3.3.1) or [AWS FPGA Developer AMI Version 1.6.0](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) your host application could fail with following error:
   
   ```
   : symbol lookup error: /opt/xilinx/xrt/lib/libxrt_aws.so: undefined symbol: uuid_parse!

   ```  
   The SDAccel examples included in the developer kit use a SDAccel configuration file [sdaccel.ini]. To workaround this error please copy the SDAccel configuration file [sdaccel.ini](SDAccel/examples/aws/helloworld_ocl_runtime/sdaccel.ini) to your executable directory and try executing your application again.
   AWS is working with Xilinx to release a XRT patch to fix this issue.
   
