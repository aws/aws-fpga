
# Enabling on-premises development with Xilinx tools

**NOTE: If you are developing on the AWS cloud and using AWS FPGA Developer AMI provided on AWS Marketplace, you can skip this document.**

This document helps developers who choose to develop on-premises with specifying and licensing AWS-compatible Xilinx tools for use with the AWS FPGA HDK.

<a name="requirements"></a>
## Requirements for AWS HDK 1.3.7+ (2017.4)
 * Xilinx Vivado v2017.4.op (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * SW Build 2193838 on Tue Apr 10 18:06:59 MDT 2018
 * IP Build 2189296 on Tue Apr 10 19:39:46 MDT 2018

 * On-Premises customers may need a new or updated license
    * Existing F1 on-premises customers will not need a new license
    * New users will need to obtain an on-premises license of Vivado, please follow the instructions at: https://www.xilinx.com/products/design-tools/acceleration-zone/ef-vivado-sdx-vu9p-op-fl-nl.html
    * The correct ordering number for the product is EF-VIVADO-SDX-VU9P-OP-(NL/FL)
    * You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
       * EncryptedWriter_v2
       * Synthesis
       * Implementation
       * XCVU9P
       * XCVU9P_bitgen
       * ap_opencl
       * Analyzer
       * HLS
       * PartialReconfiguration
       * Simulation
       * SysGen

<a name="download"></a>
## Downloading the development tool from Xilinx

 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_2017.4_0411_1_Lin64.bin&akdm=0
 * MD5 SUM Value: e0b59c86d5ddee601ab17a069d231207


<a name="requirements"></a>
## Requirements for AWS HDK 1.3.0+ (2017.1_sdx)
 * Xilinx Vivado v2017.1_sdx (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * SW Build 1933108 on Fri Jul 14 11:54:19 MDT 2017
 * IP Build 1908669 on Fri Jul 14 13:31:24 MDT 2017

 * On-Premises customers may need a new or updated license
    * Existing F1 on-premises customers will not need a new license
    * New users will need to obtain an on-premises license of Vivado, please follow the instructions at: https://www.xilinx.com/products/design-tools/acceleration-zone/ef-vivado-sdx-vu9p-op-fl-nl.html
    * The correct ordering number for the product is EF-VIVADO-SDX-VU9P-OP-(NL/FL)
    * You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
       * EncryptedWriter_v2
       * Synthesis
       * Implementation
       * XCVU9P
       * XCVU9P_bitgen
       * ap_opencl
       * Analyzer
       * HLS
       * PartialReconfiguration
       * Simulation
       * SysGen

<a name="download"></a>
## Downloading the development tool from Xilinx

 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_2017.1_sdx_0715_1_Lin64.bin&akdm=0
 * MD5 SUM Value: cfa96d3af608954eb2bc0bf4abb892f8

