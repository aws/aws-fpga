
# Enabling On-premise development with Xilinx tools

**NOTE: If you are developing on AWS cloud and using AWS FPGA Developer AMI provided on AWS Marketplace, you can skip this document.**

This document helps on-premise developers (or cloud developers that prefer not to use AWS FPGA Developer AMI) with specifying and licensing AWS-compatible Xilinx tools for use with the AWS FPGA HDK.


<a name="requirements"></a>
## Requirements for AWS HDK 1.2.0
 * Xilinx Vivado v2017.1 (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * SW Build 1846317 on Fri Apr 14 18:54:47 MDT 2017
 * IP Build 1846188 on Fri Apr 14 20:52:08 MDT 2017

 * On-Premise customers may need a new or updated license
    * Existing F1 On-Premise customers using the 2016.3 developer preview will not need a new license
    * New users will need to purchase an on-premise license of Vivado 2017.1, please click on the appropriate "Buy Online From Xilinx"   
      links here: https://www.xilinx.com/products/design-tools/acceleration-zone/ef-vivado-sdx-vu9p-op-fl-nl.html
    * The correct ordering number for the product is EF-VIVADO-SDX-VU9P-OP-(NL/FL)
    * You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
       * Analyzer
       * EncryptedWriter_v1
       * EncryptedWriter_v2
       * HLS
       * PartialReconfiguration
       * Simulation
       * SysGen
       * XCVU9P
       * XCVU9P-ES2_bitgen
       * ap_opencl
       * wtt_override
       * xcvu9p_bitgen

<a name="download"></a>
## Downloading the development tool from Xilinx

 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_Vivado_2017.1_op_0415_1_Lin64.bin&akdm=0
 * MD5 SUM Value: 6b2a5b9c2af6110dad8036c78ca74fb4

