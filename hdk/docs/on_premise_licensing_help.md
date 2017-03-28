
# Enabling On-premise development with Xilinx tools

**NOTE: If you are developing on AWS cloud and using AWS FPGA Developer AMI provided on AWS Marketplace, you can skip this document.**

This document helps on-premise developers (or cloud developers that prefer not to use AWS FPGA Developer AMI) with specifying and licensing AWS-compatible Xilinx tools for use with the AWS FPGA HDK.


<a name="requirements"></a>
## Requirements for AWS HDK 1.1.0
 * Xilinx 2016.4 SDx
 * License: EF-VIVADO-SDX-VU9P-OP
 * SW Build 1806307 on Thu Mar 9
 * IP Build 1759159 on Thu Jan 26

 * All On-Premise customers will need a new/updated license, please email _*vivado_op@xilinx.com*_ with the following information to receive and updated license:
    * Xilinx Website Account log-in
    * Identify yourself as existing 2016.3 on-premise user vs. new on-premise user
    * Existing users will receive a license that accompanies their existing license and enables VU9P ES2
    * New users will need to purchase an on-premise license of Vivado 2016.4 SDx
    * The correct ordering number for the product is **EF-VIVADO-SDX-VU9P-OP-(NL/FL)**
    * You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
       * Analyzer
       * EncryptedWriter_v1
       * EncryptedWriter_v2
       * HLS
       * PartialReconfiguration
       * Simulation
       * SysGen
       * XCVU9P
       * XCVU9P-ES2
       * XCVU9P-ES2_bitgen
       * ap_opencl
       * wtt_override
       * xcvu9p_bitgen

<a name="download"></a>
## Downloading the development tool from Xilinx

 * URL: https://survey.xilinx.com/ss/wsb.dll/Xilinx/SDSoC_Download_Survey.htm?wsb5=xef.html&wsb7=Xilinx_SDx_2016.4_sdx_0310_1.tar.gz&wsb6=1
 * MD5 SUM Value: c18b84807b51dab7aea24f28983661af

<a name="es2setup"></a>
## Setting up local development environmnet to support VU9P ES2 FPGA

 * To enable the VU9P ES2 device, the following line needs to be added to your Vivado init.tcl:
    * enable_beta_device xcvu9p\*
  
 * More information on init.tcl can be found at https://www.xilinx.com/support/answers/53090.html

