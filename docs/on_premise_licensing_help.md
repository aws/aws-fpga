# Enabling on-premises development with Xilinx tools

**NOTE: If you are developing on the AWS cloud and using AWS FPGA Developer AMI provided on AWS Marketplace, you can skip this document.**

This document helps developers who choose to develop on-premises with specifying and licensing AWS-compatible Xilinx tools for use with the AWS FPGA HDK.
## Requirements for AWS HDK 1.4.18+ (2020.2)
 * Xilinx Vivado or Vitis v2020.2
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_Unified_2020.2_1118_1232.tar.gz
 * MD5 SUM Value: 523e8596f114ab5e389c14df50ecb1d8

## Requirements for AWS HDK 1.4.16+ (2020.1)
 * Xilinx Vivado or Vitis v2020.1
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_Unified_2020.1_0602_1208.tar.gz
 * MD5 SUM Value: b018f7b331ab0446137756156ff944d9
 
## Requirements for AWS HDK 1.4.13+ (2019.2)
 * Xilinx Vivado or Vitis v2019.2
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef-vitis.html?filename=Xilinx_Vitis_2019.2_1106_2127.tar.gz
 * MD5 SUM Value: d63bae9cad9bcaa4b2c7f6df9480eaa6
 
## Requirements for AWS HDK 1.4.11+ (2019.1)
 * Xilinx Vivado v2019.1 or v2019.1.op (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDAccel_2019.1_0524_1430_Lin64.bin
 * MD5 SUM Value: aa20eba36ebe480ec7ae59a4a8c85896
 
## Requirements for AWS HDK 1.4.8+ (2018.3)
 * Xilinx Vivado v2018.3 or v2018.3.op (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_Lin_2018.3_1207_2324_Lin64.bin&akdm=0
 * MD5 SUM Value: aa20eba36ebe480ec7ae59a4a8c85896
 
## Requirements for AWS HDK 1.4.4+ (2018.2)
 * Xilinx Vivado v2018.2 or v2018.2.op (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_Lin_2018.2_0614_1954_Lin64.bin&akdm=0
 * MD5 SUM Value: 6b6939e70d4fa90677d2c54a37ec25c7

## Requirements for AWS HDK 1.3.7+ (2017.4)
 * Xilinx Vivado v2017.4.op (64-bit)
 * License: EF-VIVADO-SDX-VU9P-OP
 * URL: https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_2017.4_0411_1_Lin64.bin&akdm=0
 * MD5 SUM Value: e0b59c86d5ddee601ab17a069d231207

## Licensing Details
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
