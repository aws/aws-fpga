# Enabling on-premises development with Xilinx tools

This document helps developers who choose to develop on-premises with specifying and licensing AWS-compatible Xilinx tools for use with the AWS FPGA HDK.

## Requirements for AWS HDK (2024.1)

- Xilinx Vivado ML Enterprise Edition v2024.1
- Floating License: EF-VIVADO-ENTER-FL
- Node locked License: EF-VIVADO-ENTER-NL
- URL: https://www.xilinx.com/member/forms/download/xef.html?filename=FPGAs_AdaptiveSoCs_Unified_2024.1_0522_2023.tar.gz
- MD5 SUM Value: 372c0b184e32001137424e395823de3c

## Licensing Details

- On-Premises customers may need a new or updated license
  - New users will need to obtain a Vivado ML Enterprise license.  This can be purchased via the AMD website [Vivado License Link](https://www.xilinx.com/products/design-tools/vivado/vivado-buy.html)
  - The correct ordering number for the Node-locked is EF-VIVADO-ENTER-NL and Floating is EF-VIVADO-ENTER-FL
  - Please send a request to xilinx_security_app@amd.com to have the encryption license added to your existing one
  - You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
    - EncryptedWriter_v2
    - Analyzer
    - Synthesis
    - Implementation
    - HLS
    - SDK
    - Partial Reconfiguration
    - Simulation
