
# On-premise licensing help

This document helps on-premise developers with licensing Xilinx tools for use with the HDK.

<a name="requirements"></a>
## Requirements
Xilinx 2016.4 SDx
License: EF-VIVADO-SDX-VU9P-OP
SW Build 1806307 on Thu Mar 9
IP Build 1759159 on Thu Jan 26

All On-Premise customers will need a new/updated license, please email vivado_op@xilinx.com with the following information
Xilinx Website Account log-in
Identify yourself as existing 2016.3 on-premise user vs. new on-premise user
Existing users will receive a license that accompanies their existing license and enables VU9P ES2
New users will need to purchase an on-premise license of Vivado 2016.4 SDx
The correct ordering number for the product is EF-VIVADO-SDX-VU9P-OP-(NL/FL)
You can confirm you are using the correct license for this product by ensuring you have the following in Xilinx License Manager:
Analyzer
EncryptedWriter_v1
EncryptedWriter_v2
HLS
PartialReconfiguration
Simulation
SysGen
XCVU9P
XCVU9P-ES2
XCVU9P-ES2_bitgen
ap_opencl
wtt_override
xcvu9p_bitgen

<a name="download"></a>
## Download

URL: https://survey.xilinx.com/ss/wsb.dll/Xilinx/SDSoC_Download_Survey.htm?wsb5=xef.html&wsb7=Xilinx_SDx_2016.4_sdx_0310_1.tar.gz&wsb6=1
MD5 SUM Value: c18b84807b51dab7aea24f28983661af

<a name="es2setup"></a>
## ES2 Step
To enable the VU9P ES2 device to show, the following line needs to be added to your Vivado init.tcl:
enable_beta_device xcvu9p*
Design files available on the F1 GitHub should have this setting in place 
More information on init.tcl can be found at https://www.xilinx.com/support/answers/53090.html

