# Release notes for Xilinx SDAccel on AWS FPGA

## Pre-release version:

### Known Restrictions

* Single AFI per each FPGA: Runtime environment would not be able to switch AFIs without restarting
* Four DRAM controllers configuration only. Designs with less DRAM controllers is not supported
* SysMon values (Voltage level reads, temperature read, fan control, and max current) report nominal values and not the actual values in the hardware. So getDeviceInfo() will not return proper values for the above metrics.
* There is no support for hot reset API.
* There is no support for preserving the DRAM content between different loads to the same FPGA card
* The instance to FPGA kernel write function support single 32-bit word only, it doesn't support write-combine or 64Byte range

