# Release notes for Xilinx SDAccel on AWS FPGA

## Pre-release version

### Known Restrictions

* Single AFI per each FPGA: Runtime environment would not be able to switch AFIs without restarting
* Four DRAM controllers configuration only. Designs with less DRAM controllers is not supported
* SysMon values (Voltage level reads, temperature read, fan control, and max current) report nominal values and not the actual values in the hardware

