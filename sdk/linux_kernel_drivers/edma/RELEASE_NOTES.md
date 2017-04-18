# EDMA Driver Release notes 

This is first release of the EDMA driver. This driver is still under development and performance may not be achieving maximal potential.

This is a Linux kernel driver only

## Supported Distributions
- Amazon Linux
- Centos 7.x
- More ditributions will be tested later.

## Expected performance
- For smaller block size write performance is around 10MByte/s, read performance is around 150MByte/s
- For a block size of 64KByte the expected performance is around 80MByte/s for write and 1GByte/s for read.
