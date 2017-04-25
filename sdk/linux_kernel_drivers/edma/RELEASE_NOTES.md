# EDMA Driver Release Notes 

This is the first release of the EDMA driver. This driver is still under development and performance may not be achieving maximal potential.

This is a Linux kernel driver only

## Supported Distributions
- Amazon Linux
- Centos 7.x
- More distributions will be tested later.

## Known Issues
- Reads, in rare cases, might lead to a software hang. To avoid the hang, please do one of the following:
 - The address being read is 4K aligned. i.e. bits 0:11 are 0. Any read size is supported.
 - Reading from an address that is not 4K aligned should not cross to the next 4K page.

## Expected performance
- For smaller block size write performance is around 10MByte/s, read performance is around 150MByte/s
- For a block size of 4MByte, the expected performance is around 1.5GByte/s for write and 1.5GByte/s for read.
- To increase performance for larger block sizes the module parameter of single_transaction_size should be increased. 
-- Note that **single_transaction_size * edma_queue_depth should** should be greater than **transient_buffer_size**.
