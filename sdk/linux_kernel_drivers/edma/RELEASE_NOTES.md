# EDMA Driver Release notes 

This is a pre-alpha release of the EDMA driver. This driver is still under development and operformance is not yet optimal.

## Supported distributions
- Amazon Linux
- Centos
- More ditributions will be tested later.

## Known Issues
- The EDMA driver crashes when many writes are issued without being followed by fsync.

## Expected performance
- For smaller block size write performance is around 10MB/s, read performance is around 150MB/s
- for a block size of 64k the expected performance is around 80MB/s for write and 1GB/s for read.
