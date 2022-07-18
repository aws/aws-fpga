# Overview:

This directory contains the FIO benchmarking tool and FIO scripts to run IO benchmarks and stress testing on the FPGA DMA devices.

Since the FPGA DMA drivers expose character devices, FIO can be used for stress testing, R/W data verification, etc.  

FIO is found on github here:
	https://github.com/axboe/fio

To get FIO to work with the FPGA DMA devices, a small and temporary change was made to have FIO 'don't care' about the zero length DMA 
character devices.  Other than that, FIO works 'as-is' on the FPGA DMA devices.

# Getting started:

These steps assume that you are going to run the FPGA DMA benchmark tests on an EC2 F1 instance, have already cloned the aws-fpga GitHub repo, and are using the 1.3.5 (or later) aws-fpga GitHub release.

## Initial setup

0. sudo su

For simplicity, we're using root access throughout these steps because root access is needed to open the character devices files in later steps.  'sudo <cmd>' may be used instead if preferred when root access is required.

## Install and build FIO

```
cd $SDK_DIR/tests/fio_dma_tools/scripts
./fio_install.py <install_dir>
```

Where <install_dir> is the directory that will be created for the FIO build.  For convenience, a soft-link to the fio executable will be automatically created in the $SDK_DIR/tests/fio_dma_tools/scripts directory. 

## Load AGFI

Load the cl-dram-dma AGFI and force a re-load of the shell to ensure the FPGA is in a clean state for DMA benchmarking.

```
fpga-load-local-image -S 0 -I <cl-dram-dma AGFI> -F
```

## Load DMA Driver

Load the XDMA driver in an interrupt or polled mode.  In the verify and benchmark steps below, we are using the XDMA driver.

```
insmod $SDK_DIR/linux_kernel_drivers/xdma/xdma.ko
```

-or-

```
insmod $SDK_DIR/linux_kernel_drivers/xdma/xdma.ko poll_mode=1 
```

## Run DMA verify test

Verify DMA IOs are working as expected, assuming the XDMA driver has been loaded.

```
./fio xdma_4-ch_4-1M_verify.fio
echo $?  
```

`The above step should report 0 for the verify exit status. If non-zero 'fpga-describe-local-image -S 0 -M' may report errors such as dma-pcis-timeouts`

## Run DMA benchmark tests

### Write benchmark 

```
./fio xdma_4-ch_4-1M_write.fio
```

```
XDMA Write Results:

2xl int mode: 11.4GB/s

    WRITE: bw=10.7GiB/s (11.4GB/s), 2727MiB/s-2758MiB/s (2859MB/s-2892MB/s), io=64.0GiB (68.7GB), run=5940-6009msec

2xl poll mode: 11.5GB/s

    WRITE: bw=10.7GiB/s (11.5GB/s), 2748MiB/s-2755MiB/s (2882MB/s-2888MB/s), io=64.0GiB (68.7GB), run=5948-5962msec
```

### Read benchmark 

```
./fio xdma_4-ch_4-1M_read.fio
```

```
XDMA Read Results:

2xl int mode: 12.3GB/s

    READ: bw=11.4GiB/s (12.3GB/s), 2921MiB/s-2977MiB/s (3063MB/s-3121MB/s), io=64.0GiB (68.7GB), run=5504-5609msec

2xl poll mode: 12.8GB/s

    READ: bw=11.9GiB/s (12.8GB/s), 3048MiB/s-3054MiB/s (3196MB/s-3202MB/s), io=64.0GiB (68.7GB), run=5365-5376msec
```

# FAQ

## What are the FIO config file naming conventions?

The FIO config file naming conventions are: 

```
<xdma>_<# DMA channels>_<# FIO workers>-<IO size>_<verify | write | read>.fio
	
	'# DMA channels' is 4 DMA channels in these sample FIO config files 
	'# FIO workers' is 4 concurrent FIO worker processes to drive the 4 DMA channels 
	'IO size' is the pwrite/pread user buffer size (that may be segmented by the XDMA driver into single_transaction_size DMA IO segments).
```
	
## What is the benefit of using `poll_mode`?

The DMA verify and benchmark tests can be run in interrupt or polled descriptor completion modes (see 'poll_mode=1' in the 'Load DMA Driver' step).  Polled completion mode allows the smaller IO sizes to reach a significantly greater level of performance due to the reduction in per-IO system overhead (e.g. eliminates interrupts and context switching).  

To see the performance difference in interrupt and polled modes using smaller IO sizes, the following FIO scripts are provided:

```
XDMA:
./fio xdma_4-ch_4-X_write.fio
./fio xdma_4-ch_4-X_read.fio
	
```
The above '4-X' scripts include 4 channel group reporting for a set of blocksizes {4KB, 8KB, 16KB, 32KB, 64KB, 256KB, 1MB, 2MB}

## What is the XDMA driver test methodology?

The XDMA driver is benchmarked in interrupt and polled modes. FIO was configured for pwrite/pread (ioengine=psync) and to allocate memory using mmap (iomem=mmap).  When using malloc instead of mmap, throughput becomes less consistent for the larger IO sizes. To maximize DMA IO concurrency, 4 parallel FIO workers each drive their own DMA channel to their own 16GB section of the 64GB FPGA DDR.

## How did we capture the above XDMA FIO performance metrics?

At the end of the test, FIO will report the individual worker (per DMA channel) results and the aggregated results for all workers in the group (e.g. 'Run status group 0 (all jobs)').  The aggregated results are the results posted above in 'Results' for the 'Run DMA benchmark tests' step.
   
## How do I use a different DMA IO size?

To use a different DMA IO size, the blocksize can be changed within the "*.fio" files (e.g. 'bs=256k').  New "*.fio" config files may be easily created, and this is `recommended` for consistency with file naming conventions.

### Quick change to the DMA IO blocksize example

To make a quick and non-permanent change to any of the FIO parameters within a FIO config file, use the `--showcmd` option to show the full FIO command line that would be executed using the given FIO config file:

```
./fio --showcmd xdma_4-ch_4-1M_write.fio
```

#### Note the blocksize "--bs=1m"

```
./fio --allow_file_create=0 --ioengine=psync --mem=mmap --filesize=64g --bs=1m --rate_min=1m --name=w1 --size=16g --offset=0 --rw=write --filename=/dev/xdma0_h2c_0 --name=w2 --size=16g --offset=16g --rw=write --filename=/dev/xdma0_h2c_1 --name=w3 --size=16g --offset=32g --rw=write --filename=/dev/xdma0_h2c_2 --name=w4 --size=16g --offset=48g --rw=write --filename=/dev/xdma0_h2c_3
```

#### Now run this command with the changed blocksize "--bs=256k"

```
./fio --allow_file_create=0 --ioengine=psync --mem=mmap --filesize=64g --bs=256k --rate_min=1m --name=w1 --size=16g --offset=0 --rw=write --filename=/dev/xdma0_h2c_0 --name=w2 --size=16g --offset=16g --rw=write --filename=/dev/xdma0_h2c_1 --name=w3 --size=16g --offset=32g --rw=write --filename=/dev/xdma0_h2c_2 --name=w4 --size=16g --offset=48g --rw=write --filename=/dev/xdma0_h2c_3
```

#### Blocksize specified on the command line, use FIO config file for other parameters

As an alternative to the above, a variable blocksize (or other parameters) may be specified on the command line as long as they are not present in the FIO config file.  Any parameters that are present in the FIO config file will override command line options that may be specified.  For example, assuming we have created a new FIO config file called `xdma_4-ch_4_var_write.fio` for a 4 DMA channel, 4 write worker, and variable DMA IO size.  The blocksize parameter in the FIO config file has been removed so we can vary the blocksize via the command line:

```
./fio --blocksize=128k xdma_4-ch_4_var_write.fio
```
	
## FIO is very useful and configurable, how do I learn about the other supported options?

Please see this [link](https://github.com/axboe/fio/blob/master/HOWTO.rst) for the full FIO command set.    


