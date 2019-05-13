# Reducing AFI load times

To support customers using multiple FPGA images in sequence, AWS strives to minimize the time to load an Amazon FPGA image (AFI). 
Many of these improvements will be available to users with no action required through automatic improvements to Amazon systems, but customers can use AWS F1 features like caching and [data retention](data_retention.md) to maximize AFI pipeline performance. 
Data retention (the -D flag) is especially valuable because it significantly reduces AFI load times, and can eliminate the time consumption of copying and reloading data from FPGA DRAM.

Customers can view locally cached AFIs via fpga-describe-local-image, and request AFIs be cached without actually modifying the FPGA with the -p flag in fpga-describe-local-image.

## Caching recently used AFIs
AWS will automatically cache the most recent 16 AFIs used on that FPGA slot. If more than 16 AFIs are loaded, the least recently used AFI will be removed from the cache. The cache will also be cleared when an FPGA slot is cleared with fpga-clear-local-image, or when an instance is stopped or terminated.

## Prefetching an upcoming AFI
If more than 16 AFIs are needed for an AFI pipeline, customers will need to prefetch AFIs into the cache to maximize performance. Prefetching an AFI doesn't affect currently running FPGA images, so it is safe to prefetch an AFI while the currently running AFI is processing data. Prefetching just returns 0 without printing if the prefetch was successful, since it doesn't change the FPGA state. If the cache is already full of 16 AFIs, prefetching an AFI will remove the least recently used AFI from the cache.

To prefetch an AFI into the cache, use fpga-load-local-image with the -P flag, for example:
```
sudo fpga-load-local-image -S 0 -I agfi-0fcf87119b8e97bf3 -P
```

## Viewing cached AFIs
To see which AGFIs are cached on an FPGA slot, use fpga-describe-local-image with the -M flag:

```
sudo fpga-describe-local-image -S 0 -M
AFI          0       agfi-01dc2520aaf357e86  loaded            0        ok               0       0x04261818
AFIDEVICE    0       0x1d0f      0xf001      0000:00:1d.0
....
Cached agfis:
   agfi-0fcf87119b8e97bf3
   agfi-01dc2520aaf357e86
```

## Other load time considerations

To minimize AFI load time, in addition to caching the AGFI and using data retention (-D flag), also ensure:

* The AFI being loaded is on the same shell as the previous AFI
* The AFI being loaded is using a new shell, especially shell 1.4 or above
* The FPGA image tools are up to date from Github
