Reducing AFI load times
=======================

To support customers using multiple FPGA images in sequence, AWS strives
to minimize the time to load an Amazon FPGA image (AFI). Many of these
improvements will be available to users with no action required through
automatic improvements to Amazon systems, but customers can use AWS F2
features like caching.

Customers can view locally cached AFIs via fpga-describe-local-image,
and request AFIs be cached without affecting the AFI currently loaded on
the FPGA with the -P flag in fpga-load-local-image.

Caching recently used AFIs
--------------------------

AWS will automatically cache the most recently used AFIs on that FPGA
slot, up to the available cache size. When the cache reaches its limit,
the least recently used AFI will be removed to make room for new AFIs.
The cache will also be cleared when an FPGA slot is stopped or
terminated.

Prefetching an upcoming AFI
---------------------------

If multiple AFIs are needed for an AFI pipeline, customers will need
to prefetch AFIs into the cache to maximize performance. Prefetching an
AFI doesn't affect currently running FPGA images, so it is safe to
prefetch an AFI while the currently running AFI is processing data.
Prefetching just returns 0 without printing if the prefetch was
successful, since it doesn't change the FPGA state. If the cache is
full, prefetching an AFI will remove the least recently used AFI from
the cache.

To prefetch an AFI into the cache, use fpga-load-local-image with the -P
flag, for example:

::

   sudo fpga-load-local-image -S 0 -I agfi-0fcf87119b8e97bf3 -P

Viewing cached AFIs
-------------------

To see which AGFIs are cached on an FPGA slot, use
fpga-describe-local-image with the -M flag:

::

   sudo fpga-describe-local-image -S 0 -M
   AFI          0       agfi-01dc2520aaf357e86  loaded            0        ok               0       0x04261818
   AFIDEVICE    0       0x1d0f      0xf001      0000:00:1d.0
   ....
   Cached agfis:
      agfi-0fcf87119b8e97bf3
      agfi-01dc2520aaf357e86
