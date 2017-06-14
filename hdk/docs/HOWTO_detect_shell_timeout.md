
# How to detect a shell timeout has occured

* Shell-CL interface timeouts can be detected by checking for non-zero counter metrics using this command:  
```
$sudo fpga-describe-local-image -S 0 -M
AFI          0       none                    cleared           1        ok               0       0x04151701
AFIDEVICE    0       0x1d0f      0x1042      0000:00:1d.0
sdacl-slave-timeout=0
virtual-jtag-slave-timeout=0
ocl-slave-timeout=0
bar1-slave-timeout=0
dma-pcis-timeout=0
pcim-range-error=0
pcim-axi-protocol-error=0
pcim-axi-protocol-4K-cross-error=0
pcim-axi-protocol-bus-master-enable-error=0
pcim-axi-protocol-request-size-error=0
pcim-axi-protocol-write-incomplete-error=0
pcim-axi-protocol-first-byte-enable-error=0
pcim-axi-protocol-last-byte-enable-error=0
pcim-axi-protocol-bready-error=0
pcim-axi-protocol-rready-error=0
pcim-axi-protocol-wchannel-error=0
sdacl-slave-timeout-addr=0x0
sdacl-slave-timeout-count=0
virtual-jtag-slave-timeout-addr=0x0
virtual-jtag-slave-timeout-count=0
ocl-slave-timeout-addr=0x8001
ocl-slave-timeout-count=0
bar1-slave-timeout-addr=0x2001
bar1-slave-timeout-count=0
dma-pcis-timeout-addr=0x0
dma-pcis-timeout-count=0
pcim-range-error-addr=0x0
pcim-range-error-count=0
pcim-axi-protocol-error-addr=0x0
pcim-axi-protocol-error-count=0
pcim-write-count=0
pcim-read-count=0
DDR0
   write-count=0
   read-count=0
DDR1
   write-count=0
   read-count=0
DDR2
   write-count=0
   read-count=0
DDR3
   write-count=0
   read-count=0
```
