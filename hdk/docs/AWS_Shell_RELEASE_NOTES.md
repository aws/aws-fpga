# AWS Shell Release Notes

# v04261818
* Fixed AXI-L Interface Ordering.  Read requests on the AXI-L interfaces (BAR1, OCL, SDA) will not pass previous write requests.
* Increased XDMA PCIS interface timeout to 5 seconds
* Clock group A supports synchronous clocks within the group (default is clocks are synchronous)
* Added backpressure signalling to XDMA (note added signals to cl_ports.vh - **cl_sh_dma_wr_full/cl_sh_dma_rd_full**  _Note: If not required, these signals should be tied to '0'_)
* Shell update capability (Shell can be updated without requiring CL re-build)
* Added AxBURST to DDR_C interface (note added signals to cl_ports.vh - **cl_sh_ddr_awburst[1:0]/cl_sh_ddr_arburst[1:0]** _Note: Only INCR burst mode is supported so these signals must be tied to 2'b01_)
