`ifndef CL_DRAM_DMA_DEFINES
`define CL_DRAM_DMA_DEFINES

//Put module name of the CL design here.  This is used to instantiate in top.sv
`define CL_NAME cl_dram_dma

//Highly recommeneded.  For lib FIFO block, uses less async reset (take advantage of
// FPGA flop init capability).  This will help with routing resources.
`define FPGA_LESS_RST

`define SH_SDA
//uncomment below to make SH and CL async
`define SH_CL_ASYNC

`endif

