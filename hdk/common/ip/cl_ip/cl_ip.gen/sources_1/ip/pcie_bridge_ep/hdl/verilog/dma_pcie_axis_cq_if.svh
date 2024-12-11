`ifndef IF_AXIS_CQ_PCIE_DMA_PORT_SV
`define IF_AXIS_CQ_PCIE_DMA_PORT_SV
interface dma_pcie_axis_cq_if#(DATA_WIDTH = 512, USER_WIDTH = 183)();

  wire [DATA_WIDTH-1:0]         tdata;
  wire [USER_WIDTH-1:0]         tuser;
  wire                          tlast;
  wire [DATA_WIDTH/32-1:0]      tkeep;
  wire                 tvalid;
  wire [21:0]          tready;
  
  modport m (

    output             tdata 
   ,output             tuser 
   ,output             tlast 
   ,output             tkeep 
   ,output             tvalid 
   ,input              tready 
  
  );

  modport s (

    input              tdata 
   ,input              tuser 
   ,input              tlast 
   ,input              tkeep 
   ,input              tvalid 
   ,output             tready 
  
  );

endinterface : dma_pcie_axis_cq_if
`endif // IF_AXIS_CQ_PCIE_DMA_PORT_SV
