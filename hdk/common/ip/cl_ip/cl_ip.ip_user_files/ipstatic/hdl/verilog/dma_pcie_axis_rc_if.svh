`ifndef IF_AXIS_RC_PCIE_DMA_PORT_VS
`define IF_AXIS_RC_PCIE_DMA_PORT_VS
interface dma_pcie_axis_rc_if#(DATA_WIDTH = 512, USER_WIDTH = 161)();

  wire [DATA_WIDTH-1:0]         tdata;
  wire                          tlast;
  wire [USER_WIDTH-1:0]         tuser;
  wire [DATA_WIDTH/32-1:0]      tkeep;
  wire                          tvalid;
  wire  [21:0]                  tready;

  modport m (
 
     output            tdata
    ,output            tlast
    ,output            tuser
    ,output            tkeep
    ,output            tvalid
    ,input             tready

  ); 

  modport s (
 
     input             tdata
    ,input             tlast
    ,input             tuser
    ,input             tkeep
    ,input             tvalid
    ,output            tready

  ); 

endinterface : dma_pcie_axis_rc_if
`endif // PCIE4_IF_AXIS_RC_PCIE_PORT
