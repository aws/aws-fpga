`ifndef iF_AXIS_CC_PCIE_DMA_PORT_VS
`define iF_AXIS_CC_PCIE_DMA_PORT_VS
interface dma_pcie_axis_cc_if#(DATA_WIDTH = 512, USER_WIDTH = 81)();

  wire [DATA_WIDTH-1:0]     tdata;
  wire [USER_WIDTH-1:0]     tuser;
  wire                      tlast;
  wire [DATA_WIDTH/32-1:0]  tkeep;
  wire                 tvalid;
  wire                 tready;

  modport s (
    
    input              tdata
   ,input              tuser
   ,input              tlast
   ,input              tkeep
   ,input              tvalid
   ,output             tready

  );

  modport m (

    output             tdata
   ,output             tuser
   ,output             tlast
   ,output             tkeep
   ,output             tvalid
   ,input              tready

  );
  
endinterface : dma_pcie_axis_cc_if
`endif // iF_AXIS_CC_PCIE_PORT_VS
