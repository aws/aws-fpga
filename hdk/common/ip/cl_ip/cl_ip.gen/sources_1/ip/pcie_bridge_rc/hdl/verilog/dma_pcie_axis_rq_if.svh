`ifndef IF_AXIS_RQ_PCIE_DMA_PORT_SV
`define IF_AXIS_RQ_PCIE_DMA_PORT_SV
interface dma_pcie_axis_rq_if#(DATA_WIDTH = 512, USER_WIDTH = 137)();

  wire [DATA_WIDTH-1:0]    tdata;
  wire                     tlast;
  wire [USER_WIDTH-1:0]    tuser;
  wire [DATA_WIDTH/32-1:0]   tkeep;
  wire                 tvalid;
  wire                 tready;

  modport s (

    input              tdata
   ,input              tlast
   ,input              tuser
   ,input              tkeep
   ,input              tvalid
   ,output             tready

  );

  modport m (

    output             tdata
   ,output             tlast
   ,output             tuser
   ,output             tkeep
   ,output             tvalid
   ,input              tready

  );

endinterface : dma_pcie_axis_rq_if
`endif // IF_AXIS_RQ_PCIE_DMA_PORT_SV
