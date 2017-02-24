`ifndef CL_DRAM_DMA_PKG
`define CL_DRAM_DMA_PKG
 
   interface axi_bus_t;
      logic[15:0] awid;
      logic[63:0] awaddr;
      logic[7:0] awlen;
      logic [2:0] awsize;
      logic awvalid;
      logic awready;
   
      logic[15:0] wid;
      logic[511:0] wdata;
      logic[63:0] wstrb;
      logic wlast;
      logic wvalid;
      logic wready;
         
      logic[15:0] bid;
      logic[1:0] bresp;
      logic bvalid;
      logic bready;
         
      logic[15:0] arid;
      logic[63:0] araddr;
      logic[7:0] arlen;
      logic [2:0] arsize;
      logic arvalid;
      logic arready;
         
      logic[15:0] rid;
      logic[511:0] rdata;
      logic[1:0] rresp;
      logic rlast;
      logic rvalid;
      logic rready;
   endinterface


   interface cfg_bus_t;
      logic [31:0] addr;
      logic [31:0] wdata;
      logic wr;
      logic rd;
      logic ack;
      logic[31:0] rdata;
   endinterface

   interface scrb_bus_t;
      logic [63:0] addr;
      logic [2:0] state;
      logic enable;
      logic done;
   endinterface

`endif //CL_DRAM_DMA_PKG
