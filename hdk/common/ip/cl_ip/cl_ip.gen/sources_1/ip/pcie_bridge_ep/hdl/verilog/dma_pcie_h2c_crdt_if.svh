`ifndef IF_PCIE_DMA_H2C_CRDT_SV
`define IF_PCIE_DMA_H2C_CRDT_SV
interface dma_pcie_h2c_crdt_if #();
    logic   [511:0]             tdata;
    logic   [512/8-1:0]         tparity;
    logic                       tlast;
    logic   [512/8-1:0]         tkeep;
    logic   [63:0]              tusr;
    logic                       tvalid;
    logic   [1:0]               tch;

    logic                       crdt;
    logic   [1:0]               crdt_ch;

    modport m (
        output                      tdata,
        output                      tparity,
        output                      tlast,
        output                      tkeep,
        output                      tusr,
        output                      tvalid,
        output                      tch,

        input                       crdt,
        input                       crdt_ch
    );

    modport s (
        input                       tdata,
        input                       tparity,
        input                       tlast,
        input                       tkeep,
        input                       tusr,
        input                       tvalid,
        input                       tch,

        output                      crdt,
        output                      crdt_ch
    );

endinterface : dma_pcie_h2c_crdt_if
`endif
