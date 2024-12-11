`ifndef IF_PCIE_DMA_GIC_SV
`define IF_PCIE_DMA_GIC_SV
interface dma_pcie_gic_if();
    logic [6:0] interrupt;
modport m (
    output interrupt
);
modport s (
    input interrupt
);

endinterface : dma_pcie_gic_if
`endif
