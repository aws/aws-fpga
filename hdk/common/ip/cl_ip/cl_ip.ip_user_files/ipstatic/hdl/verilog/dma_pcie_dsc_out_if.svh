`ifndef DMA_PCIE_DSC_OUT_IF_SV
`define DMA_PCIE_DSC_OUT_IF_SV
`include "dma_defines.svh"

interface dma_pcie_dsc_out_if();
    dma_dsc_out_crd_t      crd;
    dma_dsc_block_t        dsc;

modport snk (
    output       crd,
    input        dsc
);

modport src (
    input       crd,
    output      dsc
);

modport outputs (
    output       dsc
);

modport inputs (
    input        crd
);

endinterface : dma_pcie_dsc_out_if
`endif
