`ifndef IF_PCIE_DMA_DSC_IN_SV
`define IF_PCIE_DMA_DSC_IN_SV
`include "dma_defines.svh"

interface dma_pcie_dsc_in_if();
    dma_dsc_in_crd_t      crd;
    dma_dsc_block_t       dsc;

modport snk (
input  dsc,
output  crd
);

modport src (
input dsc,
output crd
);

endinterface : dma_pcie_dsc_in_if
`endif
