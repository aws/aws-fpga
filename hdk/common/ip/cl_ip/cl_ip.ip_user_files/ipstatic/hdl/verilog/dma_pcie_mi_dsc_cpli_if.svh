`ifndef DMA_PCIE_MI_DSC_CPLI_IF_SV
`define DMA_PCIE_MI_DSC_CPLI_IF_SV
`include "dma_defines.vh"
interface dma_pcie_mi_dsc_cpli_if();
        logic   [9:0]   wadr;  // 10 bits for MULTQ C2H
        logic   [7:0]   wen;
        logic   [3:0]  wpar;
        logic   [`CPLI_WIDTH-1:0] wdat;
        logic           ren;
        logic   [9:0]   radr;  // 10 bits for MULTQ C2H
        logic   [3:0]  rpar;
        logic   [`CPLI_WIDTH-1:0] rdat;
        logic           rsbe;
        logic           rdbe;

        modport  m (
                output  wadr,
                output  wen,
                output  wpar,
                output  wdat,
                output  ren,
                output  radr,
                input   rpar,
                input   rdat,
                input   rsbe,
                input   rdbe
         );
        modport  s (
                input   wadr,
                input   wen,
                input   wpar,
                input   wdat,
                input   ren,
                input   radr,
                output  rpar,
                output  rdat,
                output  rsbe,
                output  rdbe
         );
endinterface
`endif
