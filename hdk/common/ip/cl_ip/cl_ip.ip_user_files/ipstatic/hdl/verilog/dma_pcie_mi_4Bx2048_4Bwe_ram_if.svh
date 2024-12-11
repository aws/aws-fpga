`ifndef DMA_PCIE_MI_4BX2048_4BWE_RAM_IF_SV
`define DMA_PCIE_MI_4BX2048_4BWE_RAM_IF_SV

interface dma_pcie_mi_4Bx2048_4Bwe_ram_if();
        logic   [11:0]  wadr;
        logic           wen;
        logic   [7:0]   wpar;
        logic   [31:0]  wdat;   // 31:16 = used credits.  15:0= consumer index
        logic           ren;
        logic   [11:0]  radr;
        logic   [7:0]   rpar;
        logic   [31:0]  rdat;
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
