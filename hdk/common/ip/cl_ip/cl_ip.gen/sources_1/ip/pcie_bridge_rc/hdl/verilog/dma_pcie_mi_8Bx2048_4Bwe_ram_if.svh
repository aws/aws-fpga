`ifndef DMA_PCIE_MI_8BX2048_4BWE_RAM_IF_SV
`define DMA_PCIE_MI_8BX2048_4BWE_RAM_IF_SV

interface dma_pcie_mi_8Bx2048_4Bwe_ram_if();
        logic   [11:0]  wadr; // 1024 H2C Qs, 1024 C2H Qs
        logic    [1:0]  wen;
        logic   [7:0]   wpar;
        logic   [63:0]  wdat;  // 63:0 writeback base address
        logic           ren;
        logic   [11:0]   radr;
        logic   [7:0]   rpar;
        logic   [127:0]  rdat;
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
