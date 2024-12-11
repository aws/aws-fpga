`ifndef DMA_PCIE_MI_64BX2048_32BWE_RAM_IF_SV
`define DMA_PCIE_MI_64BX2048_32BWE_RAM_IF_SV
interface dma_pcie_mi_64Bx2048_32Bwe_ram_if();
                logic   [10:0]      wadr;
                logic   [1:0]       wen;
                logic   [63:0]      wpar;
                logic   [511:0]     wdat;
                logic               ren;
                logic   [10:0]      radr;

                logic   [63:0]      rpar;
                logic   [511:0]     rdat;
                logic               rsbe;
                logic               rdbe;

modport m (
                output        wadr,
                output        wen,
                output        wpar,
                output        wdat,
                output        ren,
                output        radr,

                input         rpar,
                input         rdat,
                input         rsbe,
                input         rdbe
);

modport s (
                input         wadr,
                input         wen,
                input         wpar,
                input         wdat,
                input         ren,
                input         radr,

                output        rpar,
                output        rdat,
                output        rsbe,
                output        rdbe
);
endinterface
`endif
