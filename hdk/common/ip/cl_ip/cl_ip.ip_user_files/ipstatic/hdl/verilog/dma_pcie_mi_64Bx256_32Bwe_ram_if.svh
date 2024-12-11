`ifndef DMA_PCIE_MI_64BX256_32BWE_RAM_IF_SV
`define DMA_PCIE_MI_64BX256_32BWE_RAM_IF_SV
interface dma_pcie_mi_64Bx256_32Bwe_ram_if();
                logic   [8:0]       wadr;  // FIXME hack should be 8 bits
                logic   [1:0]       wen;
                logic   [63:0]      wpar;
                logic   [511:0]     wdat;
                logic               ren;
                logic   [8:0]       radr;  // FIXME hack should be 8 bits

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
