`ifndef DMA_PCIE_MI_DSC_CPLD_IF_SV
`define DMA_PCIE_MI_DSC_CPLD_IF_SV
interface dma_pcie_mi_dsc_cpld_if();
        logic   [9:0]   wadr; // 10 bits for MULTQ C2H
        logic   [7:0]   wen;
        logic   [63:0]  wpar;
        logic   [511:0] wdat;
        logic           ren;
        logic   [9:0]   radr; // 10 bits for MULTQ C2H
        logic   [63:0]  rpar;
        logic   [511:0] rdat;
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
        modport s_outputs (
                output  wadr,
                output  wen,
                output  wpar,
                output  wdat,
                output  ren,
                output  radr
        );

        modport m_outputs (
                output  rpar,
                output  rdat,
                output  rsbe,
                output  rdbe
         );

        modport s_inputs (
                input   wadr,
                input   wen,
                input   wpar,
                input   wdat,
                input   ren,
                input   radr
        );

        modport m_inputs (
                input   rpar,
                input   rdat,
                input   rsbe,
                input   rdbe
        );
endinterface
`endif
