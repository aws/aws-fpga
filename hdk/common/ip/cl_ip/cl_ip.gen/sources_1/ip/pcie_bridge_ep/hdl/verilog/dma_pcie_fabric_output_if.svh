`ifndef IF_PCIE_DMA_FABRIC_OUTPUT_SV
`define IF_PCIE_DMA_FABRIC_OUTPUT_SV
interface dma_pcie_fabric_output_if();
logic            c2h_dsc_avail_inc_vld;
logic  [1:0]     c2h_dsc_avail_inc_chn;
logic  [7:0]     c2h_dsc_avail_inc_qid;
logic  [1:0]     c2h_dsc_avail_inc_state;
logic  [15:0]    c2h_dsc_avail_inc_num;
logic            s_axis_c2h_tstat_vld;
logic  [1:0]     s_axis_c2h_tstat_chn;
logic  [4:0]     s_axis_c2h_tstat_qid;
logic  [7:0]     s_axis_c2h_tstat;
logic  [3:0][7:0]    c2h_sts;
logic  [3:0][7:0]    h2c_sts;
logic            flr_set;
logic            flr_clr;
logic  [7:0]     flr_fnc;
logic  [4:0]     usr_irq_rvec;
logic  [7:0]     usr_irq_rfnc;
logic            usr_irq_fail;
logic            usr_irq_sent;

modport m (
output  c2h_dsc_avail_inc_vld,
output  c2h_dsc_avail_inc_chn,
output  c2h_dsc_avail_inc_qid,
output  c2h_dsc_avail_inc_state,
output  c2h_dsc_avail_inc_num,
output  s_axis_c2h_tstat_vld,
output  s_axis_c2h_tstat_chn,
output  s_axis_c2h_tstat_qid,
output  s_axis_c2h_tstat,
output  c2h_sts,
output  h2c_sts,
output  flr_set,
output  flr_clr,
output  flr_fnc,
output  usr_irq_rvec,
output  usr_irq_rfnc,
output  usr_irq_fail,
output  usr_irq_sent
);
modport s (
input  c2h_dsc_avail_inc_vld,
input  c2h_dsc_avail_inc_chn,
input  c2h_dsc_avail_inc_qid,
input  c2h_dsc_avail_inc_state,
input  c2h_dsc_avail_inc_num,
input  s_axis_c2h_tstat_vld,
input  s_axis_c2h_tstat_chn,
input  s_axis_c2h_tstat_qid,
input  s_axis_c2h_tstat,
input  c2h_sts,
input  h2c_sts,
input  flr_set,
input  flr_clr,
input  flr_fnc,
input  usr_irq_rvec,
input  usr_irq_rfnc,
input  usr_irq_fail,
input  usr_irq_sent
);
endinterface : dma_pcie_fabric_output_if
`endif
