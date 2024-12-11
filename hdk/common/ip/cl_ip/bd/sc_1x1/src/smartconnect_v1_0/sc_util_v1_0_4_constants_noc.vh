`ifndef sc_util_v1_0_4_constants_noc_GLOBAL_CONSTANTS
`define sc_util_v1_0_4_constants_noc_GLOBAL_CONSTANTS
parameter integer NOC_MAX_SCHED_LEN =         256;
parameter integer NOC_MAX_TKN_WIDTH =         256;
parameter integer NOC_MAX_RTR_ADDR_WIDTH =           8;
parameter integer NOC_PORT_EJECT =           0;
parameter integer NOC_PORT_ASCEND =           1;
parameter integer NOC_PORT_DESCEND =           2;
parameter integer NOC_PORT_THROUGH =           3;
parameter integer NOC_TOKEN_THROUGH =           0;
parameter integer NOC_TOKEN_ASCEND =           1;
parameter integer NOC_TOKEN_DESCEND =           2;
parameter integer NOC_CH_R =           0;
parameter integer NOC_CH_AR =           1;
parameter integer NOC_CH_AW =           2;
parameter integer NOC_CH_W =           3;
parameter integer NOC_CH_WIDTH =           2;
parameter integer K_AXI_RESP_OKAY =           0;
parameter integer K_AXI_RESP_EXOKAY =           1;
parameter integer K_AXI_RESP_SLVERR =           2;
parameter integer K_AXI_RESP_DECERR =           3;
parameter integer K_MAX_NUM_MNOC = 16;
parameter integer K_MAX_NUM_SNOC = 16;
`endif
