# Shell v1.4 Migration Document


The following documents describes the changes required when migrating your design from shell v1.3 to shell v1.4. 
The HDK build scripts have changed to reflect the new v1.4 shell’s floorplan and newer Vivado tools. It’s strongly recommended users move to these scripts. Users who have already customized v1.3 scripts should diff those with the v1.4 scripts and be sure to include all new parameters that have been added to v1.4 scripts.

1. Upgrade Vivado Tools to version 2017.4. Needs [FPGA DEVELOPER AMI 1.4 or later](../../README.md#overviewdevtools)

2. The hierarchy for CL & SH modules have changed. Now they are instantiated in  "WRAPPER_INST" Module. 
     The paths in your Build scripts, constraints &  verification components have to be updated.
 
 | v1.3 Shell | v1.4 Shell |
 |------------|------------|
 | CL/blkA/sublockB/componentC/celld/signalX | WRAPPER_INST/CL/blkA/sublockB/componentC/celld/signalX |
 | SH/blkA/sublockB/componentC/celld/signalX | WRAPPER_INST/SH/blkA/sublockB/componentC/celld/signalX |
            
3.  The  CL to Shell interface has the following additional signals. Please refer to v1.4 Shell Interface Specification for functionality.

 | Interface  | Signal Name | Width | Direction | Recommended Tie-Off | 
 |------------|-------------|-------|-----------|--------------------|
 | dma_pcis interface (BAR4)  | cl_sh_dma_wr_full | 1 | output | 1'b0 |
 | dma_pcis interface (BAR4) | cl_sh_dma_rd_full | 1 | output | 1'b0 |
 | DDR-C AXI4 CL to SH   | cl_sh_ddr_awburst | 2 | output | 2'b0 |
 | DDR-C AXI4 CL to SH   | cl_sh_ddr_arburst | 2 | output | 2'b0 |

4. If your CL is using "cl_axi_interconnect" IP which comes included with other shell IP, Please note the path changes for directory hierarchy. [CL_AXI_INTERCONNECT IP](../common/shell_stable/design/ip/cl_axi_interconnect) can be found here.

5. Upgrade to latest for [SH_DDR IP](../common/shell_v04261818/design/sh_ddr) .

6. All Xilinx IP  in your CL must to be upgraded to 2017.4 or later version. see [vivado 2017.4 release notes for recommended version](https://www.xilinx.com/support/answers/70386.html)
    
7. [ILA cores](../common/shell_v04261818/design/ip/cl_debug_bridge) need to be upgraded for 2017.4  
     Please refer to the [cl_dram_dma](../cl/examples/cl_dram_dma/design) example for ILA hookup on PCIS interface.
 
8. Please use below information to update CL pblock constraints to optimize your design in Shel v1.4.
      - Shell V1.4 is slightly larger than Shell v1.3. CL floorplan may need to be tweaked to account for the larger Shell V1.4.
        Please review pblock constriants of CL for conflicting regions.
      - Following are the interface placement changes between Shell v1.3 & v1.4
      
      
      | INTERFACE | Shell v1.3 SLR | SHELL v1.4 SLR |
      |-----------|---------------|---------------|
      | CL_SH_DDR |MID/BOTTOM SLR  | MID SLR |
      | BAR1 | MID SLR  | MID SLR |
      | PCIM | MID SLR  | MID SLR |
      | PCIS | BOTTOM SLR | BOTTOM SLR |
      | OCL | BOTTOM SLR | BOTTOM SLR |
      | DDR STAT3 | BOTTOM SLR  | BOTTOM SLR |
      | DDR STAT0  | TOP SLR | MID/BOTTOM SLR |
      | DDR STAT1 | MID SLR | MID/BOTTOM SLR |
      | SDA | BOTTOM SLR  | MID/BOTTOM SLR|

9. The following parameter is required to be set before running CL placement & routing.

      set_param hd.clockRoutingWireReduction false
