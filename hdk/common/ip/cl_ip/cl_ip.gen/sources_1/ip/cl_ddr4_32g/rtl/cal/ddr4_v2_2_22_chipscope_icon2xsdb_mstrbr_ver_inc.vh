// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////
/*----------------------------------------------------------------------------
 *-----------------------------------------------------------------------------
 *   ____  ____
 *  /   /\/   /
 * /___/  \  /   Vendor: AMD
 * \   \   \/    Date Created: 2008/08/18
 *  \   \        
 *  /   /        
 * /___/   /\    
 * \   \  /  \ 
 *  \___\/\___\
 * 
 *Device: All
 *Purpose:
 *  Define Values for Verilog instatiation of icn2xsdb_mstrbr_ver
 *
 *----------------------------------------------------------------------------*/

/*-----------------------------------------------------------------------------
 *-- C O N S T A N T S
 *-----------------------------------------------------------------------------*/

`define GC_XSDB_MSI_SL_SEL_WIDTH        8   /* Slave Select Width */
`define GC_XSDB_MSI_ADDR_WIDTH          17  /* Address Width */
`define GC_XSDB_MSI_BRST_WD_LEN_WIDTH   17
`define GC_XSDB_MSI_DATA_WIDTH          16  /* Data Width */
`define GC_XSDB_MSI_BRST_CNT_WIDTH      16  /* Burst Count Width */
`define GC_XSDB_S_IPORT_WIDTH           37  /* Slave Port input interface width */

`define GC_XSDB_S_OPORT_WIDTH           17  /* Slave Port output interface width */

`define GC_XSDB_S_ADDR_WIDTH            `GC_XSDB_MSI_ADDR_WIDTH  /* Slave Addr width */
`define GC_XSDB_S_DATA_WIDTH            `GC_XSDB_MSI_DATA_WIDTH  /* Slave Data width */

`define GC_IPORT_RST_IDX                0
`define GC_IPORT_DCLK_IDX               1
`define GC_IPORT_DEN_IDX                2
`define GC_IPORT_DWE_IDX                3
`define GC_IPORT_DADDR_IDX              4
`define GC_IPORT_DI_IDX                 `GC_IPORT_DADDR_IDX+`GC_XSDB_S_ADDR_WIDTH
`define GC_OPORT_RDY_IDX                0
`define GC_OPORT_DO_IDX                 1      

`define GC_ICN_CTL_WIDTH                36
`define GC_ICN_CMD4_WIDTH               3 + `GC_XSDB_MSI_SL_SEL_WIDTH+ `GC_XSDB_MSI_BRST_WD_LEN_WIDTH
`define GC_ICN_CMD5_WIDTH               1 + `GC_XSDB_MSI_ADDR_WIDTH
`define GC_ICN_CMD6_WIDTH               `GC_XSDB_MSI_DATA_WIDTH

