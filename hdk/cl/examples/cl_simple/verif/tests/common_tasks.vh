// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task automatic sys_init(
                        ref int error_count
                       );
   begin
      logic [63:0]  pf0_bar0_addr;
      logic [63:0]  pf0_bar2_addr;
      logic [63:0]  pf0_bar4_addr;

      logic [63:0]  pf1_bar0_addr;
      logic [63:0]  pf1_bar2_addr;
      logic [63:0]  pf1_bar4_addr;

      logic [63:0]  pf2_bar0_addr;
      logic [63:0]  pf2_bar2_addr;
      logic [63:0]  pf2_bar4_addr;

      bit           check_msix;

      logic [31:0]  read_data;

      tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;

      if ($test$plusargs("NO_MSIX")) begin
         check_msix = 1'b0;
      end else begin
         check_msix = 1'b1;
      end

`ifdef VENOM
      // Set up Dom0 Mgmt BARs
      //   BAR0 – 64K – Dom0 Management
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
         pf0_bar0_addr = 64'h0000_0080_0001_0000; // 64k
      end
`endif

`ifdef VENOM_CL
 `ifndef NO_XDMA
      // Set up DomU App BARs
      //   BAR0 –  32M – UDMA
      //   BAR2 –  64K – xDMA
      //   BAR4 – 128M – Application
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
         pf0_bar0_addr = 64'h0000_0020_0200_0000; // 32M
      end
      if (!$value$plusargs("PF0_BAR2=%h", pf0_bar2_addr)) begin
         pf0_bar2_addr = 64'h0000_0020_0401_0000; // 64k
      end
      if (!$value$plusargs("PF0_BAR4=%h", pf0_bar4_addr)) begin
         pf0_bar4_addr = 64'h0000_0020_0800_0000; // 128M
      end

      // Set up DomU Mgmt BARs
      //   BAR0 – 16K – Mailbox 
      //   BAR2 – 16K – Chipscope/Debug
      if (!$value$plusargs("PF1_BAR0=%h", pf1_bar0_addr)) begin
         pf1_bar0_addr = 64'h0000_0040_0000_4000; // 16k
      end
      if (!$value$plusargs("PF1_BAR2=%h", pf1_bar2_addr)) begin
         pf1_bar2_addr = 64'h0000_0040_0000_c000; // 16k
      end

      // Set up Dom0 Mgmt BARs
      //   BAR0 – 64K – Dom0 Management
      //   BAR2 –  4K – Mailbox 
      if (!$value$plusargs("PF2_BAR0=%h", pf2_bar0_addr)) begin
         pf2_bar0_addr = 64'h0000_0080_0001_0000; // 64k
      end
      if (!$value$plusargs("PF2_BAR2=%h", pf2_bar2_addr)) begin
         pf2_bar2_addr = 64'h0000_0080_0002_1000; // 4k
      end
 `else
      // Set up DomU App BARs
      //   BAR0 – 128G – CL
      //   BAR2 –   4K – MSI-X table 
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
//         pf0_bar0_addr = 64'h0000_0020_0000_0000; // 128G
// DEBUG: For now, use 128M
         pf0_bar0_addr = 64'h0000_0020_0800_0000; // 128M
      end
      if (!$value$plusargs("PF0_BAR2=%h", pf0_bar2_addr)) begin
         pf0_bar2_addr = 64'h0000_0040_0000_1000; // 4k
      end

      // Set up DomU Mgmt BARs
      //   BAR0 – 4K – Mailbox 
      //   BAR2 – 4K – MSI-X table 
      if (!$value$plusargs("PF1_BAR0=%h", pf1_bar0_addr)) begin
         pf1_bar0_addr = 64'h0000_0060_0000_1000; // 4k
      end
      if (!$value$plusargs("PF1_BAR2=%h", pf1_bar2_addr)) begin
         pf1_bar2_addr = 64'h0000_0060_0000_3000; // 4k
      end

      // Set up Dom0 Mgmt BARs
      //   BAR0 – 64K – Dom0 Management
      //   BAR2 –  4K – MSI-X table 
      //   BAR4 –  4K – Mailbox 
      if (!$value$plusargs("PF2_BAR0=%h", pf2_bar0_addr)) begin
         pf2_bar0_addr = 64'h0000_0080_0001_0000; // 64k
      end
      if (!$value$plusargs("PF2_BAR2=%h", pf2_bar2_addr)) begin
         pf2_bar2_addr = 64'h0000_0080_0002_1000; // 4k
      end
      if (!$value$plusargs("PF2_BAR4=%h", pf2_bar4_addr)) begin
         pf2_bar4_addr = 64'h0000_0080_0002_3000; // 4k
      end
 `endif
`endif

`ifdef TOP_CL
      // Set up DomU App BARs
      //   BAR0 – 128G – CL
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
//         pf0_bar0_addr = 64'h0000_0020_0000_0000; // 128G
// DEBUG: For now, use 128M
         pf0_bar0_addr = 64'h0000_0020_0800_0000; // 128M
      end
`endif

`ifdef DEV_TOP_CL
      // Set up DomU Mgmt BARs
      //   BAR0 – 128K – Mailbox / App
      //   BAR2 –   4K – MSI-X table
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
         pf0_bar0_addr = 64'h0000_0020_0002_0000; // 128k
      end
      if (!$value$plusargs("PF0_BAR2=%h", pf0_bar2_addr)) begin
         pf0_bar2_addr = 64'h0000_0040_0000_1000; // 4k
      end

      // Set up Dom0 Mgmt BARs
      //   BAR0 – 64K – Mgmt
      //   BAR2 –  4K – MSI-X table
      //   BAR4 –  4K – Mailbox
      if (!$value$plusargs("PF1_BAR0=%h", pf1_bar0_addr)) begin
         pf1_bar0_addr = 64'h0000_0060_0001_0000; // 64k
      end
      if (!$value$plusargs("PF1_BAR2=%h", pf1_bar2_addr)) begin
         pf1_bar2_addr = 64'h0000_0060_0002_1000; // 4k
      end
      if (!$value$plusargs("PF1_BAR4=%h", pf1_bar4_addr)) begin
         pf1_bar4_addr = 64'h0000_0060_0002_3000; // 4k
      end
`endif

`ifdef MINOTAUR
      // Set up Dom0 Mgmt BARs
      //   BAR0 – 64K – Dom0 Management
      if (!$value$plusargs("PF0_BAR0=%h", pf0_bar0_addr)) begin
         pf0_bar0_addr = 64'h0000_0080_0001_0000; // 64k
      end
`endif


`ifdef VENOM
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end
`endif

`ifdef VENOM_CL
 `ifndef NO_XDMA
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf0_bar2_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         config_bar(.bar_num(4), .bar_addr(pf0_bar4_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end

      // Read Device/Vendor ID register for PF1
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS_PF1));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf1_bar0_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf1_bar2_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
      end

      // Read Device/Vendor ID register for PF2
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS_PF2));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf2_bar0_addr), .comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf2_bar2_addr), .comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
      end
 `else
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf0_bar2_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end

      // Read Device/Vendor ID register for PF1
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS_PF1));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf1_bar0_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf1_bar2_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
      end

      // Read Device/Vendor ID register for PF2
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS_PF2));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf2_bar0_addr), .comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf2_bar2_addr), .comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
         config_bar(.bar_num(4), .bar_addr(pf2_bar4_addr), .comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS_PF2), .error_count(error_count));
      end
 `endif
`endif

`ifdef TOP_CL
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end
`endif

`ifdef DEV_TOP_CL
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf0_bar2_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end

      // Read Device/Vendor ID register for PF1
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS_PF1));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf1_bar0_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         config_bar(.bar_num(2), .bar_addr(pf1_bar2_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         config_bar(.bar_num(4), .bar_addr(pf1_bar4_addr), .comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS_PF1), .error_count(error_count));
      end
`endif

`ifdef MINOTAUR
      // Read Device/Vendor ID register for PF0
      cfg_reg_read(.reg_addr(12'h000), .read_data(read_data), .comp_id(EP_BUS_DEV_FNS));
      if (read_data[15:0] == 16'h1d0f) begin
         // Configure BARs
         config_bar(.bar_num(0), .bar_addr(pf0_bar0_addr), .comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
         // Set MPS, BusMaster, MemEnable
         config_pf(.comp_id(EP_BUS_DEV_FNS), .error_count(error_count));
      end
`endif

      if (check_msix == 1'b1) begin
         msix_init(.error_count(error_count));
      end
   end
endtask


task automatic msix_init(
                         ref int  error_count
                        );
   begin
      logic [63:0]  pf0_msix_addr;
      logic [63:0]  pf1_msix_addr;
      logic [63:0]  pf2_msix_addr;

      logic [31:0]  pf0_msix_data;
      logic [31:0]  pf1_msix_data;
      logic [31:0]  pf2_msix_data;

      bit           pf0_msix_mask;
      bit           pf1_msix_mask;
      bit           pf2_msix_mask;

      logic [7:0]   max_vector;

      // Check for MSIX_ADDR values
      if (!$value$plusargs("PF0_MSIX_ADDR=0x%x", pf0_msix_addr)) begin
         pf0_msix_addr = 64'h7357_0000_0000_0000;
      end
      if (!$value$plusargs("PF1_MSIX_ADDR=0x%x", pf1_msix_addr)) begin
         pf1_msix_addr = 64'h7357_0001_0001_0000;
      end
      if (!$value$plusargs("PF2_MSIX_ADDR=0x%x", pf2_msix_addr)) begin
         pf2_msix_addr = 64'h7357_0002_0002_0000;
      end

      // Check for MSIX_DATA values
      if (!$value$plusargs("PF0_MSIX_DATA=0x%x", pf0_msix_data)) begin
         pf0_msix_data = 32'hda7a_0000;
      end
      if (!$value$plusargs("PF1_MSIX_DATA=0x%x", pf1_msix_data)) begin
         pf1_msix_data = 32'hda7a_0100;
      end
      if (!$value$plusargs("PF2_MSIX_DATA=0x%x", pf2_msix_data)) begin
         pf2_msix_data = 32'hda7a_0200;
      end

      // Check for MSIX_MASK values
      if (!$value$plusargs("PF0_MSIX_MASK=%d", pf0_msix_mask)) begin
         pf0_msix_mask = 1'b0;
      end
      if (!$value$plusargs("PF1_MSIX_MASK=%d", pf1_msix_mask)) begin
         pf1_msix_mask = 1'b0;
      end
      if (!$value$plusargs("PF2_MSIX_MASK=%d", pf2_msix_mask)) begin
         pf2_msix_mask = 1'b0;
      end

      if (!$value$plusargs("NUM_CL_MSIX_VECTORS=%d", max_vector)) begin
         max_vector = 8'h0;
      end

      // Configure MSI-X
      for (logic [7:0] vector_num = 8'h00; vector_num < max_vector; vector_num = vector_num + 8'h01) begin
         // Report vector number in : addr[15:8], data[7:0]
         config_msix(.comp_id(EP_BUS_DEV_FNS), .addr({pf0_msix_addr[63:16], vector_num, pf0_msix_addr[7:0]}), .data({pf0_msix_data[31:8], vector_num}), .mask(pf0_msix_mask), .vector_num(vector_num), .error_count(error_count));
`ifndef NO_XDMA
         // Map User IRQs to Vectors
         map_user_irq(.comp_id(EP_BUS_DEV_FNS), .irq_num(vector_num), .vector_num(vector_num), .error_count(error_count));
         // Enable User IRQs
         enable_user_irq(.comp_id(EP_BUS_DEV_FNS), .irq_num(vector_num), .error_count(error_count));
`endif
      end
`ifdef NO_XDMA
      config_msix(.comp_id(EP_BUS_DEV_FNS_PF1), .addr(pf1_msix_addr), .data(pf1_msix_data), .mask(pf1_msix_mask), .error_count(error_count));
      config_msix(.comp_id(EP_BUS_DEV_FNS_PF2), .addr(pf2_msix_addr), .data(pf2_msix_data), .mask(pf2_msix_mask), .error_count(error_count));
`endif
   end
endtask


task automatic config_bar(
                          input int    bar_num,
                          logic [63:0] bar_addr,
                          logic [15:0] comp_id,
                          ref int      error_count      
                         );
   begin
      if (bar_num == 0) begin
         cfg_reg_write(.reg_addr(12'h010), .write_data(bar_addr[31:0]), .comp_id(comp_id));
         cfg_reg_write(.reg_addr(12'h014), .write_data(bar_addr[63:32]), .comp_id(comp_id));
         cfg_reg_read_check(.reg_addr(12'h010), .expected_data(bar_addr[31:0]), .data_mask(32'hffff_fff0), .comp_id(comp_id), .error_count(error_count));
         cfg_reg_read_check(.reg_addr(12'h014), .expected_data(bar_addr[63:32]), .comp_id(comp_id), .error_count(error_count));
      end else if (bar_num == 2) begin
         cfg_reg_write(.reg_addr(12'h018), .write_data(bar_addr[31:0]), .comp_id(comp_id));
         cfg_reg_write(.reg_addr(12'h01c), .write_data(bar_addr[63:32]), .comp_id(comp_id));
         cfg_reg_read_check(.reg_addr(12'h018), .expected_data(bar_addr[31:0]), .data_mask(32'hffff_fff0), .comp_id(comp_id), .error_count(error_count));
         cfg_reg_read_check(.reg_addr(12'h01c), .expected_data(bar_addr[63:32]), .comp_id(comp_id), .error_count(error_count));
      end else if (bar_num == 4) begin
         cfg_reg_write(.reg_addr(12'h020), .write_data(bar_addr[31:0]), .comp_id(comp_id));
         cfg_reg_write(.reg_addr(12'h024), .write_data(bar_addr[63:32]), .comp_id(comp_id));
         cfg_reg_read_check(.reg_addr(12'h020), .expected_data(bar_addr[31:0]), .data_mask(32'hffff_fff0), .comp_id(comp_id), .error_count(error_count));
         cfg_reg_read_check(.reg_addr(12'h024), .expected_data(bar_addr[63:32]), .comp_id(comp_id), .error_count(error_count));
      end else begin
         $display("[%t] : *** ERROR *** Specified invalid BAR number for configuration: %d", $realtime, bar_num);
         $finish;
      end
   end
endtask


task get_bar(
             input int    bar_num,
             logic [15:0] comp_id,
             output logic [63:0] bar_addr
            );
   begin
      logic [31:0] read_data;

      if (bar_num == 0) begin
         cfg_reg_read(.reg_addr(12'h010), .read_data(read_data), .comp_id(comp_id));
         bar_addr[31:0] = {read_data[31:4], 4'h0};
         cfg_reg_read(.reg_addr(12'h014), .read_data(read_data), .comp_id(comp_id));
         bar_addr[63:32] = read_data[31:0];
      end else if (bar_num == 2) begin
         cfg_reg_read(.reg_addr(12'h018), .read_data(read_data), .comp_id(comp_id));
         bar_addr[31:0] = {read_data[31:4], 4'h0};
         cfg_reg_read(.reg_addr(12'h01c), .read_data(read_data), .comp_id(comp_id));
         bar_addr[63:32] = read_data[31:0];
      end else if (bar_num == 4) begin
         cfg_reg_read(.reg_addr(12'h020), .read_data(read_data), .comp_id(comp_id));
         bar_addr[31:0] = {read_data[31:4], 4'h0};
         cfg_reg_read(.reg_addr(12'h024), .read_data(read_data), .comp_id(comp_id));
         bar_addr[63:32] = read_data[31:0];
      end else begin
         $display("[%t] : *** ERROR *** Specified invalid BAR number for configuration read: %d", $realtime, bar_num);
         $finish;
      end
   end
endtask


task automatic config_pf(
                         input logic [15:0] comp_id,
                         ref int            error_count
                        );
   logic [11:0]  pcie_cap_base;
   logic [31:0]  read_data;
   logic [31:0]  write_data;

   begin
      // Get base address for PCIe Capabilities space
      get_cap_base(.cap_id(8'h10), .comp_id(comp_id), .cap_base(pcie_cap_base));

      // Read Device Control Register
      cfg_reg_read(.reg_addr(pcie_cap_base + 12'h008), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data;
// DEBUG: Used to clear Enable No Snoop bit ([11])
// DEBUG: Used to clear Extended Tag Field bit ([8])
      // Enable reporting for Correctable Errors, Non-Fatal Errors, Fatal Errors, and Unsupported Requests
      write_data |= 32'h0000_000f;
      // Set Max Payload Size to 512 bytes (3'b010)
      write_data &= 32'hffff_ff1f; // Clear [7:5]
      write_data |= (3'b010) << 5;
      // Set Max Read Request Size to 512 bytes (3'b010)
      write_data &= 32'hffff_8fff; // Clear [14:12]
// DEBUG: Used to be setting Max Read Req Size of 4k (3'b101)
      write_data |= (3'b010) << 12;
      // Write Device Control Register
      cfg_reg_write(.reg_addr(pcie_cap_base + 12'h008), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(pcie_cap_base + 12'h008), .expected_data(write_data), .comp_id(comp_id), .error_count(error_count));

      // Read Command Register
      cfg_reg_read(.reg_addr(12'h004), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data;
      // Set Memory Space Enable
      write_data |= 32'h0000_0002;
      // Set Bus Master Enable
      write_data |= 32'h0000_0004;
      // Write Command Register
      cfg_reg_write(.reg_addr(12'h004), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h004), .expected_data(write_data), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic clear_bme(
                         input logic [15:0] comp_id,
                         ref int            error_count
                        );
   logic [31:0]  read_data;
   logic [31:0]  write_data;

   begin
      $display("[%t] : Clearing Bus Master Enable bit in PCIe configuration register (Comp ID 0x%04x)", $realtime, comp_id);
      // Read Command Register
      cfg_reg_read(.reg_addr(12'h004), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data;
      // Clear Bus Master Enable
      write_data &= ~(32'h0000_0004);
      // Write Command Register
      cfg_reg_write(.reg_addr(12'h004), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h004), .expected_data(write_data), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic config_msix(
                           input logic [15:0] comp_id,
                           logic [63:0]       addr,
                           logic [31:0]       data,
                           bit                mask,
                           logic [7:0]        vector_num = 8'h0,
                           ref int            error_count
                          );
   begin
      logic [63:0]  bar;

      get_bar(.bar_num(2), .comp_id(comp_id), .bar_addr(bar));
      enable_msix(.comp_id(comp_id), .error_count(error_count));
      write_msix_table(.bar(bar), .comp_id(comp_id), .addr(addr), .data(data), .mask(mask), .vector_num(vector_num), .error_count(error_count));
   end
endtask


task automatic get_msix_config(
                               input logic [15:0]  comp_id,
                               output logic [63:0] addr,
                               logic [31:0]        data,
                               bit                 mask,
                               input logic [7:0]   vector_num = 8'h0
                               );
   begin
      logic [63:0]  bar;

      get_bar(.bar_num(2), .comp_id(comp_id), .bar_addr(bar));
      read_msix_table(.bar(bar), .comp_id(comp_id), .addr(addr), .data(data), .mask(mask), .vector_num(vector_num));
   end
endtask


task automatic enable_msix(
                           input logic [15:0] comp_id,
                           ref int            error_count
                          );
   begin
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      cfg_reg_read(.reg_addr(12'h060), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data | 32'h8000_0000; // Set Enable bit
      cfg_reg_write(.reg_addr(12'h060), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h060), .expected_data(32'h8000_0011), .data_mask(32'h8000_00ff), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic disable_msix(
                            input logic [15:0] comp_id,
                            ref int            error_count
                           );
   begin
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      cfg_reg_read(.reg_addr(12'h060), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data & ~(32'h8000_0000); // Clear Enable bit
      cfg_reg_write(.reg_addr(12'h060), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h060), .expected_data(32'h0000_0011), .data_mask(32'h8000_00ff), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic enable_msi(
                          input logic [15:0] comp_id,
                          ref int            error_count
                         );
   begin
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      cfg_reg_read(.reg_addr(12'h048), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data | 32'h0001_0000; // Set Enable bit
      cfg_reg_write(.reg_addr(12'h048), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h048), .expected_data(32'h0001_0005), .data_mask(32'h0001_00ff), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic disable_msi(
                           input logic [15:0] comp_id,
                           ref int            error_count
                          );
   begin
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      cfg_reg_read(.reg_addr(12'h048), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data & ~(32'h0001_0000); // Clear Enable bit
      cfg_reg_write(.reg_addr(12'h048), .write_data(write_data), .comp_id(comp_id));
      cfg_reg_read_check(.reg_addr(12'h048), .expected_data(32'h0000_0005), .data_mask(32'h0001_00ff), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic write_msix_table(
                                input logic [63:0] bar,
                                logic [15:0]       comp_id,
                                logic [63:0]       addr,
                                logic [31:0]       data,
                                bit                mask,
                                logic [7:0]        vector_num = 8'h0,
                                ref int            error_count
                               );
   begin
      logic [63:0]  base_addr;

`ifndef NO_XDMA
      base_addr = bar + 64'h8000;
`else
      base_addr = bar;
`endif

      // Write MSI-X Address
      reg_write(.base_addr(base_addr), .reg_offset(12'h000 + (vector_num << 4)), .write_data(addr[31:0]), .comp_id(comp_id));
      reg_write(.base_addr(base_addr), .reg_offset(12'h004 + (vector_num << 4)), .write_data(addr[63:32]), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000 + (vector_num << 4)), .expected_data(addr[31:0]), .comp_id(comp_id), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004 + (vector_num << 4)), .expected_data(addr[63:32]), .comp_id(comp_id), .error_count(error_count));

      // Write MSI-X Data
      reg_write(.base_addr(base_addr), .reg_offset(12'h008 + (vector_num << 4)), .write_data(data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h008 + (vector_num << 4)), .expected_data(data), .comp_id(comp_id), .error_count(error_count));

      // Write MSI-X Mask
      reg_write(.base_addr(base_addr), .reg_offset(12'h00c + (vector_num << 4)), .write_data({31'h0, mask}), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h00c + (vector_num << 4)), .expected_data({31'h0, mask}), .comp_id(comp_id), .error_count(error_count));

      // Set variables for Root Port model to use (this task is defined in simp_pcie_usrapp_dword.v)
      set_msix_config(.comp_id(comp_id), .addr(addr), .data(data), .mask(mask), .vector_num(vector_num));
   end
endtask


task automatic read_msix_table(
                               input logic [63:0]  bar,
                               logic [15:0]        comp_id,
                               output logic [63:0] addr,
                               logic [31:0]        data,
                               bit                 mask,
                               input logic [7:0]   vector_num = 8'h0
                              );
   begin
      logic [63:0]  base_addr;
      logic [31:0]  read_data;

`ifndef NO_XDMA
      base_addr = bar + 64'h8000;
`else
      base_addr = bar;
`endif

      // Read MSI-X Address
      reg_read(.base_addr(base_addr), .reg_offset(12'h000 + (vector_num << 4)), .read_data(read_data), .comp_id(comp_id));
      addr[31:0] = read_data;
      reg_read(.base_addr(base_addr), .reg_offset(12'h004 + (vector_num << 4)), .read_data(read_data), .comp_id(comp_id));
      addr[63:32] = read_data;

      // Read MSI-X Data
      reg_read(.base_addr(base_addr), .reg_offset(12'h008 + (vector_num << 4)), .read_data(read_data), .comp_id(comp_id));
      data = read_data;

      // Read MSI-X Mask
      reg_read(.base_addr(base_addr), .reg_offset(12'h00c + (vector_num << 4)), .read_data(read_data), .comp_id(comp_id));
      mask = read_data[0];
   end
endtask


task automatic map_user_irq(
                            input logic [15:0] comp_id,
                            logic [7:0]        irq_num,
                            logic [7:0]        vector_num = 8'h0,
                            ref int            error_count
                           );
   begin
      logic [63:0]  bar;
      logic [63:0]  base_addr;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      get_bar(.bar_num(2), .comp_id(comp_id), .bar_addr(bar));
      base_addr = bar + 64'h2000;

      // Valid IRQ range: 0 - 15
      if (irq_num > 8'd15) begin
         $display("[%t] : *** ERROR *** Request to map IRQ %3d, max supported IRQ is 15 (comp_id 0x%04x)", $realtime, irq_num, comp_id);
         error_count++;
      end
      // Valid Vector range: 0 - 31
      if (vector_num > 8'd31) begin
         $display("[%t] : *** ERROR *** Request to map IRQ %3d to Vector %3d, max supported Vector is 31 (comp_id 0x%04x)", $realtime, irq_num, vector_num, comp_id);
         error_count++;
      end

      reg_read(.base_addr(base_addr), .reg_offset(12'h080 + ((irq_num / 4) << 2)), .read_data(read_data), .comp_id(comp_id));
      write_data = read_data;
      write_data &= ~(5'h1f << ((irq_num % 4) << 3));
      write_data |= vector_num << ((irq_num % 4) << 3);
      reg_write(.base_addr(base_addr), .reg_offset(12'h080 + ((irq_num / 4) << 2)), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h080 + ((irq_num / 4) << 2)), .expected_data(write_data), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic enable_user_irq(
                               input logic [15:0] comp_id,
                               logic [7:0]        irq_num,
                               ref int            error_count
                              );
   begin
      logic [63:0]  bar;
      logic [63:0]  base_addr;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      get_bar(.bar_num(2), .comp_id(comp_id), .bar_addr(bar));
      base_addr = bar + 64'h2000;

      // Valid IRQ range: 0 - 15
      if (irq_num > 8'd15) begin
         $display("[%t] : *** ERROR *** Request to enable IRQ %3d, max supported IRQ is 15 (comp_id 0x%04x)", $realtime, irq_num, comp_id);
         error_count++;
      end

      write_data = 32'h0;
      write_data |= 1'b1 << irq_num;
      reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004), .expected_data(write_data), .data_mask(write_data), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task automatic disable_user_irq(
                                input logic [15:0] comp_id,
                                logic [7:0]        irq_num,
                                ref int            error_count
                               );
   begin
      logic [63:0]  bar;
      logic [63:0]  base_addr;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      get_bar(.bar_num(2), .comp_id(comp_id), .bar_addr(bar));
      base_addr = bar + 64'h2000;

      // Valid IRQ range: 0 - 15
      if (irq_num > 8'd15) begin
         $display("[%t] : *** ERROR *** Request to disable IRQ %3d, max supported IRQ is 15 (comp_id 0x%04x)", $realtime, irq_num, comp_id);
         error_count++;
      end

      write_data = 32'h0;
      write_data |= 1'b1 << irq_num;
      reg_write(.base_addr(base_addr), .reg_offset(12'h00c), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004), .expected_data(~write_data), .data_mask(write_data), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task get_cap_base(
                  input logic [7:0]   cap_id,
                  logic [15:0]        comp_id,
                  output logic [11:0] cap_base
                 );
   logic [31:0]  read_data;
   logic [11:0]  reg_addr;
   bit           cap_found;

   begin
      cap_found = 1'b0;

      // Check bit in PCI Status Register to see if Capabilities Pointer is implemented
      cfg_reg_read(.reg_addr(12'h004), .read_data(read_data), .comp_id(comp_id));
      if (read_data[20] == 1'b1) begin
         reg_addr = 12'h034;

         // Read Capabilities Pointer
         cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(comp_id));
         reg_addr = {4'h0, read_data[7:0]};
         while ((reg_addr !== 12'h000) && (cap_found == 1'b0)) begin
            cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(comp_id));
            if (read_data[7:0] == cap_id) begin
               cap_base = reg_addr;
               cap_found = 1'b1;
            end
            // Update reg_addr based on next capability pointer value
            reg_addr = {4'h0, read_data[15:8]};
         end
      end else begin
         $display("[%t] : *** ERROR *** Called get_cap_base() but linked list for New Capabilities is not implemented (comp_id 0x%04x)", $realtime, comp_id);
         $finish;
      end

      if (cap_found == 1'b0) begin
         $display("[%t] : *** ERROR *** Called get_cap_base() but did not find specified capability 0x%02x (comp_id 0x%04x)", $realtime, cap_id, comp_id);
         $finish;
      end

   end
endtask


task read_all_caps(
                   input logic [15:0]  comp_id,
                   int                 debug = 0
                  );
   logic [31:0]  read_data;
   logic [11:0]  reg_addr;
   logic [7:0]   cap_id;

   begin

      // Check bit in PCI Status Register to see if Capabilities Pointer is implemented
      cfg_reg_read(.reg_addr(12'h004), .read_data(read_data), .comp_id(comp_id));
      if (read_data[20] == 1'b1) begin
         reg_addr = 12'h034;

         $display("[%t] : Checking capabilities for comp_id 0x%04x", $realtime, comp_id);
         cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(comp_id));
         reg_addr = {4'h0, read_data[7:0]};
         while (reg_addr !== 12'h000) begin
            if (debug) $display("[%t] : Next capability at address 0x%03x", $realtime, reg_addr);
            cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(comp_id));
            cap_id = read_data[7:0];
            if (debug) $display("[%t] :   Capability ID: 0x%02x", $realtime, cap_id);
            // Report which capability types were detected
            if (cap_id == 8'h01) begin
               // PCI Power Management Interface
               $display("[%t] :   Power Management capabilities detected", $realtime);
            end else if (cap_id == 8'h05) begin
               // MSI
               $display("[%t] :   MSI capabilities detected", $realtime);
            end else if (cap_id == 8'h10) begin
               // PCIe
               $display("[%t] :   PCIe capabilities detected", $realtime);
               read_pcie_cap(.cap_base(reg_addr), .comp_id(comp_id));
            end else if (cap_id == 8'h11) begin
               // MSI-X
               $display("[%t] :   MSI-X capabilities detected", $realtime);
               read_msix_cap(.cap_base(reg_addr), .comp_id(comp_id));
            end
            // Update reg_addr based on next capability pointer value
            reg_addr = {4'h0, read_data[15:8]};
         end
      end else begin
         $display("[%t] : Linked list for New Capabilities not implemented (comp_id 0x%04x)", $realtime, comp_id);
      end
   end
endtask


task read_pcie_cap(
                   input logic [11:0]  cap_base,
                   logic [15:0]        comp_id
                  );
   logic [31:0]  read_data;
   int           value;
   string        text;

   begin
      cfg_reg_read(.reg_addr(cap_base + 12'h000), .read_data(read_data), .comp_id(comp_id));
      // Interrupt Message Number
      $display("[%t] :     PCIe Intr Msg Num               : 0x%02x", $realtime, read_data[29:25]);
      // Device Type
      if (read_data[23:20] == 4'h0) begin
         $display("[%t] :     PCIe Device Type                : Endpoint", $realtime);
      end else if (read_data[23:20] == 4'h1) begin
         $display("[%t] :     PCIe Device Type                : Legacy Endpoint", $realtime);
      end else begin
         $display("[%t] :     PCIe Device Type                : 0x%1x", $realtime, read_data[23:20]);
      end
      // Capability Version
      if (read_data[19:16] !== 4'h2) begin
         $display("[%t] : *** ERROR *** PCIe Capability Verion was 0x%1x, expected 0x2", $realtime, read_data[19:16]);
         $finish;
      end

      cfg_reg_read(.reg_addr(cap_base + 12'h004), .read_data(read_data), .comp_id(comp_id));
      // Max Supported Payload Size
      case (read_data[2:0])
        3'b000: value = 128;
        3'b001: value = 256;
        3'b010: value = 512;
        3'b011: value = 1024;
        3'b100: value = 2048;
        3'b101: value = 4096;
        default: begin
           $display("[%t] : *** ERROR *** PCIe Max Supported Payload Size setting was 0x%1x, not recognized as a valid setting", $realtime, read_data[2:0]);
           $finish;
        end
      endcase
      $display("[%t] :     PCIe Max Supported Payload Size : %4d bytes", $realtime, value);

      cfg_reg_read(.reg_addr(cap_base + 12'h008), .read_data(read_data), .comp_id(comp_id));
      // Max Read Request Size
      case (read_data[14:12])
        3'b000: value = 128;
        3'b001: value = 256;
        3'b010: value = 512;
        3'b011: value = 1024;
        3'b100: value = 2048;
        3'b101: value = 4096;
        default: begin
           $display("[%t] : *** ERROR *** PCIe Max Read Request Size setting was 0x%1x, not recognized as a valid setting", $realtime, read_data[2:0]);
           $finish;
        end
      endcase
      $display("[%t] :     PCIe Max Read Request Size      : %4d bytes", $realtime, value);
      // Max Payload Size
      case (read_data[7:5])
        3'b000: value = 128;
        3'b001: value = 256;
        3'b010: value = 512;
        3'b011: value = 1024;
        3'b100: value = 2048;
        3'b101: value = 4096;
        default: begin
           $display("[%t] : *** ERROR *** PCIe Max Payload Size setting was 0x%1x, not recognized as a valid setting", $realtime, read_data[2:0]);
           $finish;
        end
      endcase
      $display("[%t] :     PCIe Max Payload Size           : %4d bytes", $realtime, value);

      cfg_reg_read(.reg_addr(cap_base + 12'h00c), .read_data(read_data), .comp_id(comp_id));
      $display("[%t] :     PCIe Port Number                : 0x%02x", $realtime, read_data[31:24]);
      $display("[%t] :     PCIe Max Link Width             : x%2d", $realtime, read_data[9:4]);
      // Max Link Speed
      case (read_data[3:0])
        4'h1: text = "2.5 GT/s";
        4'h2: text = "5.0 GT/s";
        4'h3: text = "8.0 GT/s";
        default: begin
           $display("[%t] : *** ERROR *** PCIe Max Link Speed setting was 0x%1x, not recognized as a valid setting", $realtime, read_data[3:0]);
           $finish;
        end
      endcase
      $display("[%t] :     PCIe Max Link Speed             : %s", $realtime, text);

      cfg_reg_read(.reg_addr(cap_base + 12'h010), .read_data(read_data), .comp_id(comp_id));
      $display("[%t] :     PCIe Negotiated Link Width      : x%2d", $realtime, read_data[25:20]);
      // Current Link Speed
      case (read_data[19:16])
        4'h1: text = "2.5 GT/s";
        4'h2: text = "5.0 GT/s";
        4'h3: text = "8.0 GT/s";
        default: begin
           $display("[%t] : *** ERROR *** PCIe Current Link Speed setting was 0x%1x, not recognized as a valid setting", $realtime, read_data[19:16]);
           $finish;
        end
      endcase
      $display("[%t] :     PCIe Current Link Speed         : %s", $realtime, text);
   end
endtask


task read_msix_cap(
                   input logic [11:0]  cap_base,
                   logic [15:0]        comp_id
                  );
   logic [31:0]  read_data;
   begin
      cfg_reg_read(.reg_addr(cap_base + 12'h000), .read_data(read_data), .comp_id(comp_id));
      $display("[%t] :     MSI-X Cap ID       : 0x%02x", $realtime, read_data[7:0]);
      $display("[%t] :     MSI-X Control      : 0x%04x", $realtime, read_data[31:16]);

      cfg_reg_read(.reg_addr(cap_base + 12'h004), .read_data(read_data), .comp_id(comp_id));
      $display("[%t] :     MSI-X Table BIR    : 0x%01x", $realtime, read_data[2:0]);
      $display("[%t] :     MSI-X Table Offset : 0x%08x", $realtime, {read_data[31:3], 2'b00});

      cfg_reg_read(.reg_addr(cap_base + 12'h008), .read_data(read_data), .comp_id(comp_id));
      $display("[%t] :     MSI-X PBA BIR      : 0x%01x", $realtime, read_data[2:0]);
      $display("[%t] :     MSI-X PBA Offset   : 0x%08x", $realtime, {read_data[31:3], 2'b00});
   end
endtask


task automatic program_cl_addr_range(
                           input logic [63:0] base_addr,
                           bit [1:0]          range_num,
                           logic [63:0]       range_addr_low,
                           logic [63:0]       range_addr_high,
                           logic [15:0]       comp_id,
                           ref int            error_count
                          );
   begin
      reg_write(.base_addr(base_addr), .reg_offset(12'h220 + (range_num << 4)), .write_data(range_addr_low[31:0]), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h220 + (range_num << 4)), .expected_data(range_addr_low[31:0]), .data_mask(32'hffff_ffff), .comp_id(comp_id), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h224 + (range_num << 4)), .write_data(range_addr_low[63:32]), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h224 + (range_num << 4)), .expected_data(range_addr_low[63:32]), .data_mask(32'hffff_ffff), .comp_id(comp_id), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h228 + (range_num << 4)), .write_data(range_addr_high[31:0]), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h228 + (range_num << 4)), .expected_data(range_addr_high[31:0]), .data_mask(32'hffff_ffff), .comp_id(comp_id), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h22c + (range_num << 4)), .write_data(range_addr_high[63:32]), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h22c + (range_num << 4)), .expected_data(range_addr_high[63:32]), .data_mask(32'hffff_ffff), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task gen_random_access_addr(
                            output logic [63:0] addr,
                            input bit           allowed = 1'b1,
                            logic [63:0]        align = 64'h0003, // 4-byte (DW) aligned
                            int                 region = 99
                           );
   begin
      addr[63:32] = $urandom();
      addr[31:0] = $urandom();

      // Clear bits to achieve specified alignment
      addr &= ~align;

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      // Set bits to place address in specified region
      case (region)
        0: addr[63:62] = 2'b00;
        1: addr[63:62] = 2'b01;
        2: addr[63:62] = 2'b10;
        3: addr[63:62] = 2'b11;
      endcase

      // Set addr[61] if address needs to be in "not allowed" region
      if (allowed == 1'b1) begin
         addr[61] = 1'b0;
      end else begin
         addr[61] = 1'b1;
      end
   end
endtask


task automatic reg_read_check(
                              input logic [63:0] base_addr,
                              logic [11:0]       reg_offset,
                              logic [31:0]       expected_data,
                              logic [31:0]       data_mask = 32'hffff_ffff,
                              logic [15:0]       comp_id = EP_BUS_DEV_FNS,
                              int                timeout_count = 2000,
                              ref int            error_count
                             );
   begin
      logic [31:0]  read_data;
      logic [31:0]  mask_read_data;
      logic [31:0]  mask_expected_data;

      reg_read(.base_addr(base_addr), .reg_offset(reg_offset), .read_data(read_data), .comp_id(comp_id), .timeout_count(timeout_count));
      mask_read_data = read_data & data_mask;
      mask_expected_data = expected_data & data_mask;
      if (mask_read_data !== mask_expected_data) begin
         $display("[%t] : *** ERROR *** Read data from register 0x%03x was 0x%08x, expected 0x%08x (mask 0x%08x)", $realtime, reg_offset, read_data, expected_data, data_mask);
         error_count++;
      end
   end
endtask


task reg_read(
              input logic [63:0]  base_addr,
              logic [11:0]        reg_offset,
              output logic [31:0] read_data,
              input logic [15:0]  comp_id = EP_BUS_DEV_FNS,
              int                 timeout_count = 2000,
              bit                 allow_timeout = 1'b0
             );
   begin
`ifdef VIVADO_SIM
      // Vivado does not support "disable fork"
      automatic bit reg_access_done = 1'b0;
      fork
         begin
            TSK_MEM_READ_64_PF (.addr(base_addr + reg_offset), .rdata(read_data), .comp_id(comp_id));
            reg_access_done = 1'b1;
         end
         begin
            wait_for_clock(timeout_count);
            if (reg_access_done == 1'b0) begin
               if (allow_timeout == 1'b1) begin
                  $display("[%t] : Detected an expected timeout waiting for read from register 0x%03x", $realtime, reg_offset);
               end else begin
                  $display("[%t] : *** ERROR *** Timeout waiting for read from register 0x%03x", $realtime, reg_offset);
                  $finish;
               end
            end
         end
      join_any
`else
      fork
         begin
            TSK_MEM_READ_64_PF (.addr(base_addr + reg_offset), .rdata(read_data), .comp_id(comp_id));
         end
         begin
            wait_for_clock(timeout_count);
            if (allow_timeout == 1'b1) begin
               $display("[%t] : Detected an expected timeout waiting for read from register 0x%03x", $realtime, reg_offset);
            end else begin
               $display("[%t] : *** ERROR *** Timeout waiting for read from register 0x%03x", $realtime, reg_offset);
               $finish;
            end
         end
      join_any
      disable fork;
`endif
   end
endtask


task reg_write(
               input logic [63:0] base_addr,
               logic [11:0]       reg_offset,
               logic [31:0]       write_data,
               logic [15:0]       comp_id = EP_BUS_DEV_FNS
              );
   begin
      TSK_MEM_WRITE_64_PF (.addr(base_addr + reg_offset), .data(write_data), .comp_id(comp_id));
//      $display("[%t] : Writing 0x%08x to register 0x%03x", $realtime, write_data, reg_offset);
   end
endtask


task automatic cfg_reg_read_check(
                                  input logic [11:0] reg_addr,
                                  logic [31:0]       expected_data,
                                  logic [31:0]       data_mask = 32'hffff_ffff,
                                  logic [15:0]       comp_id,
                                  ref int            error_count
                                 );
   begin
      logic [31:0]  read_data;
      logic [31:0]  mask_read_data;
      logic [31:0]  mask_expected_data;

      cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(comp_id));
      mask_read_data = read_data & data_mask;
      mask_expected_data = expected_data & data_mask;
      if (mask_read_data !== mask_expected_data) begin
         $display("[%t] : *** ERROR *** Configuration read data from register 0x%03x was 0x%08x, expected 0x%08x (mask 0x%08x)", $realtime, reg_addr, read_data, expected_data, data_mask);
         error_count++;
      end
   end
endtask


task cfg_reg_read(
                  input logic [11:0]  reg_addr,
                  output logic [31:0] read_data,
                  input logic [15:0]  comp_id
                 );
   begin
`ifdef VIVADO_SIM
      // Vivado does not support "disable fork"
      automatic bit reg_access_done = 1'b0;
      fork
         begin
            TSK_TYPE0_CFG_READ(.reg_addr_(reg_addr), .rdata(read_data), .comp_id(comp_id));
            reg_access_done = 1'b1;
         end
         begin
            wait_for_clock(1000);
            if (reg_access_done == 1'b0) begin
               $display("[%t] : *** ERROR *** Timeout waiting for cfg read from register 0x%03x, comp_id=0x%x", $realtime, reg_addr, comp_id);
               $finish;
            end
         end
      join_any
`else
      fork
         begin
            TSK_TYPE0_CFG_READ(.reg_addr_(reg_addr), .rdata(read_data), .comp_id(comp_id));
         end
         begin
            wait_for_clock(1000);
            $display("[%t] : *** ERROR *** Timeout waiting for cfg read from register 0x%03x, comp_id=0x%x", $realtime, reg_addr, comp_id);
            $finish;
         end
      join_any
      disable fork;
`endif
   end
endtask


task cfg_reg_write(
                   input logic [11:0] reg_addr,
                   logic [31:0]       write_data,
                   logic [15:0]       comp_id,
                   bit                typ = 1'b0
                  );
   begin
      if (typ == 1'b0) begin
         TSK_TYPE0_CFG_WRITE(.reg_addr_(reg_addr), .reg_data_(write_data), .comp_id(comp_id));
//         $display("[%t] : Writing 0x%08x to configuration register 0x%03x", $realtime, write_data, reg_addr);
      end else if (typ == 1'b1) begin
         $display("[%t] : *** ERROR *** Type 1 Configuration Writes currently unsupported.", $realtime);
         $finish;
      end else begin
         $display("[%t] : *** ERROR *** Invalid Type specified for Configuration Write: %1d", $realtime, typ);
         $finish;
      end
   end
endtask


task wait_for_clock(
                    input int count = 0
                   );
   begin
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(count);
   end
endtask


task request_bus_control();
   begin
      while (tb.pcie_access.try_get() == 1'b0) wait_for_clock(10);
   end
endtask


task release_bus_control();
   begin
      tb.pcie_access.put();
   end
endtask
