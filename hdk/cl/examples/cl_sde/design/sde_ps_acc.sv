// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

// SDE PCIS Accumulator

module sde_ps_acc #(parameter PCIS_DATA_WIDTH = 512,
                    parameter PCIS_ADDR_WIDTH = 64,
                    parameter ACC_WIDTH = 64,
                    parameter ACC_WIDTH_DW = ACC_WIDTH >> 5,
                    parameter START_ADDR = 64'd0,
		    parameter LIMITED_SUPPORT = 1
                   )
   (
    input                            clk,
    input                            rst_n,

    output logic                     ooo_error,
    output logic                     unalin_error,

    // PS FSM to PCIS-ACC Block
    input                            pcis_req_wr,
    input [PCIS_ADDR_WIDTH-1:0]      pcis_req_addr,

    // PCIS Write Data Bus
    input [PCIS_DATA_WIDTH-1:0]      pcis_wdata,
    input [(PCIS_DATA_WIDTH>>3)-1:0] pcis_wstrb,
    input                            pcis_wlast,
    input                            pcis_wvalid,
    output logic                     pcis_wready,

    // PCIS-ACC to Slave
    output logic                     acc_wr_req,
    output logic [ACC_WIDTH-1:0]     acc_wdata,
    input                            acc_ack

    );

   localparam PCIS_ADDR_BYTE_IDX_WIDTH = $clog2(PCIS_DATA_WIDTH>>3);
   localparam PCIS_ADDR_DW_IDX_WIDTH = PCIS_ADDR_BYTE_IDX_WIDTH - 2;
   localparam ACC_DW_IDX_WIDTH = $clog2(ACC_WIDTH_DW) + 1;
   localparam ACC_MAX_DW_IDX_WIDTH = ACC_DW_IDX_WIDTH > PCIS_ADDR_DW_IDX_WIDTH ? ACC_DW_IDX_WIDTH : PCIS_ADDR_DW_IDX_WIDTH;

if (LIMITED_SUPPORT == 0) begin

   // Following logic supports any DW length of data coming on pcis_wdata and any address alignment. But at increased resource utilization.
   logic [PCIS_ADDR_DW_IDX_WIDTH:0] pcis_wr_num_dw_d;
   logic [PCIS_ADDR_DW_IDX_WIDTH:0] pcis_wr_num_dw_q;
   logic                            pcis_first_q;
   logic [PCIS_DATA_WIDTH-1:0]      pcis_wdata_q;
   logic                            pcis_wvalid_q;

   logic [ACC_MAX_DW_IDX_WIDTH:0]   acc_in_dw_cnt_remain;
   logic                            acc_out_transmit;
   logic [ACC_DW_IDX_WIDTH:0]       acc_out_num_dw_needed;
   logic [ACC_MAX_DW_IDX_WIDTH:0]   acc_num_dw_to_accumulate;
   logic [ACC_DW_IDX_WIDTH:0]       acc_wr_num_dw_d;
   logic                            acc_out_stall;
   logic [ACC_WIDTH-1:0]            acc_in_wdata_acc;
   logic [ACC_WIDTH-1:0]            acc_in_wdata_d;
   logic [ACC_DW_IDX_WIDTH:0]       acc_wr_num_dw;

   always_comb
     for (int dw_idx = 0; dw_idx < (PCIS_DATA_WIDTH>>5); dw_idx++)
       if (pcis_wstrb[dw_idx*4])
         pcis_wr_num_dw_d <= dw_idx + 1;

   always @(posedge clk)
     if (!rst_n) begin
        pcis_first_q <= 1;
        pcis_wdata_q <= '{default:'0};
        pcis_wr_num_dw_q <= 0;
        pcis_wvalid_q <= 0;
     end
     else begin
        pcis_first_q <= pcis_wvalid & pcis_wready & pcis_wlast ? 1'b1 :
                        pcis_wvalid & pcis_wready ? 1'b0 : pcis_first_q;

        pcis_wdata_q <= pcis_wvalid && ~pcis_wvalid_q && pcis_first_q ? pcis_wdata >> {pcis_req_addr[PCIS_ADDR_BYTE_IDX_WIDTH-1:0], 3'b000} :
                        pcis_wvalid && ~pcis_wvalid_q ? pcis_wdata :
                        pcis_wvalid_q && ~acc_out_stall ? (pcis_wdata_q >> {acc_num_dw_to_accumulate, 5'd0}) :
                        pcis_wdata_q;

        pcis_wr_num_dw_q <= pcis_wvalid && ~pcis_wvalid_q && pcis_first_q ? pcis_wr_num_dw_d - pcis_req_addr[PCIS_ADDR_BYTE_IDX_WIDTH-1:2] :
                            pcis_wvalid && ~pcis_wvalid_q ? pcis_wr_num_dw_d :
                            pcis_wvalid_q && ~acc_out_stall ? pcis_wr_num_dw_q - acc_num_dw_to_accumulate :
                            pcis_wr_num_dw_q;

        pcis_wvalid_q <= ~pcis_wvalid_q & pcis_wvalid & pcis_req_wr ? 1'b1 :
                         pcis_wvalid_q & ~acc_out_stall & (pcis_wr_num_dw_q == acc_num_dw_to_accumulate) ? 1'b0 :
                         pcis_wvalid_q;

     end
   assign pcis_wready = pcis_req_wr & ~pcis_wvalid_q;

   // Number of bytes in the input that are not transmitted/are remaining to be sent
   assign acc_in_dw_cnt_remain = pcis_wr_num_dw_q; // Zero extend if required

   assign acc_out_transmit = (acc_wr_num_dw >= ACC_WIDTH_DW);

   // Number of total bytes still needed
   assign acc_out_num_dw_needed = acc_out_transmit ? ACC_WIDTH_DW : ACC_WIDTH_DW - acc_wr_num_dw;

   // Number of bytes to accumulate in this clock
   assign acc_num_dw_to_accumulate = (acc_in_dw_cnt_remain > acc_out_num_dw_needed) ? acc_out_num_dw_needed : acc_in_dw_cnt_remain;

   // Number of bytes in the output
   assign acc_wr_num_dw_d = acc_out_transmit & pcis_wvalid_q ? acc_num_dw_to_accumulate :
                            acc_out_transmit ? 0 :
                            pcis_wvalid_q ? acc_wr_num_dw + acc_num_dw_to_accumulate : acc_wr_num_dw;

   // Output should stall if request is outstanding and there is an ack
   assign acc_out_stall = acc_wr_req & ~acc_ack;

   // Case1 : Accumulate
   always_comb
     for (int dw_idx = 0; dw_idx < ACC_WIDTH_DW; dw_idx++) begin
        if (dw_idx < acc_wr_num_dw)
          acc_in_wdata_acc[dw_idx*32 +: 32] = acc_wdata[dw_idx*32 +: 32];
        else
          acc_in_wdata_acc[dw_idx*32 +: 32] = pcis_wdata_q[(dw_idx - acc_wr_num_dw)*32 +: 32];
     end

   // Output data
   assign acc_in_wdata_d =  acc_out_transmit & pcis_wvalid_q ? pcis_wdata_q[ACC_WIDTH-1:0] :
                            pcis_wvalid_q ? acc_in_wdata_acc :
                            acc_wdata;

   always @(posedge clk)
     if (!rst_n) begin
        acc_wr_num_dw <= 0;
        acc_wr_req <= 0;
        acc_wdata <= '{default:'0};
     end
     else begin
        acc_wr_num_dw <= ~acc_out_stall ? acc_wr_num_dw_d : acc_wr_num_dw;
        acc_wr_req <= ~acc_out_stall ? (acc_wr_num_dw_d == ACC_WIDTH_DW) : acc_wr_req;
        acc_wdata <= ~acc_out_stall ? acc_in_wdata_d : acc_wdata;
     end // else: !if(!rst_n)

   logic [PCIS_ADDR_WIDTH-1:0] pcis_req_addr_q;

   always @(posedge clk)
     if (!rst_n) begin
        pcis_req_addr_q <= 0;
        ooo_error <= 0;
        unalin_error <= 0;
     end
     else begin
        pcis_req_addr_q <= pcis_req_wr ? pcis_req_addr : pcis_req_addr_q;
        ooo_error <= ~ooo_error & pcis_req_wr & (pcis_req_addr_q > pcis_req_addr) & (pcis_req_addr != START_ADDR);
        unalin_error <= ~unalin_error & pcis_req_wr & (pcis_req_addr[5:0] != 6'd0);
     end

end // if (LIMITED_SUPPORT == 0)

else begin

   // Following logic assumes these:
   // 1. Always 64Byte aligned address coming on pcis_addr from host.
   // 2. The MSB 256 bits on pcis_wdata bus should NOT contain any valid descriptors. Only pcis_wdata[255:0] is used.
   // 3. Only supports 1DW, 4DW or 8DW coming on pcis_wdata from the host.
   logic [PCIS_ADDR_DW_IDX_WIDTH:0] pcis_wr_num_dw_d;
   logic [PCIS_ADDR_DW_IDX_WIDTH:0] pcis_wr_num_dw_q;
   logic                            pcis_first_q;

   localparam PCIS_WDATAQ_WIDTH = (PCIS_DATA_WIDTH <= 256) ? PCIS_DATA_WIDTH : 256;
   logic [PCIS_WDATAQ_WIDTH-1:0]    pcis_wdata_q;

   logic                            pcis_wvalid_q;

   logic [ACC_MAX_DW_IDX_WIDTH:0]   acc_in_dw_cnt_remain;
   logic                            acc_out_transmit;
   logic [ACC_DW_IDX_WIDTH:0]       acc_out_num_dw_needed;
   logic [ACC_MAX_DW_IDX_WIDTH:0]   acc_num_dw_to_accumulate;
   logic [ACC_DW_IDX_WIDTH:0]       acc_wr_num_dw_d;
   logic                            acc_out_stall;
   logic [ACC_WIDTH-1:0]            acc_in_wdata_acc;
   logic [ACC_WIDTH-1:0]            acc_in_wdata_d;
   logic [ACC_DW_IDX_WIDTH:0]       acc_wr_num_dw;

   always_comb
     for (int dw_idx = 0; dw_idx < (PCIS_DATA_WIDTH>>5)/2; dw_idx++) //(512/32)/2=8
       if ((pcis_wstrb[dw_idx*4]) && (dw_idx == 0 || dw_idx == 3 || dw_idx == 7))
         pcis_wr_num_dw_d <= dw_idx + 1; //Supported DW= 1DW, 4DW and 8DW

   always @(posedge clk)
     if (!rst_n) begin
        pcis_first_q <= 1;
        pcis_wdata_q <= '{default:'0};
        pcis_wr_num_dw_q <= 0;
        pcis_wvalid_q <= 0;
     end
     else begin
        pcis_first_q <= pcis_wvalid & pcis_wready & pcis_wlast ? 1'b1 :
                        pcis_wvalid & pcis_wready ? 1'b0 : pcis_first_q;

	pcis_wdata_q <= pcis_wvalid && ~pcis_wvalid_q ? pcis_wdata : //assuming the addr will always be 64 Byte aligned.
                        pcis_wvalid_q && ~acc_out_stall ? (pcis_wdata_q >> {acc_num_dw_to_accumulate, 5'd0}) :
                        pcis_wdata_q;

	pcis_wr_num_dw_q <= pcis_wvalid && ~pcis_wvalid_q ? pcis_wr_num_dw_d :
                            pcis_wvalid_q && ~acc_out_stall ? pcis_wr_num_dw_q - acc_num_dw_to_accumulate :
                            pcis_wr_num_dw_q;

        pcis_wvalid_q <= ~pcis_wvalid_q & pcis_wvalid & pcis_req_wr ? 1'b1 :
                         pcis_wvalid_q & ~acc_out_stall & (pcis_wr_num_dw_q == acc_num_dw_to_accumulate) ? 1'b0 :
                         pcis_wvalid_q;

     end
   assign pcis_wready = pcis_req_wr & ~pcis_wvalid_q;

   // Number of bytes in the input that are not transmitted/are remaining to be sent
   assign acc_in_dw_cnt_remain = pcis_wr_num_dw_q; // Zero extend if required

   assign acc_out_transmit = (acc_wr_num_dw >= ACC_WIDTH_DW);

   // Number of total bytes still needed
   assign acc_out_num_dw_needed = acc_out_transmit ? ACC_WIDTH_DW : ACC_WIDTH_DW - acc_wr_num_dw;

   // Number of bytes to accumulate in this clock
   assign acc_num_dw_to_accumulate = (acc_in_dw_cnt_remain > acc_out_num_dw_needed) ? acc_out_num_dw_needed : acc_in_dw_cnt_remain;

   // Number of bytes in the output
   assign acc_wr_num_dw_d = acc_out_transmit & pcis_wvalid_q ? acc_num_dw_to_accumulate :
                            acc_out_transmit ? 0 :
                            pcis_wvalid_q ? acc_wr_num_dw + acc_num_dw_to_accumulate : acc_wr_num_dw;

   // Output should stall if request is outstanding and there is an ack
   assign acc_out_stall = acc_wr_req & ~acc_ack;

   // Case1 : Accumulate
   always_comb
     for (int dw_idx = 0; dw_idx < ACC_WIDTH_DW; dw_idx++) begin
        if (dw_idx < acc_wr_num_dw)
          acc_in_wdata_acc[dw_idx*32 +: 32] = acc_wdata[dw_idx*32 +: 32];
        else
          acc_in_wdata_acc[dw_idx*32 +: 32] = pcis_wdata_q[(dw_idx - acc_wr_num_dw)*32 +: 32];
     end

   // Output data
   assign acc_in_wdata_d =  acc_out_transmit & pcis_wvalid_q ? pcis_wdata_q[ACC_WIDTH-1:0] :
                            pcis_wvalid_q ? acc_in_wdata_acc :
                            acc_wdata;

   always @(posedge clk)
     if (!rst_n) begin
        acc_wr_num_dw <= 0;
        acc_wr_req <= 0;
        acc_wdata <= '{default:'0};
     end
     else begin
        acc_wr_num_dw <= ~acc_out_stall ? acc_wr_num_dw_d : acc_wr_num_dw;
        acc_wr_req <= ~acc_out_stall ? (acc_wr_num_dw_d == ACC_WIDTH_DW) : acc_wr_req;
        acc_wdata <= ~acc_out_stall ? acc_in_wdata_d : acc_wdata;
     end // else: !if(!rst_n)

   logic [PCIS_ADDR_WIDTH-1:0] pcis_req_addr_q;

   always @(posedge clk)
     if (!rst_n) begin
        pcis_req_addr_q <= 0;
        ooo_error <= 0;
        unalin_error <= 0;
     end
     else begin
        pcis_req_addr_q <= pcis_req_wr ? pcis_req_addr : pcis_req_addr_q;
        ooo_error <= ~ooo_error & pcis_req_wr & (pcis_req_addr_q > pcis_req_addr) & (pcis_req_addr != START_ADDR);
	unalin_error <= ~unalin_error & pcis_req_wr & (pcis_req_addr[5:0] != 6'd0);
     end
end // else: !if(LIMITED_SUPPORT == 0)

endmodule // sde_ps_acc
