// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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



// Descriptions:
//  A 32 deep synchronous FIFO with parameterized width built from SRL32E configured LUTs
//  and flops
//
//-----------------------------------------------------------------------------
//Module Declaration

module srl_fifo #(parameter WIDTH = 64,
                  parameter DEPTH = 8,
                  parameter WATERMARK = DEPTH-1, // Should be minus1 of the actual watermark (for eg. if Depth = 4 and watermark = 3, then watermark is asserted when occupancy reaches 4)
                  parameter bit PIPELINE = 1
                  )
   (
    input                    clk,
    input                    rst_n,

    input [WIDTH-1:0]        push_data,
    input                    push,
    input                    pop,

    output logic [WIDTH-1:0] pop_data,
    output logic             data_valid,

    output logic             watermark = 0,
    output logic             empty = 1
    );

   localparam WATERMARK_MINUS1 = WATERMARK - 1;
   localparam PTR_WIDTH = DEPTH > 16 ? 5 : 4;

   logic                     rd_stall;
   logic                     rd_en;
   logic [PTR_WIDTH-1:0]     rd_ptr = '1;
   logic [WIDTH-1:0]         srl_q;
   logic                     data_valid_p = 0;

   assign rd_stall = (PIPELINE == 1) ? data_valid & ~pop : ~pop;
   assign rd_en = ~empty & ~rd_stall;

   always @(posedge clk)
     if (!rst_n) begin
        rd_ptr <= '{default:'1};
        watermark <= 0;
        empty <= 1;
        data_valid_p <= 0;
     end
     else begin
        rd_ptr <= push & ~rd_en ? rd_ptr + 1 :
                  ~push & rd_en ? rd_ptr - 1 : rd_ptr;

        watermark <= push & ~rd_en ? (rd_ptr == WATERMARK_MINUS1) :
                     ~push & rd_en ? 0 :
                     watermark;

        empty <= push & ~rd_en ? 0 :
                 ~push & rd_en ? (rd_ptr == 0) :
                 empty;

        data_valid_p <= pop || ~data_valid_p ? rd_en :
                        data_valid_p;

     end // else: !if(!rst_n)

   genvar                    bit_idx;
   generate

      for (bit_idx = 0; bit_idx < WIDTH; bit_idx++) begin : srl_pipe

         if (WIDTH > 16)  begin: srl32
            SRLC32E
              #(.INIT (32'h00000000),
                .IS_CLK_INVERTED (1'b0)
                ) SRL
                (.CLK (clk),
                 .D   (push_data[bit_idx]),
                 .CE  (push),
                 .A   (rd_ptr[PTR_WIDTH-1:0]),
                 .Q   (srl_q[bit_idx]),
                 .Q31 ()
                 );

         end // block: srl_instance

         else begin : srl16
            SRL16E
              #(.INIT (16'h0000),
                .IS_CLK_INVERTED (1'b0)
                ) SRL
                (.CLK (clk),
                 .D   (push_data[bit_idx]),
                 .CE  (push),
                 .A3  (rd_ptr[3]),
                 .A2  (rd_ptr[2]),
                 .A1  (rd_ptr[1]),
                 .A0  (rd_ptr[0]),
                 .Q   (srl_q[bit_idx])
                 );
         end // block: srl16

         if (PIPELINE == 1) begin : out_data_reg
            FDRE #(.INIT (1'b0),
                   .IS_C_INVERTED (1'b0),
                   .IS_D_INVERTED (1'b0),
                   .IS_R_INVERTED (1'b1)
                   )
            OUT_DATA_REG (.C  (clk),
                          .R  (rst_n),
                          .CE (rd_en),
                          .D  (srl_q[bit_idx]),
                          .Q  (pop_data[bit_idx])
                          );
         end // block: out_data_reg
         else begin : out_data_wire
            assign pop_data[bit_idx] = srl_q[bit_idx];
         end

      end // block: srl_pipe

   endgenerate

   assign data_valid = (PIPELINE == 1) ? data_valid_p : ~empty;

//Simulation checks
//synopsys translate_off

   always @(posedge clk)
     if (rst_n) begin
        if (DEPTH > 32) begin
           $display ("%m: *** ERROR ***: Maximum Supported Depth is 32");
           $finish;
        end

        if (DEPTH < 2) begin
           $display ("%m: *** ERROR ***: Minimum Supported Depth is 2");
           $finish;
        end
     end

//synopsys translate_on


endmodule // srl_fifo



