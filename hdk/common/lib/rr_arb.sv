// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


//-------------------------------------------------------------
// This is a simple round robin arbiter.  Runs every clock
//-------------------------------------------------------------

module rr_arb #(  parameter WINNER_WIDTH=3,                       //Number of bits in the "winner" signal
                  parameter REQ_WIDTH = 32'h1<<WINNER_WIDTH,      //Number of requests to arbitrate between
                  parameter DO_ARB_IS_CHANGE_STATE = 0            // The do_arb signal acts like a change state - Useful for cases where arbitration takes many cycles and we do not want to change the state of the arbiter until later
                  )
(
   input clk,
   input rst_n,

   input [REQ_WIDTH-1:0] req,                //Request vector
   input do_arb,                             //Do the arbitration
   output[WINNER_WIDTH-1:0] winner           //Winner
);



wire[WINNER_WIDTH-1:0] hi_pri;               //Next hi priority
wire[REQ_WIDTH-1:0] req_shifted;             //Shift request based on hi_pri

reg[WINNER_WIDTH-1:0] winner_q;

reg[WINNER_WIDTH:0] tmp_winner;              //Make this one bit more to deal with overflow cases, where winner is
                                             // temporarily more than REQ_WIDTH, and we adjust later

//Shift the request based on high priority
assign req_shifted = {2{req}} >> hi_pri;

//Cycle through the shifted request, select the lowest asserted value as the winner
integer i;
always_comb
begin
   if (do_arb || (DO_ARB_IS_CHANGE_STATE == 1))
   begin
      tmp_winner = 0;
      for (i=REQ_WIDTH-1; i>=0; i=i-1)
      begin
         if (req_shifted[i])
         begin
            tmp_winner = hi_pri + i;

            //Adjustment for odd width cases, where winner is larger than number
            // of requests.
            if (tmp_winner >= REQ_WIDTH)
            begin
               tmp_winner = tmp_winner - REQ_WIDTH;
            end
         end
      end
   end
   else
      tmp_winner = winner_q;
end

assign winner = tmp_winner;

//Latch the next high priority
always_ff @(negedge rst_n or posedge clk)
   if (!rst_n)
      winner_q <= 0;
   else if (do_arb)
      winner_q <= winner;

//Note if timing is an issue, could flop this.  For now going a bit
// more aggressive and basing hi_pri on winner_q
assign hi_pri = (winner_q==(REQ_WIDTH-1))? 0: winner_q + 1;

endmodule
