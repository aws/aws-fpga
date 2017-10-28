// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


module test_clk_recipe();
   import tb_type_defines_pkg::*;

   //Starts checking clock frequency.
   tb.set_chk_clk_freq(0, 1'b1);

   //power up with Clock Recipe A0, B0, C0
   tb.power_up(.clk_recipe_a(ClockRecipe::A0), 
               .clk_recipe_b(ClockRecipe::B0), 
               .clk_recipe_c(ClockRecipe::C0));

   
   #500ns;
   // Power down
   tb.power_down();

   #500ns;
   //power up with Clock Recipe A1, B0, C0
   tb.power_up(.clk_recipe_a(ClockRecipe::A1), 
               .clk_recipe_b(ClockRecipe::B0), 
               .clk_recipe_c(ClockRecipe::C0));

   
   // Power down
   #500ns;
   tb.power_down();

   #500ns;
   //power up with Clock Recipe A2, B1, C0
   tb.power_up(.clk_recipe_a(ClockRecipe::A2), 
               .clk_recipe_b(ClockRecipe::B1), 
               .clk_recipe_c(ClockRecipe::C0));

   
   // Power down
   #500ns;
   tb.power_down();

   #500ns;
   //power up with Clock Recipe A3, B1, C1
   tb.power_up(.clk_recipe_a(ClockRecipe::A3), 
               .clk_recipe_b(ClockRecipe::B1), 
               .clk_recipe_c(ClockRecipe::C1));

   
   // Power down
   #500ns;
   tb.power_down();

endmodule // test_clk_recipe
