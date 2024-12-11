//----------------------------------------------------------------------------------
//Copyright (c) 2014
//
//Permission is hereby granted, free of charge, to any person obtaining a copy
//of this software and associated documentation files (the "Software"), to deal
//in the Software without restriction, including without limitation the rights
//to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//copies of the Software, and to permit persons to whom the Software is
//furnished to do so, subject to the following conditions:
//
//The above copyright notice and this permission notice shall be included in
//all copies or substantial portions of the Software.
//
//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//THE SOFTWARE.
//----------------------------------------------------------------------------------
//------------------------------------------------------------
// These are routines to report design errors uniformly
//------------------------------------------------------------

//import uvm_pkg::*;

task design_error (input string err_str);
begin
   `ifdef UVM_ENABLED
      `uvm_error("DESIGN", $psprintf("%m: %s", err_str));
   `else
      $display($time,,,"%m: ***DESIGN ERROR*** %s", err_str);
   `endif

   `ifndef DISABLE_DESIGN_ERROR_FINISH
      $display("Design Error killing sim...");
      repeat(5)
         @(posedge clk);
      $finish;
   `endif
end
endtask
