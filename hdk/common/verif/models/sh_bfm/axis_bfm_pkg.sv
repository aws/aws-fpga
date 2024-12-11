//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

`include "anp_base_macros.svh"

package axis_bfm_pkg;

   //---------------------------------------------------------------------------
   // Type forward declaration and common typedefs
   //---------------------------------------------------------------------------
   typedef class                    axis_bfm_pkt;
   typedef mailbox#(axis_bfm_pkt)   axis_mbx_t;

   //---------------------------------------------------------------------------
   // Function: print_array
   // Common function to print the data array content
   //---------------------------------------------------------------------------
   function automatic string print_array(bit [7:0] data[$]);
      string s;
      int bytes;
      bytes = data.size();
      s = $sformatf("data.size() = %0d", data.size());
      for (int i = 0; i < bytes; i += 8) begin
         s = {s, $sformatf("\n   [%4d:%4d]: ", i, (((i + 8) > bytes) ? bytes - 1: i + 7))};
         for (int j = 0; j < 8; j++) begin
            if ((i + j) < bytes) begin
               s = {s, $sformatf(" %02H", data[i+j])};
            end
         end
      end
      return s;
   endfunction : print_array

   //---------------------------------------------------------------------------
   // Function: read_stim
   // Common function to read the stimulus file that matched the AXIS packet 
   // stimulus format
   //---------------------------------------------------------------------------
   task automatic read_stim(
      axis_mbx_t  mbx_h, 
      int         fp,
      string      msg_id
   );
      int         _eof;
      bit [7:0]   data_tmp[$];
      int         delay;

      _eof = 0;
      
      while (!_eof) begin
         string      _line;
         int         _line_ret;
         
         _line_ret = $fgets(_line, fp);
         _eof = $feof(fp);

         if (!_eof) begin
            string first;
            string second;
            int    ret;

            first = "";
            second = "";

            ret = $sscanf(_line, "%s %s", first, second);
            `anp_debug($sformatf("first=%0s, second=%0s", first, second), msg_id)

            if (!is_comment(first)) begin
               if (!is_comment(second)) begin
                  // This should be an IDLE instruction
                  if (first == "IDLE") begin
                     delay = second.atoi();
                  end
               end

               if (first != "") begin
                  `anp_debug($sformatf("read_stim: first=%0s, delay=%0d, data_tmp[$]=%02H",
                     first, delay, data_tmp[$]), msg_id)

                  if (first == "EOP") begin
                     axis_bfm_pkt pkt = new();
                     pkt.delay = delay;
                     pkt.data  = data_tmp;
                     mbx_h.put(pkt);
                     delay = 0;
                     data_tmp.delete();
                  end
                  else if (first != "SOP" && first != "IDLE") begin
                     int str_len;
                     str_len = first.len();
                     
                     if (str_len % 2) begin
                        `anp_fatal({
                           "read_stim: Detected HEX data length which is not aligned with format. ",
                           "Input stimulus packet data must be hex value with format 001122334455..."},
                           msg_id)
                     end

                     for (int b = 0; b < str_len; b += 2) begin
                        int data_value;
                        data_value = first.substr(b, b+1).atohex();
                        data_tmp.push_back(data_value);
                        `anp_debug($sformatf("read_stim: Pushed 0x%02H into data_tmp. data_tmp.size=%0d", 
                           data_value, data_tmp.size()), msg_id)
                     end

                  end
               end
            end
         end
      end
   endtask : read_stim

   //---------------------------------------------------------------------------
   // Function: is_comment
   // To check if the word is a comment or not
   //---------------------------------------------------------------------------
   function automatic bit is_comment(string s);
      if ((s != "#") && (s != "--")) begin
         return 0;
      end
      else begin
         return 1;
      end
   endfunction : is_comment

   //---------------------------------------------------------------------------
   // Class: axis_bfm_pkt
   // Base packet class for AXIS BFM
   //---------------------------------------------------------------------------
   class axis_bfm_pkt;

      rand bit [7:0] data[$];
      rand int       delay;

      //------------------------------------------------------------------------
      // Function: dump
      // Function to dump the data array into a text file
      //------------------------------------------------------------------------
      function void dump(int fp, int delay = -1);
         int    bytes;
         int    bytes_per_line_max;
         int    bytes_per_line;
         string data_str;

         bytes_per_line_max = 20;
         bytes = data.size();

         if (delay != -1 && $test$plusargs("AXIS_DUMP_PACKET_WITH_IDLE")) begin
            $fdisplay(fp, "IDLE %0d", delay);
         end
         $fdisplay(fp, "SOP");

         for (int i = 0; i < bytes; i++) begin
`ifdef AXIS_STIM_ONE_BYTE_PER_LINE
            $fdisplay(fp, "%02X", data[i]);
`else
            data_str = {data_str, $sformatf("%02X", data[i])};
            bytes_per_line++;
            if (bytes_per_line >= bytes_per_line_max) begin
               data_str = {data_str, "\n"};
               bytes_per_line = 0;
            end
`endif
         end

`ifndef AXIS_STIM_ONE_BYTE_PER_LINE
         $fdisplay(fp, data_str);
`endif
         $fdisplay(fp, "EOP");
      endfunction : dump

      //------------------------------------------------------------------------
      // Function: compare
      // Function to compare the AXIS packet and report the result
      //------------------------------------------------------------------------
      function bit compare (axis_bfm_pkt rhs, string message);
         int m_compare_failures;
         if (rhs == null) begin
            `anp_error({"compare: ", message, "Got null rhs object"})
            return 0;
         end
         else begin
            int lhs_size = data.size();
            int rhs_size = rhs.data.size();
            int max_compare_size = (lhs_size > rhs_size) ? rhs_size: lhs_size;
            bit result = 1;
            if (lhs_size != rhs_size) begin
               result = 0;
               `anp_error($sformatf(
                  "compare: (%0s) Size mismatch -> exp.size=%0d, act.size=%0d",
                  message, lhs_size, rhs_size))
            end
            for (int i = 0; i < max_compare_size; i++) begin
               if (data[i] != rhs.data[i]) begin
                  result = 0;
                  m_compare_failures++;
                  `anp_warning($sformatf(
                     "compare: (%0s) Data mismatch -> exp[%4d]=0x%02H, act[%4d]=0x%02H.",
                     message, i, data[i], i, rhs.data[i]))
               end
            end
            if (!result) begin
               `anp_error($sformatf(
                  "compare: (%0s) Failed! PacketLength=%0d, %0d mismatches",
                  message, rhs_size, m_compare_failures))
            end
            else begin
               `anp_info($sformatf(
                  "compare: (%0s) Passed! PacketLength=%0d", 
                  message, rhs_size))
            end
            return result;
         end
      endfunction : compare

      //------------------------------------------------------------------------
      // Function: print
      // Function to print the data packet content
      //------------------------------------------------------------------------
      function string print();
         return axis_bfm_pkg::print_array(this.data);
      endfunction : print

   endclass : axis_bfm_pkt

endpackage : axis_bfm_pkg

