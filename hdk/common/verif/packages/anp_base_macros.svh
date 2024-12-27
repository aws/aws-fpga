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


`ifndef __ANP_BASE_MACROS_SVH__
`define __ANP_BASE_MACROS_SVH__

//
// Macro: anp_info
//
`define anp_print(SVRT, ID, MSG)\
   begin\
      $display("%0s @ %0t: %0s%0s",\
         SVRT, $time, (ID != "") ? {"[", ID, "] "}: "", MSG);\
   end

`define anp_print_file_name_line(SVRT, ID, MSG)\
   begin\
      $display("%0s %0s(%0d) @ %0t: %0s%0s",\
         SVRT, `__FILE__, `__LINE__, $time, (ID != "") ? {"[", ID, "] "}: "", MSG);\
   end

`define anp_debug(MSG, ID="", VERB=)\
   if (anp_base_pkg::msg_debug) begin\
      `anp_print_file_name_line("DEBUG", ID, MSG)\
   end

`define anp_info(MSG, ID="", VERB=)\
   if (!anp_base_pkg::msg_no_info) begin\
      if (anp_base_pkg::msg_show_file_info) begin\
         `anp_print_file_name_line("INFO", ID, MSG)\
      end\
      else begin\
         `anp_print("INFO", ID, MSG)\
      end\
      anp_base_pkg::infos++;\
   end

`define anp_warning(MSG, ID="")\
   begin\
      if (anp_base_pkg::msg_show_file_info) begin\
         `anp_print_file_name_line("WARNING", ID, MSG)\
      end\
      else begin\
         `anp_print("WARNING", ID, MSG)\
      end\
      anp_base_pkg::warnings++;\
   end

`define anp_error(MSG, ID="")\
   begin\
      `anp_print_file_name_line("ERROR", ID, MSG)\
      anp_base_pkg::errors++;\
      if (anp_base_pkg::errors >= anp_base_pkg::errors_quit_count) begin\
         anp_base_pkg::end_of_test();\
      end\
   end

`define anp_fatal(MSG, ID="")\
   begin\
      `anp_print_file_name_line("FATAL", ID, MSG)\
      anp_base_pkg::fatals++;\
      if (!anp_base_pkg::msg_no_fatal_exit) begin\
         anp_base_pkg::end_of_test();\
      end\
   end
//
// Macro: anp_base_test_timeout
// Convinience macro to register the implementation of the UVM
// test's timeout
//
`define anp_base_test_timeout(MSG_ID=msg_id)\
   begin\
      string   tout_str;\
      if ($value$plusargs("timeout=%s", tout_str)) begin\
         string   unit;\
         int      value;\
         if ($sscanf(tout_str, "%d%s", value, unit)) begin\
            `anp_info($sformatf(\
               "timeout : Timeout is set to %0d[%s]", value, unit), MSG_ID)\
            /* Set the timeout into UVM Root */\
            case (unit)\
            "ns" : sim_timeout = value*1ns;\
            "us" : sim_timeout = value*1us;\
            "ms" : sim_timeout = value*1ms;\
            default :\
               `anp_error($sformatf(\
                  "timeout : Specified unit = %0s isn't supported!", unit), MSG_ID)\
            endcase\
         end\
         else begin\
            `anp_error($sformatf(\
               "timeout : Specified +timeout=%0s isn't correct!", tout_str), MSG_ID)\
         end\
      end\
   end
//
// Dummy wrapper macros that works/meaningful in UVM mode.
// We do nothing here in non UVM tests
//
`define anp_base_set_config_db(TYPE, NAME, INST, HIER="*", FROM=this)\
`define anp_base_get_config_db(TYPE, NAME, INST, FROM=this)\
`define anp_set_elab_done\
`define anp_base_add_test_phase_seq(PHASE, SEQ, VSEQR=env.vseqr)\
`define anp_base_urm_cov_parg(MSG_ID=msg_id)

`endif//__ANP_BASE_MACROS_SVH__
