#!/bin/bash

vcs -R -sverilog +vcs+lic+wait\
   -timescale=1ns/1ns\
   -debug_access+all\
   +incdir+$HDK_COMMON_DIR/verif/packages\
   $HDK_COMMON_DIR/verif/packages/anp_base_pkg.sv\
   ../axis_bfm_pkg.sv\
   ../axis_bfm.sv\
   test.sv\
   +ANP_DEBUG\
   +ANP_MSG_SHOW_FILE_INFO\
   +AXIS_DUMP_MONITORED_PACKET\
   -l sim.log\
   $*  

