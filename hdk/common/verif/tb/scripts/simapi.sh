#!/bin/bash

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.
# =============================================================================


if [ ! -z "$SIMSCR_DEBUG" ]
then
   debug=1
else
   debug=0
fi

color_mode=0
last_command_return=0

function error () {
   print_msg "ERROR" "1;31m" $@
} # error

function warn () {
   print_msg "WARNING" "1;33m" $@
} # warn

function info () {
   print_msg "INFO" "1;34m" $@
} # info

function print_msg () {
   local type=$1;  shift
   local color=$1; shift
   if [ $color_mode = 1 ]
   then
      echo -e "\e[$color-$type-\e[0m $@"
   else
      echo "$type: $@"
   fi
} # print_msg

function dbg () {
   if [ $debug = 1 ]
   then
      print_msg "D" "0;36m" $@
   fi
} # dbg

function execmd () {
   dbg run: $@
   rm -rf passed failed > /dev/null 2>&1
   set -o pipefail
   eval $@
   last_command_return=$?
} # execmd

function runcmd () {
   local mode=$1; shift
   local log=$1;  shift

   dbg runcmd $log $@

   if [ -z "$SIMSCR_NORUN" ]
   then
      echo "Command: $@" > $log
      execmd "$@ 2>&1 | tee -a $log"
      if [ $last_command_return == 0 ]
      then
         if [ "$mode" == "sim" ]
         then
            if [ -f $SCRIPTS_DIR/sim.clean.sh ]; then
               $SCRIPTS_DIR/sim.clean.sh $log
               mv $log.clean $log
            fi
            if [ ! -f "passed" ]
            then
               error "FAIL: See `realpath $log`"
               exit 255
            else
               info  "PASS: See `realpath $log`"
            fi
         else
            info  "PASS: See `realpath $log`"
         fi
      else
         error "FAIL: See `realpath $log`"
         exit $last_command_return
      fi
   else
      dbg run: $@
   fi

} # runcmd

function do_build () {
   runcmd build $@
} # do_build

function do_sim () {
   runcmd sim $@
} # do_sim

function pre_ip_gen () {
   local dir=$1; shift
   info "Generate Xilinx IPs under $dir"
   info "This could take 5-10 minutes, please be patient!"

   # Cleaning up the files
   git clean -fXdq $dir

   # List out all of the *.xci files and create a backup to undo the
   # auto modification done by vivado in post generation
   echo > $dir/post_gen.sh
   for i in `find $dir -name "*.xci"`
   do
      cp -f $i $i.bak
      echo "mv $i.bak $i" >> $dir/post_gen.sh
   done
   chmod +x $dir/post_gen.sh

} # pre_ip_gen

function post_ip_gen () {
   local dir=$1; shift
   info "Completed generating Xilinx IPs under $dir"
   . $dir/post_gen.sh
   rm -f $dir/post_gen.sh
} # post_ip_gen
