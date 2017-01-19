#!/tools/perl/perl/5.20.1/bin/perl -w -s

## Amazon FGPA Hardware Development Kit
## 
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
## 
## Licensed under the Amazon Software License (the "License"). You may not use
## this file except in compliance with the License. A copy of the License is
## located at
## 
##    http://aws.amazon.com/asl/
## 
## or in the "license" file accompanying this file. This file is distributed on
## an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
## implied. See the License for the specific language governing permissions and
## limitations under the License.

use strict;
use warnings;
use File::Copy;

# The timestamp is an input to the script
my $timestamp = $ARGV[0];

copy("${timestamp}.vivado.log", "vivado_temp.log") or die "Copy failed: $!";

open(FILE1, "vivado_temp.log")
      or die "Can't open < vivado_temp.log: $!";
open(my $fh_wr, ">", "${timestamp}.vivado.log")
      or die "Can't open > ${timestamp}.vivado.log: $!";

my $match;
my @warning_regexps = ("CRITICAL WARNING.*BRAM instance.*Please verify the instance name in the \.bmm file and the netlist. The BRAM initialization strings will not get populated with data.*",
                       "CRITICAL WARNING.*Setting IOB or IOB_TRI_REG property to TRUE for instance.*conflicts with its current constrained placement.*The conflicting constraint will be removed.*",
                       "CRITICAL WARNING.*No valid object.*found for.*get_clocks cl_clk.*cl_synth_aws.xdc.*",
                       "CRITICAL WARNING.*Invalid constraint on register.*It has the property IOB=TRUE, but it is not driving or driven by any IO element.*"
                      ); 


while (<FILE1>) {
   $match = 0;
   foreach my $regexp (@warning_regexps) {
      if($_ =~ /$regexp/) {
         $match = 1;
      }
   }
   if($match==0) {
      print $fh_wr $_;
   }
}

close(FILE1);
close($fh_wr);
unlink("vivado_temp.log");
