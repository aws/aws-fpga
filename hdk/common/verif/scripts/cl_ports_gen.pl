#!/usr/bin/env perl

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


#===============================================================================
# Perl libs to be used in this script.
#===============================================================================
use strict;
use File::Basename;
use Cwd;
use Cwd 'abs_path';
use File::Path qw(make_path remove_tree);
use File::Copy qw(copy move);
use Data::Dumper;
$Data::Dumper::Sortkeys = 1;
$Data::Dumper::Indent   = 1;

foreach (
   "HDK_SHELL_DESIGN_DIR",
   "HDK_COMMON_DIR",
   "COMPILE_DIR",
   "OUTPUT_DIR"
) {
   debug("$_ : $ENV{$_}");
}

my $ifile = (defined $ARGV[0]) ? $ARGV[0]
          : "$ENV{HDK_SHELL_DESIGN_DIR}/interfaces/cl_ports.vh";
#
# Read the content of the file and store it into temporary variable and then
# remove all the comments and prettify the valid code to ease the parsing
#
open (F, $ifile) || die "Can't open $ifile";
my $s;
while (<F>) {$s .= $_;}
close F;
foreach (
   '\/\/.*',
   '\/[*](?:(?![*]\/)[\s\S])*+[*]\/',
   '\([*](?:(?![*]\))[\s\S])*+[*]\)',
) {
   $s =~ s/$_//g;
}
$s =~ s/(\n\);)\n/$1\n/g;
$s =~ s/\s+(,|;|\))/$1/g;
$s =~ s/(\w)(\[)/$1 $2/g;
$s =~ s/(\])(\w)/$1 $2/g;
#
# Extract the ports and apply the conversion for each of the desired
# output type
#
my %str;
foreach (split(/\n/, $s)) {
   $_ =~ s/\s+logic|wire\s+/ /g;
   $_ =~ s/^\s+//g;
   $_ =~ s/\s+$//g;
   $_ =~ s/\s+/ /g;
   next if $_ eq "";
   my %tmp;
   $tmp{tch} = $_;
   $tmp{dut} = $_;
   $tmp{shb} = $_;
   $tmp{fps} = $_;
   $tmp{fpe} = $_;
   $tmp{uvc} = $_;
   if (/^output\s+/) {
      $tmp{tch} =~ s/(^\s*)output\b/$1input/g;
      $tmp{shb} =~ s/(^\s*)output\b/$1input/g;
      $tmp{dut} =~ s/(^\s*)output\b/$1wire/g;
      $tmp{fps} =~ s/(^\s*)output\b/$1logic/g;
      $tmp{uvc} =~ s/(^\s*)output\b/$1inout/g;
   }
   elsif (/^input\s+/) {
      $tmp{tch} =~ s/(^\s*)input\b/$1inout/g;
      $tmp{shb} =~ s/(^\s*)input\b/$1output-logic/g;
      $tmp{dut} =~ s/(^\s*)input\b/$1wire/g;
      $tmp{fps} =~ s/(^\s*)input\b/$1logic/g;
      $tmp{uvc} =~ s/(^\s*)input\b/$1input/g;
   }
   elsif (/^inout\s+/) {
      $tmp{dut} =~ s/(^\s*)inout\b/$1wire/g;
      $tmp{fps} =~ s/(^\s*)inout\b/$1logic/g;
   }
   elsif (/^(\w+)\.(\w+)(\s+)/) {
      my $a = $1;
      my $b = $2;
      my $c = $3;
      $tmp{tch} =~ s/^$a\.$b$c/interface${c}/g;
      $tmp{shb} =~ s/^$a\.$b$c/interface${c}/g;
      $tmp{uvc} =~ s/^$a\.$b$c/interface${c}/g;
      foreach my $t ("dut", "fps") {
         debug("(".__LINE__.") $t $tmp{$t}");
         $tmp{$t} =~ s/^$a\.$b$c/${a}${c}/g;
         $tmp{$t} =~ s/(,|)$/()/;
         debug("(".__LINE__.") $t $tmp{$t}");
      }
   }
   foreach my $t ("dut", "fps") {
      debug("(".__LINE__.") $t $tmp{$t}");
      $tmp{$t} =~ s/(,|)$/;/;
      $tmp{$t} =~ s/(`if(n|)def\s+\w+);$/$1/;
      $tmp{$t} =~ s/(`endif);$/$1/;
      debug("(".__LINE__.") $t $tmp{$t}");
   }
   foreach my $t ("tch", "dut", "shb", "fps", "fpe", "uvc") {
      my $is_ext_port;
      if ($tmp{$t} !~ m/^`(if(n|)def|endif)/) {
         if ($tmp{$t} =~ m/^(\S+)\s+(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-12s %-8s %-s", "", $1, $2, $3);
            $is_ext_port = is_ext_port($3);
         }
         elsif ($tmp{$t} =~ m/^(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-21s %-s", "", $1, $2);
            $is_ext_port = is_ext_port($2);
         }
         elsif ($tmp{$t} =~ m/^(\S+)\s+(\S+)\s+(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-12s %-8s %-s", "", $1, $2.$3, $4);
            $is_ext_port = is_ext_port($4);
         }
         elsif ($tmp{$t} =~ m/^(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-12s %-8s %-s", "", $1, $2.$3.$4, $5);
            $is_ext_port = is_ext_port($5);
         }
         elsif ($tmp{$t} =~ m/^(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-12s %-8s %-s", "", $1, $2.$3.$4.$5, $6);
            $is_ext_port = is_ext_port($6);
         }
         elsif ($tmp{$t} =~ m/^(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)$/) {
            $tmp{$t} = sprintf("%-3s%-12s %-8s %-s", "", $1, $2.$3.$4.$5.$6, $7);
            $is_ext_port = is_ext_port($7);
	 }
      }
      $tmp{$t} =~ s/\boutput-logic\b/output logic/g;
      if ($t =~ m/^fps|shb$/) {
         $str{$t} .= "$tmp{$t}\n" if !$is_ext_port;
      }
      elsif ($t =~ m/^fpe$/) {
         $tmp{$t}  =~ s/(\w+)$/$1,/;
         $str{$t} .= "$tmp{$t}\n" if $is_ext_port;
      }
      else {
         $str{$t} .= "$tmp{$t}\n";
      }
   }
}
foreach my $t ("dut", "fps") {
   chop($str{$t});
   $str{$t} .= ";\n";
   $str{$t} =~ s/;;/;/g;
}
$str{fpe} .= ",";
$str{fpe} =~ s/[,]+$//g;

write_file("$ENV{HDK_COMMON_DIR}/verif/models/sh_bfm/cl_ports_sh_bfm.vh", "shb");
write_file("$ENV{HDK_COMMON_DIR}/verif/models/fpga/fpga_signals.vh", "fps");
write_file("$ENV{HDK_COMMON_DIR}/verif/models/fpga/fpga_ports.vh", "fpe");
if (defined $ENV{COMPILE_DIR} || defined $ENV{OUTPUT_DIR}) {
   foreach my $t ("tch", "dut", "uvc") {
      write_file("$ENV{COMPILE_DIR}/cl_${t}_ports.svh", $t);
   }
}

sub write_file {
   my $fname = shift;
   my $type  = shift;
   if (defined $ENV{OUTPUT_DIR}) {
      debug("(".__LINE__.")");
      make_path($ENV{OUTPUT_DIR}) if !-d $ENV{OUTPUT_DIR};
      $fname = "$ENV{OUTPUT_DIR}/".basename($fname);
      debug("(".__LINE__.")");
   }
   $str{$type} =~ s/`ifndef\s+\w+,\n`endif,/,/g;
   $str{$type} =~ s/,$//g;
   my $year = get_year();
   open (F, ">$fname") || die "Can't write to $fname";
   print F <<EOM;
//------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright $year Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// GENERATED FILE. DO NOT MODIFY!
//------------------------------------------------------------------------------
EOM
   print F $str{$type};
   close F;
   debug("Generated $fname");
} # write_file

sub info {
   my $s = shift;
   print "-I- $s\n";
}

sub debug {
   my $s = shift;
   print "-D- $s\n" if defined $ENV{DEBUG_PRINT};
}

sub is_ext_port {
   my $sig = shift;
   my $ret = 0;
   if ($sig =~ /^cl_RST_DIMM/) {
      $ret = 1;
   }
   else {
      $ret = 1 if $sig eq uc($sig);
   }
   return $ret;
}

sub get_year {
   my $ret = `date +%Y`;
   chomp($ret);
   return $ret;
}
