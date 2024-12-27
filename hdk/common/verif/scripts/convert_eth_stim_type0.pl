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

error_exit("1st argument (input file) is not defined")  if !defined $ARGV[0];
error_exit("2nd argument (output file) is not defined") if !defined $ARGV[1];

my $ifile = $ARGV[0];
my $ofile = $ARGV[1];

my $odir = dirname($ofile);

open (FI, $ifile)    || die "Can't open $ifile";
open (FO, ">$ofile") || die "Can't open $ofile";

my @data;
my $idle;
my $packets = 0;
while (<FI>) {
   my $str = get_line($_);
   debug("(".__LINE__.") $str");
   if ($str ne "") {
      if ($str =~ m/^Bytes\s+(\d+)/) {
         debug("(".__LINE__.") $str");
         my $bytes = $1;
         for (my $i = 0; $i < $bytes; $i+=4) {
            for (my $j = 0; $j < 4; $j++) {
               my $bnum = $i + $j;
               if ($bnum < $bytes) {
                  my $wnum = $bnum >> 2;
                  push @data, ($j == 0) ? $wnum & 0xFF
                            : ($j == 1) ? ($wnum >> 8) & 0xFF
                            : ($j == 2) ? $packets
                            : 0;
               }
            }
         }
         add_stim();
         $packets++;
      }
      elsif ($str =~ m/^Delay\s+(\d+)/) {
         print FO "IDLE $1\n";
      }
   }
}
close FI;
close FO;

sub add_stim {
   my $bytes_per_line = 0;
   if (@data > 0) {
      debug("(".__LINE__.") ".join(" ", @data));
      print FO "SOP\n";
      my $size = @data;
      for (my $i = 0; $i < $size; $i++) {
         my $data_tmp = $data[$i] & 0xFF;
         if (defined $ENV{AXIS_STIM_ONE_BYTE_PER_LINE}) {
            print FO sprintf("%02x\n", $data_tmp);
         }
         else {
            print FO sprintf("%02x", $data_tmp);
            $bytes_per_line++;
            if ($bytes_per_line >= 20) {
               print FO "\n" if ($i + 1) < $size;
               $bytes_per_line = 0;
            }
         }
      }
      print FO "\n";
      print FO "EOP\n";
      $idle = undef;
      @data = ();
   }
} # add_stim

info("Generated: $ofile");


sub get_line {
   my $s = shift;
   chomp($s);
   $s =~ s/^\s+//g;
   $s =~ s/\s+$//g;
   return $s;
}

sub info {
   my $s = shift;
   print "-I- $s\n";
}

sub error {
   my $s = shift;
   print "-E- $s\n";
}

sub error_exit {
   my $s = shift;
   error($s);
   exit 255;
}

sub debug {
   my $s = shift;
   print "-D- $s\n" if defined $ENV{DEBUG_PRINT};
}
