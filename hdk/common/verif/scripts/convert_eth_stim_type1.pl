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
my $min_delay = (defined $ARGV[2]) ? $ARGV[2]
              : 200;
my $max_delay = (defined $ARGV[3]) ? $ARGV[3]
              : (defined $ARGV[2]) ? $ARGV[2]
              : 200;

info(sprintf("TYPE1-Convert $ifile to $ofile (ipg:min=%0d, max=%0d)", $min_delay, $max_delay));

my $odir = dirname($ofile);

open (FI, $ifile)    || die "Can't open $ifile";
open (FO, ">$ofile") || die "Can't open $ofile";

my @data;
my @data_8bytes;
my $idle;
while (<FI>) {
   my $str = get_line($_);
   debug("(".__LINE__.") $str");
   if ($str ne "") {
      if ($str =~ m/^(\#\#\s+){2,}/) {
         debug("(".__LINE__.") $str");
         add_stim();
      }
      elsif ($str !~ m/^\-\-/) {
         debug("(".__LINE__.") $str");
         foreach my $byte (split(/\s+/, $str)) {
            push @data_8bytes, $byte;
            if (@data_8bytes == 8) {
               push @data, reverse @data_8bytes;
               @data_8bytes = ();
            }
         }
         debug("(".__LINE__.") ".join(" ", @data));
      }
   }
}
add_stim();
close FI;
close FO;

info("Generated: $ofile");

sub add_stim {
   my $bytes_per_line = 0;
   if (@data > 0) {
      debug("(".__LINE__.") ".join(" ", @data));
      print FO "SOP\n";
      my $size = @data;
      for (my $i = 0; $i < $size; $i++) {
         if (defined $ENV{AXIS_STIM_ONE_BYTE_PER_LINE}) {
            print FO sprintf("%02x\n", hex($data[$i]));
         }
         else {
            print FO sprintf("%02x", hex($data[$i]));
            $bytes_per_line++;
            if ($bytes_per_line >= 20) {
               print FO "\n" if ($i + 1) < $size;
               $bytes_per_line = 0;
            }
         }
      }
      print FO "\n";
      print FO "EOP\n";
      $idle = $min_delay + int(rand($max_delay - $min_delay));
      if (defined $idle) {
         print FO "IDLE $idle\n";
      }
      $idle = undef;
      @data = ();
   }
} # add_stim

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
