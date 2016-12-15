#!/tools/perl/perl/5.20.1/bin/perl -w -s
use strict;
use warnings;
use File::Copy;

copy("vivado.log", "vivado_temp.log") or die "Copy failed: $!";

open(FILE1, "vivado_temp.log")
      or die "Can't open < vivado_temp.log: $!";
open(my $fh_wr, ">", "vivado.log")
      or die "Can't open > vivado.log: $!";

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
