#!/usr/bin/perl -w

#
# Author: Sonal Santan
# Script to generate frequency table used to program clock wiz 5.1
# Be wary of making any change to the algorithm as not all possible multiplier
# and dividers work in practive with the clock wiz
# The C static const table generated here is copied verbatim to xdma-ioctl.c
# 1. We avoid using fractional portion of divide in config2 as it does not work
#    on Ultrascale parts.
# 2. Using step of 5 MHz does not work either.
# 3. VCO should be less than 1200

# Input frequency
my $input = 100;
# Maximum supported frequency
my $maxFreq = 500;

my $maxVCO = 1400;
my $minVCO = 600;
my $step = 100;
my $delim = "\n";
my %table;

for (my $vco = $minVCO; $vco <= $maxVCO; $vco += $step)
{
    my $freq = $vco;
    my $config0 = 0x1;
    my $mul = $vco / $step;
    $mul <<= 8;
    $config0 |= $mul;
    for (my $config1 = 2; $config1 <= 10; $config1++) {
	printf($delim);
	$freq = $vco/$config1;
	if ($freq > $maxFreq) {
	    next;
	}
	#printf("\t\t{%4u, 0x%04x, 0x%04x}", int($freq), int($config0), int($config1));
	$delim = ",\n";
	$table{int($freq)} = [int($config0), int($config1), $vco];
    }
}

foreach my $freq (sort {$a <=> $b} keys %table) {
#    printf($delim);
    my @values = @{$table{$freq}};
#    printf("\t\t{%4u, 0x%04x, 0x%04x}", $freq, $values[0], $values[1]);
#    $delim = ",\n";
}

printf("\nconst static struct xdma_ocl_clockwiz frequency_table[] = {");
$delim = "\n";
my $prevFreq = 10;;
foreach my $freq (sort {$a <=> $b} keys %table) {
    if (($freq - $prevFreq) < 5) {
	next;
    }
    $prevFreq = $freq;
    printf($delim);
    my @values = @{$table{$freq}};
    printf("\t\t{/*%4u*/, %4u, 0x%04x, 0x%04x}", $values[2], $freq, $values[0], $values[1]);
    $delim = ",\n";
}
printf("\n};\n");



# printf("const static struct xdma_ocl_clockwiz frequency_table[] = {");
# my $delim = "\n";
# for (my $freq = $step; $freq <= 250; $freq += $step) {
#     printf($delim);
#     my $config0 = 0x1;
#     my $config2 = $input / $step;
#     my $mul = $freq/$step;
#     $mul <<= 8;
#     $config0 |= $mul;
#     printf("\t\t{%4u, 0x%04x, 0x%04x}", $freq, int($config0), int($config2));
#     $delim = ",\n";
# }

# for (my $freq = 250 + $step; $freq <= 500; $freq += $step) {
#     printf($delim);
#     my $config0 = 0xa;
#     my $config2 = 0x1; $input / $step;
#     my $mul = $freq/$config0;
#     $mul <<= 8;
#     $config0 |= $mul;
#     printf("\t\t{%4u, 0x%04x, 0x%04x}", $freq, int($config0), int($config2));
#     $delim = ",\n";
# }
# printf("\n};\n");
