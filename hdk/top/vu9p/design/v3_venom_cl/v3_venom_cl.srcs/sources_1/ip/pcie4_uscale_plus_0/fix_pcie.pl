#!/usr/bin/env perl

system("cp synth/pcie4_uscale_plus_0.v synth/pcie4_uscale_plus_0.v.orig ");
system("cp sim/pcie4_uscale_plus_0.v sim/pcie4_uscale_plus_0.v.orig ");

open (ORIG, "< synth/pcie4_uscale_plus_0.v.orig");
open (NEW, "> synth/pcie4_uscale_plus_0.v");

while (<ORIG>)
{
   s/\.SRIOV_CAP_ENABLE\(\'D0001\)/\.SRIOV_CAP_ENABLE\(\'D0000\)/;
   s/\.TL_CREDITS_CD\(\'H000\)/\.TL_CREDITS_CD\(\'H780\)/;
   s/\.TL_CREDITS_CH\(\'H00\)/\.TL_CREDITS_CH\(\'H7f\)/;
   s/\.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\)/\.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\),\n     \.LEGACY_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\)/;
   #if (/\.SRIOV_CAP_ENABLE\(\'D000/) #D0001\)/)
   #{
   #   print "HERE: $_"
   #}
   print NEW $_;
}

open (ORIG, "< sim/pcie4_uscale_plus_0.v.orig");
open (NEW, "> sim/pcie4_uscale_plus_0.v");

while (<ORIG>)
{
   s/\.SRIOV_CAP_ENABLE\(\'D0001\)/\.SRIOV_CAP_ENABLE\(\'D0000\)/;
   s/\.TL_CREDITS_CD\(\'H000\)/\.TL_CREDITS_CD\(\'H780\)/;
   s/\.TL_CREDITS_CH\(\'H00\)/\.TL_CREDITS_CH\(\'H7f\)/;
   s/\.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\)/\.EXTENDED_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\),\n    \.LEGACY_CFG_EXTEND_INTERFACE_ENABLE\(\"TRUE\"\)/;

   #if (/\.SRIOV_CAP_ENABLE\(\'D000/) #D0001\)/)
   #{
   #   print "HERE: $_"
   #}
   print NEW $_;
}
