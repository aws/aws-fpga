##################################################
### Tcl Procs and Params - 2017.1_sdx
##################################################
####Set params to disable OREG_B* in URAM for synthesis and physical synthesis
set_param synth.elaboration.rodinMoreOptions {rt::set_parameter disableOregPackingUram true}
set_param physynth.ultraRAMOptOutput false

####Enable support of clocking from one RP to another (SH-->CL)
set_param hd.supportClockNetCrossDiffReconfigurablePartitions 1 

