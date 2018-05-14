# IP Integrator - Frequently Asked Questions

## Table of Content

[AWS IP](#ip)

[Vivado Project Flows](#proj)

[Simulation](#sim)

[Synthesis/Implementation](#impl)


<a name="ip"></a>
# AWS IP

<a name="proj"></a>
# Vivado Project Flows

**Q: Why does a critical warning appear for DDR4?**

The DDR4 IP currently doesn't have a board associated with the XCI that is used with the HLx flow.  
The critical warning can safely be ignored as the IP will not change.

**Q: Why is cl\_pnr\_user.xdc file disabled in the project?**

This file is used when the SH and CL are linked during implementation.  The file is disabled for the flow at this time and will be enabled with future versions of the tools.


**Q: How does the user encrypt RTL sources or IP sources in the BD with the IP Integrator Flow?**

This is not supported at this time.

**Q: How does the user encrypt RTL sources with the RTL flow?**

This is not supported at this time. However, the user can try the following manual flow.

Add RTL unencrypted sources as simulation only sources.

Simulation passes user tests.

User modified encrypt.tcl to encrypted unencrypted source to another area/directory and sources the tcl in vivado in batch mode. 

Add RTL encrypted sources directory as sources.

On each encrypted source file in the Source tab, deselect USED\_IN\_SIMULATION.

**Q: What IP Integrator Flows are supported with this release for user RTL?**

RTL Referencing Flow is supported. An example is provided in the AWS Tutorials Examples documentation.

For advanced flows, using IP Packager is supported (no examples provided currently).

Using AXI External Interfaces between IPI and RTL modules in the Vivado project are not supported at this time.

**Q: What limitations are with the RTL Referencing Flow and IP Packager?**

VHDL/Verilog only (System Verilog not supported)


<a name="sim"></a>
# Simulation


**Q: What simulators and simulation flows are supported?**

When using the Vivado GUI, the Vivado Simulator is supported and is the default simulator.  Currently Windows only support Vivado Simulator.  The next set of questions/answers describe linking in 3rd party vendor simulator support.

Customer example System Verilog testbench (.sv/BFM) is supported.

When using the Vivado GUI, DPI simulation is supported (C simulation).  The RTL example cl\_hello\_world contains simulation with test\_hello\_world.c for DPI simulation where the flow can be used with other designs.

**Q: How to add DPI support for XSIM simulator with GUI flow?**

By default, XSIM is the default simulator for all examples.  When creating new projects the following should have configured in the project.

In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test_null.c script.  This file can be copied and modified to another area where an example exists for other .c stimulus.

`set_property -name {xsim.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi_xsim.tcl -objects [get_filesets sim_1]`

Right click on SIMULATION in the Project Manager and select Simulation Settings.

In the Elaboration tab, for xsim.elaborate.xelab.more_options add in the following value.

`-sv_lib dpi`

**Q: How to use Questa simulator with GUI flow?**

For Questa, libraries need to be compiled and the following changes are needed to the Vivado GUI project.  Note the user must install Questa and handle the licenses (not described in this document).

Invoke vivado (no project needs to be open).  In the TCL console run the following compile to compile libraries.

`compile_simlib -simulator questa -directory path/simlib/2017.1_questa_sdx`

Open any Vivado project where simulation needs to be changed to Questa.

Right click on SIMULATION in the Project Manager and select Simulation Settings.

Change Target simulator to Questa Advanced Simulator. Click Yes to change the simulator to 'Questa Advanced Simulator'.

Change the Compiled library location to the path that was used for compiling libraries.

When creating new projects the following should have configured in the project.

In the Compilation tab, for questa.compile.vlog.more_options add in the following value.

`-timescale 1ps/1ps +define+QUESTA_SIM`

Click OK, Click Apply, Click OK to back into the Vivado project.

**Q: How to add DPI support for Questa simulator with GUI flow?**

When creating new projects the following should have configured in the project.

The project needs to be configured based upon the above question/answer for adding Questa simulator support.

In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test_null.c script.  This file can be copied and modified to another area where an example exists for other .c stimulus.

`set_property -name {questa.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]`

Right click on SIMULATION in the Project Manager and select Simulation Settings.

In the Simulation tab, for questa.simulate.vsim.more_options add in the following value.

`-sv_lib libdpi`

**Q: How to use VCS simulator with GUI flow?**

For VCS, libraries need to be compiled and the following changes are needed to the Vivado GUI project.  Note the user must install VCS and handle the licenses (not described in this document).

Invoke vivado (no project needs to be open).  In the TCL console run the following compile to compile libraries.

`compile_simlib -simulator vcs_mx -directory path/simlib/2017.1_vcs_sdx`

Open any Vivado project where simulation needs to be changed to VCS.

Right click on SIMULATION in the Project Manager and select Simulation Settings.

Change Target simulator to Verilog Compiler Simulator (VCS). Click Yes to change the simulator to 'Verilog Compiler Simulator'.

Change the Compiled library location to the path that was used for compiling libraries.

When creating new projects the following should have configured in the project.

In the Compilation tab, for vcs.compile.vlogan.more_options add in the following value.

`-ntb_opts tb_timescale=1ps/1ps -timescale=1ps/1ps -sverilog +systemverilogext+.sv +libext+.sv +libext+.v -full64 -lca -v2005 +v2k +define+VCS_SIM +lint=TFIPC-L`

Certain 3rd party simulators might need the explicit include path to the design directory for provided RTL example designs like cl\_hello\_world and cl\_dram\_dma.  For Verilog options select the ... box and click the + button under Verilog Include Files Search Paths.  Select the path to the cl/cl\_example/design directory.

Click OK, Click Apply, Click OK to back into the Vivado project.

**Q: How to add DPI support for VCS simulator with GUI flow?**

The project needs to be configured based upon the above question/answer for adding VCS simulator support.  When creating new projects the following should have configured in the project.

In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test_null.c script.  This file can be copied and modified to another area where an example exists for other .c stimulus.

`set_property -name {vcs.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]`

Right click on SIMULATION in the Project Manager and select Simulation Settings.

In the Simulation tab, for vcs.simulate.vcs.more_options add in the following value.

`-sv_lib libdpi`

**Q: How to use IES simulator with GUI flow?**

For IES, libraries need to be compiled and the following changes are needed to the Vivado GUI project.  Note the user must install IES and handle the licenses (not described in this document).

Invoke vivado (no project needs to be open).  In the TCL console run the following compile to compile libraries.

`compile_simlib -simulator ies -directory path/simlib/2017.1_ies_sdx`

Open any Vivado project where simulation needs to be changed to IES.  Note DPI framework is required with this simulator.

Right click on SIMULATION in the Project Manager and select Simulation Settings.

Change Target simulator to Incisive Enterprise Simulator. Click Yes to change the simulator to 'Incisive Enterprise Simulator'.

Change the Compiled library location to the path that was used for compiling libraries.

When creating new projects the following should have configured in the project.

In the Compilation tab, for ies.compile.ncvlog.more_options add in the following value.

`+define+SV_TEST +define+SCOPE +define+IES_SIM`

In the Elaboration tab, for ies.elaborate.ncelab.more_options add in the following value.

`+libext+.v+.sv -disable_sem2009  -timescale 1ps/1ps`

In the Simulation tab, for ies.simulate.ncsim.more_options add in the following value.

`-sv_lib libdpi`

For ies.simulate.runtime, delete the value and leave empty.

Certain 3rd party simulators might need the explicit include path to the design directory for provided RTL example designs like cl\_hello\_world and cl\_dram\_dma.  For Verilog options select the ... box and click the + button under Verilog Include Files Search Paths.  Select the path to the cl/cl\_example/design directory.

Click OK, Click Apply, Click OK to back into the Vivado project.

In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test_null.c script.  This file can be copied and modified to another area where an example exists for other .c stimulus.

`set_property -name {ies.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]`

**Q: With IP Integrator flow with AWS IP configured with no DDR4 in the CL, why does errors show up with Vivado Simulator?**

This is a known issue and will be fixed in a later release. For now type in run -all 3 times or more for the simulation to bypass the error with missing .mem files.

**Q: With IP Integrator Flow, why does the DDR4 IPs and Reg Slice IP need to be disabled with DDR4 in the CL enabled ?**

This is a known issue and will be fixed in a future release. At this time the AWS IP and DDR4 IPs in the HDK area conflict when simulation sources that are generated.

Disabling the HDK area IPs allows for DDR4 sources to come directly from the AWS IP only.  If sources coming from both IPs, missing .mem files will appear in the simulator
causing errors.

<a name="impl"></a>
# Synthesis/Implementation

**Q: What are the advantages of using Out of Context(OOC) runs instead of global runs for IPs?**

Global synthesis for IPs will require synthesis to be run every time a design synthesis run is kicked off.  However, with RTL flow at this time IPs only support global mode at this time.  

OOC builds the synthesized one time where the dcp and cache is saved.  When executing a design synthesis the .dcp and cache is reused which saves building time. Current IP Integrator flows supports this method.


**Q: Why do critical warnings show up in synthesis with the AWS IP when no DDR4 memories enabled in the CL?**

This is a known issue and should be fixed in a future release. These critical warnings can safely be ignored.

**Q: How to change synthesis/implementation options?**

Currently synthesis is using default directives and implementation tools using Explore as directives.  At this time in all cases don't use strategies for synthesis and implementation only change directives.   

