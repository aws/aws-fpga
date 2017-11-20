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

When using the Vivado GUI, the Vivado Simulator is supported and is the default simulator.  

We plan to support other linking in 3rd party vendor simulator support.  However, Questa simulator is supported (see next question/answer)

Customer example System Verilog testbench (.sv/BFM) is supported

When using the Vivado GUI, DPI simulation (C simulation is not supported) is not supported at this time.

**Q: How to use Questa simulator with GUI flow?**

For Questa, libraries need to be compiled and the following changes are needed to the Vivado GUI project.  Note the user must install Questa and handle the licenses (not described in this document).

Invoke vivado (no project needs to be open).  In the TCL console run the following compile to compile libraries.

compile_simlib -simulator questa -directory path/simlib/2017.1\_sdx 

Open any Vivado project where simulation needs to be changed to Questa.

Right click on SIMULATION in the Project Manager and select Simulation Settings.

Change Target simulator to Questa Advanced Simulator. Click Yes to change the simulator to 'Questa Advanced Simulator'.

Change the Compiled library location to the path that was used for compiling libraries.

For Verilog options select the ... box and add the following Defines.

`QUESTA_SIM`

In the Compilation tab, for questa.compile.vlog.more_options add in the following value.

`-timescale 1ps/1ps`

Click OK, Click Apply, Click OK to back into the Vivado project.


**Q: With IP Integrator flow with AWS IP configured with no DDR4 in the CL, why does errors show up with Vivado Simulator?**

This is a known issue and should be fixed in the next release. For now type in run -all 3 times for the simulation to bypass the error with missing .mem files.

**Q: With IP Integrator Flow, why does the DDR4 IPs and Reg Slice IP need to be disabled with DDR4 in the CL enabled ?**

This is a known issue and should be fixed in a future release. At this time the AWS IP and DDR4 IPs in the HDK area conflict when simulation sources that are generated.

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

