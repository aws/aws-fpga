# Vivado AWS HLx - Frequently Asked Questions

## Table of Content

[AWS IP](#ip)

[Vivado Project Flows](#proj)

[Simulation](#sim)

[Synthesis/Implementation](#impl)



<a name="ip"></a>
**Q: **

<a name="proj"></a>
**Q: Why does a critical warning appear for DDR4?**

The DDR4 IP currently doesn't have a board associated with the XCI that is used with the HLx flow that locks the IP.  The critical warning can
safely be ignored as the IP will not change.

**Q: Why does synth_1 and impl_1 report Out-of-date?**

cl_clocks_aws.xdc is dynamically created before synthesis which makes the sources out of date.
The status can be safely ignored. However, right clicking on impl_1 and then synth_1 and select
Force Up-To-Date to get the correct status.

cl_clocks_aws.xdc is dynamically created before synthesis which makes the sources out of date.
The status can be safely ignored. However, right clicking on impl_1 and then synth_1 and select
Force Up-To-Date to get the correct status.

**Q: Why is cl_pnr_user.xdc file disabled in the project?**

This file is used when the SH and CL are linked during implementation.  The file is disabled for the flow at this time and will be enabled with future versions of the tools.


**Q: How does the user encrypt RTL sources or IP sources in the BD with the IP Integrator Flow?**

This is not supported at this time.

**Q: How does the user encrypt RTL sources with the RTL flow?**

This is not supported at this time. However, the user can try the following manual flow.

Add RTL unencrypted sources as simulation only sources.
Simulation passes user tests.
User modified encrypt.tcl to encrypted unencrypted source to another area/directory and sources the tcl in vivado in batch mode. 
Add RTL encrypted sources directory as sources.
On each encrypted source file in the Source tab, deselect USED_IN_SIMULATION.

**Q: What IP Integrator Flows are supported with this release for user RTL?**

RTL Referencing Flow is supported. An example is provided in the AWS Tutorials Examples documentation.
For advanced flows, using IP Packager is supported as well (no examples provided currently)


**Q: What limitations are with the RTL Referencing Flow and IP Packager?**

VHDL/Verilog only (System Verilog not supported)


<a name="sim"></a>

**Q: What simulators and simulation flows are supported with this release?**

Currently only Vivado Simulator is supported at this time.
System Verilog testbench .sv/BFM flow supported. 
No DPI simulation (C simulation is not supported)

**Q: With IP Integrator flow with AWS IP configured with no DDR4 in the CL, why does errors show up with Vivado Simulator?**

This is a known issue and should be fixed in the next release. For now type in run -all 3 times for the simulation to bypass the error with missing .mem files.

**Q: With IP Integrator Flow, why does the DDR4 IPs and Reg Slice IP need to be disabled with DDR4 in the CL enabled ?**

This is a known issue and should be fixed in the next release. At this time the AWS IP and DDR4 IPs in the HDK area conflict when simulation sources that are generated.
Disabling the HDK area IPs allows for DDR4 sources to come directly from the AWS IP only.  If sources coming from both IPs, missing .mem files will appear in the simulator
causing errors.


<a name="impl"></a>
**Q: What are the advantages of using OOC(Out of Context) runs instead of global runs for IPs?**

Global synthesis for IPs will require synthesis to be run every time a design synthesis run is kicked off.  However, with RTL flow at this time IPs only support global mode at this time.  
OOC builds the synthesized one time where the dcp and cache is saved.  When executing a design synthesis the .dcp and cache is reused which saves building time. Current IP Integrator flows supports this method.


**Q: Why do critical warnings show up in synthesis with the AWS IP when no DDR4 memories enabled in the CL?**

This is a known issue and should be fixed in the next release. These critical warnings can safely be ignored.

**Q: How to change synthesis/implementation options?**

Currently right now synthesis is using default directives and implementation tools using Explore as directives.  
At this time in all cases don't use strategies for synthesis and implementation only change directives.   

