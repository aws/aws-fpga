# Virtual JTAG for Real-time FPGA Debug
  
# Overview

EC2 FPGA platforms supports Virtual JTAG capability, by emulating JTAG over PCIe. 

Xilinx Virtual Cable (XVC) allows Vivado to connect to hardware device to connect FPGA designs with hardware debug cores like ILA, VIO, and others. XVC on top of AWS Virtual JTAG allows similar debug flow to what traditionally used actual JTAG to connect to a physical FPGA, to perform debug through Vivado to perform the debug. With XVC on top of AWS FPGA, developer can get Integrated Logic Analyzer (ILA) waveform capture, VIO debug control, and interaction with other Xilinx debug cores through the Vivado debug tools.

There are three main components which enable XVC debug an AWS FPGA enabled instances like F1, shown in the following figure:  

- **[A]** XVC-Server running on F1 instance (or any other EC2 instance with Xilinx FPGA).  

-	**[B]** XVC-AWS linux kernel driver, running on F1 instance.  

- **[C]** Debug cores (CL Debug Bridge, Xilinx ILA, VIO etc) inside the FPGA CustomLogic (CL) portion.  


# Embedding Debug Cores in CL

The Custom Logic (CL) is required to include the [CL Debug Bridge](../common/shell_latest/TBD) provided by AWS as part of the HDK, and any required standard Xilinx debug IP components like ILAs and VIOs. 

The following list describes the steps to successfully setup debug in a CL where debug is required:  

**Step 1:**	CL Debug Bridge must be instanciated at top-level of the CL, and the nets connecting to the CL Debug Bridge must have the same as the port names of the CL Debug Bridge, except the clock. The clock to the CL Debug Bridge should be one of the 8 input CL clocks. When the net names are correct, these nets connect should automatically to the top level of the CL. The below code snippet shows the instance fthe CL Debug Bridge.

```
cl_debug_bridge CL_DEBUG_BRIDGE (
      .clk(clk_main_a0),
      .drck(drck),
      .shift(shift),
      .tdi(tdi),	
      .update(update),
      .sel(sel),
      .tdo(tdo),
      .tms(tms),
      .tck(tck),
      .runtest(runtest),
      .reset(reset),
      .capture(capture),
      .bscanid(bscanid)
   );
```  
  
  
**Step 2:**	To instance Xilinx' [Integrated Logic Analyzer (ILA)](https://www.xilinx.com/products/intellectual-property/ila.html), an ILA IP should be created using Vivado IP Catalog and it should be customized according to the desired probes. The ILA can be instanced at any level in the hierarchy inside the CL and the nets requiring debug have to be connected probe input ports of the ILA. The clock to the ILA should be the same clock of the clock domain to which the nets under debug belong to. A separate ILA is required for nets belonging to different clock domains. (Please see section “Suggested Background” for more details).

3)	To instance a VIO, VIO IP should be created using Vivado IP Catalog and it should be customized as desired. The VIO can be instanced at any level in the hierarchy inside the CL and the input/output nets should be connected as desired. The clock to the VIO should be the same clock of the clock domain to which the VIO output/input probe signals belong to. A separate VIO is required for different clock domains. (Please see section “Suggested Background” for more details).

4)	Xilinx implementation tools perform the connections and wiring between the debug IP components (ILAs/VIOs) and the CL Debug Bridge. Care should be taken to set the parameter “chipscope.enablePRflow” to true using the following tcl command during synthesis and implementation. This is automatically included if the CL synthesis and implementation scripts are used from the HDK.
set_param chipscope.enablePRFlow true

4.2	Connecting Vivado to the XVC over PCIe Enabled FPGA 
The required AFI, containing the CL containing the CL Debug Bridge and other required debug IP components, should be loaded to the FPGA. Following a successful AFI load, the software components required for debugging over XVC will need to be used. 

