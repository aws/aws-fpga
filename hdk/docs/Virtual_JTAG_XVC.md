# Virtual JTAG for Real-time FPGA Debug

## Table of Content

1. [Overview](#overview)  

2. [Embedding Debug Cores in CL/AFI](#embeddingDebugCores)  

3. [Enabling Debug on FPGA-enabled EC2 Instance, using XVC](#startVJtag)

4. [Connecting Xilinx Hardware Manager(Vivado Lab Edition) to the Debug Target FPGA-enabled EC2 Instance](#connectToTarget)

5. [Frequently Asked Questions](#faq)





<a name="overview"></a>
# Overview 

EC2 FPGA platforms supports Virtual JTAG capability, by emulating JTAG over PCIe

To take advantage of this capability, [AWS FPGA Management Tools](./../../sdk/management/fpga_image_tools/README.md) enables running an in-target service (in Linux userspace), implementing Xilinx Virtual Cable (XVC) protocol, which allows (local or remote) Vivado to connect to target FPGA for debug leveraging standard Xilinx standard debug cores like [Integrated Logic Analyzer - ILA](https://www.xilinx.com/products/intellectual-property/ila.html), [Virtual Input/Output - VIO](https://www.xilinx.com/products/intellectual-property/vio.html), and others. 

Traditionally, a physical JTAG connection is used to debug FPGAs.  AWS have developed a virtual JTAG, leveraging Xilinx XVC, for debug flow that enables debug in the cloud.

There are three main components which enable XVC debug an AWS FPGA enabled instances like F1, shown in the following figure:  

- **[A]** [Debug cores](#embeddingDebugCores) like CL Debug Bridge, Xilinx ILA, VIO, etc., inside the FPGA CustomLogic (CL) portion. It is the developer's responsibility to instance these cores in the CL design, with [CL Hello World Example](../cl/examples/cl_hello_world/)

- **[B]** [Virtual-JTAG service](#startVJtag) acting as XVC Server, running on target F1 instance (or any other EC2 instance with Xilinx FPGA).  

-	**[C]** [(Local or Remote) Vivado](#connectToTarget) application for interactive debug.

![alt tag](./images/Virtual_JTAG_XVC_Server.jpg)  
  
  
<a name="embeddingDebugCores"></a>
# Embedding Debug Cores in CL 

The Custom Logic (CL) is required to include the [CL Debug Bridge](../common/shell_latest/TBD) provided by AWS as part of the HDK, and any required standard Xilinx debug IP components like ILAs and VIOs. 

The following list describes the steps to successfully setup debug in a CL:  

**Step 1:**	CL Debug Bridge must be instantiated at top-level of the CL, and the nets connecting to the CL Debug Bridge must have the same as the port names of the CL Debug Bridge, except the clock. The clock to the CL Debug Bridge should be one of the 8 input CL clocks. When the net names are correct, these nets should connect automatically to the top level of the CL. The below code snippet shows the instance for the CL Debug Bridge.

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
  
  
**Step 2:**	To instance Xilinx' [Integrated Logic Analyzer (ILA)](https://www.xilinx.com/products/intellectual-property/ila.html). An ILA IP should be created using Vivado IP Catalog and it should be customized according to the desired probes. The ILA can be instanced at any level in the hierarchy inside the CL and the nets requiring debug have to be connected with the probe input ports of the ILA. The clock to the ILA should be the same clock of the clock domain to which the nets under debug belong to. A separate ILA is required for nets belonging to different clock domains. (Please see [Xilinx UG908](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_4/ug908-vivado-programming-debugging.pdf) for further details)

**Step 3:**	To instance Xilinx' [Virtual Input/Output (VIO)](https://www.xilinx.com/products/intellectual-property/vio.html). A VIO IP should be created using Vivado IP Catalog and it should be customized as needed. The VIO can be instanced at any level in the hierarchy inside the CL and the input/output nets should be connected as desired. The clock to the VIO should be the same clock of the clock domain to which the VIO output/input probe signals belong to. A separate VIO is required for different clock domains. (Please see [Xilinx UG908](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2016_4/ug908-vivado-programming-debugging.pdf) for further details)

**Step 4:**	Xilinx Vivado implementation tools perform the connections and wiring between the debug IP components (ILAs/VIOs) and the CL Debug Bridge. Care should be taken to set `set_param chipscope.enablePRFlow true` in the tcl command during synthesis and implementation. This is automatically included if AWS CL Build scripts are delivered with this HDK.

<a name="startVJtag"></a>
# Starting Virtual JTAG (XVC) Debug Server on the Target FPGA-enabled EC2 Instance 

To start debugging a given FPGA slot, which has the [CL debug cores](#embeddingDebugCores), the developer needs to call FPGA Management Tool `$ fpga-start-virtual-jtag` from Linux shell on the target instance (i.e. AWS EC2 F1 instance). This management tool starts Xilinx's Virtual Cable (XVC) service for a given FPGA slot, listening to a given TCP port.

``` 

$ sudo fpga-start-virtual-jtag -P 10201 -S 0
Starting Virtual JTAG XVC Server for FPGA slot id 0, listening to TCP port 10201.
Press CTRL-C to stop the service.

```

You could call `sudo fpga-start-virtual-jtag -?` for further details on the available options and general help using this tool.
  
  

<a name="connectToTarget"></a>
# Connecting Xilinx Hardware Manager (Vivado Lab Edition) to the Debug Target FPGA-enabled EC2 Instance 

The interactive debug can use Xilinx Hardware Manager (Vivado Lab Edition) running on the target instance (i.e. the F1 itself) or it can be running remotely on a different host. The TCP port on which the Virtual JTAG XVC Server is listening must be accessible to the host running Xilinx Hardware Management (See [FAQ](#faq) for configuring Linux firewall and AWS EC2 Network Security Groups). 

To connect the debug Xilinx Hardware Manager to Virtual JTAG XVC server on the target, the following should be called on the machine hosting Vivado:

1)	Launch Vivado Lab Edition (or full featured Vivado) 

2)	Select “Open HW Manager”

3)	Start Vivado hw_server using the following command in the Vivado .tcl console
`> connect_hw_server`  

4)	Connect to the target instance Virtual JTAG XVC server using the following command in the Vivado tcl console. 
`> open_hw_target -xvc_url <hostname or IP address>:10201`

The Vivado Hardware panel will be populated with a debug bridge instance. 
 
**Note:** At this point the Virtual JTAG XVC-server running on the target should acknowledge the Vivado connection by printing the following in `dmesg` log:

`**TBD8*`

5)	Select the debug bridge instance from the Vivado Hardware panel.

6)	In the Hardware Device Properties window select the appropriate “Probes file” for your design by clicking the icon next to the “Probes file” entry, selecting the file, and clicking “OK”. This will refresh the hardware device and it should now show the debug cores present in your design.
 
Vivado can now be used to debug your design.

The connection Vivado and the target instance can be terminated by closing the XVC server from Vivado using the right click menu. If the target FPGA PCIe connection is lost, a new AFI is loaded or the Virtual JTAG Server application stops running, the connection to the FPGA and associated debug cores will also be lost. 

**NOTE:** Xilinx Hardware Manager (Vivado Lab Edition) should not be connected to the target Virtual JTAG XVC Server when the AFI is not in READY state. If the AFI going to go through `fpga-clear-image` or `fpga-load-local-image`, Vivado should be disconnected, and the Virtual JTAG XVC Server should be terminated. (TBD - how to terminate)
  
    
<a name="faq"></a>
# Frequently Asked Questions 
  
  
  
**Q: Do I need to run Vivado or Hardware Manager on target EC2 instance to debug?**  
  
  
**Q: How do I configure Linux firewalls and EC2 network security groups to enable remote debug?**
 
 
**Q: Can I have a secure connection (i.e. SSL/TLS) to the target FPGA-enable EC2 Instance running Virtual JTAG service?**

 
**Q: Do I need a Vivado license to use Virtual JTAG and Xilinx' VIO / LIA debug capabilities?**
  
  
  
**Q: How do I stop the Virtual JTAG service on the target instance?**
  
  
  
**Q: Can I debug multiple FPGAs on same target EC2 instance concurrently?**



**Q: What are some of the best practices I should be aware when working with Virtual JTAG?**


**Q: Can other instances running on the same F1 server access the Virtual JTAG of my instance?**


**Q: What is XVC and where can I learn about it?""

Xilinc Virtual Cable (XVC) is a protocol for transferring JTAG commands over TCP/IP network connection between a debug tool (like Vivado Lab Edition Hardware Manager) and a debug target.

The full specification for XVC version 1.0 is available [here](https://github.com/Xilinx/XilinxVirtualCable/blob/master/README_XVC_v1_0.txt).  