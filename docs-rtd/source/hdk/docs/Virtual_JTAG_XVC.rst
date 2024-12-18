Virtual JTAG for Real-time FPGA Debug
=====================================

Table of Contents
-----------------

- `Virtual JTAG for Real-time FPGA
  Debug <#virtual-jtag-for-real-time-fpga-debug>`__

  - `Table of Contents <#table-of-contents>`__
  - `Overview <#overview>`__
  - `Install XVC Driver on F2
    Instances <#install-xvc-driver-on-f2-instances>`__
  - `Start Local Debug Server on F2
    Instances <#start-local-debug-server-on-f2-instances>`__
  - `Connect to target FPGA via Virtual
    JTAG <#connect-to-target-fpga-via-virtual-jtag>`__
  - `Start Remote Debug Server on F2 Instances (Coming
    Soon) <#start-remote-debug-server-on-f2-instances-coming-soon>`__
  - `Embedded Debug Bridge in CL <#embedded-debug-bridge-in-cl>`__
  - `Frequently Asked Questions <#frequently-asked-questions>`__

Overview
--------

Amazon EC2 F2 instances offer debugging capabilities through Virtual
JTAG. This feature leverages the Xilinx Virtual Cable (XVC) protocol to
emulate JTAG cable connectivity to a target FPGA over the PCIe
interface. Developers can connect to Xilinx debug cores, such as the
`Integrated Logic Analyzer
(ILA) <https://www.xilinx.com/products/intellectual-property/ila.html>`__
and `Virtual Input/Output
(VIO) <https://www.xilinx.com/products/intellectual-property/vio.html>`__
in Custom Logic (CL) designs within Vivado, to monitor, control, and
debug their designs.

The Virtual JTAG solution consists of three main elements:

- [A] Debug cores and a debug bridge that must be implemented and
  connected properly in the CL design. Refer to the
  `cl_dram_hbm_dma <../cl/examples/cl_dram_hbm_dma>`__ example design
  for details.
- [B] A Virtual-JTAG service acting as an XVC server that runs on the
  target F2 instance.
- [C] A local or remote Vivado application for interactive debugging.

Install XVC Driver on F2 Instances
----------------------------------

To begin debugging a CL design, the developer must first install the XVC
driver (skip this step if the driver is pre-installed). This section
provides a guide for installing the XVC driver on F2 instances using the
AWS FPGA developer AMI. For detailed compilation and installation
information, refer to the `AMD prodct
guide <https://docs.amd.com/r/en-US/pg195-pcie-dma/Compiling-and-Loading-the-Driver>`__.

- Locate and unzip the XVC driver file from the Vivado tool installation
  directory:

  - ⚠️ Remember to update tool installation directory with the one if
    you own AMI. The example below is for demonstration only.

.. code:: bash

       unzip /opt/Xilinx/Vivado/2024.1/data/xicom/drivers/pcie/xvc_pcie.zip
       cd driver_v0.4

- To correctly bind the XVC driver to the FPGA, update the
  ``PCIE_VENDOR_ID`` and ``PCIE_DEVICE_ID`` in
  ``xvc_pcie_user_config.h`` file:

.. code:: bash

       vim xvc_pcie_user_config.h

       ...
       #define PCIE_VENDOR_ID  0x1D0F // Update to use PF1 for Virtual JTAG
       #define PCIE_DEVICE_ID  0x9248 // Update to use PF1 for Virtual JTAG

       ...
       {
           .name = "",
           .config_space   = AUTO,
           .config_info = {
               .config_vsec_id  = 0x0008,
               .config_vsec_rev = 0x0,
           },
           .bar_info = {
               .bar_index      = 0x2,    // Update to bind to BAR2
               .bar_offset     = 0x0000, // Update to bind to offset 0
           },
       },

⚠️ Developers may encounter a compilation error in some operating
systems due to driver incompatibility, like this:

.. code:: bash

   /home/ubuntu/driver_v0.4/xvc_pcie_driver_base.c:306:25: error: too many arguments to function ‘class_create’
     306 |         xvc_dev_class = class_create(THIS_MODULE, "xil_xvc_class");

- To resolve the error, update the ``xvc_pcie_driver_base.c`` file as
  follows:

.. code:: C

       305 // Register the character device class for the actual files
       306    xvc_dev_class = class_create("xil_xvc_class"); // Remove THIS_MODULE here
       307    if (IS_ERR(xvc_dev_class)) {
       308            xil_xvc_cleanup();
       308            xil_xvc_cleanup();
       309            return PTR_ERR(xvc_dev_class);
       310    }

- Next, compile and install the XVC driver:

.. code:: bash

       sudo su
       cd driver_v0.4
       make install
       depmod -a
       modprobe xilinx_xvc_pci_driver
       lsmod | grep xilinx
       ...
       xilinx_xvc_pci_driver    20480  0 ---> This means XVC driver is successfully installed

Start Local Debug Server on F2 Instances
----------------------------------------

- To start the XVC server on a instance, run the ``xvc_pcie`` executable
  in Vivado installation directory. The application should spit out the
  host server name and port number. These information will later be used
  to create a virtual JTAG cable in Vivado Hardware Manager.

.. code:: bash

       sudo su
       cd /opt/Xilinx/Vivado/2024.1/bin/
       ./xvc_pcie

       Description:
       Xilinx xvc_pcie v2024.1
       Build date : May 22 2024-19:19:01
       Copyright 1986-2018 Xilinx, Inc. All Rights Reserved.

       INFO: XVC PCIe Driver character file - /dev/xil_xvc/cfg_ioc0
       INFO: XVC PCIe Driver configured to communicate with Debug Bridge IP in AXI mode (PCIe BAR space).
       INFO: PCIe BAR index=0x0002 and PCIe BAR offset=0x0000
       INFO: XVC PCIE Driver Loopback test successful.

       INFO: xvc_pcie application started
       INFO: Use Ctrl-C to exit xvc_pcie application

       INFO: To connect to this xvc_pcie instance use url: tcp:ip-172-31-8-59:10200 ---> This shows the host server name and the port nummber

Connect to target FPGA via Virtual JTAG
---------------------------------------

With a XVC server up and running, a Virutal JTAG cable connection to the
target FPGA is ready to be built in Vivado.

- Prior to executing Vivado, verify that the ``.LTX`` probe file from
  the CL design DCP tarball is saved on the instance.

.. code:: bash

       $ tar -tvf 2024_08_21-122520.Developer_CL.tar

       drwxr-sr-x 0 2024-08-21 13:15 to_aws/
       -rw-r--r-- 91676787 2024-08-21 13:15 to_aws/2024_08_21-122520.SH_CL_routed.dcp
       -rw-r--r--   655601 2024-08-21 13:15 to_aws/2024_08_21-122520.debug_probes.ltx ---> This is the probe file
       -rw-r--r--      398 2024-08-21 13:54 to_aws/2024_08_21-122520.manifest.txt

- Open Vivado GUI and select "Open Hardware Manager"

|vjtag_1|

- Click "Open target" and select the "Open New Target...".

|vjtag_2|

- For hardware server setting, connect to "Local server" and click
  "Next"

|vjtag_3|

- Click "Add Xilinx Virtual Cable (XVC)" and put in "Host name" and
  "Port" collected previously from the XVC server. Click "OK" to
  proceed.

|vjtag_4|

- The debug bridge in the target design should be detected and listed in
  "Hardware Targets". Click "Next" and "Finish" to finish setting up the
  Virutal JTAG connection.

|vjtag_5|

- All the debug cores embedded in the CL design should be now listed
  under ``debug_bridge_0``. Highlight ``debug_bridge_0`` and add the CL
  design ``.LTX`` probe file to "Probes file" in the "Hardware Device
  Properties" window. After the probe file gets loaded, the waveform and
  configuration windows will be avaliable for each debug core in Vivado.
  The CL design at this point is ready to be debugged.

|vjtag_6|

Start Remote Debug Server on F2 Instances (Coming Soon)
-------------------------------------------------------

Guide for debugging designs through Vivado running on a remote machine
is coming soon.

Embedded Debug Bridge in CL
---------------------------

The
`CL_Debug_Bridge <./../common/ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_debug_bridge/cl_debug_bridge.xci>`__
IP must be embedded in the CL design to enable the use of debug cores
like ILA and VIO. According to the `AMD user
guide <https://docs.amd.com/r/en-US/ug908-vivado-programming-debugging/Debug-Cores-Clocking-Guidelines>`__,
the clock of ``CL_Debug_Bridge`` must be at least 2.5 times faster than
the JTAG clock. The JTAG clock frequency is fixed at 31.25 MHz in the F2
shells. Therefore, the frequency of the clock connected to the
``CL_Debug_Bridge`` should be at least 2.5 x 31.25 MHz = 78.125 MHz.
Failure to meet this requirement will result in the debug network not
functioning correctly. However, this minimum clock frequency requirement
does not apply to the ILA or VIO debug cores or the rest of the CL
logic. If the CL design is running on a slower clock from the available
clock recipes, care must be taken to ensure that the ``CL_Debug_Bridge``
is clocked at 78.125 MHz or above.

.. code:: verilog

       //-----------------------------------
       // Debug bridge
       //-----------------------------------
       cl_debug_bridge CL_DEBUG_BRIDGE
       (
         .clk                  (aclk       ),
         .S_BSCAN_drck         (drck       ),
         .S_BSCAN_shift        (shift      ),
         .S_BSCAN_tdi          (tdi        ),
         .S_BSCAN_update       (update     ),
         .S_BSCAN_sel          (sel        ),
         .S_BSCAN_tdo          (tdo        ),
         .S_BSCAN_tms          (tms        ),
         .S_BSCAN_tck          (tck        ),
         .S_BSCAN_runtest      (runtest    ),
         .S_BSCAN_reset        (reset      ),
         .S_BSCAN_capture      (capture    ),
         .S_BSCAN_bscanid_en   (bscanid_en )
       );

All debug cores within the Compute Logic (CL) must be connected to the
``CL_Debug_Bridge``. These connections can be automatically inserted
during the design synthesis process. For an example implementation,
please refer to the `synth_cl_dram_hbm_dma.tcl
script <./../cl/examples/cl_dram_hbm_dma/build/scripts/synth_cl_dram_hbm_dma.tcl>`__
in the cl_dram_hbm_dma example.

.. code:: bash

   AWS FPGA: (12:35:47): Connecting debug network

   ## set cl_ila_cells [get_cells [list CL_ILA/CL_DMA_ILA_0 CL_ILA/ddr_A_hookup.CL_DDRA_ILA_0]]
   ## if {$cl_ila_cells != ""} {
   ##   connect_debug_cores -master [get_cells [get_debug_cores -filter {NAME=~*CL_DEBUG_BRIDGE*}]] \
   ##                       -slaves $cl_ila_cells
   ## }

   INFO: [Constraints 18-11670] Building netlist checker database with flags, 0x8
   Done building netlist checker database: Time (s): cpu = 00:00:00.12 ; elapsed = 00:00:00.13 . Memory (MB): peak = 7233.012 ; gain = 0.000 ; free physical = 1006692 ; free virtual = 1545285
   INFO: [Chipscope 16-344] Connected debug slave core CL_ILA/CL_DMA_ILA_0 to master core CL_ILA/CL_DEBUG_BRIDGE/inst/xsdbm
   INFO: [Chipscope 16-344] Connected debug slave core CL_ILA/ddr_A_hookup.CL_DDRA_ILA_0 to master core CL_ILA/CL_DEBUG_BRIDGE/inst/xsdbm
   connect_debug_cores: Time (s): cpu = 00:00:07 ; elapsed = 00:00:07 . Memory (MB): peak = 7233.012 ; gain = 0.000 ; free physical = 1006693 ; free virtual = 1545287

Frequently Asked Questions
--------------------------

**Q: Do I need full Vivado installation to run Virtual JTAG debug on a
F2 instance?**

A: No. If you are utilizing the AWS FPGA developler AMI, you can leverge
the built-in Vivado. If you using a different runtime AMI, you can
download the standalone Vivado Lab Solutions from `AMD
website <https://www.xilinx.com/support/download/index.html/content/xilinx/en/downloadNav/vivado-design-tools.html>`__
and use that for free.

**Q: Do I need a Vivado license to use Virtual JTAG and Xilinx VIO/LIA
debug capabilities?**

A: No. All you require is the Vivado Hardware Manager, which is included
with the Vivado Lab Solutions and is available free of charge.

.. |vjtag_1| image:: ./images/VJTAG_images/vjtag_1.jpg
.. |vjtag_2| image:: ./images/VJTAG_images/vjtag_2.jpg
.. |vjtag_3| image:: ./images/VJTAG_images/vjtag_3.jpg
.. |vjtag_4| image:: ./images/VJTAG_images/vjtag_4.jpg
.. |vjtag_5| image:: ./images/VJTAG_images/vjtag_5.jpg
.. |vjtag_6| image:: ./images/VJTAG_images/vjtag_6.jpg
