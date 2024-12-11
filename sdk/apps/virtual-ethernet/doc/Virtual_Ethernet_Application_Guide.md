# Virtual Ethernet Application Guide

## Table of Contents:

* [Overview](#Overview)

* [Example Workflows](#ExampleWorkflows)

   * ["Hello World" Loopback](#HelloWorldLoopback)

* [FAQ](#FAQ)


<a name="Overview"></a>
## Overview

The Virtual Ethernet architecture ([here](../README.md)) supports your development phases with sample applications that include loopback paths for bringup and debug of the Virtual Ethernet application and custom CL, all the way to end-to-end application integration with live traffic.

## Virtual Ethernet Application Setup and Use
The distinct phases of Virtual Ethernet Application setup and use are:

* Software installation and build
* System setup and device binding (e.g. FPGA and ENI)
* Application setup and start

The next sections walk through the setup and usage phases including example workflows.

<a name="ExampleWorkflows"></a>
## Example Workflows

<a name="HelloWorldLoopback"></a>
### "Hello World" DPDK testpmd loopback mode, auto-start
This example maximizes PPS for 64B packets with a single vCPU using the DPDK testpmd application to drive the DPDK SPP PMD and the FPGA SDE IP.  This may be used for streaming CL bringup and performance measurements in an isolated loopback environment.  It runs testpmd in auto-start mode, sends the first burst of TX packets (32 packets by default), and displays packet statistics every 3 seconds (including PPS).  To exit the example, use `ctrl-c`.

Software installation and build phase

```
cd $(SDK_DIR)/apps/virtual-ethernet/scripts
sudo ./virtual_ethernet_install.py <install_dir>
```

System setup and device bind phase, e.g. on instance boot

```
sudo fpga-load-local-image -S <fpga-slot> -I <SDE loopback CL AGFI>
cd $(SDK_DIR)/apps/virtual-ethernet/scripts
sudo ./virtual_ethernet_setup.py <install_dir>/dpdk <fpga-slot>
```

Testpmd application setup and start phase

```
cd <install_dir>/dpdk
sudo ./build/app/dpdk-testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=3
```

The testpmd application will display the number of TX-packets RX-packets sent to/from the SDE. Everything three seconds, the number of TX-packets and RX-packets will be updated to show the new packet total. In addition, the packets per second throughput is calculated and updated.

```
  ######################## NIC statistics for port 0  ########################
  RX-packets: 28791397   RX-missed: 0          RX-bytes:  1842650496
  RX-errors: 0
  RX-nombuf:  0
  TX-packets: 28791429   TX-errors: 0          TX-bytes:  1842651456

  Throughput (since last show)
  Rx-pps:      4798711          Rx-bps:   2456940768
  Tx-pps:      4798711          Tx-bps:   2456940424
  ############################################################################
```

Please refer to [DPDK testpmd](#testpmd) for a quick reference guide on the supported testpmd features and the link to the full testpmd documentation.

<a name="FAQ"></a>
## FAQ

### Q: What is the AGFI ID for the SDE loopback CL?

The AGFI ID for the SDE loopback CL is found in the `CL_SDE Example Metadata` section at the bottom of the `CL_SDE README` [here](../../../../hdk/cl/examples/cl_sde/README.md).

<a name="testpmd"></a>
### Q: Where can I find DPDK testpmd feature documentation?

The full documentation for DPDK testpmd features is found [here](http://dpdk.org/doc/guides/testpmd_app_ug/index.html).

Note that not all of the DPDK testpmd features are supported by the SPP and ENI PMDs.  SPP supports a limited subset of the DPDK Ethernet upper API (e.g. DPDK eth_dev_ops) to the DPDK application(s) (e.g. testpmd) for purposes of passing through streaming packets to/from the SDE.

The application examples use testpmd auto-start mode.  testpmd also supports an interactive mode that may be used during debug and test sessions.  Interactive mode is especially useful when running testpmd within the `gdb` debugger.  Below is a quick reference guide for some of the supported testpmd interactive mode commands that may be used with the application examples.

### Q: What performance should I expect?

The goal of SPP on F2 is to sustain line rate network bandwidth for all network configurations supported on the AWS FPGA instances.

### Q: How does packet drop and flow control work?

Packet drop and flow control characteristics are application specific, since you are free to use the DPDK drivers and environment in the best way that suits your specific application.

As an example, let’s assume we have a packet forwarding topology that directly connects an ENI to an SPP that does not drop any remaining TX packets after partial TX packet burst has been submitted to ENI.  Since the application is in control of the packet processing, it can flow off the SPP RX side by asking for fewer RX packets in the next call to the SPP RX packet burst API.  If the ENI TX backpressure condition persists, the application may stop calling the SPP RX packet burst API.  At this point, SPP will stop processing RX descriptors, the C2H buffer in the SDE will become full (see the SDE HW Guide [here](./SDE_HW_Guide.md)), and this will backpressure the AXI-Stream interface (e.g. the SDE will de-assert the ‘ready’ signal on the C2H AXI-Stream interface).  This may then backpressure the SPP TX side, which is again under application control.  If the SPP TX side backpressure condition persists, the application may stop processing ENI RX packets and this will eventually cause packet drops on the ENI RX side facing the network.

### Q: How are SDE errors reported?

On each call to the SPP TX/RX packet burst APIs, the DPDK SPP PMD checks the SDE write-back TX/RX status.  If the SDE write-back status is non-zero, the SPP PMD takes the following steps:

* Log-info the TX/RX channel SPP driver status variables and the SDE status write-back variables
* Log-info the specific SDE error info from the SDE block that encountered the error
* Log-info the descriptor ring entries
* Increments the TX/RX sde_error stat
* Log-error and return from the TX/RX status checking method.
* Return 0 packets processed from the SPP TX/RX packet burst APIs (e.g. the DPDK TX/RX packet burst APIs return a uint16_t that indicates the number of packets that were processed in the current call).

Your application should periodically check to see if the TX/RX sde_error stat is non-zero (e.g. by calling the eth_dev_ops xstats_get API for error checking in the `slow-path`).  If the TX/RX sde_error stat is non-zero, your application should take the following error recovery steps:

* Quiesce all calls to TX/RX packet burst (e.g. discontinue calling `rte_eth_dev tx/rx_pkt_burst`)
* Release all of the SPP queues (e.g. call `eth_dev_ops tx/rx_queue_release`)
* Remove the SPP PCI device (e.g. call `rte_pci_driver remove`)
* Reload the AGFI using `fpga-load-local-image` to ensure the CL is fully reset

At this point, the DPDK SPP driver and SDE may be re-initialized as normal.  The SDE is reset during the SPP PCI device probe initialization step, and the TX/RX queues are re-initialized during the TX/RX queue setup phase.

### Q: What is the minimal packet size supported by AWS FPGA virtual ethernet IP?

FPGA CL must generate packets with 64Byte or more to meet the Ethernet minimum frame size requirement.

### Q: What is the maximal packet size?

It is the maximal packet size offered by ENI on your instance (including the 4-byte CRC).

### Q: Should I calculate the Ethernet frame CRC32?

No, SPP relies on the ENI to check CRC on receive and calculate it on transmit.

### Q: What MAC address should I use for SPP?

The SPP MAC address is normally unused for testpmd port based forwarding and defaults to all zeroes.  The default SPP MAC address may be changed if needed using the testpmd ‘mac_addr set’ command when using the testpmd application, or by your custom application using the DPDK APIs.

Note that the SPP and SDE do not perform any modifications to the TX packets (e.g. from the application to the CL), or the RX packets (e.g. from the CL to the application).  The SDE does not perform any packet filtering (e.g. based on the packet destination MAC address).

### Q: How many TX and RX descriptors are supported?

The number of supported TX and RX descriptors per SPP queue pair is parameterized within the SDE block and reported by the SDE to SPP via registers within the SDE block (see the SDE H2C and C2H channels [here](./SDE_HW_Guide.md)).  SPP defines a minimum and the maximum number of descriptors between 64 and 32K.  The number of TX and RX descriptors implemented in the SDE and requested by the DPDK application in the SPP queue setup phase must be equal, and a power of 2.

### Q: How do I configure SPP to use SDE regular or compact descriptors?

The SDE may be built with regular or compact descriptor types (see the C2H_DESC_TYPE and H2C_DESC_TYPE in the Design Parameters section [here](./SDE_HW_Guide.md)).  The SPP PMD also supports regular or compact descriptor types at compile time via the SPP_USE_COMPACT_DESCS define within spp_defs.h.  The default descriptor type for the SDE and SPP is `regular` to support the full 64-bit DMA addressing.  If there is a mismatch between the SDE and SPP descriptor type build options, the SPP driver will log an error similar to the following:

Mismatched build options: SDE descriptor type is `regular`, SPP PMD decriptor type is `compact`.

```
PMD: spp_dev_cap_get(): SDE C2H Desc Info(0x00400000), type=regular, is not supported
```

Mismatched build options: SDE descriptor type is `compact`, SPP PMD decriptor type is `regular`.

```
PMD: spp_dev_cap_get(): SDE C2H Desc Info(0x00800001), type=compact, is not supported
```

### Q: What operating systems are supported?

The Virtual Ethernet application is tested and supported for Linux operating systems (Amazon Linux and Ubuntu).

### Q: How do I update DPDK and SPP with the Vendor/Device ID for my CL?

Within `<install_dir>/dpdk/drivers/net/spp` there is a file called `spp_ethdev.c`.  Your Vendor and Device ID should be added to the following table in `spp_ethdev.c` and then DPDK should be recompiled.

```C
static const struct rte_pci_id pci_id_spp_map[] = {
        { RTE_PCI_DEVICE(PCI_VENDOR_ID_AMAZON, PCI_DEVICE_ID_SDE_LOOPBACK_CL) },
        { RTE_PCI_DEVICE(<Your Vendor ID>, <Your Device ID>) },
        { .device_id = 0 },
};
```

Rebuild DPDK as follows:

```
cd <install dir>/dpdk
ninja -C build
```

Within `<install dir>/dpdk/usertools` there is a file called `dpdk-devbind.py`.  Your Vendor and Device ID should be added to the following table in `dpdk-devbind.py`.

```python
aws_fpga_sde = {'Class': '05', 'Vendor': '1d0f', 'Device': 'f002',
              'SVendor': None, 'SDevice': None}
<your tag> = {'Class': '05', 'Vendor': '<Your Vendor ID>', 'Device': '<Your Device ID>',
              'SVendor': None, 'SDevice': None}

network_devices = [network_class, cavium_pkx, avp_vnic, aws_fpga_sde, <your tag>]
```

You should then run the `virtual_ethernet_setup.py` script which will re-run the `dpdk-devbind.py` script to bind DPDK and SPP to your Vendor and Device Id.
