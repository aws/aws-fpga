.. _software-performance-optimizations-for-f248xlarge-instances:

Software Performance Optimizations for F2.48xlarge Instances
============================================================

This guide outlines strategies for maximizing performance on
``f2.48xlarge`` instances through effective CPU-to-FPGA mapping and NUMA
optimization. In dual-socket configurations, implementing NUMA-aware
techniques is essential for minimizing latency and maximizing PCIe
bandwidth between CPUs and FPGA accelerators. The optimizations within
this document do not apply to ``f2.6xlarge`` and ``f2.12xlarge``
instances because all CPU resources, memory, NVMe devices, and FPGA
devices are on a single NUMA node.

Quick Start Guide
-----------------

To optimize your application's performance running on an ``f2.48xlarge``
instance, refer to the `Script to Construct a FPGA to NUMA Node and vCPU
Mapping <#script-to-construct-an-fpga-to-numa-node-and-vcpu-mapping>`__
or follow the steps below:

1. Determine the FPGA slot numbers using ``fpga-describe-local-image``
2. Locate the optimal vCPUs for your slot in the `mapping
   table <#ideal-vcpu-to-fpga-mapping-for-optimal-pcie-performance>`__
3. Apply CPU pinning using either:

   - ``numactl --localalloc --physcpubind <vCPU list> <bash command>``
     command
   - Application-specific CPU affinity settings

F2 Instance Overview
--------------------

The ``f2.48xlarge`` instance consists of 2 AMD Milan CPUs in a
dual-socket configuration with 192 vCPUs, 2,048 GiB (2 TiB) of memory,
7,600 GiB across 8 NVMe SSDs, and 8 FPGAs. Each socket directly connects
to 96 vCPUs, 1 TiB of memory, 3,800 GiB across 4 NVMe SSDs, and 4 FPGAs.
The networking interface directly connects to CPU socket 0.

Linux System Tools
~~~~~~~~~~~~~~~~~~

The following Linux tools help verify system configuration:

============== ========================= ==========================
Tool           Purpose                   Installation/Usage
============== ========================= ==========================
``lspci -tv``  View PCI topology         Built-in
``lstopo``     Visualize system topology ``sudo apt install hwloc``
``lscpu -e``   View CPU/NUMA mapping     Built-in
``numactl -H`` Show NUMA configuration   Built-in
============== ========================= ==========================

Note: For FPGA visibility, use ``lstopo --whole-io`` or
``lstopo-no-graphics --whole-io``

NUMA Best Practices for F2 Instances
------------------------------------

NUMA (Non-Uniform Memory Access) is a computer memory design where
memory access time depends on the memory location relative to a
processor. In a NUMA system, a processor can access its own local memory
faster than non-local memory (memory local to another processor or
memory shared between processors). The ``f2.48xlarge`` instance has two
NUMA nodes, each associated with a CPU socket and all colocated devices:

- Each NUMA node contains:

  - 96 vCPUs
  - 1 TiB of local memory
  - 4 FPGAs
  - 4 NVMe drives

- Memory access characteristics:

  - Local memory access (same NUMA node) results in the lowest latency
  - Remote memory access (different NUMA node) results in higher latency

Why NUMA Matters
~~~~~~~~~~~~~~~~

NUMA awareness is crucial for performance because:

1. Local memory access is significantly faster than remote access
2. PCIe devices (like FPGAs) perform best when the controlling process
   runs on CPUs in the same NUMA node
3. Memory bandwidth is higher for local access
4. Improper NUMA alignment can cause significant performance degradation

This is why the `vCPU to FPGA mapping
table <#ideal-vcpu-to-fpga-mapping-for-optimal-pcie-performance>`__ in
this guide is important - it ensures your application uses the optimal
CPU cores for each FPGA device.

Identifying the CPU to FPGA NUMA Mapping
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``bus:device:function`` (BDF) mapping of FPGA devices is in slot
order. On an f2.48xlarge instance, the lowest BDF hex value will be slot
0 and the highest BDF hex value will be slot 7. The
``fpga-describe-local-image`` command will display this:

.. code:: bash

   $ sudo fpga-describe-local-image -S 0 -H
   Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
   AFI          0       No AFI                  cleared           1        ok               0       0x10162423
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    0       0x1d0f      0x9048      0000:9f:00.0```

   The NUMA node for this device can be found in the Linux PCI hierarchy:

   ```bash
   $ cat /sys/bus/pci/devices/0000\:9f\:00.0/numa_node
   1

The vCPU NUMA node mappings can be found with ``numactl -H``. An
``f2.48xlarge`` instance would display the following:

.. code:: bash

   $ numactl -H
   available: 2 nodes (0-1)
   node 0 cpus: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136 137 138 139 140 141 142 143
   node 0 size: 1023962 MB
   node 0 free: 1021988 MB
   node 1 cpus: 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 144 145 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190 191
   node 1 size: 1023981 MB
   node 1 free: 1022619 MB
   node distances:
   node   0   1
     0:  10  32
     1:  32  10

Ideal vCPU to FPGA Mapping for Optimal PCIe Performance
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Processes can be pinned to particular vCPUs by using Linux tools such as
``numactl``. The "Optimal vCPUs" below refer to the optimal 16 vCPUs
(shared L3 cache) for that slot. Below is a table of the optimal vCPUs
for each FPGA slot on an ``f2.48xlarge`` instance.

.. list-table::
  :header-rows: 1
  :class: f2-numa-table
  :widths: 20 20 20 20 20

  * - FPGA Slot #
    - NUMA Node
    - Optimal vCPUs
    - Example of ``numactl`` command
    - Colocated vCPUs
  * - 0
    - 1
    - 48-55, 144-151
    - ``numactl --localalloc --physcpubind 48,55``
    - 48-95, 144-191
  * - 1
    - 1
    - 56-63, 152-159
    - ``numactl --localalloc --physcpubind 56,63``
    - 48-95, 144-191
  * - 2
    - 1
    - 64-71, 160-167
    - ``numactl --localalloc --physcpubind 64, 71``
    - 48-95, 144-191
  * - 3
    - 1
    - 72-79, 168-175
    - ``numactl --localalloc --physcpubind 72, 79``
    - 48-95, 144-191
  * - 4
    - 0
    - 0-7, 96-103
    - ``numactl --localalloc --physcpubind 0, 7``
    - 0-47, 96-143
  * - 5
    - 0
    - 8-15, 104-111
    - ``numactl --localalloc --physcpubind 8, 15``
    - 0-47, 96-143
  * - 6
    - 0
    - 16-23, 112-119
    - ``numactl --localalloc --physcpubind 16, 23``
    - 0-47, 96-143
  * - 7
    - 0
    - 24-31, 120-127
    - ``numactl --localalloc --physcpubind 24, 31``
    - 0-47, 96-143

**NOTE:** in place of the ``--physcpubind <vCPU list>`` argument, users
can also pass in ``--cpunodebind <NUMA node ID``

Script to Construct an FPGA to NUMA Node and vCPU Mapping
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Execute the following bash command to construct a table that maps the
FPGA devices to their NUMA node and colocated vCPUs:

.. code:: bash

   (
       printf "%-8s %-11s %-11s %-13s %-10s %s\n" "SLOT" "VENDOR_ID" "DEVICE_ID" "BDF" "NUMA_NODE" "vCPUs_(Physical,Virtual)"
       sudo fpga-describe-local-image-slots | while read -r dev slot vendor device bdf; do
           numa_node=$(sudo cat /sys/bus/pci/devices/$bdf/numa_node)
           vcpus=$(lscpu -p=CPU,NODE | grep "^[0-9]*,$numa_node$" | cut -d',' -f1)

           # Organize CPUs into ranges
           physical_cpus=$(echo "$vcpus" | awk -v ORS='' '
               function print_range(start, end) {
                   if (start == end) return start;
                   return start "-" end;
               }
               NR==1 {start=end=$1; prev=$1; next}
               {
                   if ($1 != prev+1) {
                       printf "%s,", print_range(start, end);
                       start=$1;
                   }
                   end=$1;
                   prev=$1;
               }
               END {printf "%s", print_range(start, end)}
           ')

           printf "%-8s %-11s %-11s %-13s %-10s %s\n" \
               "$slot" "$vendor" "$device" "$bdf" "$numa_node" "$physical_cpus"
       done
   ) | column -t

Sample output from a ``f2.48xlarge`` instance:

.. code:: bash

   SLOT  VENDOR_ID  DEVICE_ID  BDF           NUMA_NODE  vCPUs_(Physical,Virtual)
   0     0x1d0f     0x9048     0000:9f:00.0  1          48-95,144-191
   1     0x1d0f     0x9048     0000:a1:00.0  1          48-95,144-191
   2     0x1d0f     0x9048     0000:a3:00.0  1          48-95,144-191
   3     0x1d0f     0x9048     0000:a5:00.0  1          48-95,144-191
   4     0x1d0f     0x9048     0000:ae:00.0  0          0-47,96-143
   5     0x1d0f     0x9048     0000:b0:00.0  0          0-47,96-143
   6     0x1d0f     0x9048     0000:b2:00.0  0          0-47,96-143
   7     0x1d0f     0x9048     0000:b4:00.0  0          0-47,96-143

--------------

Frequently Asked Questions (FAQ)
--------------------------------

How can I investigate system performance issues?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To Investigate low performance (high latency or decreased bandwidth)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- Verify the process accessing the FPGA is being served by the expected
  vCPU with ``top -H -p <pid>``
- Check the NUMA alignment by hand with ``numactl --hardware``
- Monitor the PCIe traffic on AMD processors with tools such as
  `amd-uprof <https://www.amd.com/en/developer/uprof.html>`__

To Investigate inconsistent performance (latency or bandwidth spikes)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- Ensure no other processes are using the same vCPUs with tools such as
  ``htop``
- Monitor system resources with ``sar``
- Verify memory allocation with ``numastat``

Where can I reach out for additional help?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For any issues with the devkit documentation or code, please open a
`GitHub issue <https://github.com/aws/aws-fpga/issues>`__ with all steps
to reproduce.

For questions about F2 instances, please open a `re:Post issue with the
'FPGA Development'
tag <https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development>`__.

`Back to SDK README <../README.html>`__