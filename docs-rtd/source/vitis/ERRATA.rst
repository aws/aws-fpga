Vitis Errata
============

Examples
--------

The following examples are not currently supported by AMD:

- ``host_xrt/host_memory_copy_buffer_xrt``
- ``host_xrt/host_memory_copy_kernel_xrt``
- ``host_xrt/host_memory_simple_xrt``
- ``host_xrt/multiple_cus_asymmetrical_xrt``
- ``host_xrt/p2p_fpga2fpga_xrt``
- ``host_xrt/p2p_simple_xrt``
- ``performance/kernel_global_bandwidth``
- ``performance/host_global_bandwidth``
- ``performance/host_memory_bandwidth``
- ``performance/host_memory_bandwidth_xrt``
- ``sys_opt/multiple_devices``

Hardware Emulation
------------------

The following examples do not support Hardware Emulation runtime
simulation.

- ``rtl_kernels/rtl_vadd_hw_debug``
- ``host_xrt/kernel_chain``

.. _vitis-20241:

Vitis 2024.1
------------

For this tool version, the following designs do not meet timing and have
reduced HBM clock speeds:

- ``host_xrt/copy_buffer_xrt``

  - Actual: 425MHz
  - Expected: 450MHz

- ``performance/iops_test_xrt``

  - Actual: 437MHz
  - Expected: 450MHz
