SDE CL Example Simulation
=========================

Table of Contents
-----------------

- `SDE CL Example Simulation <#sde-cl-example-simulation>`__

  - `Table of Contents <#table-of-contents>`__
  - `Overview <#overview>`__
  - `Dump Waves <#dump-waves>`__

Overview
--------

This readme provides information about the simulation environment for
the ``cl_sde`` example. For more details about overall HDK simulation
environment and CL bringup in simulation please refer to `RTL Simulation
Guide for HDK Design
Flow <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md>`__.

The system verilog simulation tests can be run from the
``$CL_DIR/verif/scripts/`` directory with all supported simulators. You
can run each test by setting ``TEST=\<Test Name\>``.

.. code:: bash

   cd aws-fpga
   source hdk_setup.sh
   cd hdk/cl/examples/cl_sde
   export CL_DIR=$(pwd)
   cd ${CL_DIR}/verif/scripts

Run the tests

.. code:: bash

   make TEST=test_simple_h2c (Runs with XSIM by default)
   make TEST=test_simple_c2h (Runs with XSIM by default)

   make TEST=test_simple_h2c VCS=1
   make TEST=test_simple_c2h VCS=1

   make TEST=test_simple_h2c QUESTA=1
   make TEST=test_simple_c2h QUESTA=1

Dump Waves
----------

For information about how to dump waves with XSIM or VCS, please refer
to
`debugging-custom-logic-using-the-aws-hdk <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md#debugging-custom-logic-using-the-aws-hdk>`__
