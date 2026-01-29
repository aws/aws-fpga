HLx GUI Flows with Vivado IP Integrator
=======================================

Table of Contents
-----------------

- `HLx GUI Flows with Vivado IP
  Integrator <#hlx-gui-flows-with-vivado-ip-integrator>`__

  - `Table of Contents <#table-of-contents>`__
  - `Overview <#overview>`__
  - `Create IP Integrator Project with Example
    Design <#create-ip-integrator-project-with-example-design>`__

    - `Create Design <#create-design>`__
    - `Run Simulation <#run-simulation>`__
    - `Run Implementation <#run-implementation>`__
    - `AFI Creation <#afi-creation>`__
    - `Runtime Example <#runtime-example>`__

Overview
--------

This document covers top level steps for using the HLx GUI flows.

Create IP Integrator Project with Example Design
------------------------------------------------

This section specifies the end-to-end flow for creating a pre-defined
IPI example design and executing it on an F2 instance.

Create Design
~~~~~~~~~~~~~

- To launch Vivado GUI

  - Change to the ``hdk/cl/examples/<CL_HLX_EXAMPLE>`` directory, e.g.
    ``hdk/cl/examples/hello_world_hlx``

  - Invoke Vivado by typing ``vivado`` in the console

  - In the Vivado Tcl console type in the following to create the HLx
    example.

    .. code:: Tcl

       aws::make_ipi -examples <IPI_EXAMPLE_NAME>

    **NOTE**: See what examples are possible, type
    ``aws::make_ipi -examples`` into Tcl console.
    **NOTE**: IPI example design names do not include ``_hlx``,
    which differs from the CL name ``<CL_HLX_EXAMPLE>``.

  - The example will be generated in
    ``cl/examples/<CL_HLX_EXAMPLE>/example_projects``. The Vivado
    project is ``examples_projects/<CL_HLX_EXAMPLE>.xpr``

  - Once the Block diagram is opened, review the different IP blocks
    especially the settings in the AWS IP

Run Simulation
~~~~~~~~~~~~~~

The simulation settings are already configured.

- To launch simulation from within the Vivado GUI

  - Click on 'SIMULATION' -> 'Run Simulation' -> 'Run Behavioral
    Simulation'
  - Add signals needed in the simulation
  - Type ``run -all`` in the Tcl console

Run Implementation
~~~~~~~~~~~~~~~~~~

- To run implementation from within the GUI is opened, in the Design
  Runs tab:

  - Right click on 'impl_1' in the Design Runs tab and select Launch
    Runs…
  - Click 'OK' in the Launch Runs Dialog Box.
  - Click 'OK' in the Missing Synthesis Results Dialog Box

- This step will run both synthesis and implementation.

AFI Creation
~~~~~~~~~~~~

The completed tarball file for a successfully implemented example design
can be found in:

.. code:: bash

   $CL_DIR/build/scripts/example_projects/<CL_HLX_EXAMPLE>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar

For information on how to create AFI from this tarball file, follow the
`Submit Generated DCP for AFI
Creation <./../README.html#step-6-submit-generated-dcp-for-afi-creation>`__
section in the HDK step-by-step quick start guide.

Runtime Example
~~~~~~~~~~~~~~~

The runtime software must be compiled before the AFI can run on F2
instances. Copy the example's software directory to your preferred
location and compile it using the following commands:

.. code:: bash

   source $AWS_FPGA_REPO_DIR/sdk_setup.sh
   cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/<CL_HLX_EXAMPLE>/software <any_directory>
   cd software
   make all
   sudo ./test_cl

`Back to Vivado IPI GUI Setup Guide <./IPI-GUI-Vivado-Setup.html>`__
