AWS EC2 FPGA Software Development Kit
=====================================

The AWS FPGA SDK directory provides drivers and runtime tools for
managing Amazon FPGA Images (AFIs) on EC2 FPGA instances. Use this SDK
to load, clear, and interact with pre-built AFIs on F2 instances in
Linux environments.

**Note:** This SDK is for **deploying** AFIs, not building or
registering them. For AFI development, see the
`HDK <../hdk/README.html>`__.

New to F2? Try the Interactive Workshop
---------------------------------------

If you are getting started with F2, `The AWS F2 FPGA
Workshop <https://catalog.us-east-1.prod.workshops.aws/workshops/9391f9b2-8011-460c-ab4c-ac8ff1adcf03/en-US>`__
provides a guided, hands-on companion to the CLI-driven Quick Start
below. It walks engineers of all backgrounds through F2’s architecture
and the end-to-end flow of loading a design onto an FPGA and interacting
with it - the same runtime tools this SDK documents.

Quick Start
-----------

The AWS FPGA SDK requires ``gcc`` to be installed on a Linux
distribution AMI: ``sudo {yum|apt-get} install gcc``

.. code-block:: bash

   # Clone and setup and install the SDK with env variables (if not already done)
   git clone https://github.com/aws/aws-fpga.git
   cd aws-fpga
   source sdk_setup.sh

   # Check FPGA management tools
   fpga-describe-local-image --help
   fpga-load-local-image --help

   # Verify SDK environment
   echo $SDK_DIR

   # Load an AFI (replace with your AFI ID and slot)
   sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0

   # Verify AFI loaded
   sudo fpga-describe-local-image -S 0

   # Test management tools
   cd $SDK_DIR/userspace/fpga_mgmt_examples
   make
   sudo ./fpga_mgmt_example

Core Tools
----------

Fully documented in `FPGA Management
Tools <./userspace/fpga-mgmt-tools/README.html>`__

.. list-table::
   :header-rows: 1
   :widths: auto

   * - Tool
     - Purpose
   * - ``fpga-describe-local-image-slots``
     - List available FPGA slots
   * - ``fpga-load-local-image``
     - Load AFI to FPGA slot
   * - ``fpga-describe-local-image``
     - Check AFI status
   * - ``fpga-clear-local-image``
     - Clear AFI from slot

**All tools require ``sudo`` privileges.** Use ``-help`` flag for
detailed options.

SDK Components
--------------

Management Tools
~~~~~~~~~~~~~~~~

- `FPGA Management Tools <./userspace/fpga-mgmt-tools/README.html>`__ -
  Command-line AFI management
- `C API Examples <./userspace/fpga-mgmt-examples/README.html>`__ -
  Programmatic AFI control
- `Python Bindings <./userspace/cython-bindings/README.html>`__ - Python
  interface to FPGA APIs

Applications
~~~~~~~~~~~~

- `Virtual Ethernet <./apps/virtual-ethernet/README.html>`__ -
  High-performance networking
- `MSI-X Interrupts <./apps/msix-interrupts/README.html>`__ - Interrupt
  handling implementation

Interactive Jupyter Notebooks
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- `F2 Jupyter Notebooks <./notebooks/README.html>`__ - Hands-on tutorials
  for FPGA register access and development from Python

Performance & Optimization
~~~~~~~~~~~~~~~~~~~~~~~~~~

- `Performance Optimization
  Guide <./docs/F2-Software-Performance-Optimization-Guide.html>`__
- `Load Times Analysis <./docs/Load-Times.html>`__

Troubleshooting
---------------

Refer to the `FAQ section for FPGA Mgmt
Tools <./userspace/fpga-mgmt-tools/README.html#faq>`__ or respective
applications and tools.

**Need help?**

- `GitHub Issues <https://github.com/aws/aws-fpga/issues>`__ -
  Code/documentation problems
- `AWS
  re:Post <https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development>`__
  - F2 instance questions

Additional SDK Documentation
----------------------------

.. toctree::
   :maxdepth: 1

   apps/virtual-ethernet/README
   apps/virtual-ethernet/doc/SDE-HW-Guide
   apps/virtual-ethernet/doc/Virtual-Ethernet-Application-Guide

   apps/msix-interrupts/README

   userspace/fpga-mgmt-examples/README

   userspace/cython-bindings/README

   userspace/fpga-mgmt-tools/README
   docs/F2-Software-Performance-Optimization-Guide
   docs/Load-Times

   notebooks/README

`Back to Home <../index.html>`__
