.. F2 documentation master file, created by
   sphinx-quickstart on Sat Nov 23 04:21:40 2024.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.


AWS EC2 F2 Developer Documentation
==================================

Welcome to the AWS EC2 F2 Developer documentation!

The `AWS EC2 FPGA Development Kit User Guide <./User-Guide-AWS-EC2-FPGA-Development-Kit.html>`__ provides a high-level overview of the development kit, design flows, simulation flows, and recommendations for development environment usage.
If you are new to AWS EC2 FPGA-accelerated instances, we recommend you read this guide before proceeding.

.. list-table::
   :header-rows: 1
   :class: landing-page-table
   :widths: 33 33 33

   * - Development Kit Component
     - Target Developer/Use Case
     - Development Flow Tool
   * - `HDK <./hdk/README.html>`__
     - Developers with RTL experience
     - Vivado/3rd-party Simulation Tools
   * - `SDK <./sdk/README.html>`__
     - Runtime software development, using our provided APIs and CLIs
     - Python/C/C++
   * - `Vitis (Software-Defined) <./vitis/README.html>`__
     - Software developers with C/C++ or RTL experience
     - Vitis HLS/RTL/Hardware Emulation

Table of Contents
-----------------

.. toctree::
  :maxdepth: 1

  User-Guide-AWS-EC2-FPGA-Development-Kit

  hdk/README
  sdk/README
  vitis/README

  developer-resources/Amazon-DCV-Setup-Guide.rst

  ERRATA

  RELEASE-NOTES

This development kit includes example programs and RTL that are easy to build and demonstrate the platform's capabilities. Several examples are listed below.

Example Applications
--------------------

.. toctree::
  :maxdepth: 1

  hdk/cl/examples/cl-sde/software/src/README
  sdk/apps/virtual-ethernet/README

For a listing of all pages on our ReadTheDocs site, `click here <./all-links.html>`__.
