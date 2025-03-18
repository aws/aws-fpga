.. F2 documentation master file, created by
   sphinx-quickstart on Sat Nov 23 04:21:40 2024.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

AWS EC2 F2 Developer Documentation
==================================

Welcome to the AWS EC2 F2 Developer documentation!

The `AWS EC2 FPGA Development Kit User Guide <./User_Guide_AWS_EC2_FPGA_Development_Kit.html>`__ provides a high-level overview of the development kit, design flows, simulation flows, and recommendations for development environment usage.
If you are new to AWS EC2 FPGA-accelerated instances, we recommend you read this guide before proceeding.

.. list-table::
   :header-rows: 1
   :class: landing-page-table
   :widths: 33 33 33

   * - Development Kit Component
     - Target Developer
     - Development Flow Tool
   * - `HDK <./hdk/README.html>`__
     - Developers with advanced RTL experience
     - Vivado/XSIM/VCS/Questa
   * - `SDK <./sdk/README.html>`__
     - Software developers on the F2 platform
     - C/C++
   * - `Vitis (Software-Defined) <./vitis/README.html>`__
     - Intermediate to advanced RTL experience
     - Vitis HLS/Hardware Emulation

Table of Contents
-----------------

.. toctree::
  :maxdepth: 1

  User_Guide_AWS_EC2_FPGA_Development_Kit

  hdk/README
  sdk/README
  vitis/README

  developer_resources/DCV.rst

  ERRATA
  RELEASE_NOTES

  all_links

This development kit includes example programs and RTL that are easy to build and demonstrate the platform's capabilities. Several examples are listed below.

Example Applications
--------------------
