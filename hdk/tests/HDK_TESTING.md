# HDK Testing

This page describes how HDK releases are tested.

## Overview

See [AWS FPGA Repo Testing](../../shared/tests/TESTING.md) for an explanation of the general testing methodology.
This section covers tests that are specific to testing the HDK.

All pytest test modules must be located under the hdk/tests directory.

## Simulations

The simulation tests are defined by the following module:

``hdk/tests/simulation_tests/test_sims.py``

These tests require the Xilinx tools supplied by the FPGA Developers' AMI.

They can be run with the following command:

```
pytest hdk/tests/simulation_tests -v
```

## DCP Generation

These tests test the DCP generation for all example CLs.

```
pytest hdk/tests/dcp_generation_tests
```

## AFI Generation

## F1 AFI Test

```
pytest hdk/tests/afi_runtime_tests
```
