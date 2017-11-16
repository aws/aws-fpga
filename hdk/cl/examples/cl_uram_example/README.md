# URAM CL Example

## Table of Contents

1. [Overview](#overview)
2. [Functional Description](#description)
3. [Implementation Options](#impt_opt)
4. [Running This Design](#runme)

<a name="overview"></a>
## Overview

This simple *URAM* example builds a Custom Logic (CL) that will enable the instance to "peek" and "poke" registers in the Custom Logic (CL).
These registers will be in the memory space behind AppPF BAR0, which is the ocl\_cl\_ AXI-lite bus on the Shell to CL interface.

This example demonstrates a basic use-case of the URAMs and the different implementations available.

All of the unused interfaces between the AWS Shell and the CL are tied to fixed values.
It is recommended that the developer use similar values for every unused interface in the developer's CL.

Please read here for [general instructions to build the CL, register an AFI, and start using it on an F1 instance](./../README.md).


<a name="description"></a>
## Functional Description

The cl\_uram\_example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and URAM implementation options. The cl\_uram\_example implements a single register in the FPGA AppPF BAR0 memory space connected to the OCL AXI-L interface. The register is:

1. URAM Register (offset 0x500)

Please refer to the [FPGA PCIe memory space overview](../../../docs/AWS_Fpga_Pcie_Memory_Map.md)

The URAM Register is a 32-bit read/write register.

### Unused interfaces

The cl\_uram\_example does not use most of AWS Shell interface, hence the unused signals are tied off.
At the beginning of `cl_uram_example.sv` file, there is a specific `include` command for an interface-specific `.inc` file, to handle the tie-off\'s for every unused interface.


<a name="impt_opt"></a>
## Implementation Options

Availability of 100% of URAM sites on F1 FPGAs across the entire CL region has now been enabled rather than the previous support for 50%. To utilize up to 100% of URAM, cascading as well as output register inference must be disabled. This option is included in the 1.3.0 HDK build scripts alongside the existing solutions which limits URAM usage to 50% or 75% but does allow a cascade height of 2 or 3 and output register inference. The table below outlines the options available: 

URAM Options | Max Cascade Height | URAMs Limitations
--- | --- | ---
2 | Max Cascade = 2 | Top 2 URAMs Prohibited (50% of URAMs ~ *400 URAMs available*)
3 | Max Cascade = 3 | Top 1 URAM Prohibited (75% of URAMs ~ *600 URAMs available*)
4 | No Cascade | All URAMs Enabled (100% of URAMs ~ *800 URAMs available*)

*Please note that the options start from 2 to 4 included*

<a name="runme"></a>
## Running This Design

### Hardware - HDK Flow
You can run this design like the other examples designs by:
- `source hdk\_setup.sh`
- `cd hdk/cl/examples/cl_uram_example`
- `export CL_DIR=$(pwd)`
- `cd $CL\_DIR/build/scripts`
- Running the .tar file generation using:
  - Option 2:
    - `./aws_build_dcp_from_cl.sh -uram_option 2`
  - Option 3:
    - `./aws_build_dcp_from_cl.sh -uram_option 3`
  - Option 4 (default option):
    - `./aws_build_dcp_from_cl.sh -uram_option 4`

### Software
You can generate the software by:
```
source sdk_setup.sh
cd hdk/cl/examples/cl_uram_example/software/runtime
make
```

__How to use it?__

This software allows you to read from and write into the URAMs.
Do not forget to run it in sudo mode:
- `sudo ./uram_example`

You have 3 commands available:
- find: Command which allows you to find a 32 bits hexadecimal data inside the URAM
- add : Command which allows you to add a 32 bits hexadecimal data inside the URAM
- del : Command which allows to find and delete a 32 bits hexadecimal data inside the URAM

(e.g. add DEADBEEF)
(Please note that you do not need the "0x" in front of the 32 bits hexadecimal value)
