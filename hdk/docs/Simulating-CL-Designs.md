# Introduction
Before finalizing your CL design and registering it with AWS EC2 as Amazon FPGA Image (AFI), you probably want to simulate the design to validate the functionality. The HDK supports RTL-level simulation using Vivado XSIM and MentorGraphics Questa simulators. You can write your tests in SystemVerilog and C languages. If you choose to use the supplied C framework, you can use the same C code for simulation and for runtime on your FPGA-enabled instance like F1.

<img src="./ppts/simulation/Slide2.PNG" alt="Testbench Top-Level Diagram">

# Quick Start
### Have an EC2 instance or other server with Xilinx Vivado tools and an active license.

One easy way is to have a pre-installed environment is to use the AWS FPGA Developer AMI available on AWS Marketplace [add link to instructions], and follow the README.md provided within that AMI

### Install the HDK and setup environment

AWS FPGA HDK can be cloned and installed on your EC2 instance or server by calling:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_setup.sh

### Try out our examples or write your own

    $ cd cl/examples/cl_hello_world/verif/scripts    # simulations are launched from the scripts subdir of the design
    $ make                                       # run the default test using the Vivado XSIM
         Running compilation flow
         Done compilation
         ...
         Vivado Simulator 2016.4_sdx
         Time resolution is 1 ps
         ...
         $finish called
    $ cd ../sim                                  # to view the test log files

# Writing and Running Your Own Tests for RTL simulation

## SystemVerilog Tests

One fast way to write your own test is to start with an example test from one of the examples designs and customize it for your design. All SV tests must be placed in the verif/tests sub-directory of CL design root and use the ".sv" file extension.

    cl_my_design                 # Custom Logic (CL) design root directory
    |-- build
    |-- design
    |-- software
    |   |-- include              # C header files
    |   `-- src                  # C source
    `-- verif
        |-- scripts              # Makefiles and filelists
        |-- sim                  # sim results directory
        |-- sv                   # additional CL-specific test bench source
        `-- tests                # test directory

**NOTE: All the tests are written to run on 64-bit instances/servers and 64-bit linux, Many of the test and reference CustomLogic (CL) examples use 64-bit address formats**

```
module test_peek_poke();

`define WR_INSTR_INDEX 64'h1c
`define WR_ADDR_LOW    64'h20
`define WR_ADDR_HIGH   64'h24
`define WR_DATA        64'h28
`define WR_SIZE        64'h2c

`define RD_INSTR_INDEX 64'h3c
`define RD_ADDR_LOW    64'h40
`define RD_ADDR_HIGH   64'h44
`define RD_DATA        64'h48
`define RD_SIZE        64'h4c

`define CNTL_REG       64'h08

`define WR_START_BIT   32'h00000001
`define RD_START_BIT   32'h00000002
   
   logic [63:0] pcim_address = 64'h0000_0000_1234_0000;
   
   initial begin

      tb.sh.power_up();

      tb.poke_ocl(`WR_INSTR_INDEX, 0);                   // write index
      tb.poke_ocl(`WR_ADDR_LOW, pcim_address[31:0]);     // write address low
      tb.poke_ocl(`WR_ADDR_HIGH, pcim_address[63:32]);   // write address high
      tb.poke_ocl(`WR_DATA, 32'h0000_0000);              // write data
      tb.poke_ocl(`WR_SIZE, 32'h0000_0002);              // write 32b

      tb.poke_ocl(`RD_INSTR_INDEX, 0);                   // read index
      tb.poke_ocl(`RD_ADDR_LOW, pcim_address[31:0]);     // read address low
      tb.poke_ocl(`RD_ADDR_HIGH, pcim_address[63:32]);   // read address high
      tb.poke_ocl(`RD_DATA, 32'h0000_0000);              // read data
      tb.poke_ocl(`RD_SIZE, 32'h0000_0002);              // read 32b

      tb.poke_ocl(`CNTL_REG, 32'h0003);                  // start read & write

      #500ns;   // give the hardware time to run
         
      ...
           
      tb.power_down();
      
      $finish;
   end

endmodule // test_peek_poke
```

Once your test is written, you are ready to run a simulation. The *scripts/* directory is where you must launch all simulations.

    $ cd verif/scripts
    $ make TEST={your_test_name} # compile and run using XSIM (NOTE: Do Not include .sv)
    $ cd ../sim/{your_test_name} # to view the test log files

If your have Mentor Graphics' Questa simulator, then add "SIMULATOR=questa".

    $ make TEST={your_test_name} QUESTA=1  # compile and run using Questa

```
========================================  NOTE ============================================
Use only the SV test APIs supplied with the developer's kit to stimulate your CL 
design. They were designed specifically to mimic the behavior of the actual AWS Shell logic.
If you choose to control CL signalling via another method, proper operation with Shell
logic is not guaranteed.

The AWS Shell Interface specification can be found [here](https://github.com/aws/aws-fpga/hdk/docs/AWS_Shell_Interface_Specification.md)
============================================================================================
```

## C Tests

As with the SV testing, one fast way to write your own test is to start with an example test from one of the examples designs and customize it for your design. All C tests must be placed in the software/src sub-directory of CL design root and use the ".c" file extension.


```
#include <stdio.h>
#include <stdint.h>

#include "sh_dpi_tasks.h"

#define WR_INSTR_INDEX UINT64_C(0x1c)
#define WR_ADDR_LOW    UINT64_C(0x20)
#define WR_ADDR_HIGH   UINT64_C(0x24)
#define WR_DATA        UINT64_C(0x28)
#define WR_SIZE        UINT64_C(0x2c)

#define RD_INSTR_INDEX UINT64_C(0x3c)
#define RD_ADDR_LOW    UINT64_C(0x40)
#define RD_ADDR_HIGH   UINT64_C(0x44)
#define RD_DATA        UINT64_C(0x48)
#define RD_SIZE        UINT64_C(0x4c)

#define CNTL_REG       UINT64_C(0x08)

#define WR_START_BIT   0x00000001
#define RD_START_BIT   0x00000002

void test_main(uint32_t *exit_code) {
  long long addr;
  uint8_t *buffer;
  int j;

  buffer = (uint8_t *)malloc(1024);

  sv_map_host_memory(buffer);

  log_printf("test_main is running...");

  cl_poke(WR_INSTR_INDEX, 0);
  cl_poke(WR_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(WR_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(WR_DATA, 0);
  cl_poke(WR_SIZE, 2);

  cl_poke(RD_INSTR_INDEX, 0);
  cl_poke(RD_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(RD_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(RD_DATA, 0);
  cl_poke(RD_SIZE, 2);

  cl_poke(CNTL_REG, WR_START_BIT | RD_START_BIT);      // start read & write

  sv_pause(2);                                            // wait 2us

  // for fun print out the incrementing pattern
  // written by the CL
  for (j=0; j<64; j++)
    printf("buffer[%d] = %0x\n", j, buffer[j]);

  log_printf("test_main is done.");

  *exit_code = 0;
}
```

Once your test is written, you are ready to run a simulation. The *scripts/* directory is where you must launch all simulations.

    $ cd verif/scripts
    $ make C_TEST={your_test_name} # compile and run using XSIM (NOTE: Do Not include .c)
    $ cd ../sim/{your_test_name} # to view the test log files

## Accessing Host Memory During Simulation
Your design may share data between host memory and logic within the CL. To verify your CL is accessing host memory, the test bench includes two types of host memory: SV and C domain host memory. If you are are only using SV to verify your CL, then use SV domain host memory. An associative array represents host memory, where the address is the key to locate a 32-bit data value.

```
   logic [31:0]        sv_host_memory[*];
```

If you are are using C to verify your CL, then use C domain host memory. Allocate a memory buffer in your C code and pass the pointer to the SV domain. The AXI BFM connected to the PCIeM port will use DPI calls to read and write the memory buffer.

<img src="./ppts/simulation/Slide3.PNG" alt="C/SV Host Memory">


Backdoor access to host memory is provided by two functions:

```
   function void hm_put_byte(input longint unsigned addr, byte d);
   function byte hm_get_byte(input longint unsigned addr);
```
Use these functions when you need to access data in either SV or C domain host memory. They take zero simulation time and are useful for initializing memory or checking results stored in memory. 

# SV Test API Reference

## _poke_
## Description
The SV Test API task 'poke' writes 64 bits of data to the CL via the AXI PCIeS interface.
## Declaration
#### task poke(input int slot_id = 0, logic [63:0] addr, logic [63:0] data, logic [5:0] id = 6'h0, DataSize::DATA_SIZE size = DataSize::UINT32, AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Write Address |
| data | Write Data |
| id | AXI ID |
| size | Data Size |
| intf | AXI CL Port |

## _peek_
## Description
The SV Test API task 'peek' reads up to 64 bits of data from the CL via the AXI PCIeS interface.
## Declaration
#### task peek(input logic [63:0] addr, output logic [63:0] data, input logic [5:0] id = 6'h0, DataSize::DATA_SIZE size = DataSize::UINT32, AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Read Address |
| data | Read Data |
| id | AXI ID |
| size | Data Size |
| intf | AXI CL Port |

## _peek_bar1_
## Description
The SV Test API function 'task peek_bar1' reads 32 bits of data from the CL via the AXI BAR1 interface.
## Declaration
#### task peek(input int slot_id = 0, logic [63:0] addr, output logic [31:0] data, input logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Read Address |
| data | Read Data |
| id | AXI ID |

## _poke_bar1_
## Description
The SV Test API task 'poke_bar1' writes 32 bits of data to the CL via the AXI BAR1 interface.
## Declaration
#### task poke_bar1(input int slot_id = 0, logic [63:0] addr, logic [31:0] data, logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Write Address |
| data | Write Data |
| id | AXI ID |

## _peek_ocl_
## Description
The SV Test API function 'task peek_ocl' reads 32 bits of data from the CL via the AXI OCL interface.
## Declaration
#### task peek_ocl(input int slot_id = 0, logic [63:0] addr, output logic [31:0] data, input logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Read Address |
| data | Read Data |
| id | AXI ID |

## _poke_ocl_
## Description
The SV Test API task 'poke_ocl' writes 32 bits of data to the CL via the AXI OCL interface.
## Declaration
#### task poke_ocl(input int slot_id = 0, logic [63:0] addr, logic [31:0] data, logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Write Address |
| data | Write Data |
| id | AXI ID |

## _peek_sda_
## Description
The SV Test API function 'task peek_sda' reads 32 bits of data from the CL via the AXI SDA interface.
## Declaration
#### task peek_sda(input int slot_id = 0, logic [63:0] addr, output logic [31:0] data, input logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Read Address |
| data | Read Data |
| id | AXI ID |

## _poke_sda_
## Description
The SV Test API task 'poke_sda' writes 32 bits of data to the CL via the AXI OCL interface.
## Declaration
#### task poke_sda(input int slot_id = 0, logic [63:0] addr, logic [31:0] data, logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Write Address |
| data | Write Data |
| id | AXI ID |

## _peek_pcis_
## Description
The SV Test API function 'task peek_pcis' reads 512 bits of data from the CL via the AXI PCIS interface.
## Declaration
#### task peek_pcis(input int slot_id = 0, logic [63:0] addr, output logic [511:0] data, input logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Read Address |
| data | Read Data |
| id | AXI ID |

## _poke_pcis_
## Description
The SV Test API task 'poke_pcis' writes 512 bits of data to the CL via the AXI PCIE interface.
## Declaration
#### task poke_pcis(input int slot_id = 0, logic [63:0] addr, logic [511:0] data, logic [5:0] id = 6'h0);

| Argument | Description |
| --- | --- |
| slot_id | Slot ID |
| addr | Write Address |
| data | Write Data |
| id | AXI ID |





## _map_host_memory_
## Description
The SV Test API function 'task map_host_memory(input logic [63:0] addr)' maps host memory to 64-bit address.
## Declaration
#### task map_host_memory(input logic [63:0] addr);

| Argument | Description |
| --- | --- |
| addr | Address |

## _hm_put_byte_
## Description
The SV Test API function 'function void hm_put_byte(input longint unsigned addr, byte d)' is used to backdoor load host memory.
## Declaration
#### function void hm_put_byte(input longint unsigned addr, byte d);

| Argument | Description |
| --- | --- |
| addr | Address |
| d | data |

## _hm_get_byte_
## Description
The SV Test API function 'function void hm_get_byte(input longint unsigned addr)' is used to read data from host memory using backdoor.
## Declaration
#### function void hm_get_byte(input longint unsigned addr);

| Argument | Description |
| --- | --- |
| addr | Address |

# C Test API Reference

## _cl_poke_
## Description
The C Test API function 'extern void cl_poke(uint64_t addr, uint32_t data)' writes 32 bits of data to the CL via the AXI PCIeS interface. This function calls the SV poke function via DPI calls.
## Declaration
#### extern void cl_poke(uint64_t addr, uint32_t data);

| Argument | Description |
| --- | --- |
| addr | Write Address |
| data | Write Data |

## _cl_peek_
## Description
The C Test API function 'extern void cl_peek(uint64_t addr)' Reads 32 bits of data from the CL via the AXI PCIeS interface. This function calls the SV peek function via DPI calls.
## Declaration
#### extern void cl_peek(uint64_t addr, uint32_t data);

| Argument | Description |
| --- | --- |
| addr | Read Address |
| data | Read Data |

##_sv_map_host_memory_
## Description
The C Test API function 'extern void sv_map_host_memory(uint8_t *memory)' maps host memory to memory allocated by memory buffer. This function calls the SV map_host_memory function via DPI calls.
## Declaration
#### extern void sv_map_host_memory(uint8_t *memory);

| Argument | Description |
| --- | --- |
| *memory | pointer to memory buffer|

## _host_memory_putc_
## Description
The C Test API function 'void host_memory_putc(uint64_t addr, uint8_t data)' is used to backdoor load host memory.
## Declaration
#### void host_memory_putc(uint64_t addr, uint8_t data)

| Argument | Description |
| --- | --- |
| addr | Address |
| data | data |

## _host_memory_getc_
## Description
The C Test API function 'void host_memory_getc(uint64_t addr)' is used to backdoor load host memory.
## Declaration
#### void host_memory_putc(uint64_t addr, uint8_t data)

| Argument | Description |
| --- | --- |
| addr | Address |

## _log_printf_
## Description
The C Test API function 'void log_printf(const char *format, ...)' is used to print messages when running a simulation. The regular 'C' printf will not work when running a 'C' and 'SV' mixed language simulation. This 'C' function calls SV function sv_printf via DPI calls.
## Declaration
#### void log_printf(const char *format, ...);

| Argument | Description |
| --- | --- |
| *format | message to be printed | 

## _sv_printf_
## Description
The C Test API function 'extern void sv_printf(char *msg)' is used to send a message buffer to the SV side of simulation. 
## Declaration
#### extern void sv_printf(char *msg);

| Argument | Description |
| --- | --- |
| *msg | Character buffer | 

## _sv_pause_
## Description
The C test API function 'extern void sv_pause(uint32_t x);' is used to add delay to a simulation. 
## Declaration
#### extern void sv_pause(uint32_t x);

| Argument | Description |
| --- | --- |
| x | Delay in micro seconds | 
