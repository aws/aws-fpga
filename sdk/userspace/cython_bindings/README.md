# Python Bindings

These bindings exist to provide Python interfaces to the FPGA on AWS F2 EC2 Instances,
allowing developers to control and interact with FPGAs using Python instead of C code directly.

## Cython Overview

A typical Cython binding setup creates a bridge between Python and C code through a specific file structure: 
the `.pxd` file declares the external C functions and types (similar to a C header file), 
while the `.pyx` file implements the actual Python-facing wrappers around these C functions, 
handling type conversions and memory management. 

When compiled, Cython transforms the `.pyx` file into C code, which is then built into a shared object (`.so`) file that Python can import directly as a module, allowing Python code to seamlessly call C functions while maintaining Python's ease of use but with C's performance benefits.

## Setup 

### How to Build Bindings

```bash
git clone https://github.com/aws/aws-fpga.git
cd aws-fpga
source sdk_setup.sh
```

This process will generate the necessary `*_wrapper.c` files that enable Python-to-C communication.

### Instructions to run examples

Navigate to the `aws-fpga/sdk/userspace/cython_bindings` directory

```bash
sudo python3 fpga_mgmt_example.py
sudo python3 fpga_clkgen_example.py
sudo python3 fpga_pci_example.py
```

## Troubleshooting

- FPGA Unresponsive: Run Python scripts with sudo privileges
- Library not found: Verify AWS FPGA SDK installation is complete and sourced
- Invalid slot ID: Verify slot number is valid for instance type
- AFI load timeout: Check AFI ID and instance permissions, and ensure sufficient time after async FPGA clears and loads
- Debug: Enable verbose logging by setting logging.INFO in `utils.py`
- Supported Python Versions: Bindings can be used by all Python versions supported by Cython
- How do I find my instance type during runtime: [Instance Meta Data Documentation](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/configuring-instance-metadata-service.html#instance-metadata-retrieval-examples)

## FPGA Management Library Functions

These are the core functions that provide direct interaction with AWS F2 FPGA instances. The primary functions include FPGA slot initialization, image loading/clearing, status checking, and metric gathering. These functions form the API layer between Python applications and the low-level FPGA hardware management, allowing developers to control FPGA resources without dealing directly with the hardware registers or low-level C interfaces.

- `load_local_image(self, slot_id: int, afi_id: str) -> dict`
- `clear_local_image(self, slot_id: int) -> dict`
- `describe_local_image(self, slot_id: int, flags: uint32_t) -> dict`
- `strerror(error: int) -> str`
- `strerror_long(err: int) -> str`
- `get_status_name(status: int) -> str`
- `get_status(self, slot_id: int) -> dict`
- `set_cmd_timeout(self, value: uint32_t) -> None`
- `set_cmd_delay_msec(self, value: uint32_t) -> None`
- `get_vLED_status(self, slot_id: int) -> uint16_t`
- `set_vDIP(self, slot_id: int, value: uint16_t) -> None`
- `get_vDIP_status(self, slot_id: int) -> uint16_t`
- `clear_local_image_sync(self, slot_id: int, timeout: uint32_t, delay_msec: uint32_t) -> dict`
- `load_local_image_flags(self, slot_id: int, afi_id: str, flags: uint32_t) -> dict`
- `load_local_image_sync_flags(self, slot_id: int, afi_id: str, flags: uint32_t, timeout: uint32_t, delay_msec: uint32_t) -> dict`

## FPGA Clock Generation Library Functions

The Clock Generation Library provide essential clock management capabilities for AWS FPGA instances, allowing precise control over clock frequencies and configurations. The primary functions include retrieving current clock settings, applying predefined clock recipes, and dynamically adjusting frequencies across multiple clock domains (A, B, C, and HBM). These functions form the API layer between Python applications and the low-level clock management system, allowing developers to precisely control FPGA clock resources without directly manipulating hardware registers. More information on clock generation functions are available in the [Clock Recipes User Guide](https://github.com/aws/aws-fpga/blob/f2/hdk/docs/Clock_Recipes_User_Guide.md) document.

- `get_dynamic(self, slot_id: int) -> str`
- `set_recipe(self, slot_id: int, clk_a_recipe: uint32_t, clk_b_recipe: uint32_t, clk_c_recipe: uint32_t, clk_hbm_recipe: uint32_t, reset: uint32_t) -> None`
- `set_dynamic(self, slot_id: int, clk_a_freq: uint32_t, clk_b_freq: uint32_t, clk_c_freq: uint32_t, clk_hbm_freq: uint32_t, reset: uint32_t) -> None`

## FPGA PCI Library Functions

The FPGA PCI library provides a comprehensive set of functions for managing and interacting with the PCI bus on AWS FPGA instances. The library starts with initialization to set up the PCI management interface, and `pci_attach()`/`pci_detach()` to establish and terminate connections to specific PCI Base Address Registers (BARs). These functions form the basis for accessing PCI-mapped hardware resources.

- `pci_attach(self, slot_id: int, pf_id: int, bar_id: int, flags: uint32_t) -> pci_bar_handle_t`
- `pci_detach(self, handle: pci_bar_handle_t) -> None`
- `pci_poke(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint32_t) -> None`
- `pci_poke8(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint8_t) -> None`
- `pci_poke64(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint64_t) -> None`
- `pci_write_burst(self, handle: pci_bar_handle_t, offset: uint64_t, data: List[int], dword_len: uint64_t) -> None`
- `pci_peek(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint32_t`
- `pci_peek8(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint8_t`
- `pci_peek64(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint64_t`
- `pci_get_slot_spec(self, slot_id: int) -> fpga_slot_spec`
- `pci_get_all_slot_specs(self, size: int) -> List[fpga_slot_spec]`
- `pci_get_resource_map(self, slot_id: int, pf_id: int) -> fpga_pci_resource_map`
- `pci_rescan_slot_app_pfs(self, slot_id: int) -> None`
- `pci_get_address(self, handle: pci_bar_handle_t, offset: uint64_t, dword_len: uint64_t) -> uintptr_t`
- `pci_memset(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint32_t, dword_len: uint64_t) -> None`
