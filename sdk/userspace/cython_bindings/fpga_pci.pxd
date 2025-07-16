# Cython Header File for FPGA PCI Functions

from libc.stdint cimport uint8_t, uint32_t, uint64_t
from fpga_common cimport fpga_pci_resource_map

# fpga_pci.pxd
cdef extern from "fpga_pci.h":
    ctypedef int pci_bar_handle_t

    struct fpga_slot_spec:
        fpga_pci_resource_map[2] map

    int fpga_pci_init()

    int fpga_pci_attach(int slot_id, int pf_id, int bar_id, uint32_t flags,
        pci_bar_handle_t *handle)

    int fpga_pci_detach(pci_bar_handle_t handle)

    int fpga_pci_poke(pci_bar_handle_t handle, uint64_t offset, uint32_t value)
    int fpga_pci_poke8(pci_bar_handle_t handle, uint64_t offset, uint8_t value)

    int fpga_pci_poke64(pci_bar_handle_t handle, uint64_t offset, uint64_t value)

    int fpga_pci_write_burst(pci_bar_handle_t handle, uint64_t offset,
    uint32_t* datap, uint64_t dword_len)

    int fpga_pci_peek(pci_bar_handle_t handle, uint64_t offset, uint32_t *value)

    int fpga_pci_peek8(pci_bar_handle_t handle, uint64_t offset, uint8_t *value)

    int fpga_pci_peek64(pci_bar_handle_t handle, uint64_t offset, uint64_t *value)

    int fpga_pci_get_slot_spec(int slot_id, fpga_slot_spec *spec)

    int fpga_pci_get_all_slot_specs(fpga_slot_spec[] spec_array, int size)

    int fpga_pci_get_resource_map(int slot_id, int pf_id, fpga_pci_resource_map *map)

    int fpga_pci_rescan_slot_app_pfs(int slot_id)

    int fpga_pci_get_address(pci_bar_handle_t handle, uint64_t offset,
	uint64_t dword_len, void **ptr)

    int fpga_pci_memset(pci_bar_handle_t handle, uint64_t offset, uint32_t value,
        uint64_t dword_len)
