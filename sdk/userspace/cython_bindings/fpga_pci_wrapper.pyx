# Cython Code File for FPGA PCI library

from fpga_pci cimport *
from fpga_mgmt cimport *
from libc.stdint cimport uint8_t, uint32_t, uint64_t, uintptr_t
from fpga_utils import check_return_code
from typing import List
from libc.stdlib cimport malloc, free

class FpgaPCI:
    def __init__(self) -> None:
        ret = fpga_pci_init()
        check_return_code(ret, "initialize PCI Library", -1)

    def pci_attach(self, slot_id: int, pf_id: int, bar_id: int, flags: uint32_t) -> pci_bar_handle_t:
        cdef pci_bar_handle_t handle = -1
        ret = fpga_pci_attach(slot_id, pf_id, bar_id, flags, &handle)
        check_return_code(ret, "pci attach", slot_id)
        return handle

    def pci_detach(self, handle: pci_bar_handle_t) -> None:
        ret = fpga_pci_detach(handle)
        check_return_code(ret, "pci detach", -1)

    def pci_poke(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint32_t) -> None:
        ret = fpga_pci_poke(handle, offset, value)
        check_return_code(ret, "pci poke", -1)

    def pci_poke8(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint8_t) -> None:
        ret = fpga_pci_poke8(handle, offset, value)
        check_return_code(ret, "pci poke", -1)

    def pci_poke64(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint64_t) -> None:
        ret = fpga_pci_poke64(handle, offset, value)
        check_return_code(ret, "pci poke", -1)

    def pci_write_burst(self, handle: pci_bar_handle_t, offset: uint64_t, data: List[int], dword_len: uint64_t) -> None:
        cdef uint32_t* datap = <uint32_t*>malloc(dword_len * sizeof(uint32_t))
        if not datap:
            raise MemoryError("Failed to allocate memory for burst write")
        try:
            for i in range(dword_len):
                datap[i] = data[i]
            ret = fpga_pci_write_burst(handle, offset, datap, dword_len)
            check_return_code(ret, "pci write burst", -1)
        finally:
            free(datap)

    def pci_peek(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint32_t:
        cdef uint32_t value
        ret = fpga_pci_peek(handle, offset, &value)
        check_return_code(ret, "pci peek", -1)
        return value

    def pci_peek8(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint8_t:
        cdef uint8_t value
        ret = fpga_pci_peek8(handle, offset, &value)
        check_return_code(ret, "pci peek", -1)
        return value

    def pci_peek64(self, handle: pci_bar_handle_t, offset: uint64_t) -> uint64_t:
        cdef uint64_t value
        ret = fpga_pci_peek64(handle, offset, &value)
        check_return_code(ret, "pci peek", -1)
        return value

    def pci_get_slot_spec(self, slot_id: int) -> fpga_slot_spec:
        cdef fpga_slot_spec spec
        ret = fpga_pci_get_slot_spec(slot_id, &spec)
        check_return_code(ret, "get slot spec", slot_id)
        return spec

    def pci_get_all_slot_specs(self, size: int) -> List[fpga_slot_spec]:
        cdef fpga_slot_spec* spec_array = <fpga_slot_spec*>malloc(size * sizeof(fpga_slot_spec))
        if spec_array == NULL:
            raise MemoryError("Failed to allocate memory for spec array")

        ret = fpga_pci_get_all_slot_specs(spec_array, size)
        check_return_code(ret, "get all slot specs", -1)
        specs = [spec_array[i] for i in range(size)]
        free(spec_array)
        return specs

    def pci_get_resource_map(self, slot_id: int, pf_id: int) -> fpga_pci_resource_map:
        cdef fpga_pci_resource_map map
        ret = fpga_pci_get_resource_map(slot_id, pf_id, &map)
        check_return_code(ret, "get resource map", slot_id)
        return map

    def pci_rescan_slot_app_pfs(self, slot_id: int) -> None:
        ret = fpga_pci_rescan_slot_app_pfs(slot_id)
        check_return_code(ret, "rescan slot app pfs", slot_id)

    def pci_get_address(self, handle: pci_bar_handle_t, offset: uint64_t, dword_len: uint64_t):
        cdef void* ptr
        ret = fpga_pci_get_address(handle, offset, dword_len, &ptr)
        check_return_code(ret, "pci get address", -1)
        return  <uintptr_t>ptr

    def pci_memset(self, handle: pci_bar_handle_t, offset: uint64_t, value: uint32_t, dword_len: uint64_t) :
        ret = fpga_pci_memset(handle, offset, value, dword_len)
        return check_return_code(ret, "memset", -1)
