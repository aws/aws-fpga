#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#
# Python bindings for pci library
# -*- coding: utf-8 -*-
#
# WORD_SIZE is: 8
# POINTER_SIZE is: 8
# LONGDOUBLE_SIZE is: 16
#
import ctypes


_libraries = {}
_libraries['libfpga_mgmt.so'] = ctypes.CDLL('libfpga_mgmt.so')
# if local wordsize is same as target, keep ctypes pointer function.
if ctypes.sizeof(ctypes.c_void_p) == 8:
    POINTER_T = ctypes.POINTER
else:
    # required to access _ctypes
    import _ctypes
    # Emulate a pointer class using the approriate c_int32/c_int64 type
    # The new class should have :
    # ['__module__', 'from_param', '_type_', '__dict__', '__weakref__', '__doc__']
    # but the class should be submitted to a unique instance for each base type
    # to that if A == B, POINTER_T(A) == POINTER_T(B)
    ctypes._pointer_t_type_cache = {}
    def POINTER_T(pointee):
        # a pointer should have the same length as LONG
        fake_ptr_base_type = ctypes.c_uint64 
        # specific case for c_void_p
        if pointee is None: # VOID pointer type. c_void_p.
            pointee = type(None) # ctypes.c_void_p # ctypes.c_ulong
            clsname = 'c_void'
        else:
            clsname = pointee.__name__
        if clsname in ctypes._pointer_t_type_cache:
            return ctypes._pointer_t_type_cache[clsname]
        # make template
        class _T(_ctypes._SimpleCData,):
            _type_ = 'L'
            _subtype_ = pointee
            def _sub_addr_(self):
                return self.value
            def __repr__(self):
                return '%s(%d)'%(clsname, self.value)
            def contents(self):
                raise TypeError('This is not a ctypes pointer.')
            def __init__(self, **args):
                raise TypeError('This is not a ctypes pointer. It is not instanciable.')
        _class = type('LP_%d_%s'%(8, clsname), (_T,),{}) 
        ctypes._pointer_t_type_cache[clsname] = _class
        return _class

c_int128 = ctypes.c_ubyte*16
c_uint128 = c_int128
void = None
if ctypes.sizeof(ctypes.c_longdouble) == 16:
    c_long_double_t = ctypes.c_longdouble
else:
    c_long_double_t = ctypes.c_ubyte*16



pci_bar_handle_t = ctypes.c_int32
fpga_pci_init = _libraries['libfpga_mgmt.so'].fpga_pci_init
fpga_pci_init.restype = ctypes.c_int32
fpga_pci_init.argtypes = []
uint32_t = ctypes.c_uint32
fpga_pci_attach = _libraries['libfpga_mgmt.so'].fpga_pci_attach
fpga_pci_attach.restype = ctypes.c_int32
fpga_pci_attach.argtypes = [ctypes.c_int32, ctypes.c_int32, ctypes.c_int32, uint32_t, POINTER_T(ctypes.c_int32)]

# values for enumeration 'c__Ea_BURST_CAPABLE'
c__Ea_BURST_CAPABLE__enumvalues = {
    1: 'BURST_CAPABLE',
    4294967294: 'FPGA_ATTACH_RESERVED',
}
BURST_CAPABLE = 1
FPGA_ATTACH_RESERVED = 4294967294
c__Ea_BURST_CAPABLE = ctypes.c_int # enum
fpga_pci_detach = _libraries['libfpga_mgmt.so'].fpga_pci_detach
fpga_pci_detach.restype = ctypes.c_int32
fpga_pci_detach.argtypes = [pci_bar_handle_t]
uint64_t = ctypes.c_uint64
fpga_pci_poke = _libraries['libfpga_mgmt.so'].fpga_pci_poke
fpga_pci_poke.restype = ctypes.c_int32
fpga_pci_poke.argtypes = [pci_bar_handle_t, uint64_t, uint32_t]
uint8_t = ctypes.c_uint8
fpga_pci_poke8 = _libraries['libfpga_mgmt.so'].fpga_pci_poke8
fpga_pci_poke8.restype = ctypes.c_int32
fpga_pci_poke8.argtypes = [pci_bar_handle_t, uint64_t, uint8_t]
fpga_pci_poke64 = _libraries['libfpga_mgmt.so'].fpga_pci_poke64
fpga_pci_poke64.restype = ctypes.c_int32
fpga_pci_poke64.argtypes = [pci_bar_handle_t, uint64_t, uint64_t]
fpga_pci_write_burst = _libraries['libfpga_mgmt.so'].fpga_pci_write_burst
fpga_pci_write_burst.restype = ctypes.c_int32
fpga_pci_write_burst.argtypes = [pci_bar_handle_t, uint64_t, POINTER_T(ctypes.c_uint32), uint64_t]
fpga_pci_peek = _libraries['libfpga_mgmt.so'].fpga_pci_peek
fpga_pci_peek.restype = ctypes.c_int32
fpga_pci_peek.argtypes = [pci_bar_handle_t, uint64_t, POINTER_T(ctypes.c_uint32)]
fpga_pci_peek8 = _libraries['libfpga_mgmt.so'].fpga_pci_peek8
fpga_pci_peek8.restype = ctypes.c_int32
fpga_pci_peek8.argtypes = [pci_bar_handle_t, uint64_t, POINTER_T(ctypes.c_ubyte)]
fpga_pci_peek64 = _libraries['libfpga_mgmt.so'].fpga_pci_peek64
fpga_pci_peek64.restype = ctypes.c_int32
fpga_pci_peek64.argtypes = [pci_bar_handle_t, uint64_t, POINTER_T(ctypes.c_uint64)]
class struct_fpga_slot_spec(ctypes.Structure):
    pass

fpga_pci_get_slot_spec = _libraries['libfpga_mgmt.so'].fpga_pci_get_slot_spec
fpga_pci_get_slot_spec.restype = ctypes.c_int32
fpga_pci_get_slot_spec.argtypes = [ctypes.c_int32, POINTER_T(struct_fpga_slot_spec)]
class struct_fpga_pci_resource_map(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('vendor_id', ctypes.c_uint16),
    ('device_id', ctypes.c_uint16),
    ('subsystem_device_id', ctypes.c_uint16),
    ('subsystem_vendor_id', ctypes.c_uint16),
    ('domain', ctypes.c_uint16),
    ('bus', ctypes.c_ubyte),
    ('dev', ctypes.c_ubyte),
    ('func', ctypes.c_ubyte),
    ('resource_burstable', ctypes.c_bool * 5),
    ('resource_size', ctypes.c_uint64 * 5),
     ]

struct_fpga_slot_spec._pack_ = True # source:True
struct_fpga_slot_spec._fields_ = [
    ('map', struct_fpga_pci_resource_map * 2),
]

fpga_pci_get_all_slot_specs = _libraries['libfpga_mgmt.so'].fpga_pci_get_all_slot_specs
fpga_pci_get_all_slot_specs.restype = ctypes.c_int32
fpga_pci_get_all_slot_specs.argtypes = [struct_fpga_slot_spec * 0, ctypes.c_int32]
fpga_pci_get_resource_map = _libraries['libfpga_mgmt.so'].fpga_pci_get_resource_map
fpga_pci_get_resource_map.restype = ctypes.c_int32
fpga_pci_get_resource_map.argtypes = [ctypes.c_int32, ctypes.c_int32, POINTER_T(struct_fpga_pci_resource_map)]
fpga_pci_rescan_slot_app_pfs = _libraries['libfpga_mgmt.so'].fpga_pci_rescan_slot_app_pfs
fpga_pci_rescan_slot_app_pfs.restype = ctypes.c_int32
fpga_pci_rescan_slot_app_pfs.argtypes = [ctypes.c_int32]
fpga_pci_get_address = _libraries['libfpga_mgmt.so'].fpga_pci_get_address
fpga_pci_get_address.restype = ctypes.c_int32
fpga_pci_get_address.argtypes = [pci_bar_handle_t, uint64_t, uint64_t, POINTER_T(POINTER_T(None))]
fpga_pci_memset = _libraries['libfpga_mgmt.so'].fpga_pci_memset
fpga_pci_memset.restype = ctypes.c_int32
fpga_pci_memset.argtypes = [pci_bar_handle_t, uint64_t, uint32_t, uint64_t]

class union_c__UA_pthread_mutex_t(ctypes.Union):
    pass

class struct___pthread_mutex_s(ctypes.Structure):
    pass

class struct___pthread_internal_list(ctypes.Structure):
    pass

struct___pthread_internal_list._pack_ = True # source:False
struct___pthread_internal_list._fields_ = [
    ('__prev', POINTER_T(struct___pthread_internal_list)),
    ('__next', POINTER_T(struct___pthread_internal_list)),
]

struct___pthread_mutex_s._pack_ = True # source:False
struct___pthread_mutex_s._fields_ = [
    ('__lock', ctypes.c_int32),
    ('__count', ctypes.c_uint32),
    ('__owner', ctypes.c_int32),
    ('__nusers', ctypes.c_uint32),
    ('__kind', ctypes.c_int32),
    ('__spins', ctypes.c_int16),
    ('__elision', ctypes.c_int16),
    ('__list', struct___pthread_internal_list),
]

union_c__UA_pthread_mutex_t._pack_ = True # source:False
union_c__UA_pthread_mutex_t._fields_ = [
    ('__data', struct___pthread_mutex_s),
    ('__size', ctypes.c_char * 40),
    ('__align', ctypes.c_int64),
    ('PADDING_0', ctypes.c_ubyte * 32),
]


fpga_pci_readdir_mutex = None # Variable union_c__UA_pthread_mutex_t
fpga_acquire_readdir_lock = _libraries['libfpga_mgmt.so'].fpga_acquire_readdir_lock
fpga_acquire_readdir_lock.restype = ctypes.c_int32
fpga_acquire_readdir_lock.argtypes = []
fpga_release_readdir_lock = _libraries['libfpga_mgmt.so'].fpga_release_readdir_lock
fpga_release_readdir_lock.restype = ctypes.c_int32
fpga_release_readdir_lock.argtypes = []

# values for enumeration 'c__Ea_FPGA_CMD_RSVD'
c__Ea_FPGA_CMD_RSVD__enumvalues = {
    1: 'FPGA_CMD_RSVD',
    2: 'FPGA_CMD_GET_HW_METRICS',
    4: 'FPGA_CMD_CLEAR_HW_METRICS',
    8: 'FPGA_CMD_FORCE_SHELL_RELOAD',
    16: 'FPGA_CMD_DRAM_DATA_RETENTION',
    64: 'FPGA_CMD_EXTENDED_METRICS_SIZE',
    128: 'FPGA_CMD_PREFETCH',
    222: 'FPGA_CMD_ALL_FLAGS',
}
FPGA_CMD_RSVD = 1
FPGA_CMD_GET_HW_METRICS = 2
FPGA_CMD_CLEAR_HW_METRICS = 4
FPGA_CMD_FORCE_SHELL_RELOAD = 8
FPGA_CMD_DRAM_DATA_RETENTION = 16
FPGA_CMD_EXTENDED_METRICS_SIZE = 64
FPGA_CMD_PREFETCH = 128
FPGA_CMD_ALL_FLAGS = 222
c__Ea_FPGA_CMD_RSVD = ctypes.c_int # enum

# values for enumeration 'c__Ea_FPGA_ERR_OK'
c__Ea_FPGA_ERR_OK__enumvalues = {
    0: 'FPGA_ERR_OK',
    3: 'FPGA_ERR_AFI_CMD_BUSY',
    5: 'FPGA_ERR_AFI_ID_INVALID',
    11: 'FPGA_ERR_AFI_CMD_API_VERSION_INVALID',
    12: 'FPGA_ERR_CL_ID_MISMATCH',
    13: 'FPGA_ERR_CL_DDR_CALIB_FAILED',
    14: 'FPGA_ERR_FAIL',
    16: 'FPGA_ERR_SHELL_MISMATCH',
    17: 'FPGA_ERR_POWER_VIOLATION',
    18: 'FPGA_ERR_DRAM_DATA_RETENTION_NOT_POSSIBLE',
    19: 'FPGA_ERR_HARDWARE_BUSY',
    20: 'FPGA_ERR_PCI_MISSING',
    21: 'FPGA_ERR_AFI_CMD_MALFORMED',
    22: 'FPGA_ERR_DRAM_DATA_RETENTION_FAILED',
    23: 'FPGA_ERR_DRAM_DATA_RETENTION_SETUP_FAILED',
    24: 'FPGA_ERR_SOFTWARE_PROBLEM',
    25: 'FPGA_ERR_UNRESPONSIVE',
    26: 'FPGA_ERR_END',
}
FPGA_ERR_OK = 0
FPGA_ERR_AFI_CMD_BUSY = 3
FPGA_ERR_AFI_ID_INVALID = 5
FPGA_ERR_AFI_CMD_API_VERSION_INVALID = 11
FPGA_ERR_CL_ID_MISMATCH = 12
FPGA_ERR_CL_DDR_CALIB_FAILED = 13
FPGA_ERR_FAIL = 14
FPGA_ERR_SHELL_MISMATCH = 16
FPGA_ERR_POWER_VIOLATION = 17
FPGA_ERR_DRAM_DATA_RETENTION_NOT_POSSIBLE = 18
FPGA_ERR_HARDWARE_BUSY = 19
FPGA_ERR_PCI_MISSING = 20
FPGA_ERR_AFI_CMD_MALFORMED = 21
FPGA_ERR_DRAM_DATA_RETENTION_FAILED = 22
FPGA_ERR_DRAM_DATA_RETENTION_SETUP_FAILED = 23
FPGA_ERR_SOFTWARE_PROBLEM = 24
FPGA_ERR_UNRESPONSIVE = 25
FPGA_ERR_END = 26
c__Ea_FPGA_ERR_OK = ctypes.c_int # enum

# values for enumeration 'c__Ea_FPGA_STATUS_LOADED'
c__Ea_FPGA_STATUS_LOADED__enumvalues = {
    0: 'FPGA_STATUS_LOADED',
    1: 'FPGA_STATUS_CLEARED',
    2: 'FPGA_STATUS_BUSY',
    3: 'FPGA_STATUS_NOT_PROGRAMMED',
    7: 'FPGA_STATUS_LOAD_FAILED',
    8: 'FPGA_STATUS_END',
}
FPGA_STATUS_LOADED = 0
FPGA_STATUS_CLEARED = 1
FPGA_STATUS_BUSY = 2
FPGA_STATUS_NOT_PROGRAMMED = 3
FPGA_STATUS_LOAD_FAILED = 7
FPGA_STATUS_END = 8
c__Ea_FPGA_STATUS_LOADED = ctypes.c_int # enum
class struct_fpga_common_cfg(ctypes.Structure):
    _pack_ = True # source:False
    _fields_ = [
    ('reserved', ctypes.c_uint32),
     ]


# values for enumeration 'c__Ea_FPGA_APP_PF'
c__Ea_FPGA_APP_PF__enumvalues = {
    0: 'FPGA_APP_PF',
    1: 'FPGA_MGMT_PF',
    2: 'FPGA_PF_MAX',
}
FPGA_APP_PF = 0
FPGA_MGMT_PF = 1
FPGA_PF_MAX = 2
c__Ea_FPGA_APP_PF = ctypes.c_int # enum

# values for enumeration 'c__Ea_APP_PF_BAR0'
c__Ea_APP_PF_BAR0__enumvalues = {
    0: 'APP_PF_BAR0',
    1: 'APP_PF_BAR1',
    4: 'APP_PF_BAR4',
    5: 'APP_PF_BAR_MAX',
}
APP_PF_BAR0 = 0
APP_PF_BAR1 = 1
APP_PF_BAR4 = 4
APP_PF_BAR_MAX = 5
c__Ea_APP_PF_BAR0 = ctypes.c_int # enum

# values for enumeration 'c__Ea_MGMT_PF_BAR0'
c__Ea_MGMT_PF_BAR0__enumvalues = {
    0: 'MGMT_PF_BAR0',
    2: 'MGMT_PF_BAR2',
    4: 'MGMT_PF_BAR4',
    5: 'MGMT_PF_BAR_MAX',
}
MGMT_PF_BAR0 = 0
MGMT_PF_BAR2 = 2
MGMT_PF_BAR4 = 4
MGMT_PF_BAR_MAX = 5
c__Ea_MGMT_PF_BAR0 = ctypes.c_int # enum
class struct_afi_device_ids(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('vendor_id', ctypes.c_uint16),
    ('device_id', ctypes.c_uint16),
    ('svid', ctypes.c_uint16),
    ('ssid', ctypes.c_uint16),
     ]

class struct_fpga_meta_ids(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('afi_id', ctypes.c_char * 64),
    ('afi_device_ids', struct_afi_device_ids),
     ]

class struct_fpga_ddr_if_metrics_common(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('write_count', ctypes.c_uint64),
    ('read_count', ctypes.c_uint64),
     ]

class struct_fpga_clocks_common(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('frequency', ctypes.c_uint64 * 7),
     ]

class struct_fpga_metrics_common(ctypes.Structure):
    _pack_ = True # source:True
    _fields_ = [
    ('int_status', ctypes.c_uint32),
    ('pcim_axi_protocol_error_status', ctypes.c_uint32),
    ('dma_pcis_timeout_addr', ctypes.c_uint64),
    ('dma_pcis_timeout_count', ctypes.c_uint32),
    ('pcim_range_error_addr', ctypes.c_uint64),
    ('pcim_range_error_count', ctypes.c_uint32),
    ('pcim_axi_protocol_error_addr', ctypes.c_uint64),
    ('pcim_axi_protocol_error_count', ctypes.c_uint32),
    ('reserved2', ctypes.c_ubyte * 12),
    ('ocl_slave_timeout_addr', ctypes.c_uint64),
    ('ocl_slave_timeout_count', ctypes.c_uint32),
    ('bar1_slave_timeout_addr', ctypes.c_uint64),
    ('bar1_slave_timeout_count', ctypes.c_uint32),
    ('sdacl_slave_timeout_addr', ctypes.c_uint32),
    ('sdacl_slave_timeout_count', ctypes.c_uint32),
    ('virtual_jtag_slave_timeout_addr', ctypes.c_uint32),
    ('virtual_jtag_slave_timeout_count', ctypes.c_uint32),
    ('pcim_write_count', ctypes.c_uint64),
    ('pcim_read_count', ctypes.c_uint64),
    ('ddr_ifs', struct_fpga_ddr_if_metrics_common * 4),
    ('clocks', struct_fpga_clocks_common * 3),
    ('power_mean', ctypes.c_uint64),
    ('power_max', ctypes.c_uint64),
    ('power', ctypes.c_uint64),
    ('cached_agfis', ctypes.c_uint64 * 16),
    ('flags', ctypes.c_uint64),
     ]


# values for enumeration 'c__Ea_FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT'
c__Ea_FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT__enumvalues = {
    1: 'FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT',
    2: 'FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT',
    131072: 'FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT',
    262144: 'FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR',
    524288: 'FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR',
    268435456: 'FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT',
    536870912: 'FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT',
    806223875: 'FPGA_INT_STATUS_ALL',
}
FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT = 1
FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT = 2
FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT = 131072
FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR = 262144
FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR = 524288
FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT = 268435456
FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT = 536870912
FPGA_INT_STATUS_ALL = 806223875
c__Ea_FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT = ctypes.c_int # enum

# values for enumeration 'c__Ea_FPGA_PAP_4K_CROSS_ERROR'
c__Ea_FPGA_PAP_4K_CROSS_ERROR__enumvalues = {
    2: 'FPGA_PAP_4K_CROSS_ERROR',
    4: 'FPGA_PAP_BM_EN_ERROR',
    8: 'FPGA_PAP_REQ_SIZE_ERROR',
    16: 'FPGA_PAP_WR_INCOMPLETE_ERROR',
    32: 'FPGA_PAP_FIRST_BYTE_EN_ERROR',
    64: 'FPGA_PAP_LAST_BYTE_EN_ERROR',
    256: 'FPGA_PAP_BREADY_TIMEOUT_ERROR',
    512: 'FPGA_PAP_RREADY_TIMEOUT_ERROR',
    1024: 'FPGA_PAP_WCHANNEL_TIMEOUT_ERROR',
    1918: 'FPGA_PAP_ERROR_STATUS_ALL',
}
FPGA_PAP_4K_CROSS_ERROR = 2
FPGA_PAP_BM_EN_ERROR = 4
FPGA_PAP_REQ_SIZE_ERROR = 8
FPGA_PAP_WR_INCOMPLETE_ERROR = 16
FPGA_PAP_FIRST_BYTE_EN_ERROR = 32
FPGA_PAP_LAST_BYTE_EN_ERROR = 64
FPGA_PAP_BREADY_TIMEOUT_ERROR = 256
FPGA_PAP_RREADY_TIMEOUT_ERROR = 512
FPGA_PAP_WCHANNEL_TIMEOUT_ERROR = 1024
FPGA_PAP_ERROR_STATUS_ALL = 1918
c__Ea_FPGA_PAP_4K_CROSS_ERROR = ctypes.c_int # enum
class union_c__UA_pthread_mutex_t(ctypes.Union):
    pass

class struct___pthread_mutex_s(ctypes.Structure):
    pass

class struct___pthread_internal_list(ctypes.Structure):
    pass

struct___pthread_internal_list._pack_ = True # source:False
struct___pthread_internal_list._fields_ = [
    ('__prev', POINTER_T(struct___pthread_internal_list)),
    ('__next', POINTER_T(struct___pthread_internal_list)),
]

struct___pthread_mutex_s._pack_ = True # source:False
struct___pthread_mutex_s._fields_ = [
    ('__lock', ctypes.c_int32),
    ('__count', ctypes.c_uint32),
    ('__owner', ctypes.c_int32),
    ('__nusers', ctypes.c_uint32),
    ('__kind', ctypes.c_int32),
    ('__spins', ctypes.c_int16),
    ('__elision', ctypes.c_int16),
    ('__list', struct___pthread_internal_list),
]

union_c__UA_pthread_mutex_t._pack_ = True # source:False
union_c__UA_pthread_mutex_t._fields_ = [
    ('__data', struct___pthread_mutex_s),
    ('__size', ctypes.c_char * 40),
    ('__align', ctypes.c_int64),
    ('PADDING_0', ctypes.c_ubyte * 32),
]

__all__ = \
    ['APP_PF_BAR0', 'APP_PF_BAR1', 'APP_PF_BAR4', 'APP_PF_BAR_MAX',
    'BURST_CAPABLE', 'FPGA_APP_PF', 'FPGA_ATTACH_RESERVED',
    'FPGA_CMD_ALL_FLAGS', 'FPGA_CMD_CLEAR_HW_METRICS',
    'FPGA_CMD_DRAM_DATA_RETENTION', 'FPGA_CMD_EXTENDED_METRICS_SIZE',
    'FPGA_CMD_FORCE_SHELL_RELOAD', 'FPGA_CMD_GET_HW_METRICS',
    'FPGA_CMD_PREFETCH', 'FPGA_CMD_RSVD',
    'FPGA_ERR_AFI_CMD_API_VERSION_INVALID', 'FPGA_ERR_AFI_CMD_BUSY',
    'FPGA_ERR_AFI_CMD_MALFORMED', 'FPGA_ERR_AFI_ID_INVALID',
    'FPGA_ERR_CL_DDR_CALIB_FAILED', 'FPGA_ERR_CL_ID_MISMATCH',
    'FPGA_ERR_DRAM_DATA_RETENTION_FAILED',
    'FPGA_ERR_DRAM_DATA_RETENTION_NOT_POSSIBLE',
    'FPGA_ERR_DRAM_DATA_RETENTION_SETUP_FAILED', 'FPGA_ERR_END',
    'FPGA_ERR_FAIL', 'FPGA_ERR_HARDWARE_BUSY', 'FPGA_ERR_OK',
    'FPGA_ERR_PCI_MISSING', 'FPGA_ERR_POWER_VIOLATION',
    'FPGA_ERR_SHELL_MISMATCH', 'FPGA_ERR_SOFTWARE_PROBLEM',
    'FPGA_ERR_UNRESPONSIVE', 'FPGA_INT_STATUS_ALL',
    'FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT',
    'FPGA_ERR_FAIL', 'FPGA_ERR_OK', 'FPGA_ERR_PCI_MISSING',
    'FPGA_ERR_POWER_VIOLATION', 'FPGA_ERR_SHELL_MISMATCH',
    'FPGA_ERR_SOFTWARE_PROBLEM', 'FPGA_ERR_UNRESPONSIVE',
    'FPGA_INT_STATUS_ALL', 'FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT',
    'FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT',
    'FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT',
    'FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR',
    'FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR',
    'FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT',
    'FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT', 'FPGA_MGMT_PF',
    'FPGA_PAP_4K_CROSS_ERROR', 'FPGA_PAP_BM_EN_ERROR',
    'FPGA_PAP_BREADY_TIMEOUT_ERROR', 'FPGA_PAP_ERROR_STATUS_ALL',
    'FPGA_PAP_FIRST_BYTE_EN_ERROR', 'FPGA_PAP_LAST_BYTE_EN_ERROR',
    'FPGA_PAP_REQ_SIZE_ERROR', 'FPGA_PAP_RREADY_TIMEOUT_ERROR',
    'FPGA_PAP_WCHANNEL_TIMEOUT_ERROR', 'FPGA_PAP_WR_INCOMPLETE_ERROR',
    'FPGA_PF_MAX', 'FPGA_STATUS_BUSY', 'FPGA_STATUS_CLEARED',
    'FPGA_STATUS_END', 'FPGA_STATUS_LOADED',
    'FPGA_STATUS_LOAD_FAILED', 'FPGA_STATUS_NOT_PROGRAMMED',
    'MGMT_PF_BAR0', 'MGMT_PF_BAR2', 'MGMT_PF_BAR4', 'MGMT_PF_BAR_MAX',
    'c__Ea_APP_PF_BAR0', 'c__Ea_BURST_CAPABLE', 'c__Ea_FPGA_APP_PF',
    'c__Ea_FPGA_CMD_RSVD', 'c__Ea_FPGA_ERR_OK',
    'c__Ea_FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT',
    'c__Ea_FPGA_PAP_4K_CROSS_ERROR', 'c__Ea_FPGA_STATUS_LOADED',
    'c__Ea_MGMT_PF_BAR0', 'fpga_acquire_readdir_lock',
    'fpga_pci_attach', 'fpga_pci_detach', 'fpga_pci_get_address',
    'fpga_pci_get_all_slot_specs', 'fpga_pci_get_resource_map',
    'fpga_pci_get_slot_spec', 'fpga_pci_init', 'fpga_pci_memset',
    'fpga_pci_peek', 'fpga_pci_peek64', 'fpga_pci_peek8',
    'fpga_pci_poke', 'fpga_pci_poke64', 'fpga_pci_poke8',
    'fpga_pci_readdir_mutex', 'fpga_pci_rescan_slot_app_pfs',
    'fpga_pci_write_burst', 'fpga_release_readdir_lock',
    'pci_bar_handle_t', 'struct___pthread_internal_list',
    'struct___pthread_mutex_s', 'struct_afi_device_ids',
    'struct_fpga_clocks_common', 'struct_fpga_common_cfg',
    'struct_fpga_ddr_if_metrics_common', 'struct_fpga_meta_ids',
    'struct_fpga_metrics_common', 'struct_fpga_pci_resource_map',
    'struct_fpga_slot_spec', 'uint32_t', 'uint64_t', 'uint8_t',
    'union_c__UA_pthread_mutex_t']
