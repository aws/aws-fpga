# Cython Header File for FPGA Management Functions

from libc.stdint cimport uint8_t, uint16_t, uint32_t
from fpga_common cimport f1_metrics_common, f2_metrics_common, fpga_pci_resource_map

# fpga_mgmt.pxd
cdef extern from "fpga_mgmt.h":

    struct fpga_meta_ids:
        char[64] afi_id

    struct fpga_slot_spec:
        fpga_pci_resource_map[2] map

    struct metrics:
        f1_metrics_common f1_metrics
        f2_metrics_common f2_metrics

    struct fpga_mgmt_image_info:
        int status
        int status_q
        int slot_id
        fpga_meta_ids ids
        fpga_slot_spec spec
        uint32_t sh_version
        metrics metrics

    struct options:
        int slot_id
        char[64] afi_id
        uint32_t flags
        uint32_t[3] clock_mains

    union fpga_mgmt_load_local_image_options:
        uint8_t[1024] reserved
        options opt

    ctypedef fpga_mgmt_load_local_image_options fpga_mgmt_load_local_image_options_t

    int fpga_mgmt_init()
    int fpga_mgmt_close()

    const char *fpga_mgmt_strerror(int err)
    const char *fpga_mgmt_strerror_long(int err)

    void fpga_mgmt_set_cmd_timeout(uint32_t value)
    void fpga_mgmt_set_cmd_delay_msec(uint32_t value)

    int fpga_mgmt_describe_local_image(int slot_id, fpga_mgmt_image_info *info, uint32_t flags)

    int fpga_mgmt_get_status(int slot_id, int *status, int *status_q)
    const char *fpga_mgmt_get_status_name(int status)

    int fpga_mgmt_clear_local_image(int slot_id)
    int fpga_mgmt_clear_local_image_sync(int slot_id,
        uint32_t timeout, uint32_t delay_msec, fpga_mgmt_image_info *info)

    int fpga_mgmt_load_local_image(int slot_id, char *afi_id)
    int fpga_mgmt_load_local_image_flags(int slot_id, char *afi_id, uint32_t flags)

    int fpga_mgmt_load_local_image_sync_flags(int slot_id, char *afi_id, uint32_t flags,
        uint32_t timeout, uint32_t delay_msec, fpga_mgmt_image_info *info)

    int fpga_mgmt_get_vLED_status(int slot_id, uint16_t *status)
    int fpga_mgmt_set_vDIP(int slot_id, uint16_t value)
    int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value)
