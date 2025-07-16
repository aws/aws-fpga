from libc.stdint cimport uint8_t, uint16_t, uint32_t, uint64_t
from libcpp cimport bool

cdef extern from "hal/fpga_common.h":
    struct fpga_ddr_if_metrics_common:
        uint64_t write_count
        uint64_t read_count

    struct fpga_clocks_common:
        uint64_t[7] frequency

    struct fpga_pci_resource_map:
        uint16_t vendor_id
        uint16_t device_id
        uint16_t subsystem_device_id
        uint16_t subsystem_vendor_id
        uint16_t domain
        uint8_t  bus
        uint8_t  dev
        uint8_t  func
        bool[5]  resource_burstable
        uint64_t[5] resource_size

    struct f1_metrics_common:
        uint32_t int_status
        uint32_t pcim_axi_protocol_error_status
        uint64_t dma_pcis_timeout_addr
        uint32_t dma_pcis_timeout_count
        uint64_t pcim_range_error_addr
        uint32_t pcim_range_error_count
        uint64_t pcim_axi_protocol_error_addr
        uint32_t pcim_axi_protocol_error_count
        uint8_t[12] reserved2
        uint64_t ocl_slave_timeout_addr
        uint32_t ocl_slave_timeout_count
        uint64_t bar1_slave_timeout_addr
        uint32_t bar1_slave_timeout_count
        uint32_t sdacl_slave_timeout_addr
        uint32_t sdacl_slave_timeout_count
        uint32_t virtual_jtag_slave_timeout_addr
        uint32_t virtual_jtag_slave_timeout_count
        uint64_t pcim_write_count
        uint64_t pcim_read_count
        fpga_ddr_if_metrics_common[4] ddr_ifs
        fpga_clocks_common[3] clocks
        uint64_t power_mean
        uint64_t power_max
        uint64_t power
        uint64_t[16] cached_agfis
        uint64_t flags

    struct f2_metrics_common:
        uint32_t int_status
        uint32_t pcim_axi_protocol_error_status
        uint64_t pcim_range_error_addr
        uint32_t pcim_range_error_count
        uint64_t pcim_axi_protocol_error_addr
        uint32_t pcim_axi_protocol_error_count
        uint64_t pcim_write_count
        uint64_t pcim_read_count
        uint64_t dma_pcis_timeout_addr
        uint32_t dma_pcis_timeout_count
        uint32_t ocl_slave_timeout_addr
        uint32_t ocl_slave_timeout_count
        uint64_t sda_slave_timeout_addr
        uint32_t sda_slave_timeout_count
        uint32_t virtual_jtag_slave_timeout_addr
        uint32_t virtual_jtag_slave_timeout_count
        uint32_t virtual_jtag_write_count
        uint32_t virtual_jtag_read_count
        fpga_ddr_if_metrics_common[1] ddr_ifs
        fpga_clocks_common[3] clocks
        uint64_t power_mean
        uint64_t power_max
        uint64_t power
        uint64_t[16] cached_agfis
        uint64_t flags
