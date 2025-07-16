"""
 * Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.

 * This example demonstrates how to measure and monitor FPGA clock frequencies using the C API, including:
 * - PCI operations for reading clock frequency counters
 * - Monitoring multiple clock domains
 * - Resource mapping
 *
 * 0. Prerequisites: This example must be run on an F2 instance with an FPGA. Source the sdk
 *    by navigating to the root of this repo and running `source ./sdk_setup.sh`.
 * 1. Initialize FPGA management and PCI wrappers
 * 2. Load a specific memory performance AFI
 * 3. Attach to PCI device and access control registers
 * 4. Reset and trigger frequency measurements
 * 5. Read frequency counters for multiple clock domains:
 *    - Main clock (clk_main_a0)
 *    - Extra clocks (a1-a3, b0-b1, c0-c1)
 *    - HBM clocks (axi and ref)
 * 6. Display measured frequencies and resource mapping
 * 7. Clean up PCI resources
"""

from fpga_pci_wrapper import FpgaPCI
from fpga_mgmt_wrapper import FpgaMgmt
import time, json
from typing import Dict, Any
from utils import setup_logger, convert_info_to_json


def read_freq_counters(handle: int, base_addr: int) -> Dict[str, float]:
    fpga_pci_wrapper = FpgaPCI()
    freq_counters: Dict[str, float] = {}
    clk_names = [
        "clk_main_a0",
        "clk_extra_a1",
        "clk_extra_a2",
        "clk_extra_a3",
        "clk_extra_b0",
        "clk_extra_b1",
        "clk_extra_c0",
        "clk_extra_c1",
        "clk_hbm_axi",
        "clk_hbm_ref",
    ]

    for i, name in enumerate(clk_names):
        addr = base_addr + 0x10 + (i * 4)  # FREQ_CTR_0 starts at base + 0x10
        value = fpga_pci_wrapper.pci_peek(handle, addr)
        freq_mhz = value / 1000000.0
        freq_counters[name] = freq_mhz

    return freq_counters


def main() -> None:
    setup_logger()

    GET_HW_METRICS = 1 << 1

    fpga_mgmt_wrapper = FpgaMgmt()
    fpga_pci_wrapper = FpgaPCI()

    slot_id = 0

    public_cl_mem_perf_afi_id = "agfi-080817d089f3cd2ed"
    print(f"Loading AFI for Mem Perf CL Example:  {public_cl_mem_perf_afi_id}\n")
    image_info: Dict[str, Any] = fpga_mgmt_wrapper.load_local_image(slot_id, public_cl_mem_perf_afi_id)
    status: str = image_info["status"]
    while status == "busy":
        status = fpga_mgmt_wrapper.describe_local_image(slot_id, GET_HW_METRICS)[
            "status"
        ]

    info: Dict[str, Any] = fpga_mgmt_wrapper.describe_local_image(slot_id, GET_HW_METRICS)
    print(f"Info {convert_info_to_json(info)}\n")

    pf_id = 0
    bar_id = 0
    fpga_attach_flags = 0
    addr = 0x600  # CTL_REG

    handle = fpga_pci_wrapper.pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags)

    # Reset frequency counters
    rc = fpga_pci_wrapper.pci_poke(handle, addr, value=0x80000000)
    rc = fpga_pci_wrapper.pci_poke(handle, addr, value=0x0)

    # Trigger measurement
    rc = fpga_pci_wrapper.pci_poke(handle, addr, value=0x1)

    # Wait for measurement to complete
    for _ in range(10):
        time.sleep(1)
        value = fpga_pci_wrapper.pci_peek(handle, addr)
        if value == 0:  # Measurement complete
            break

    # Read the frequency counters
    base_addr = 0x600
    ref_freq: int = fpga_pci_wrapper.pci_peek(handle, base_addr + 0x04)
    print(f"Reference Frequency: {ref_freq} Hz")

    freq_counters = read_freq_counters(handle, base_addr)
    print("\nClock Frequencies:")
    for name, freq in freq_counters.items():
        print(f"{name}: {freq:.4f} MHz")

    fpga_pci_wrapper.pci_detach(handle)

    print("\nResource Map")
    map: Dict[str, Any] = json.dumps(fpga_pci_wrapper.pci_get_resource_map(slot_id, pf_id=0), indent=2)
    print(f"{map}\n")


if __name__ == "__main__":
    main()
