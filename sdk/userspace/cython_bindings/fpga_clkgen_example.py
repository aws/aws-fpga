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

* This example demonstrates how to manage FPGA clock settings using the C API, including:
* - Reading FPGA status and clock information
* - Loading an AFI (Amazon FPGA Image)
* - Setting dynamic clock frequencies
* - Applying clock recipes
*
* 0. Prerequisites: This example must be run on an F2 instance with an FPGA. Source the sdk
*    by navigating to the root of this repo and running `source ./sdk_setup.sh`.
* 1. The example initializes FPGA management and clock generation wrappers
* 2. Checks FPGA status and loads a specified AFI
* 3. Retrieves current clock information
* 4. Demonstrates setting dynamic clock frequencies for different clock groups
* 5. Shows how to apply a predefined clock recipe
* 6. Verifies clock settings after modifications
"""

from fpga_clkgen_wrapper import FpgaClkgen
from typing import Dict, Any
from fpga_mgmt_wrapper import FpgaMgmt
from utils import setup_logger
import json


def main() -> None:
    setup_logger()

    GET_HW_METRICS = 1 << 1

    fpga_mgmt_wrapper = FpgaMgmt()
    fpga_clkgen_wrapper = FpgaClkgen()

    slot = 0
    status: str = fpga_mgmt_wrapper.describe_local_image(slot, GET_HW_METRICS)["status"]
    print(f"FPGA Status {status}")

    public_cl_mem_perf_afi_id = "agfi-080817d089f3cd2ed"
    print(f"Loading AFI: {public_cl_mem_perf_afi_id}\n")
    image_info: Dict[str, Any] = fpga_mgmt_wrapper.load_local_image(
        slot, public_cl_mem_perf_afi_id
    )

    status: str = image_info["status"]
    while status == "busy":
        status = fpga_mgmt_wrapper.describe_local_image(slot, GET_HW_METRICS)[
            "status"
        ]

    info: Dict[str, Any] = json.dumps(fpga_clkgen_wrapper.get_dynamic(slot), indent=2)
    print(f"Clock Information\n {info}")

    print("Setting dynamic clock\n")
    fpga_clkgen_wrapper.set_dynamic(
        slot, clk_a_freq=125, clk_b_freq=125, clk_c_freq=150, clk_hbm_freq=125, reset=0
    )

    info = json.dumps(fpga_clkgen_wrapper.get_dynamic(slot), indent=2)
    print(f"New Clock Information\n {info}\n")

    print("Setting Recipe\n")
    # Recipe information available at aws-fpga/hdk/docs/Clock_Recipes_User_Guide.md
    fpga_clkgen_wrapper.set_recipe(
        slot_id=0,
        clk_a_recipe=0,
        clk_b_recipe=3,
        clk_c_recipe=3,
        clk_hbm_recipe=4,
        reset=0,
    )

    info = json.dumps(fpga_clkgen_wrapper.get_dynamic(slot), indent=2)
    print(f"Clock Information after setting recipe\n {info}\n")


if __name__ == "__main__":
    main()
