/*
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
 */

/*
 * This example demonstrates how to load an AFI to multiple FPGA image slots using the C API.
 * 0. Prerequisites: This example must be run on an F2 instance with an FPGA at FPGA image slots 0, 1, 2, 3, 4, 5, 6,
 *    7. Source the sdk by navigating to the root of this repo and running `source ./sdk_setup.sh`.
 * 1. fpga_mgmt_init: Initialize the fpga_mgmt library to allow use of the other API calls used in this example.
 * 2. fpga_mgmt_load_local_image: For the fastest loading times, multiple FPGA image slots can be loaded with the AFI
 *    in parallel.
 * 3. Poll: Poll using fpga_mgmt_describe_local_image until the slots are no longer busy or perform other operations
 *    while the FPGA load is completing. If the info status returned by the fpga_mgmt_describe_local_image call is not
 *    FPGA_STATUS_LOADED, then a retry can be performed on the image slot to load the AFI.
 * 4. fpga_pci_rescan_slot_app_pfs: Rescan the pci bus to allow the SDK to pick up any changes in vendor id or device
 *    id.
 * 5. Display and Verify: Display and verify the contents returned in the fpga_mgmt_image_info struct.
 * 6. fpga_mgmt_close: Close the fpga_mgmt library at the end of the example.
 */

#include <stdio.h>
#include <fpga_mgmt.h>
#include <fpga_pci.h>
#include <utils/log.h>
#include <unistd.h>
#include <string.h>

void display_image_info(struct fpga_mgmt_image_info *info);
int verify_image_info_loaded(struct fpga_mgmt_image_info *info, char* afi_id);

int main(int argc, char ** argv) {
  (void)argc;
  (void)argv;

  int slot_ids[] = {0, 1, 2, 3, 4, 5, 6, 7};
  size_t slot_id_count = sizeof(slot_ids)/sizeof(slot_ids[0]);
  char* afi_image = "agfi-0925b211f5a81b071";

  int ret = FPGA_ERR_FAIL;

  /* 1. fpga_mgmt_init: */
  ret = fpga_mgmt_init();
  fail_on(ret != 0, err, "fpga_mgmt_init failed. Running this example on a non-F2 instance or not sourcing the sdk can cause this call to fail.");

  /* 2. fpga_mgmt_load_local_image: */
  for (size_t i = 0; i < slot_id_count; ++i) {
    int slot_id = slot_ids[i];
    printf("Loading FPGA image slot %d\n", slot_id);
    ret = fpga_mgmt_load_local_image(slot_id, afi_image);
    fail_on(ret != 0, err, "fpga_mgmt_load_local_image failed. An incorrect slot_id or afi_image can cause this call to fail.");
  }

  /* 3. Poll: */
  uint8_t busy_state = 0;
  do {
    busy_state = 0;
    printf("Polling for each slot to no longer be busy\n");
    for (size_t i = 0; i < slot_id_count; ++i) {
      struct fpga_mgmt_image_info info;
      int slot_id = slot_ids[i];
      ret = fpga_mgmt_describe_local_image(slot_id, &info, 0);

      uint8_t card_busy_state = (info.status == FPGA_STATUS_BUSY);
      busy_state |= (card_busy_state << i);
    }
  } while (busy_state);

  for (size_t i = 0; i < slot_id_count; ++i) {
    int slot_id = slot_ids[i];
    struct fpga_mgmt_image_info info;

  /* 4. fpga_pci_rescan_slot_app_pfs: */
    ret = fpga_pci_rescan_slot_app_pfs(slot_id);
    fail_on(ret != 0, err, "fpga_pci_rescan_slot_app_pfs failed. An incorrect slot_id can cause this call to fail.");

  /* 5. Display and Verify: */
    ret = fpga_mgmt_describe_local_image(slot_id, &info, 0 /* flags */);
    fail_on(ret != 0, err, "fpga_mgmt_describe_local_image failed. An incorrect slot_id can cause this call to fail.");

    display_image_info(&info);
    ret = verify_image_info_loaded(&info, afi_image);
    fail_on(ret != 0, err, "Image info verification failed");
  }

err:
  /* 6. fpga_mgmt_close: */
  fpga_mgmt_close();
  return ret;
}

void display_image_info(struct fpga_mgmt_image_info *info) {
  printf("Contents of fpga_mgmt_image_info\n");
  printf("status: %s\n", FPGA_STATUS2STR(info->status));
  printf("status qualifier: %s\n", FPGA_ERR2STR(info->status_q));
  printf("slot id: %d\n", info->slot_id);
  printf("afi id: %s\n", info->ids.afi_id);
  struct fpga_pci_resource_map* app_map = &info->spec.map[FPGA_APP_PF];
  printf("Application PF domain:bus:dev.func: %04X:%02X:%02X.%X\n", app_map->domain, app_map->bus, app_map->dev, app_map->func);
  struct fpga_pci_resource_map* mgmt_map = &info->spec.map[FPGA_MGMT_PF];
  printf("Management PF domain:bus:dev.func: %04X:%02X:%02X.%X\n", mgmt_map->domain, mgmt_map->bus, mgmt_map->dev, mgmt_map->func);
  printf("Shell version: 0x%X\n", info->sh_version);
}

int verify_image_info_loaded(struct fpga_mgmt_image_info *info, char* afi_id) {
  if (info->status != FPGA_STATUS_LOADED) {
    printf("Image status is not loaded\n");
    return -1;
  }
  if (info->status_q != FPGA_ERR_OK) {
    printf("Image status qualifier is not ok\n");
    return -1;
  }
  if (info->spec.map[FPGA_APP_PF].device_id != 0xf002) {
    printf("Device ID is not the cl_sde id\n");
    return -1;
  }
  if (info->spec.map[FPGA_APP_PF].vendor_id != 0x1d0f) {
    printf("Vendor ID is not the cl_sde id\n");
    return -1;
  }
  if (strcmp(info->ids.afi_id, afi_id)) {
    printf("AFI ID is not the cl_sde id\n");
    return -1;
  }
  return 0;
}