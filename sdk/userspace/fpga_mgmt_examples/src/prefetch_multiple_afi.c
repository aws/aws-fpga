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
 * This example demonstrates how to prefetch (cache) multiple distinct AFIs into a single FPGA image slot using the C
 * API.
 * 0. Prerequisites: This example must be run on an F2 instance with an FPGA at FPGA image slot 0. Source the sdk by
 *    navigating to the root of this repo and running `source ./sdk_setup.sh`.
 * 1. fpga_mgmt_init: Initialize the fpga_mgmt library to allow use of the other API calls used in this example.
 * 2. fpga_mgmt_load_local_image_sync_flags: Load the each AFI to the FPGA sequentially using the prefetch option (FPGA_CMD_PREFETCH). This
 *    operation will load the specified AFI into the AFI cache on the FPGA image slot. The AFI is not loaded to the
 *    FPGA. Allows faster subsequent loading of pre-cached AFIs.
 * 3. fpga_mgmt_load_local_image_sync: Load a specific AFI from the prefetched set using a synchronous method.
 * 4. Display and Verify: Display and verify the contents returned in the fpga_mgmt_image_info struct.
 * 5. Customer Workflow: Perform your workflow using your loaded AFI.
 * 6. Load additional AFIs to the FPGA image slots after workflows complete and before new workflows requiring new AFIs
 *    are run.
 * 7. fpga_mgmt_close: Close the fpga_mgmt library at the end of the example.
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

  int slot_id = 0;
  /* Number of internal calls to fpga_mgmt_describe_local_image attempted by the fpga_mgmt_load_local_image_sync_flags function. */
  uint32_t num_retries = 30000;
  /* Delay in milliseconds between internal calls to fpga_mgmt_describe_local_image by the fpga_mgmt_load_local_image_sync_flags function. */
  uint32_t retry_delay = 2;
  char* afi_images[] = {
    "agfi-0925b211f5a81b071",
    "agfi-09d63a981b83fa3ea" };
  size_t afi_image_count = sizeof(afi_images)/sizeof(afi_images[0]);

  int ret = FPGA_ERR_FAIL;

  /* 1. fpga_mgmt_init: */
  ret = fpga_mgmt_init();
  fail_on(ret != 0, err, "fpga_mgmt_init failed. Running this example on a non-F2 instance or not sourcing the sdk can cause this call to fail.");

  /* 2. fpga_mgmt_load_local_image_sync_flags: */
  struct fpga_mgmt_image_info info;
  for (size_t i = 0; i < afi_image_count; ++i) {
    printf("Prefetching afi: %s to FPGA image slot %d\n", afi_images[i], slot_id);
    ret = fpga_mgmt_load_local_image_sync_flags(slot_id, afi_images[i], FPGA_CMD_PREFETCH, num_retries, retry_delay, &info);
    fail_on(ret != 0, err, "fpga_mgmt_load_local_image_sync_flags failed. An incorrect slot_id, incorrect afi_image, or a lower num_retries can cause this call to fail.");
  }

  /* 3. fpga_mgmt_load_local_image_sync: */
  printf("Loading FPGA image slot %d\n", slot_id);
  ret = fpga_mgmt_load_local_image_sync(slot_id, afi_images[0], num_retries, retry_delay, &info);
  fail_on(ret != 0, err, "fpga_mgmt_load_local_image_sync failed. An incorrect slot_id, incorrect afi_image, or a lower num_retries can cause this call to fail.");

  /* 4. Display and Verify: */
  ret = fpga_mgmt_describe_local_image(slot_id, &info, 0 /* flags */);
  fail_on(ret != 0, err, "fpga_mgmt_describe_local_image failed. An incorrect slot_id can cause this call to fail.");

  display_image_info(&info);
  ret = verify_image_info_loaded(&info, afi_images[0]);
  fail_on(ret != 0, err, "Image info verification failed");

  /* 5. Customer Workflow */
  printf("Customer workflow will run here.\n");

  /* 6. Load additional AFIs */
  printf("Loading FPGA image slot %d\n", slot_id);
  ret = fpga_mgmt_load_local_image_sync(slot_id, afi_images[1], num_retries, retry_delay, &info);
  fail_on(ret != 0, err, "fpga_mgmt_load_local_image failed. An incorrect slot_id or afi_image can cause this call to fail.");

  ret = fpga_mgmt_describe_local_image(slot_id, &info, 0 /* flags */);
  fail_on(ret != 0, err, "fpga_mgmt_describe_local_image failed. An incorrect slot_id can cause this call to fail.");

  display_image_info(&info);
  // Verify the new image is loaded

  /* Customer Workflow */
  printf("Customer workflow will run here.\n");

err:
  /* 7. fpga_mgmt_close: */
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