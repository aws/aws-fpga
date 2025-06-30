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

#include <sde_utility.h>
#include <hal/fpga_common.h>
#include <fpga_mgmt.h>
#include <utils/log.h>
#include <stdio.h>
#include <sys/time.h>
#include <stdlib.h>

int sde_fill_pkt_data (uint8_t* data_ptr, size_t size, uint32_t start_dw) {
  int ret = 0;

  fail_on_with_code(data_ptr == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid data_ptr parameter");

  uint32_t lcl_start_dw = start_dw;
  uint32_t* lcl_data_ptr = (uint32_t*)data_ptr;
  size_t size_dw = size >> 2;

  for (size_t dw_idx = 0; dw_idx < size_dw; ++dw_idx) {
    *lcl_data_ptr = lcl_start_dw;
    lcl_data_ptr++;
    lcl_start_dw++;
  }

err:
  return ret;
}

size_t sde_aligned_size(size_t size, size_t bit_alignment) {
  return (size + (bit_alignment - 1)) & ~(bit_alignment - 1);
}

const char *sde_mgmt_strerror(int err) {
  if (err < 0x1000) {
    return fpga_mgmt_strerror(err);
  }
  return SDE_ERR2STR(err);
}

const char *sde_mgmt_strerror_long(int err)
{
  if (err < 0x1000) {
    return fpga_mgmt_strerror(err);
  }

  switch (err) {
  default:
    return NULL;
  case SDE_UNEXPECTED_REGISTER_VALUE:
    return "An unexpected value was read from an SDE Register. Check that an FPGA image built from the CL SDE example is loaded into the FPGA.";
  case SDE_ALLOCATION_FAILURE:
    return "Failed to allocate memory on the host. Check that the user is allowed to allocate memory. If the instance is out of resources, reboot the instance.";
  case SDE_STATUS_COUNTER_ERROR:
    return "A status counter error was detected. Check the SDE_HW_Guide for more information about what the specific error bit indicates.";
  case SDE_DESC_LIMIT_TIMEOUT:
    return "A descriptor limit timeout was detected. The SDE logic will update the Descriptor Credit \"Limit\" Counter in local memory. Check that the device has bus mastering enabled.";
  case SDE_METADATA_VALID_TIMEOUT:
    return "A metadata valid timeout was detected. The Metadata indicates information about a completed transfer. Ensure a descriptor was written to the C2H before reading the Metadata.";
  }
}

void sde_print_payload(uint8_t* payload, int pkt_size) {
  int i;
  printf ("Payload: ");
  for (i = 0; i < pkt_size; i++) {
    printf ("%02x", payload[i]);
  }
  printf ("\n");
  return;
}

void sde_print_help(const char* example_name) {
  printf ("The following arguments are required to run this program\n");
  printf ("Arg1: pkt_cnt\n");
  printf ("Arg2: pkt_size\n");
  printf ("Arg3: slot_id\n");
  printf ("./%s 1 1024 0\n", example_name);
  return;
}

int sde_parse_args(int argc, char **argv, struct sde_parameters* params, const char* example) {

  if (argc < 4) {
     printf ("*** ERROR ***: parse_args: Arguments needed\n");
     sde_print_help(example);
     return(1);
  }

  params->pkt_cnt = atoi(argv[1]);
  params->pkt_size = atoi(argv[2]);
  params->slot_id = atoi(argv[3]);
  return(0);
}

double sde_get_curr_time() {
  struct timeval curr_time;
  gettimeofday(&curr_time, NULL);
  return((double) curr_time.tv_sec + ((double) curr_time.tv_usec / 1e6));
}

void print_timing(double start_time, double end_time, int pkt_size, size_t num_packets, enum SDE_EXAMPLE_DIR test_direction) {
  double total_run_time = (end_time - start_time);
  double mpps = (((double)num_packets)/1e6) / total_run_time;
  double bw = (((double) num_packets * (double) pkt_size)/1e9)/total_run_time ;

  char* str_direction;
  switch (test_direction) {
    case SDE_EXAMPLE_DIR_C2H:
      str_direction = "c2h";
      break;
    case SDE_EXAMPLE_DIR_H2C:
      str_direction = "h2c";
      break;
    case SDE_EXAMPLE_DIR_LOOPBACK:
      str_direction = "loopback";
      break;
  }

  printf ("Start Time = %.2f, Current Time = %.2f\n", start_time, end_time);
  printf ("Total Run time: %.2f secs\n", total_run_time);
  printf ("Total Number of Packets: %ld\n", num_packets);
  printf ("%s_mpps: %.3f MPPS\n", str_direction, mpps);
  printf ("%s BW: %.3f GB/s\n", str_direction, bw);
}
