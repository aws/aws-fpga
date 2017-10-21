// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

#ifndef TEST_HELLO_WORLD_H
#define TEST_HELLO_WORLD_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>

#ifdef SV_TEST
   #ifndef VIVADO_SIM
      #include "svdpi.h"
   #endif
   #include "fpga_pci_sv.h"
#else
   #include <fpga_pci.h>
   #include <fpga_mgmt.h>
   #include <utils/lcd.h>
#endif

#ifndef SV_TEST
   extern void sv_printf(char *msg);
   extern void sv_map_host_memory(uint8_t *memory);
   extern void sv_pause(uint32_t x);
#endif

void log_printf(const char *format, ...) 
{                                        
  static char sv_msg_buffer[256];        
  va_list args;                          

  va_start(args, format);                
  vsprintf(sv_msg_buffer, format, args); 
#ifdef SV_TEST
  sv_printf(sv_msg_buffer);                
#else
  printf(sv_msg_buffer); 
#endif

  va_end(args);                          
}

#define LOW_32b(a)  ((uint32_t)((uint64_t)(a) & 0xffffffff))
#define HIGH_32b(a) ((uint32_t)(((uint64_t)(a)) >> 32L))

#endif
