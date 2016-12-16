// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

#include <stdio.h>
#include <stdint.h>
#include <unistd.h>

void 
sv_printf(char *msg)
{
  printf("%s\n", msg);
}

void 
sv_map_host_memory(uint8_t *memory)
{
  // Does nothing on EC2 instance
}


void 
cl_peek(uint64_t addr, uint32_t *data)
{
  *data = peek((uint32_t) (addr & 0xffffffff));
}


void 
cl_poke(uint64_t addr, uint32_t  data)
{
  poke((uint32_t) (addr & 0xffffffff), data);
}

void 
sv_pause(uint32_t x)
{
  usleep(x);
}

