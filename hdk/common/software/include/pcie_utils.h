// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

#include <stdint.h>
#include <stdbool.h>

void poke(uint32_t addr, uint32_t value);
uint32_t peek(uint32_t addr);
bool pcie_connect(int *argcP, char ***argvP);
