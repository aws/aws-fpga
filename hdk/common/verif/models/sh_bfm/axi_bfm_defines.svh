// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

`ifndef AXI_BFM_DEFINES
`define AXI_BFM_DEFINES

typedef struct {
   logic [63:0] addr;
   logic [7:0]  len;
   logic [5:0]  id;
   logic [1:0]  resp;
   logic        last;
} AXI_Command;
   
typedef struct {
   logic [511:0] data;
   logic [63:0]  strb;
   logic [5:0]   id;
   logic         last;
} AXI_Data;

`endif
