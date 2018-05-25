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

// Xilinx template design file for Amazon FPGA Hardware Development Kit
//
// File: cl_top.sv
// Starting-point top-level HDL Custom Logic (CL) design file
// If all custom logic is contained within the cl.bd block diagram,
//   then no further changes are required to this cl_top file.

module cl_top (
  // Do not modify the interface of this module.
  // User-defined custom logic cannot create additional external ports.
  `include "cl_ports_hlx.vh"
  );
  
  // Instantiate the Xilinx Vivado IP Integrator Block Diagram.
  cl cl_inst (
    // Users optionally add new BD external port connections here.
    // Terminate user-defined port connections list with a trailing comma.
    
    // Do not remove the following mandatory port connections.
    `include "sh_connectors.vh"
    );
    
  // Users optionally add custom RTL logic here.

endmodule    
