`ifndef CL_ID_DEFINES
`define CL_ID_DEFINES

  // This file is required for all CL designs in order to generate the proper manifest file for AFI creation

  // CL_SH_ID0
  // - PCIe Vendor/Device ID Values
  //    31:16: PCIe Device ID
  //    15: 0: PCIe Vendor ID
  //    - A Vendor ID value of 0x8086 is not valid.
  //    - If using a Vendor ID value of 0x1D0F (Amazon) then valid
  //      values for Device ID's are in the range of 0xF000 - 0xF0FF.
  //    - A Vendor/Device ID of 0 (zero) is not valid.
  `define CL_SH_ID0       32'hF010_1D0F

  // CL_SH_ID1
  // - PCIe Subsystem/Subsystem Vendor ID Values
  //    31:16: PCIe Subsystem ID
  //    15: 0: PCIe Subsystem Vendor ID
  // - A PCIe Subsystem/Subsystem Vendor ID of 0 (zero) is not valid
  `define CL_SH_ID1       32'h1D51_FEDC


`endif
