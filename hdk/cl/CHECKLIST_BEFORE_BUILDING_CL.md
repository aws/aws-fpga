This checklist includes important items that the developer should check before calling the `$CL_DIR/build/create_dcp_from_cl.tcl`:

1. Verify that the environment variables `$HDK_SHELL_DIR` and `$CL_DIR` are set correctly.
2. Verify that the `$CL_DIR` directory has a `/build` sub-directory.
3. Verity that the `/build` directory has AWS recommended subdirectories: `/constrains`, `/scripts`, `/src_port_encryption`, `/reports`, `/to_aws`.
4. Update `$CL_DIR/build/script/encrypt.tcl` script for your design specific changes.
5. Update `$CL_DIR/build/script/create_dcp_from_cl` for your design specific changes.
6. Update the timing and placement constraints under `$CL_DIR/build/constraints` for your design specific changes.
