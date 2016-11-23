This checklist include important checks that the developer should check before calling the `$CL_DIR/build/create_dcp_from_cl.tcl`

1. Verify that the environment variables HDK_SHELL_DIR and CL_DIR are set correctly.
2. Verify that the CL_DIR have the `/build` directory under the directory pointed by CL_DIR
3. Verity that the /build directory have AWS recommended subdirectories: /constrains, /scripts, /src_port_encryption, /reports, /to_aws
4. update encrypt.tcl script under $CL_DIR/build/script for your design specific changes.
5. update create_dcp_from_cl under $CL_DIR/build/script for your design specific changes.
6. update the timing and placement constraints under $CL_DIR/build/constraints for your design specific changes.
