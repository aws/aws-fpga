This checklist includes important items that the developer should check before calling the `$CL_DIR/build/scripts/aws_build_dcp_from_cl.sh` which starts the implementation step resulting in final Design Checkpoint (DCP):

1. Verify that the environment variables `$HDK_SHELL_DIR` and `$CL_DIR` are set correctly.
  
2. Verify that the `$CL_DIR` directory has a `/build` sub-directory.

3. Verity that the `/build` directory has AWS recommended subdirectories: `/constraints`, `/scripts`, `/src_post_encryption`, `/reports`, `checkpoints/to_aws`.

4. Update `$CL_DIR/build/script/encrypt.tcl` script for your design specific changes, including the list of all the source files (including header files like .inc and .h/.vh), so they all get encrypted and copied to `src_post_encryption` directory

5. Update the timing and placement constraints under `$CL_DIR/build/constraints` for your design specific changes.

6. Update `$CL_DIR/build/scripts/create_dcp_from_cl.tcl` for your design specific changes, specifically around IP sources and xdc files, and your specific design xdc files.
