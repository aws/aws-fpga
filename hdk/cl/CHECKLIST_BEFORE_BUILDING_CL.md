# Checklist Before Building

This checklist includes important items that the developer should check before building a CL Design Check Point (DCP) file for AFI generation.

1. Verify that the environment variables `$HDK_SHELL_DIR` and `$CL_DIR` are set correctly.

1. Verify that the `$CL_DIR` directory has a `/build` sub-directory.

1. Update `$CL_DIR/build/script/encrypt.tcl` script for your design specific changes, including the list of all the source files (including header files like .inc and .h/.vh), so they all get copied to `src_post_encryption` directory

1. Update the timing and placement constraints under `$CL_DIR/build/constraints` for your design specific changes.
