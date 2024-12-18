This checklist includes important items that the developer should check
before running a build (Vivado implementation)

1. Verify that the environment variables ``$HDK_SHELL_DIR`` and
   ``$CL_DIR`` are set correctly.

2. Verify that the ``$CL_DIR`` directory has a ``/build`` sub-directory.

3. Update ``$CL_DIR/build/script/encrypt.tcl`` script for your design
   specific changes, including the list of all the source files
   (including header files like .inc and .h/.vh), so they all get copied
   to ``src_post_encryption`` directory

4. Update the timing and placement constraints under
   ``$CL_DIR/build/constraints`` for your design specific changes.
