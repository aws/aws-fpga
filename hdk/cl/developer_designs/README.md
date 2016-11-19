# Starting your own Custom Logic

The developer has two ways to start a new Custom Logic design:

 1) Copy one of the example directory from `$(HDK_DIR)/cl/examples`, or
 
 2) Call `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh` from within the directory you want to use for your CL development

In both cases, the developer should

 A) Set the environment variable CL_DIR pointing to directory where the CL is (`export CL_DIR=Directory_You_Want_For_Your_New_CL`)
 
 B) Keep AWS recommended directory structure for the $CL_DIR/build and $CL_DIR/design

Once your design is ready and you would like to start the build/create process, please refer to `$HDK_DIR/cl/CHECKLIST.txt` file to verify all the necessary steps are set.

Once your verified the checklist, you can run `$(CL_DIR)/build/scripts/create_dcp_from_cl.tcl` .  A detailed walkthrough how to build is also available in `$(CL_DIR)/build/scripts/README.md`

