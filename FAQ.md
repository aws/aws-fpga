# Frequently Asked Questions



### Error while running `hdk_setup.sh`

Q. I see error ##vivado not found## ?

This is an indication that Xilinx vivado tool set are not installed. Try installing the tool, or alternative use AWS FPGA Development AMI available on AWS Marketplace, which comes with pre-installed Vivado toolset and license


## AFI on AWS Marketplace

### Q. Do AWS Marketplace customers see FPGA source code or is it just a bitstream?

Neither: AWS Marketplace customers that pick up an AMI with with one our more AFIs associated with it would not see any source code nor bitstream. Marketplace customers actually have permission to use the AFI but not permission to see its code. The Customer would call`fpga-local-load-image` which will result in AWS loading the AFI into the FPGA.  This way, your design is not exposed.
