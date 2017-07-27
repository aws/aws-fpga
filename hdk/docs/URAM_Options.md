# URAM Options

The build scripts allow developers to specify the percentage of URAM sites that are used for their design. The options are 50% of the URAM sites, 75% of the URAM sites, or 100% of the URAM sites.

The developer will specify the desired URAM sites by using the -uram_option argument when calling the aws_build_dcp_from_cl.sh script.  This is an optional argument and the default value is 2. A value of 2 indicates 50%, a value of 3 indicates 75%, and a value of 4 indicates 100%. 

Please refer to the [CL examples build README](../common/shell_v071417d3/new_cl_template/build/README.md) for more information on how to run the build script.

