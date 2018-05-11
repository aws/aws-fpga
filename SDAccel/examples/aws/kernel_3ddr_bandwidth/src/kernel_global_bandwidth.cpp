// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* 3-DDR Example for testing */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "xcl.h"
#include <CL/cl_ext.h>

/* Works for 3 DDR_BANKS */
#define DDR_BANKS 3

int main(int argc, char** argv) {

    if(argc != 1) {
        printf("Usage: %s\n", argv[0]);
        return EXIT_FAILURE;
    }

    xcl_world world = xcl_world_single();
    cl_program program = xcl_import_binary(world, "krnl_kernel_global");
    cl_kernel krnl = xcl_get_kernel(program, "bandwidth");

    int err;

    size_t globalbuffersize = 1024*1024*1024;    /* 1GB */

    /* Reducing the data size for emulation mode */
    char *xcl_mode = getenv("XCL_EMULATION_MODE");
    if (xcl_mode != NULL){
        globalbuffersize = 1024 * 1024;  /* 1MB */
    }

    /* Input buffer */
    unsigned char *input_host = ((unsigned char *) malloc(globalbuffersize));
    if(input_host==NULL) {
        printf("Error: Failed to allocate host side copy of OpenCL source buffer of size %zu\n",globalbuffersize);
        return EXIT_FAILURE;
    }

    for(size_t i = 0; i < globalbuffersize; i++) {
        input_host[i] = i % 256;
    }

    short ddr_banks = DDR_BANKS;

    /* Index for the ddr pointer array: 4=4, 2=2, 1=2 */
/*    char num_buffers = ddr_banks + (ddr_banks % 2); */
    char num_buffers = ddr_banks;

    /* buffer[0] is input0
     * buffer[1] is output0
     * buffer[2] is output1 */
    cl_mem buffer[num_buffers];

    cl_mem_ext_ptr_t ext_buffer[num_buffers];

        unsigned xcl_bank[3] = {
            XCL_MEM_DDR_BANK0,
            XCL_MEM_DDR_BANK1,
            XCL_MEM_DDR_BANK2,
        };

        for (int i = 0; i < ddr_banks; i++) {
            ext_buffer[i].flags = xcl_bank[i];
            ext_buffer[i].obj = NULL;
            ext_buffer[i].param = 0;

            buffer[i] = clCreateBuffer(world.context,
                                       CL_MEM_READ_WRITE | CL_MEM_EXT_PTR_XILINX,
                                       globalbuffersize,
                                       &ext_buffer[i],
                                       &err);
            if(err != CL_SUCCESS) {
                printf("Error: Failed to allocate buffer in DDR bank %zu\n", globalbuffersize);
                return EXIT_FAILURE;
            }
        } /* End for (i < ddr_banks) */

    cl_ulong num_blocks = globalbuffersize/64;
    double dbytes = globalbuffersize;
    double dmbytes = dbytes / (((double)1024) * ((double)1024));
    printf("Starting kernel to read/write %.0lf MB bytes from/to global memory... \n", dmbytes);

    /* Write input buffer */
    /* Map input buffer for PCIe write */
    unsigned char *map_input_buffer0;
    map_input_buffer0 = (unsigned char *) clEnqueueMapBuffer(world.command_queue,
                                                             buffer[0],
                                                             CL_FALSE,
                                                             CL_MAP_WRITE_INVALIDATE_REGION,
                                                             0,
                                                             globalbuffersize,
                                                             0,
                                                             NULL,
                                                             NULL,
                                                             &err);
    if (err != CL_SUCCESS) {
            printf("Error: Failed to clEnqueueMapBuffer0 OpenCL buffer\n");
            printf("Error: Test failed\n");
            return EXIT_FAILURE;
    }
    clFinish(world.command_queue);

    /* prepare data to be written to the device */
    for(size_t i = 0; i<globalbuffersize; i++) {
        map_input_buffer0[i] = input_host[i];
    }

    err = clEnqueueUnmapMemObject(world.command_queue,
                                  buffer[0],
                                  map_input_buffer0,
                                  0,
                                  NULL,
                                  NULL);
    if (err != CL_SUCCESS) {
        printf("Error: Failed to copy input dataset to OpenCL buffer\n");
        printf("Error: Test failed\n");
        return EXIT_FAILURE;
    }
    clFinish(world.command_queue);
    
    /* Execute kernel */
    int arg_index = 0;
    int buffer_index = 0;

    xcl_set_kernel_arg(krnl, arg_index++, sizeof(cl_mem), &buffer[buffer_index++]);
    xcl_set_kernel_arg(krnl, arg_index++, sizeof(cl_mem), &buffer[buffer_index++]);
    xcl_set_kernel_arg(krnl, arg_index++, sizeof(cl_mem), &buffer[buffer_index++]);
    xcl_set_kernel_arg(krnl, arg_index++, sizeof(cl_ulong), &num_blocks);

    unsigned long nsduration = xcl_run_kernel3d(world, krnl, 1, 1, 1);

    /* Copy results back from OpenCL buffer */
    unsigned char *map_output_buffer0;
    map_output_buffer0 = (unsigned char *)clEnqueueMapBuffer(world.command_queue,
                                                             buffer[1],
                                                             CL_FALSE,
                                                             CL_MAP_READ,
                                                             0,
                                                             globalbuffersize,
                                                             0,
                                                             NULL,
                                                             NULL,
                                                             &err);
    if (err != CL_SUCCESS) {
        printf("ERROR: Failed to read output size buffer %d\n", err);
        printf("ERROR: Test failed\n");
        return EXIT_FAILURE;
    }
    clFinish(world.command_queue);

    /* Check the results of output0 */
    for (size_t i = 0; i < globalbuffersize; i++) {
        if (map_output_buffer0[i] != input_host[i]) {
            printf("ERROR : kernel failed to copy entry %zu input %i output %i\n",i,input_host[i], map_output_buffer0[i]);
            return EXIT_FAILURE;
        }
    }
    #ifdef USE_4DDR
        unsigned char *map_output_buffer1;
        map_output_buffer1 = (unsigned char *)clEnqueueMapBuffer(world.command_queue,
                                                                 buffer[2],
                                                                 CL_FALSE,
                                                                 CL_MAP_READ,
                                                                 0,
                                                                 globalbuffersize,
                                                                 0,
                                                                 NULL,
                                                                 NULL,
                                                                 &err);

        if (err != CL_SUCCESS) {
            printf("ERROR: Failed to read output size buffer %d\n", err);
            printf("ERROR: Test failed\n");
            return EXIT_FAILURE;
        }
        clFinish(world.command_queue);

        /* Check the results of output1 */
        for (size_t i = 0; i < globalbuffersize; i++) {
            if (map_output_buffer1[i] != input_host[i]) {
                printf("ERROR : kernel failed to copy entry %zu input %i output %i\n", i, input_host[i], map_output_buffer1[i]);
                return EXIT_FAILURE;
            }
        }
    #endif

    /* Profiling information */
    double dnsduration = ((double)nsduration);
    double dsduration = dnsduration / ((double) 1000000000);

    double bpersec = (dbytes/dsduration);
    double mbpersec = bpersec / ((double) 1024*1024 ) * ddr_banks;

    printf("Kernel completed read/write %.0lf MB bytes from/to global memory.\n", dmbytes);
    printf("Execution time = %f (sec) \n", dsduration);
    printf("Concurrent Read and Write Throughput = %f (MB/sec) \n", mbpersec);

    clReleaseKernel(krnl);
    clReleaseProgram(program);
    xcl_release_world(world);

    printf("TEST PASSED\n");
    return EXIT_SUCCESS;
}
