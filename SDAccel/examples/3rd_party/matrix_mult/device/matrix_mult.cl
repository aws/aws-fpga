// Copyright (C) 2013-2016 Altera Corporation, San Jose, California, USA. All rights reserved.
// Permission is hereby granted, free of charge, to any person obtaining a copy of this
// software and associated documentation files (the "Software"), to deal in the Software
// without restriction, including without limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to
// whom the Software is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
// OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
// HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
// WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
// 
// This agreement shall be governed in all respects by the laws of the State of California and
// by the laws of the United States of America.

// This kernel computes C = A * B, where
//  A is a N x K matrix
//  B is a K x M matrix
//  C is a N x M matrix
// All dimensions must be a multiple of BLOCK_SIZE (defined below).
//
// The ND-range is two-dimensional and corresponds to the dimensions of matrix
// C. Each work-item computes one element of the output matrix.
//
// The implemented algorithm uses blocking to take advantage of data reuse
// across multiple elements in matrix C. This is just like the standard loop
// tiling optimization often used in matrix multiplication implementations.
//
// This kernel is intended to be compiled with the following compiler flags:
//  --no-interleaving default
//    This flag indicates that the global memory is divided into two logical
//    banks and allows the host program to assign buffers to specific buffers.
//    This allows the host to manage the load on each memory bank, usually
//    to maximize the memory bandwidth usage.
//
//    This flag is used for matrix multiplication because there are
//    two primary memory accesses: reads from matrix A and reads from
//    matrix B. To maximize memory bandwidth, the two input matrices
//    are placed in different memory banks, which ensures that there is no
//    contention when trying to read elements from both matrices
//    simultaneously.
// 
//  -fp-relaxed=true
//    This flag enables the order of additions in the dot product 
//    computation within a block to be rearranged. This enables the additions
//    to be computed more efficiently in hardware, using a tree structure
//    instead of a vine. 
//
//    As a simple example, take the addition of four values: a0 + a1 + a2 + a3.
//    The default implementation (without -fp-relaxed=true) is:
//      (((a0 + a1) + a2) + a3)
//    which matches the standard ordering of operations. In hardware, this
//    looks like:
//         a0   a1
//          |-+-|
//            |   a2
//            |-+-|
//              |   a3
//              |-+-|
//                |
//
//    With -fp-relaxed=true, the implementation is a balanced tree:
//      ((a0 + a1) + (a2 + a3))
//    In hardware, this looks like:
//          a0   a1   a2   a3
//           |-+-|     |-+-|
//             |         |
//             |----+----|
//                  |
//
// There are two values that need to be defined in the preprocessor.
//  BLOCK_SIZE
//    The dimension of the block used in the core computation
//    is BLOCK_SIZE x BLOCK_SIZE. This is defined in the host
//    include file because the host needs to know too (just to
//    ensure that the matrix sizes are a multiple of the block
//    size.
//  SIMD_WORK_ITEMS
//    This value tells the compiler how many work-items in the work-group
//    in a SIMD fashion. In the context of matrix multiplication, this
//    value indicates how many output elements will be computed
//    in a SIMD manner. BLOCK_SIZE must be a multiple of SIMD_WORK_ITEMS.
//    See the Optimization Guide for details about this attribute.
//
//  The combination of these values determines the number of floating-point
//  operations per cycle.

#include "matrixMult.h"

#ifndef SIMD_WORK_ITEMS
#define SIMD_WORK_ITEMS 4 // default value
#endif

__kernel 
__attribute((reqd_work_group_size(BLOCK_SIZE,BLOCK_SIZE,1)))
__attribute((num_simd_work_items(SIMD_WORK_ITEMS)))
void matrix_mult( // Input and output matrices
                 __global float *restrict C,
                 __global float *A,
                 __global float *B, 
                 // Widths of matrices.
                 int A_width, int B_width)
{
    // Local storage for a block of input matrices A and B
    __local float A_local[BLOCK_SIZE][BLOCK_SIZE];
    __local float B_local[BLOCK_SIZE][BLOCK_SIZE];

    // Block index
    int block_x = get_group_id(0);
    int block_y = get_group_id(1);

    // Local ID index (offset within a block)
    int local_x = get_local_id(0);
    int local_y = get_local_id(1);

    // Compute loop bounds
    int a_start = A_width * BLOCK_SIZE * block_y;
    int a_end   = a_start + A_width - 1;
    int b_start = BLOCK_SIZE * block_x;

    float running_sum = 0.0f;

    // Compute the matrix multiplication result for this output element. Each
    // loop iteration processes one block of the matrix.
    for (int a = a_start, b = b_start; a <= a_end; a += BLOCK_SIZE, b += (BLOCK_SIZE * B_width))
    {
        // Load the matrices to local memory. Note that the (x, y) indices
        // are swapped for A_local and B_local. This affects the reads from
        // A_local and B_local below and result in more efficient hardware.
        //
        // This is actually an optimization that the compiler can perform,
        // but is shown here for illustration purposes.
        A_local[local_y][local_x] = A[a + A_width * local_y + local_x];
        B_local[local_x][local_y] = B[b + B_width * local_y + local_x];
	
        // Wait for the entire block to be loaded.
        barrier(CLK_LOCAL_MEM_FENCE);

        // Do the dot product accumulation within this block. Fully unroll the loop.
        // As a result of the swap of indices above, memory accesses to
        // A_local and B_local are very efficient because each loop iteration
        // accesses consecutive elements. This can be seen by unrolling the
        // loop and analyzing the regions that are loaded:
        //  A_local[local_y][0..BLOCK_SIZE-1] and
        //  B_local[local_x][0..BLOCK_SIZE-1]
	__attribute__((opencl_unroll_hint()))
        for (int k = 0; k < BLOCK_SIZE; ++k)
        {
            running_sum += A_local[local_y][k] * B_local[local_x][k];
        }

        // Wait for the block to be fully consumed before loading the next
        // block.
        barrier(CLK_LOCAL_MEM_FENCE);
    }

    // Store result in matrix C
    C[get_global_id(1) * get_global_size(0) + get_global_id(0)] = running_sum;
}
