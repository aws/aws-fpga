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

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

#include "xcl2.hpp"
//#define __CL_ENABLE_EXCEPTIONS
//#include <CL/cl.hpp>

int run_krnl( cl::Context &context, std::vector<cl::Device> &device, cl::CommandQueue &queue, int &N,
             const char *fileName, const char *kernelName,
             std::pair<cl::Buffer,int> &A0, std::pair<cl::Buffer,int> &B0, std::pair<cl::Buffer,int> &C0,
             std::pair<cl::Buffer,int> &A1, std::pair<cl::Buffer,int> &B1, std::pair<cl::Buffer,int> &C1,
             std::pair<cl::Buffer,int> &A2, std::pair<cl::Buffer,int> &B2, std::pair<cl::Buffer,int> &C2,
             std::pair<cl::Buffer,int> &A3, std::pair<cl::Buffer,int> &B3, std::pair<cl::Buffer,int> &C3 );

int main( int argc, char *argv[]) {
    int  N = 64;
    if( argc == 2 ) {
        N = atoi( argv[1] );
        std::cout << "Setting vector size to: " << N << std::endl;
    } 

    //try {
    // Get list of OpenCL platforms.
    std::vector<cl::Platform> platform;
    cl::Platform::get(&platform);

    if (platform.empty()) {
        std::cerr << "OpenCL platforms not found." << std::endl;
        return 1;
    }

    // Get first available CPU device which supports double precision.
    std::vector<cl::Device> device;
    device = xcl::get_xil_devices();

    cl::Context context( device[0] );

//    for(auto p = platform.begin(); device.empty() && p != platform.end(); p++) {
//        std::vector<cl::Device> pldev;
//
//        try {
//        p->getDevices(CL_DEVICE_TYPE_CPU, &pldev);
//
//        for(auto d = pldev.begin(); device.empty() && d != pldev.end(); d++) {
//            if (!d->getInfo<CL_DEVICE_AVAILABLE>()) continue;
//
//            std::string ext = d->getInfo<CL_DEVICE_EXTENSIONS>();
//
//            if (
//                ext.find("cl_khr_fp64") == std::string::npos &&
//                ext.find("cl_amd_fp64") == std::string::npos
//               ) continue;
//
//            device.push_back(*d);
//            context = cl::Context(device);
//        }
//        } catch(...) {
//        device.clear();
//        }
//    }

//    if (device.empty()) {
//        std::cerr << "CPUs with double precision not found." << std::endl;
//        return 1;
//    }

    std::cout << device[0].getInfo<CL_DEVICE_NAME>() << std::endl;

    // Create command queue.
    cl::CommandQueue queue(context, device[0]);

    // Prepare input data.
    std::vector<int> a(N);
    std::vector<int> b(N);
    std::vector<int> c(N);
    for( int i = 0; i < N; i++ ) {
        a[ i ] = i;
        b[ i ] = i;
    }

    // Allocate device buffers and transfer input data to device.
    cl::Buffer A0(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        a.size() * sizeof(int), a.data());
    cl::Buffer B0(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        b.size() * sizeof(int), b.data());
    cl::Buffer C0(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    // Allocate device buffers and transfer input data to device.
    cl::Buffer A1(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        a.size() * sizeof(int), a.data());
    cl::Buffer B1(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        b.size() * sizeof(int), b.data());
    cl::Buffer C1(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    // Allocate device buffers and transfer input data to device.
    cl::Buffer A2(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        a.size() * sizeof(int), a.data());
    cl::Buffer B2(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        b.size() * sizeof(int), b.data());
    cl::Buffer C2(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    // Allocate device buffers and transfer input data to device.
    cl::Buffer A3(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        a.size() * sizeof(int), a.data());
    cl::Buffer B3(context, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
        b.size() * sizeof(int), b.data());
    cl::Buffer C3(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    // Final Output Buffer
    cl::Buffer D0(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    cl::Buffer D1(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    cl::Buffer D2(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));
    cl::Buffer D3(context, CL_MEM_READ_WRITE,
        c.size() * sizeof(int));

    //
    std::pair<cl::Buffer,int> vmul_A0 = std::make_pair( A0, 1 );
    std::pair<cl::Buffer,int> vmul_B0 = std::make_pair( B0, 2 );
    std::pair<cl::Buffer,int> vmul_C0 = std::make_pair( C0, 3 );
    //
    std::pair<cl::Buffer,int> vmul_A1 = std::make_pair( A1, 1 );
    std::pair<cl::Buffer,int> vmul_B1 = std::make_pair( B1, 2 );
    std::pair<cl::Buffer,int> vmul_C1 = std::make_pair( C1, 3 );
    //
    std::pair<cl::Buffer,int> vmul_A2 = std::make_pair( A2, 1 );
    std::pair<cl::Buffer,int> vmul_B2 = std::make_pair( B2, 2 );
    std::pair<cl::Buffer,int> vmul_C2 = std::make_pair( C2, 3 );
    //
    std::pair<cl::Buffer,int> vmul_A3 = std::make_pair( A3, 1 );
    std::pair<cl::Buffer,int> vmul_B3 = std::make_pair( B3, 2 );
    std::pair<cl::Buffer,int> vmul_C3 = std::make_pair( C3, 3 );
    
    run_krnl( context, device, queue, N,
              "vmulx4.xclbin", "vmul",
              vmul_A0, vmul_B0, vmul_C0,
              vmul_A1, vmul_B1, vmul_C1,
              vmul_A2, vmul_B2, vmul_C2,
              vmul_A3, vmul_B3, vmul_C3 );

    //
    std::pair<cl::Buffer,int> vadd_A0 = std::make_pair( C0, 1 );
    std::pair<cl::Buffer,int> vadd_B0 = std::make_pair( C0, 2 );
    std::pair<cl::Buffer,int> vadd_C0 = std::make_pair( D0, 3 );
    //
    std::pair<cl::Buffer,int> vadd_A1 = std::make_pair( C1, 1 );
    std::pair<cl::Buffer,int> vadd_B1 = std::make_pair( C1, 2 );
    std::pair<cl::Buffer,int> vadd_C1 = std::make_pair( D1, 3 );
    //
    std::pair<cl::Buffer,int> vadd_A2 = std::make_pair( C2, 1 );
    std::pair<cl::Buffer,int> vadd_B2 = std::make_pair( C2, 2 );
    std::pair<cl::Buffer,int> vadd_C2 = std::make_pair( D2, 3 );
    //
    std::pair<cl::Buffer,int> vadd_A3 = std::make_pair( C3, 1 );
    std::pair<cl::Buffer,int> vadd_B3 = std::make_pair( C3, 2 );
    std::pair<cl::Buffer,int> vadd_C3 = std::make_pair( D3, 3 );

    run_krnl( context, device, queue, N,
              "vaddx4.xclbin", "vadd",
              vadd_A0, vadd_B0, vadd_C0,
              vadd_A1, vadd_B1, vadd_C1,
              vadd_A2, vadd_B2, vadd_C2,
              vadd_A3, vadd_B3, vadd_C3 );

    // Get result back to host.
    queue.enqueueReadBuffer(D0, CL_TRUE, 0, c.size() * sizeof(int), c.data());
    std::cout << "\nD0 results:\n";
    for( int i = 0; i < N; i++ ) {
        if( i % 12 == 0 )
            std::cout << std::endl;
        std::cout << "[" << i << "]=" << c[i] << ", ";
    }
    // Get result back to host.
    queue.enqueueReadBuffer(D1, CL_TRUE, 0, c.size() * sizeof(int), c.data());
    std::cout << "\nD1 results:\n";
    for( int i = 0; i < N; i++ ) {
        if( i % 12 == 0 )
            std::cout << std::endl;
        std::cout << "[" << i << "]=" << c[i] << ", ";
    }
    // Get result back to host.
    queue.enqueueReadBuffer(D2, CL_TRUE, 0, c.size() * sizeof(int), c.data());
    std::cout << "\nD2 results:\n";
    for( int i = 0; i < N; i++ ) {
        if( i % 12 == 0 )
            std::cout << std::endl;
        std::cout << "[" << i << "]=" << c[i] << ", ";
    }
    // Get result back to host.
    queue.enqueueReadBuffer(D3, CL_TRUE, 0, c.size() * sizeof(int), c.data());
    std::cout << "\nD3 results:\n";
    for( int i = 0; i < N; i++ ) {
        if( i % 12 == 0 )
            std::cout << std::endl;
        std::cout << "[" << i << "]=" << c[i] << ", ";
    }
    std::cout << std::endl;

    //catch (const cl::Error &err) {
    //std::cerr
    //    << "OpenCL error: "
    //    << err.what() << "(" << err.err() << ")"
    //    << std::endl;
    //return 1;
    //}


    return 0;
}

int run_krnl( cl::Context &context, std::vector<cl::Device> &device, cl::CommandQueue &queue, int &N,
              const char *fileName, const char *kernelName,
              std::pair<cl::Buffer,int> &A0, std::pair<cl::Buffer,int> &B0, std::pair<cl::Buffer,int> &C0,
              std::pair<cl::Buffer,int> &A1, std::pair<cl::Buffer,int> &B1, std::pair<cl::Buffer,int> &C1,
              std::pair<cl::Buffer,int> &A2, std::pair<cl::Buffer,int> &B2, std::pair<cl::Buffer,int> &C2,
              std::pair<cl::Buffer,int> &A3, std::pair<cl::Buffer,int> &B3, std::pair<cl::Buffer,int> &C3 )
{
    // Compile OpenCL program for found device.
//    std::ifstream kernelFile(fileName, std::ios::in);
//    if (!kernelFile.is_open()) {
//        std::cout << "Failed to open cl file for reading: " << fileName << std::endl;
//        return -1;
//    }

//    std::ostringstream oss;
//    oss << kernelFile.rdbuf();
//    std::string srcStdStr = oss.str();
//    cl::Program::Sources sources;
//    sources.push_back( {srcStdStr.c_str(), srcStdStr.length()} );
//    cl::Program program( context, sources );
    std::string device_name = device[0].getInfo<CL_DEVICE_NAME>();
    std::string binaryFile = xcl::find_binary_file( device_name, fileName );
    cl::Program::Binaries bins = xcl::import_binary_file( binaryFile );
    cl::Program program( context, device, bins );

    //try {
        program.build(device);
    //} catch (const cl::Error&) {
    //    std::cerr
    //    << "OpenCL compilation error" << std::endl
    //    << program.getBuildInfo<CL_PROGRAM_BUILD_LOG>(device[0])
    //    << std::endl;
    //    return 1;
    //}

    cl::Kernel krnl_0(program, std::string( std::string(kernelName) + std::string("0") ).c_str() );
    cl::Kernel krnl_1(program, std::string( std::string(kernelName) + std::string("1") ).c_str() );
    cl::Kernel krnl_2(program, std::string( std::string(kernelName) + std::string("2") ).c_str() );
    cl::Kernel krnl_3(program, std::string( std::string(kernelName) + std::string("3") ).c_str() );

    // Set kernel parameters.
    krnl_0.setArg(0, static_cast<int>(N));
    krnl_0.setArg(A0.second, A0.first);
    krnl_0.setArg(B0.second, B0.first);
    krnl_0.setArg(C0.second, C0.first);
    krnl_0.setArg(4, static_cast<int>(1));
    // Set kernel parameters.
    krnl_1.setArg(0, static_cast<int>(N));
    krnl_1.setArg(A1.second, A1.first);
    krnl_1.setArg(B1.second, B1.first);
    krnl_1.setArg(C1.second, C1.first);
    krnl_1.setArg(4, static_cast<int>(2));
    // Set kernel parameters.
    krnl_2.setArg(0, static_cast<int>(N));
    krnl_2.setArg(A2.second, A2.first);
    krnl_2.setArg(B2.second, B2.first);
    krnl_2.setArg(C2.second, C2.first);
    krnl_2.setArg(4, static_cast<int>(1));
    // Set kernel parameters.
    krnl_3.setArg(0, static_cast<int>(N));
    krnl_3.setArg(A3.second, A3.first);
    krnl_3.setArg(B3.second, B3.first);
    krnl_3.setArg(C3.second, C3.first);
    krnl_3.setArg(4, static_cast<int>(3));
    
    // Launch kernel on the compute device.
    queue.enqueueNDRangeKernel(krnl_0, cl::NullRange, N, cl::NullRange);
    queue.enqueueNDRangeKernel(krnl_1, cl::NullRange, N, cl::NullRange);
    queue.enqueueNDRangeKernel(krnl_2, cl::NullRange, N, cl::NullRange);
    queue.enqueueNDRangeKernel(krnl_3, cl::NullRange, N, cl::NullRange);

    queue.finish();

    return 0;
}



