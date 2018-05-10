/**
 * Copyright (C) 2016-2018 Xilinx, Inc
 * Author: Ryan Radjabi
 * Simple command line utility to inetract with SDX PCIe devices
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

#include "dd.h"

namespace dd {
const char *ddOptString = "i:o:b:c:p:e:";

static const struct option longOpts[] = {
    { "if",    required_argument, NULL, 'i' },
    { "of",    required_argument, NULL, 'o' },
    { "bs",    required_argument, 0,    'b' },
    { "count", required_argument, 0,    'c' },
    { "skip",  required_argument, 0,    'p' },
    { "seek",  required_argument, 0,    'e' }
};

/*
enum e_direction {
    deviceToFile,
    fileToDevice,
    unset
};

static struct ddArgs_t {
    bool isValid = false;
    std::string file = "";
    int blockSize = defaultBS;
    e_direction dir;
    int count = -1;
    int skip = -1;
    int seek = -1;
} globalArgs;
*/


/*
 * parse_dd_options
 */
ddArgs_t parse_dd_options( int argc, char *argv[] )
{
    int opt = 0;
    int longIndex = 0;

    dd::ddArgs_t args;
    args.isValid = true; // assume valid, then test at the end of function
    args.file = "";
    args.dir = unset;
    args.blockSize = 0;
    args.count = 0;
    args.skip = 0;
    args.seek = 0;
    std::string tmpInFile, tmpOutFile = "";

    opt = getopt_long( argc, argv, ddOptString, longOpts, &longIndex );

    while( opt != -1 ) {
        switch( opt ) {
        case 'i':
            tmpInFile = optarg;
            std::cout << "if found: " << tmpInFile << std::endl;
            break;

        case 'o':
            tmpOutFile = optarg;
            std::cout << "of found: " << tmpOutFile << std::endl;
            break;

        case 'b':
            args.blockSize = atoi( optarg );
            std::cout << "bs found: " << args.blockSize << std::endl;
            break;

        case 'c':
            args.count = atoi( optarg );
            std::cout << "count found: " << args.count << std::endl;
            break;

        case 'p':
            args.skip = atoi( optarg ) * args.blockSize; // must be sure blockSize has been parsed first
            std::cout << "skip found: " << args.skip << std::endl;
            break;

        case 'e':
            args.seek = atoi( optarg ) * args.blockSize; // must be sure blockSize has been parsed first
            std::cout << "seek found: " << args.seek << std::endl;
            break;

        default:
            break;
        }

        opt = getopt_long( argc, argv, ddOptString, longOpts, &longIndex );
    }

    /*
     * Test for legal arguments, cannot specify both 'if' and 'of'
     * Must have a specified device index as -d#
     */
    if( tmpInFile.empty() && !tmpOutFile.empty() ) {
        // read from device into file
        args.file = tmpOutFile;
        args.dir = deviceToFile;
    } else if ( !tmpInFile.empty() && tmpOutFile.empty() ) {
        // read write to device from file
        args.file = tmpInFile;
        args.dir = fileToDevice;
    } else {
        // no legal options
        args.dir = unset;
        args.isValid = false;
    }

    // Test for legal combinations of skip/seek.
    if( args.dir == deviceToFile && args.seek > 0 ) {
        args.isValid = false;
    }
    if( args.dir == fileToDevice && args.skip > 0 ) {
        args.isValid = false;
    }

    // Test for legal count value; must be specified for dir==deviceToFile
    if( args.dir == deviceToFile && args.count < 0 ) {
        args.isValid = false;
    }

    return args;
}

};
