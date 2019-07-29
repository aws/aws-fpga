/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Ryan Radjabi
 * An argument parser to prepare for the 'dd' function in xbsak. This
 * parser is designed after the Unix 'dd' command.
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
#ifndef DD_H_
#define DD_H_

#include <iostream>
#include <errno.h>
#include <fstream>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <cstring>
#include <stdio.h>
#include <getopt.h>
#include <cstdlib>

namespace dd {

const int defaultBS = 4096;

enum e_direction {
    deviceToFile,
    fileToDevice,
    unset
};


struct ddArgs_t {
    bool isValid = false;
    std::string file = "";
    int blockSize = defaultBS;
    e_direction dir;
    int count = -1;
    int skip = -1;
    int seek = -1;
};
/*
 * parse_dd_options
 */
ddArgs_t parse_dd_options( int argc, char *argv[] );

};

#endif /* DD_H_ */
