/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Hem Neema, Ryan Radjabi
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

#include "scan.h"
#include <stdexcept>

std::vector<xcldev::pci_device_scanner::device_info> xcldev::pci_device_scanner::device_list;

namespace xcldev {

std::string get_val_string(std::string& dir, const char* key) {
    std::string file = dir + "/" + key;
    int fd = open(file.c_str(), O_RDONLY);
    if ( fd < 0) {
        std::cout << "Unable to open " << file << std::endl;
        throw std::runtime_error("Could not open file: " + dir + "/" + key );
    }

    char buf[OBJ_BUF_SIZE];
    memset(buf, 0, OBJ_BUF_SIZE);
    int err = read(fd, buf, OBJ_BUF_SIZE);

    if ( (err < 0) || (err >= OBJ_BUF_SIZE)) {
        std::cout << "Unable to read contents of " << file << std::endl;
    }
    return buf;
}

int get_val_int(std::string& dir, const char* key) {
    std::string buf = get_val_string(dir, key);
    return strtol(buf.c_str(), NULL, 0);
}

/*
 * get_render_value
 */
int get_render_value(std::string& dir) {
    struct dirent *entry;
    DIR *dp;
    int instance_num = 128;

    dp = opendir(dir.c_str());
    if (dp == NULL) {
      std::string tmp = "opendir: Path " + dir + " does not exist or could not be read";
      perror(tmp.c_str());
        return -1;
    }

    while ((entry = readdir(dp))) {
        if(strncmp(entry->d_name, "renderD", 7) == 0) {
            sscanf(entry->d_name, "renderD%d", &instance_num);
            break;
        }
    }

    closedir(dp);
    return instance_num;
}

} // end namespace
