# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

# External Modules
import logging
import os

logger = logging.getLogger('logger')
current_dir = os.path.dirname(os.path.realpath(__file__))


class FileProvider(object):
    def __init__(self, directory_to_search):

        self.exclude_files = [
            "ccf_ctl.v",
            "design_error.inc",
            "flop_ccf.sv",
            "flop_fifo_2.sv",
            "flop_fifo_lu.sv",
            "flop_fifo.sv",
            "ft_fifo_p2.v",
            "ft_fifo_p.v",
            "ft_fifo.v",
            "gray.inc",
            "lib_pipe.sv",
            "push_2_fifo_double_pop.sv",
            "push_2_fifo_guts.inc",
            "push_2_fifo.sv",
            "ram_2p_bit_en.v",
            "ram_2p_dc.v",
            "ram_2p_syn.v",
            "ram_2p_trial_synth.v",
            "ram_2p.v",
            "rr_arb.sv",
            "sync.v",
            "README",
            ".gitignore",
            "supported_vivado_versions.txt",
            "hdk_version.txt",
            "dest_register_slice.v",
            "src_register_slice.v",
        ]

        self.exclude_extensions = [
            ".md",
            ".pdf",
            ".jpg",
            ".csv",
            ".xdc",
            ".txt",
            ".f",
            ".pptx",
            ".PNG",
            ".xlsx",
            ".png"
        ]

        self.exclude_paths = {
            "/common/shell_v032117d7/design/ip",
            "/common/shell_v04151701/design/ip"
        }

        self.directory = directory_to_search

        self.exclude_paths = [self.directory + s for s in self.exclude_paths]

    def get_files(self):

        file_list = []
        valid_file_list = []
        invalid_file_list = []

        for root, dirs, files in os.walk(self.directory, topdown=True):

            # Removing the excluded paths from os.walk search
            for exclude_path in self.exclude_paths:
                dir_name = os.path.basename(exclude_path)
                parent_path = os.path.dirname(exclude_path)

                if parent_path == root:
                    if dir_name in dirs:
                        dirs.remove(dir_name)

            for file_name in files:
                file_path = os.path.join(root, file_name)
                file_list.append(file_path)

        for file_path in file_list:

            file_basename = os.path.basename(file_path)
            file_name, file_extension = os.path.splitext(file_path)

            if file_basename in self.exclude_files:
                logger.debug("Excluded File: " + file_path)
                invalid_file_list.append(file_path)
                continue

            elif file_extension in self.exclude_extensions:
                logger.debug("Excluded Extension: " + file_path)
                invalid_file_list.append(file_path)
                continue
            else:
                valid_file_list.append(file_path)

        return valid_file_list