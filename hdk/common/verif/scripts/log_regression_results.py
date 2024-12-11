#!/usr/bin/env python3

# Amazon FPGA Hardware Development Kit
#
# Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


import os
import sys
from glob import glob
from argparse import ArgumentParser, Namespace
from typing import Dict, List


parser = ArgumentParser(prog="Regression Log Generator", description="Generate a log for all tests ran for the simulator specified")
parser.add_argument('--simulator', dest='simulator', required=True)
parser.add_argument('--cl_dir', dest='cl_dir', required=True)
parser.add_argument('--regression_results_log', dest='regression_results_log', required=True)
parser.add_argument('--sim_dir_extension', dest='sim_dir_extension', required=True)


if __name__ == '__main__':
    args = parser.parse_args()

    is_python3 = sys.version_info >= (3, 0) and sys.version_info < (4, 0)
    is_greater_than_3_8 = sys.version_info >= (3, 8)
    if not (is_python3 and is_greater_than_3_8):
        raise Exception("The Python script experienced a failure. Please review and make sure Python 3.8+ is installed\n")


class LogGenerator:
    def __init__(self, args: Namespace) -> None:
        self.simulator: str = args.simulator
        self.cl_dir: str = args.cl_dir
        self.regression_results_log: str = args.regression_results_log
        self.sim_dir_extension: str = args.sim_dir_extension
        self.makefile_testlist_path: str = f"{self.cl_dir}/verif/scripts/Makefile.tests"
        self.test_results: Dict[str,str] = {}

    def generate_regression_log(self) -> None:
        self.update_test_results()

        self.warn_of_test_count_mismatch()

        with open(self.regression_results_log, 'w') as f:
            table: str = print_table(self.test_results)
            f.write(table)

    def update_test_results(self) -> str:
        all_logs: List[str] = glob(f"{self.cl_dir}/verif/sim/{self.simulator}/*{self.sim_dir_extension}/*.log")
        test_logs = [path for path in all_logs if self.is_test_log(path) and "backup" not in path]
        for test_log in test_logs:
            test_name: str = self.get_test_name_as_test_dirname(test_log)
            self.test_results[test_name] = self.get_test_result(test_log)

    @staticmethod
    def is_test_log(log_path: str) -> bool:
        test_log_name: str = os.path.basename(log_path).replace('.log', '')
        test_name: str = LogGenerator.get_test_name_as_test_dirname(log_path)
        parent_dir: str = os.path.basename(os.path.dirname(log_path))
        return test_name in parent_dir and test_log_name in parent_dir and test_log_name in test_name

    @staticmethod
    def get_test_name_as_test_dirname(log_path: str) -> str:
        path_to_parent: str = os.path.dirname(log_path)
        return os.path.basename(path_to_parent)

    def get_test_result(self, test_log: str) -> str:
        result_signature: str = "*** TEST "
        with open(test_log) as f:
            for line in f:
                line: str = line.strip()
                if result_signature in line:
                    return line.split(result_signature)[1].strip().split()[0].strip()
        return "NONE (possible compile error)"

    def warn_of_test_count_mismatch(self) -> None:
        expected_test_list: List[str] = self.get_expected_test_list(self.makefile_testlist_path)
        num_test_results: int = len(self.test_results.values())
        if num_test_results != len(expected_test_list):
            found_tests: List[str] = list(self.test_results.keys())
            raise Exception(f"""

    WARNING: Found {num_test_results} test results in 'sim' directory, but found {len(expected_test_list)} in {self.makefile_testlist_path}.
        EXPECTED: {expected_test_list}
        FOUND in 'sim' dir: {found_tests}

        MISSING: {list(set(expected_test_list) - set(found_tests))}
        ADDITIONAL: {list(set(found_tests) - set(expected_test_list))}
            """)

    @staticmethod
    def get_expected_test_list(makefile_testlist_path: str) -> List[str]:
        makefile_test_signature: str = "TEST="
        expected_tests: List[str] = []
        with open(makefile_testlist_path) as f:
            for line in f:
                line = line.strip()
                if makefile_test_signature in line and not line.startswith('#'):
                    test_name: str = line.split(makefile_test_signature)[1].strip()
                    expected_tests.append(test_name)
        return expected_tests


def print_table(data: Dict[str, str]) -> str:
    max_key_length: int = max([len(key) for key in data.keys()])
    max_value_length: int = max([len(value) for value in data.values()])
    test_name_header: str = f"{'TEST NAME':<{max_key_length}}"
    test_result_header: str = f"{'TEST RESULT':<{max_value_length}}"
    # This is in case the column values are shorter than the header text
    max_key_length = len(test_name_header)
    max_value_length = len(test_result_header)

    rows: List[str] = get_rows(data, max_key_length, max_value_length)
    border: str = get_border(max_key_length, max_value_length)
    content: str = "".join([f"{row}\n" for row in rows])
    table: str = f"""
{border}
{f"| {test_name_header} | {test_result_header} |"}
{border}
{content.strip()}
{border}"""

    print(table)
    return table


def get_border(max_key_length: int, max_value_length: int) -> str:
    SPACE_PADDING = 2
    border_sections = ['-' * (val + SPACE_PADDING) for val in [max_key_length, max_value_length]]
    return f"|{'|'.join(border_sections)}|"


def get_rows(data: Dict[str, str], max_key_length: int, max_value_length: int) -> List[str]:
    rows: List[str] = []
    for key, value in data.items():
        rows.append(f"| {str(key):<{max_key_length}} " + '|' + f" {str(value):<{max_value_length}} |")
    return rows


if __name__ == '__main__':
    try:
        generator = LogGenerator(args)
        generator.generate_regression_log()
    except:
        raise Exception("The Python script experienced a failure. Please review and make sure Python 3.8+ is installed\n")
