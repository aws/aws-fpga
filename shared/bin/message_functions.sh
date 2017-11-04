#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

function info_msg {
  echo -e "INFO: $1"
}

function debug_msg {
  if [[ $debug == 0 ]]; then
    return
  fi
  echo -e "DEBUG: $1"
}

function err_msg {
  echo -e >&2 "ERROR: $1"
}

function warn_msg {
  echo -e "WARNING: $1"
}
