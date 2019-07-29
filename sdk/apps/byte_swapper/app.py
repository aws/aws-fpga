# Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

from flask import Flask
from flask import request
import fpga_funcs
import signal,sys
import logging

logger = logging.getLogger(__name__)
fpga = fpga_funcs.FPGAFuncs()
fpga.load_afi()
app = Flask(__name__)
@app.route("/", methods=['GET', 'POST'], strict_slashes=False)
def swap_data():
    data = request.args.get('input_data')
    logger.info("Swapping data")
    return fpga.swap_bytes(data)

@app.route("/status", methods=['GET'])
def get_fpga_slot_status():
    logger.info("Checking server status")
    return fpga.slot_state()

def sig_handler(sig, frame):
    logger.info("Signal ({}) received!".format(sig))
    fpga.clear_fpga()
    fpga.clean_up()
    sys.exit(0)

signal.signal(signal.SIGINT, sig_handler)
