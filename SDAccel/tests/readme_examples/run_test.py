import unittest
import xmlrunner
import subprocess
import os
import logging
import sys

logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)-5.5s]  %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)])

logger = logging.getLogger("")


class ReadmeExampleTestCase(unittest.TestCase):

    EXAMPLE_LOCATION = "None"

    def setUp(self):
        cmdline = ['make', 'clean']
        logger.info("Calling: " + subprocess.list2cmdline(cmdline))

        try:
            output = subprocess.check_output(
                cmdline,
                cwd=self.EXAMPLE_LOCATION,
                stderr=subprocess.STDOUT
            )
            logger.info(output)
        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(str(o))

    def tearDown(self):
        cmdline = ['make', 'clean']
        logger.info("Calling: " + subprocess.list2cmdline(cmdline))
        try:
            output = subprocess.check_output(
                cmdline,
                cwd=self.EXAMPLE_LOCATION,
                stderr=subprocess.STDOUT
            )
            logger.info(output)
        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(str(o))

    def test_sw_emu(self):
        cmdline = ['make', 'check', "TARGETS=sw_emu", "DEVICES={0}".format(os.environ['AWS_PLATFORM'])]
        logger.info("Running: " + subprocess.list2cmdline(cmdline))
        logger.info("CWD: " + self.EXAMPLE_LOCATION)

        try:
            output = subprocess.check_output(
                cmdline,
                cwd=self.EXAMPLE_LOCATION,
                stderr=subprocess.STDOUT
            )
        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(str(o))

    def test_hw_emu(self):
        cmdline = ['make', 'check', "TARGETS=hw_emu", "DEVICES={0}".format(os.environ['AWS_PLATFORM'])]
        logger.info("Running: " + subprocess.list2cmdline(cmdline))
        logger.info("CWD: " + self.EXAMPLE_LOCATION)

        try:
            output = subprocess.check_output(
                cmdline,
                cwd=self.EXAMPLE_LOCATION,
                stderr=subprocess.STDOUT
            )
        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(str(o))

    def test_all(self):
        cmdline = ['make', "DEVICES={0}".format(os.environ['AWS_PLATFORM']), 'all']
        logger.info("Running: " + subprocess.list2cmdline(cmdline))
        logger.info("CWD: " + self.EXAMPLE_LOCATION)

        try:
            output = subprocess.check_output(
                cmdline,
                cwd=self.EXAMPLE_LOCATION,
                stderr=subprocess.STDOUT
            )
        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(str(o))


if __name__ == '__main__':

    try:
        sdaccel_dir = os.environ["SDACCEL_DIR"]
    except KeyError:
        logger.error("Please set the environment variable SDACCEL_DIR")
        sys.exit(1)

    xilinx_examples_dir = sdaccel_dir + "/examples/xilinx"
    if os.listdir(xilinx_examples_dir) == []:
        logger.error("Please update git submodule: git submodule update --init -- "
                     "$SDACCEL_DIR/examples/xilinx ")
        sys.exit(1)

    ReadmeExampleTestCase.EXAMPLE_LOCATION = sdaccel_dir + "/examples/xilinx/getting_started/host/helloworld_ocl/"

    unittest.main(
        testRunner=xmlrunner.XMLTestRunner(output='test-reports'),
        # these make sure that some options that are not applicable
        # remain hidden from the help menu.
        failfast=False, buffer=False, catchbreak=False)