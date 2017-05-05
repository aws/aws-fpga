#!/usr/bin/env bash

# Process command line args
while [[ $# -gt 1 ]]
do
key="$1"

case $key in
    -t|--test)
    test="$2"
    shift # past argument
    ;;
    *)
    echo -e >&2 "ERROR: Invalid option: $1\n"
    exit 1
    ;;
esac
shift # past argument or value
done

if [ "$test" = "" ]; then
    echo -e >&2 "ERROR: Invalid test: $test\n"
    exit 1
fi

#BOZO: Assume pass unless set
FAIL_FLAG=0

if [ -z "$WORKSPACE" ]; then
    export WORKSPACE=$AWS_FPGA_REPO_DIR
fi

source $WORKSPACE/hdk_setup.sh;

export CL_DIR=$HDK_DIR/cl/examples/$test

if [ ! -d $CL_DIR ]; then
    echo -e >&2 'ERROR: The test passed in does not exist!'
    exit 1
fi

cd $HDK_DIR/cl/examples/$test/build/scripts
./aws_build_dcp_from_cl.sh -foreground

# Use last_log symlink to grab logname
if [ ! -e "last_log" ]; then
    echo -e >&2 'ERROR: Could not find the log file to check (Does last_log exist?)'
    exit 1
fi

# Check the number of warnings
NUM_WARNINGS=`grep -c "^WARNING" last_log`

echo "INFO: Saw $NUM_WARNINGS warning(s) in log file";

# Compare number of warnings to expected number
EXP_NUM_WARNINGS=$(<.warnings)

echo "INFO: Expected $EXP_NUM_WARNINGS warning in log file"

if [ $NUM_WARNINGS -eq $EXP_NUM_WARNINGS ]; then
    echo "INFO: NUM_WARNINGS check passed!"
else
    echo "ERROR: NUM_WARNINGS check failed!"
    FAIL_FLAG=1
fi

# Check the number of critical warnings
NUM_CRITICAL_WARNINGS=`grep -c "^CRITICAL WARNING" last_log`

echo "INFO: Saw $NUM_WARNINGS critical warning(s) in log file";

# Compare number of warnings to expected number
EXP_NUM_CRITICAL_WARNINGS=$(<.critical_warnings)

echo "INFO: Expected $EXP_NUM_CRITICAL_WARNINGS critical warning(s) in log file"

if [ $NUM_CRITICAL_WARNINGS -eq $EXP_NUM_CRITICAL_WARNINGS ]; then
    echo "INFO: NUM_CRITICAL_WARNINGS check passed!"
else
    echo "ERROR: NUM_CRITICAL_WARNINGS check failed!"
    FAIL_FLAG=1
fi


# Check if there are any setup/hold-time violations
NUM_TIMING_VIOLATIONS=`grep -c "The design did not meet timing requirements." last_log`

if [ $NUM_TIMING_VIOLATIONS -gt 0 ]; then
    echo "WARNING: Timing violations found.  Design may not be functional."
#	FAIL_FLAG=1
else
    echo "INFO: No timing violations found!"
fi

# If FAIL_FLAG was sent, return non-zero error code!
if [ $FAIL_FLAG = 1 ]; then
    echo "ERROR: One or more more checks failed!"
    exit 1
else
    echo "INFO: All checks passing!"
    exit 0
fi


