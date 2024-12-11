#!/bin/bash

./runme.sh\
   +AXIS_CHECK_DRIVE_AND_MONITOR +AXIS_RAND_READY\
   +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE\
   +ntb_random_seed=9 +PACKETS=100 +MAX_LEN=1516

cp -rf master.out master.in

./runme.sh\
   +AXIS_CHECK_DRIVE_AND_MONITOR +AXIS_RAND_READY

./clean.sh

