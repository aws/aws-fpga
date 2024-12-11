#!/bin/bash

./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=9 +PACKETS=50 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/mac0_tx.in

./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=1 +PACKETS=50 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/mac1_tx.in

./runme.sh +GEN_STIM +AXIS_DUMP_PACKET +AXIS_DUMP_PACKET_WITH_IDLE +ntb_random_seed=5 +PACKETS=100 +MIN_LEN=20 +MAX_LEN=1516
cp -rf master.out $CL_DIR/verif/scripts/stimulus/h2c.in

./clean.sh

