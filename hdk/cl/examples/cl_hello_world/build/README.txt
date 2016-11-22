## ====================================================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## FPGA Build Flow: This document describes the procedure for creating the developer design checkpoints 
## 			that will be ingested by AWS for bitstream generation. 
## ====================================================================================================


FPGA BUILD FLOW


======================
Notes
======================
   - The transfer of developer designs (CL) to AWS occurs via encrypted placed-and-routed design checkpoints (DCP). 

   - AWS provides a DCP that includes the shell (SH) logic with a black-boxed CL for development purposes: 
      'checkpoints/from_aws/SH_CL_BB_routed.dcp'

   - AWS also provides out-of-the-box scripts that compile the "CL_simple" design as if it were developer code.

   - The scripts provided create an encrypted placed-and-routed DCP that AWS will use to generate final bitstreams. 


======================
Procedure
======================
   Overview: A developer can invoke 'scripts/create_cl.tcl' in Vivado to create the encrypted placed-and-routed DCP (AWS SH + Developer CL) that AWS will ingest. 
             Calling this script also entails encryption of developer-specified RTL files. 


   Steps: 
   1) As a pre-cursor to the encryption and build process, set up path to developer RTL files in ‘scripts/create_cl.tcl’   
      - Modify variable "RTL_ORIGIN" to point to the "root directory" of the developer RTL.
      - AWS provides an encryption script ('scripts/encrypt.tcl') that is called from 'scripts/create_cl.tcl'.  
      - 'scripts/encrypt.tcl' will copy over the specified developer RTL files and encrypt them. 

   2) Update 'scripts/create_cl.tcl' to include the encrypted RTL files (from step #1).
   
   2a) Developer may include constraints in 'constraints/cl_synth_user.xdc'

   3) Run the build from the 'scripts' folder as follows:
          “vivado -mode batch -source create_cl.tcl” 

      This runs:
         - Synthesis of CL
         - Implementation of CL with AWS Shell
         - Generates design checkpoint for AWS ingestion
         - (To aid developers in verification, the run also emulates the process AWS will use to generate bitstreams)


   Outputs:
      - ‘checkpoints/*’: Various checkpoints generated during the build process
      - ‘to_aws/SH_CL_routed.dcp’: Encrypted placed-and-routed design checkpoint for AWS ingestion
      - ‘reports/*’: Various build reports (generally, check_timing/report_timing)
      - ‘src/*’: Encrypted developer source
      - ‘constraints/*’: Implementation constraints


======================
Encryption Note
======================
   Developer RTL is encrypted using IEEE 1735 V2 encryption.  This level of encryption protects both the raw source and the implemented design.  


======================
Advanced Notes
======================
   The included implementation flow is a baseline flow.  It is possible to add advanced commands/constraints (e.g, regioning) to the flow.
   Developers are free to modify the flow, but the final output must be a combined (AWS Shell + CL), encrypted, placed-and-routed design checkpoint.

