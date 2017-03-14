// Amazon FGPA Hardware Development Kit
// 
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// 
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
// 
//    http://aws.amazon.com/asl/
// 
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

package tb_type_defines_pkg;

  virtual class ClockProfile;     
     typedef enum integer {PROFILE_0=0, PROFILE_1=1, PROFILE_2=2, PROFILE_3=3, PROFILE_4=4, PROFILE_5=5} CLK_PROFILE;
  endclass // Clock_Profile
   
endpackage
