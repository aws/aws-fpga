// Amazon FPGA Hardware Development Kit
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


//*************************************************************************************
//-------------------------------------------------------------------------------------
// Generic Buffer class.  has data array, and methods to read/write to/from host memory,
// and compare buffers.
//-------------------------------------------------------------------------------------
//*************************************************************************************


`ifndef __DEFINED_GEN_BUF_T__

   `define __DEFINED_GEN_BUF_T__

   class gen_buf_t;
   
      logic[7:0] data[$];

      bit print_ok_compare = 0;

      //Input size of buffer in bytes -- assume address of all f's is "null"
      function new ();
      endfunction
   
      //Initialization with incrementing data.  Note this assumes empty array (queue), and adds entries to the array
      virtual function init_inc(input[31:0] first_data, input int length = 4);
         bit[31:0] tmp_data;
   
         tmp_data = first_data;
         for (int i=0; i<length; i++)
         begin
            this.data.push_back(tmp_data[8*i[1:0]+:8]);
            if (i[1:0]==2'b11)
               tmp_data++;
         end
      endfunction

      //Initialization with constant.  Note this assumes empty array (queue), and adds entries to the array
      virtual function init_const(input[31:0] first_data, input int length = 4);
   
         for (int i=0; i<length; i++)
         begin
            this.data.push_back(first_data[8*i[1:0]+:8]);
         end
      endfunction

      //Initialization with random_data.  Note this assumes empty array (queue), and adds entries to the array
      virtual function init_rnd(input int length = 4);
  
         for (int i=0; i<length; i++)
         begin
            this.data.push_back($urandom());
         end
      endfunction

      //Write with incrementing data.  Note this uses existing entries in the queue/array
      // By default write the entire buffer
      virtual function write_inc(input int start_addr=0, input[31:0] first_data=0, input int length = 32'hffffffff);
         bit[31:0] tmp_data;
  
         length = (length==32'hffffffff)? data.size(): length; 
         tmp_data = first_data;
         for (int i=0; i<length; i++)
         begin
            if (i<data.size())
               this.data[i] = tmp_data[8*i[1:0]+:8];
            if (i[1:0]==2'b11)
               tmp_data++;
         end
      endfunction

      //Initialization with constant.  Note this uses existing entries int the queue/array. 
      // By default write the entire buffer
      virtual function write_const(input int start_addr=0, input[31:0] first_data=0, input int length = 32'hffffffff);
   
         length = (length==32'hffffffff)? data.size(): length; 
         for (int i=0; i<length; i++)
         begin
            if (i<data.size())
               this.data[i] = first_data[8*i[1:0]+:8];
         end
      endfunction

      //Initialization with random_data.  Note this uses existing entries in the queue/array
      // By default write the entire buffer
      virtual function write_rnd(input int length = 32'hffffffff);
  
         length = (length==32'hffffffff)? data.size(): length; 
         for (int i=0; i<length; i++)
         begin
            if (i<data.size())
               this.data[i] = $urandom();
         end
      endfunction
   
      //Compare buffer
      virtual function compare(gen_buf_t compare_to, input int length=32'hffffffff);
         bit ret = 0;
         int cmp_length;

         bit[31:0] tmp_data;
         bit[31:0] tmp_data_to;
         string tmp_s;
  
         //If length is not specified then use length of the buffer
         if (length==32'hffffffff)
         begin
            if (this.data.size() != compare_to.data.size())
            begin
               $display($time,,,"***ERROR*** gen_buf_t compare length miscompare.  this=%0d, compare_to=%0d", this.data.size(), compare_to.data.size());
            end
            cmp_length = this.data.size();
         end

         for (int i=0; i<cmp_length; i++)
         begin
            if (this.data.size()<=i)
            begin
               $display($time,,,"***ERROR*** gen_buf_t buffer too short, this.data.size()=0x%x, cmp_length=0x%x", this.data.size(), cmp_length);
               ret = 1;
            end
            else if (compare_to.data.size()<=i)
            begin
               $display($time,,,"***ERROR*** gen_buf_t.compare_to buffer too short, compare_to.data.size()=0x%x, cmp_length=0x%x", compare_to.data.size(), cmp_length);
               ret = 1;
            end
            else if (this.data[i] != compare_to.data[i])
            begin
               $display($time,,,"***ERROR*** gen_buf_t.compare data mismatch address[0x%x]: buf_t=0x%x, compare_to=0x%x", i, this.data[i], compare_to.data[i]);
               ret = 1;
            end
            //For debug can print out OK compares
            else if (this.print_ok_compare)
            begin
               $display($time,,,"!!!COMPARE OK!!!  gen_buf_t.compare address[0x%x]: buf_t=0x%x, compare_to=0x%x", i, this.data[i], compare_to.data[i]);
            end
         end

         //If got an error display entire packet 
         if (ret)
         begin
            for (int i=0; i< (cmp_length/4 + |cmp_length[1:0]); i++)
            begin
               tmp_data = 0;
               tmp_data_to = 0;

               for (int b=0; b<4; b++)
               begin
                  if ((i*4 + b) < cmp_length)
                  begin
                     tmp_data[b*8+:8] = this.data[i*4 + b]; 
                     tmp_data_to[b*8+:8] = compare_to.data[i*4 + b]; 
                  end
               end

               if (tmp_data != tmp_data_to)
                  tmp_s = "   ***MISCOMPARE***";
               else
                  tmp_s = "";
               $display($time,,,"    addr[0x%4x]:   0x%8x   0x%8x %s", i*4, tmp_data, tmp_data_to, tmp_s);
            end
         end
               
   
         compare = ret;
      endfunction
   
      //Compare just a byte array queue (if dis-similar data type)
      virtual function compare_byte_array(logic[7:0] compare_to [$], input int length=32'hffffffff);
         bit ret = 0;
         int cmp_length;
  
         //If length is not specified then use length of the buffer
         cmp_length = (length==32'hffffffff)? this.data.size(): length;
 
         for (int i=0; i<cmp_length; i++)
         begin
            if (this.data.size()<=i)
            begin
               $display($time,,,"***ERROR*** gen_buf_t buffer too short, this.data.size()=0x%x, cmp_length=0x%x", this.data.size(), cmp_length);
               ret = 1;
            end
            else if (compare_to.size()<=i)
            begin
               $display($time,,,"***ERROR*** gen_buf_t.compare_to buffer too short, compare_to.data.size()=0x%x, cmp_length=0x%x", compare_to.size(), cmp_length);
               ret = 1;
            end
            else if (this.data[i] != compare_to[i])
            begin
               $display($time,,,"***ERROR*** gen_buf_t.compare data mismatch addres[0x%x]: buf_t=0x%x, compare_to=0x%x", i, this.data[i], compare_to[i]);
               ret = 1;
            end
            //For debug can print out OK compares
            else if (this.print_ok_compare)
            begin
               $display($time,,,"!!!COMPARE OK!!!  gen_buf_t.compare addres[0x%x]: buf_t=0x%x, compare_to=0x%x", i, this.data[i], compare_to[i]);
            end
         end
 
   
         compare_byte_array = ret;
      endfunction

      virtual function display(input int length=32'hffffffff);

         logic[31:0] tmp_dw;
         int num_dw;

         int tmp_size;

         tmp_size = (length==32'hffffffff)? this.data.size(): length;

         num_dw = tmp_size/4;
         num_dw = ((tmp_size % 4)==0)? num_dw: num_dw + 1;

         $display("PktDisplay length=0x%x:", this.data.size()); 
         for (int i=0; i<num_dw; i++)
         begin
            tmp_dw = 0;
            for (int j=0; j<4; j++)
            begin
               if (this.data.size() >= ((i*4)+j))
                  tmp_dw[j*8+:8] = this.data[i*4 + j];
            end

            $display("    data[0x%4x] = 0x%8x", i*4, tmp_dw);
         end
      endfunction
      
            
   
   endclass

`endif

