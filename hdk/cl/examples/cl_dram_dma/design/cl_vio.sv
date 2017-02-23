module cl_vio (
   input clk_extra_a1

);

   // Counter running at 125MHz
   
   logic      vo_cnt_enable;
   logic      vo_cnt_load;
   logic      vo_cnt_clear;
   logic      vo_cnt_oneshot;
   logic [7:0]  vo_tick_value;
   logic [15:0] vo_cnt_load_value;
   logic [15:0] vo_cnt_watermark;

   logic      vo_cnt_enable_q = 0;
   logic      vo_cnt_load_q = 0;
   logic      vo_cnt_clear_q = 0;
   logic      vo_cnt_oneshot_q = 0;
   logic [7:0]  vo_tick_value_q = 0;
   logic [15:0] vo_cnt_load_value_q = 0;
   logic [15:0] vo_cnt_watermark_q = 0;

   logic        vi_tick;
   logic        vi_cnt_ge_watermark;
   logic [7:0]  vi_tick_cnt = 0;
   logic [15:0] vi_cnt = 0;
   
   // Tick counter and main counter
   always @(posedge clk_extra_a1) begin

      vo_cnt_enable_q     <= vo_cnt_enable    ;
      vo_cnt_load_q       <= vo_cnt_load      ;
      vo_cnt_clear_q      <= vo_cnt_clear     ;
      vo_cnt_oneshot_q    <= vo_cnt_oneshot   ;
      vo_tick_value_q     <= vo_tick_value    ;
      vo_cnt_load_value_q <= vo_cnt_load_value;
      vo_cnt_watermark_q  <= vo_cnt_watermark ;

      vi_tick_cnt = vo_cnt_clear_q ? 0 :
                    ~vo_cnt_enable_q ? vi_tick_cnt :
                    (vi_tick_cnt >= vo_tick_value_q) ? 0 :
                    vi_tick_cnt + 1;

      vi_cnt = vo_cnt_clear_q ? 0 :
               vo_cnt_load_q ? vo_cnt_load_value_q :
               ~vo_cnt_enable_q ? vi_cnt :
               (vi_tick_cnt >= vo_tick_value_q) && (~vo_cnt_oneshot_q || (vi_cnt <= 16'hFFFF)) ? vi_cnt + 1 :
               vi_cnt;

      vi_tick = (vi_tick_cnt >= vo_tick_value_q);

      vi_cnt_ge_watermark = (vi_cnt >= vo_cnt_watermark_q);
      
   end // always @ (posedge clk_extra_a1)
   

   vio_0 CL_VIO_0 (
                   .clk    (clk_extra_a1),
                   .probe_in0  (vi_tick),
                   .probe_in1  (vi_cnt_ge_watermark),
                   .probe_in2  (vi_tick_cnt),
                   .probe_in3  (vi_cnt),
                   .probe_out0 (vo_cnt_enable),
                   .probe_out1 (vo_cnt_load),
                   .probe_out2 (vo_cnt_clear),
                   .probe_out3 (vo_cnt_oneshot),
                   .probe_out4 (vo_tick_value),
                   .probe_out5 (vo_cnt_load_value),
                   .probe_out6 (vo_cnt_watermark)
                   );
   
   ila_vio_counter CL_VIO_ILA (
                   .clk     (clk_extra_a1),
                   .probe0  (vi_tick),
                   .probe1  (vi_cnt_ge_watermark),
                   .probe2  (vi_tick_cnt),
                   .probe3  (vi_cnt),
                   .probe4  (vo_cnt_enable_q),
                   .probe5  (vo_cnt_load_q),
                   .probe6  (vo_cnt_clear_q),
                   .probe7  (vo_cnt_oneshot_q),
                   .probe8  (vo_tick_value_q),
                   .probe9  (vo_cnt_load_value_q),
                   .probe10 (vo_cnt_watermark_q)
                   );


endmodule

