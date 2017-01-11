module test_xdma();
    logic status;
    int   timeout_count;
   
    initial begin

       logic [7:0] desc_buf [];

       tb.sh.power_up();

       desc_buf[0] = 8'h0;
       desc_buf[1] = 8'h1;
       desc_buf[2] = 8'h2;
       desc_buf[3] = 8'h3;
       desc_buf[4] = 8'h4;

       for (int i = 5 ; i<= 63 ; i++) begin
         desc_buf[i] = 'h0;
       end
       
       tb.sh.que_buffer_to_cl(0, desc_buf, 64);
       
       tb.sh.start_dma_to_cl(0);

       timeout_count = 0;
       do begin
         status = tb.sh.is_dma_to_cl_done(0);
         timeout_count++;
       end while ((!status) && (timeout_count < 100));
       
       desc_buf[0] = 8'h5;
       desc_buf[1] = 8'h6;
       desc_buf[2] = 8'h7;
       desc_buf[3] = 8'h8;
       desc_buf[4] = 8'h9;
       
       for (int i = 5 ; i<= 63 ; i++) begin
          desc_buf[i] = 'h0;
       end

       tb.sh.que_cl_to_buffer(0, desc_buf, 64);
       
       tb.sh.start_dma_to_buffer(0);

       timeout_count = 0;
       do begin
         status = tb.sh.is_dma_to_buffer_done(0);
         timeout_count++;
       end while ((!status) && (timeout_count < 100));
    end // initial begin

endmodule // test_xdma
