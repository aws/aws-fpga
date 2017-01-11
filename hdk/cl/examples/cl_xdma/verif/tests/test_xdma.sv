module test_xdma();

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
       que_buffer_to_cl(0, desc_buf, 64);
       
       start_dma_to_cl(0);

       desc_buf[0] = 8'h5;
       desc_buf[1] = 8'h6;
       desc_buf[2] = 8'h7;
       desc_buf[3] = 8'h8;
       desc_buf[4] = 8'h9;
       
       for (int i = 5 ; i<= 63 ; i++) begin
          desc_buf[i] = 'h0;
       end

       que_cl_to_buffer(0, desc_buf, 64);
       
       start_dma_tp_buffer(0);

    end // initial begin

endmodule // test_xdma
