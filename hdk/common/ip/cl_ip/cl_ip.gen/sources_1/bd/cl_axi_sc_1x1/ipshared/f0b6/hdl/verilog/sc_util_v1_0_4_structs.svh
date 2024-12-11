//  (c) Copyright 2016 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // cascade parameters and typedefs
  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  typedef logic [((T_SC_AWUSER_WIDTH == 0) ? 1 : T_SC_AWUSER_WIDTH)-1:0]    t_sc_awuser;
  typedef logic [((T_SC_ARUSER_WIDTH == 0) ? 1 : T_SC_ARUSER_WIDTH)-1:0]    t_sc_aruser;
  typedef logic [((T_SC_BUSER_WIDTH ==  0) ? 1 : T_SC_BUSER_WIDTH )-1:0]    t_sc_buser;
  typedef logic [((T_SC_RUSER_BITS_PER_BYTE == 0) ? 1 : (T_SC_RUSER_BITS_PER_BYTE*(T_SC_RDATA_WIDTH/8)))-1:0] t_sc_ruser;
  typedef logic [((T_SC_WUSER_BITS_PER_BYTE == 0) ? 1 : (T_SC_WUSER_BITS_PER_BYTE*(T_SC_WDATA_WIDTH/8)))-1:0] t_sc_wuser;
  typedef logic [T_SC_ADDR_WIDTH-1:0]                     t_sc_addr;
  typedef logic [T_SC_MSC_ROUTE_WIDTH-1:0]                t_sc_msc_route;
  typedef logic [T_SC_SSC_ROUTE_WIDTH-1:0]                t_sc_ssc_route;
  typedef logic [(T_SC_ID_WIDTH==0?1:T_SC_ID_WIDTH)-1:0]  t_sc_id;
  typedef logic [(T_SC_WUSER_BITS_PER_BYTE+8)-1:0]        t_sc_wuserdata_unit;
  typedef logic [(T_SC_RUSER_BITS_PER_BYTE+8)-1:0]        t_sc_ruserdata_unit;
  typedef logic [T_SC_RDATA_WIDTH -1:0]                   t_sc_rdata;
  typedef logic [T_SC_WDATA_WIDTH-1:0]                    t_sc_wdata;
  typedef logic [(T_SC_WDATA_WIDTH/8)-1:0]                t_sc_wstrb;

  typedef struct packed {
    t_sc_wuserdata_unit   userdata;
    logic                 strb;
  } t_sc_wdata_unit;

  typedef struct packed {
    t_sc_ruserdata_unit   userdata;
  } t_sc_rdata_unit;

  typedef struct packed {
    t_sc_id                 id;
    t_axi_len               len;
    t_axi_size              size;
  } t_sc_addr_exclusive;

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // payld parameters and typedefs
  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  typedef struct packed {
    t_axi_cache             cache;
    t_axi_qos               qos;
    t_axi_prot              prot;
    t_axi_lock              lock;
    t_sc_addr               addr;
    t_sc_id                 id;
    t_sc_aruser             user;
    t_max_byte_size         last_offset;
    t_sc_addr_exclusive     exclusive;
    t_max_ep_route          ep_route;
    t_axi_len               seg_len;
    t_sc_msc_route          sc_route;
  } t_sc_arpayld;

  typedef struct packed {
    t_axi_cache             cache;
    t_axi_qos               qos;
    t_axi_prot              prot;
    t_axi_lock              lock;
    t_sc_addr               addr;
    t_sc_id                 id;
    t_sc_awuser             user;
    t_max_byte_size         last_offset;
    t_sc_addr_exclusive     exclusive;
    t_max_ep_route          ep_route;
    t_axi_len               seg_len;
    t_sc_msc_route          sc_route;
  } t_sc_awpayld;

  typedef struct packed {
    t_sc_wdata_unit[(T_SC_WDATA_WIDTH/8)-1:0] bytes;
    t_axi_last              last;
    t_max_byte_size         last_offset;
    t_max_byte_size         first_offset;
    t_sc_msc_route          sc_route;
  } t_sc_wpayld;

  typedef struct packed {
    t_sc_rdata_unit[(T_SC_RDATA_WIDTH/8)-1:0] bytes;
    t_axi_last              last;
    t_axi_resp              resp;
    t_sc_id                 id;
    t_max_byte_size         last_offset;
    t_max_byte_size         first_offset;
    t_sc_ssc_route          sc_route;
  } t_sc_rpayld;

  typedef struct packed {
    t_axi_resp              resp;
    t_sc_id                 id;
    t_sc_buser              user;
    t_sc_ssc_route          sc_route;
  } t_sc_bpayld;

//synthesis translate_off
`ifdef MODEL_TECH

  function string sprint_sc_addr_exclusive(
    input t_sc_addr_exclusive  excl
  );
    string str;
    str = "";
    str = $sformatf("exclusive.id           = 0x%0x\n%s", excl.id,str);
    str = $sformatf("exclusive.len          = 0x%0x\n%s", excl.len,str);
    str = $sformatf("exclusive.size         = 0x%0x\n%s", excl.size,str);
    return (str);
  endfunction

  function string sprint_sc_awpayld(
    input t_sc_awpayld  pay
  );
    string str;
    str = "";
    str = sprint_sc_addr_exclusive(pay.exclusive);
    str = $sformatf("ep_route   = 0x%0x\n%s", pay.ep_route,str);
    str = $sformatf("user       = 0x%0x\n%s", pay.user,str);
    str = $sformatf("sc_route   = 0x%0x\n%s", pay.sc_route,str);
    str = $sformatf("seg_len    = 0x%0x\n%s", pay.seg_len,str);
    str = $sformatf("id         = 0x%0x\n%s", pay.id,str);
    str = $sformatf("addr       = 0x%0x\n%s", pay.addr,str);
    str = $sformatf("lock       = 0x%0x\n%s", pay.lock,str);
    str = $sformatf("prot       = 0x%0x\n%s", pay.prot,str);
    str = $sformatf("qos        = 0x%0x\n%s", pay.qos,str);
    str = $sformatf("cache      = 0x%0x\n%s", pay.cache,str);
    str = $sformatf("AWPAYLD\n%s",str);
    return (str);
  endfunction : sprint_sc_awpayld

  function string sprint_sc_arpayld(
    input t_sc_arpayld  pay
  );
    string str;
    str = "";
    str = sprint_sc_addr_exclusive(pay.exclusive);
    str = $sformatf("ep_route   = 0x%0x\n%s", pay.ep_route,str);
    str = $sformatf("user       = 0x%0x\n%s", pay.user,str);
    str = $sformatf("sc_route   = 0x%0x\n%s", pay.sc_route,str);
    str = $sformatf("seg_len    = 0x%0x\n%s", pay.seg_len,str);
    str = $sformatf("id         = 0x%0x\n%s", pay.id,str);
    str = $sformatf("addr       = 0x%0x\n%s", pay.addr,str);
    str = $sformatf("lock       = 0x%0x\n%s", pay.lock,str);
    str = $sformatf("prot       = 0x%0x\n%s", pay.prot,str);
    str = $sformatf("qos        = 0x%0x\n%s", pay.qos,str);
    str = $sformatf("cache      = 0x%0x\n%s", pay.cache,str);
    str = $sformatf("ARPAYLD\n%s",str);
    return (str);
  endfunction : sprint_sc_arpayld

  function string sprint_sc_wpayld(
    input t_sc_wpayld  pay
  );
    string str;
    string strb;
    string data;
    str = "";
    strb = "";
    data = "";
    str = $sformatf("first_offset = 0x%0x\n%s", pay.first_offset,str);
    str = $sformatf("last_offset  = 0x%0x\n%s", pay.last_offset,str);
    str = $sformatf("sc_route     = 0x%0x\n%S", pay.sc_route,str);
    str = $sformatf("last         = 0x%0x\n%s", pay.last,str);
    for (int i = 0; i < T_SC_WDATA_WIDTH/8;i++) begin
      data = $sformatf("%0x%s", pay.bytes[i].userdata, data);
      strb = $sformatf("%0x%s", pay.bytes[i].strb, strb);
    end
    str = $sformatf("WPAYLD\n%sdata:%s\nstrb:%d\n",str,data,strb);
    return (str);
  endfunction : sprint_sc_wpayld

  function string sprint_sc_rpayld(
    input t_sc_rpayld  pay
  );
    string str;
    string data;
    str = "";
    data = "";
    str = $sformatf("first_offset = 0x%0x\n%s", pay.first_offset,str);
    str = $sformatf("last_offset  = 0x%0x\n%s", pay.last_offset,str);
    str = $sformatf("sc_route     = 0x%0x\n%S", pay.sc_route,str);
    str = $sformatf("id           = 0x%0x\n%s", pay.id,str);
    str = $sformatf("resp         = 0x%0x\n%s", pay.resp,str);
    str = $sformatf("last         = 0x%0x\n%s", pay.last,str);
    for (int i = 0; i < T_SC_RDATA_WIDTH/8;i++) begin
      data = $sformatf("%0x%s", pay.bytes[i].userdata, data);
    end
    str = $sformatf("RPAYLD\n%sdata:%s\n",str,data);
    return (str);
  endfunction : sprint_sc_rpayld

  function string sprint_sc_bpayld(
    input t_sc_bpayld  pay
  );
    string str;
    str = "";
    str = $sformatf("user       = 0x%0x\n%s", pay.user,str);
    str = $sformatf("sc_route   = 0x%0x\n%s", pay.sc_route,str);
    str = $sformatf("id         = 0x%0x\n%s", pay.id,str);
    str = $sformatf("resp       = 0x%0x\n%s", pay.resp,str);
    str = $sformatf("BPAYLD\n%s",str);
    return (str);
  endfunction : sprint_sc_bpayld
`endif
//synthesis translate_on


typedef struct packed {
  t_axi_cache       cache;
  t_axi_qos         qos;
  t_axi_prot        prot;
  t_axi_lock        lock;
  t_axi_len         len;
  t_sc_addr         addr;
  t_sc_id           id;
  t_axi_size        size;
  t_axi_burst       burst;
  t_sc_awuser       user;
} t_sc_awvector;

typedef struct packed {
  t_axi_cache       cache;
  t_axi_qos         qos;
  t_axi_prot        prot;
  t_axi_lock        lock;
  t_axi_len         len;
  t_sc_addr         addr;
  t_sc_id           id;
  t_axi_size        size;
  t_axi_burst       burst;
  t_sc_aruser       user;
} t_sc_arvector;

typedef struct packed {
  t_sc_wstrb        strb;
  t_sc_wdata        data;
  t_axi_last        last;
  t_sc_wuser        user;
} t_sc_wvector;

typedef struct packed {
  t_sc_rdata        data;
  t_axi_last        last;
  t_axi_resp        resp;
  t_sc_id           id;
  t_sc_ruser        user;
} t_sc_rvector;


typedef struct packed {
  t_axi_resp        resp;
  t_sc_id           id;
  t_sc_buser        user;
} t_sc_bvector;
