// (c) Copyright 1995-2021, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////

#include <systemc>
#include <map>
#include <vector>

typedef std::vector<uint8_t> pg4KB;
typedef std::map<uint32_t, pg4KB*> Memory;

typedef enum{RNOP=0, ACT, PRE, PREA, REFSB, REF, PDE, SRE, SRX} rowCommands;
typedef enum{CNOP=0, RD, RDA, WR, WRA, MRS} columnCommands;

class cmd{
  public:
    cmd(uint32_t bgA, uint32_t bA):bg(bgA), bnk(bA){}
    uint32_t bg;
    uint32_t bnk;
};
class cmdRow: public cmd{
  public:
    cmdRow(uint32_t bgA, uint32_t bA, uint32_t RA, rowCommands C): cmd(bgA,bA),
      row(RA), rCmd(C){}
  uint32_t row;
  rowCommands rCmd;
  std::string print(){
    std::stringstream ss;
    ss << " For BankGrp[" <<std::hex<< bg << "], bank[" << bnk << "], page[" << row << "]" <<std::dec<< endl;
    return ss.str();
  }
};
class cmdCol: public cmd{
  public:
    cmdCol(uint32_t bgA, uint32_t bA, uint32_t CA, columnCommands C): cmd(bgA,bA),
      col(CA), cCmd(C){}
  uint32_t col;
  columnCommands cCmd;
};

typedef enum{IDLE=0, REFRESH} dramState;
typedef enum{H4=0, H8} stackHeight;
//SC_MODULE(dram){
class dram: public sc_core::sc_module{
  SC_HAS_PROCESS(dram);
  dram(sc_module_name nm, sc_time ck):sc_module(nm)
                          ,state(IDLE)
                          ,tRefi(3.9,SC_US)
                          //,tRfc(( (sh==H4)? sc_time(260,SC_NS):sc_time(350,SC_NS) ))
                          ,tRfc(sc_time(260,SC_NS))
                          ,bankXprvActivateTime(16, SC_ZERO_TIME)
                          ,rowCmdPipe(16)
                          ,colCmdPipe(16)
                          ,tCk(ck)
                          ,tActivate(2*tCk)
  {
    SC_THREAD(threadRefreshKeeper);
    SC_THREAD(threadRowCmdHandler);
  }
  ~dram(){
    for(auto &pg: mem){
      delete pg.second;
    }
  }
  friend class hbmChannel;

  private:
  Memory mem;
  sc_time tRefi;
  sc_time tRfc;
  dramState state;
  sc_event dramIdle;
  std::vector<sc_core::sc_time> bankXprvActivateTime;
  tlm::tlm_fifo<std::shared_ptr<cmdRow> > rowCmdPipe;
  tlm::tlm_fifo<std::shared_ptr<cmdCol> > colCmdPipe;


  //time periods
  sc_time tCk;
  sc_time tActivate;

 public:
  void threadRefreshKeeper(){
    while(1){
      wait(9*tRefi);
      state = REFRESH;
      wait(tRfc);                                                             //Refresh command period, Tk b/w REF and VALID
      state = IDLE;
      dramIdle.notify();
    }
  }

  void threadRowCmdHandler(){
    while (true) {
      try {
        std::shared_ptr<cmdRow> command = rowCmdPipe.peek();
        processRowCommand(command);
        rowCmdPipe.get();
        //if ( queue.used() == 0 ) {
        //  qEv.notify( sc_core::SC_ZERO_TIME );
        //}
      } catch ( sc_core::sc_unwind_exception& ex ) { // reset or kill
        if ( ex.is_reset() ) {
          // should re-start this thread
        } else {
          // killed - ends here
        }
        throw;
      }
    }
  }

  void processRowCommand(std::shared_ptr<cmdRow> c) {
    switch (c->rCmd) {
      case RNOP:
        break;
      case ACT:
        cout <<sc_time_stamp()<< "Activating " << c->print();
        wait(tActivate);
        {
          //sc_core::sc_spawn_options opts;
          //sc_core::sc_spawn([this] { sc_core::wait(this->tActivate); }, "activateTh", &opts);
        }
        break;
      default:
        break;
    }
  }

  void write(uint32_t bankPage, uint32_t row, uint8_t* data, uint32_t dataLen){
    pg4KB *pg = mem[bankPage];
    if(pg == nullptr){
      pg = new pg4KB(dataLen);
    }
    memcpy(&pg[0]+row, data, dataLen);
  }

  void read(uint32_t, uint32_t, uint32_t, uint8_t*);


};
