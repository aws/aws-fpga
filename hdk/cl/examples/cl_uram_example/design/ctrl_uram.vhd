-- Amazon FPGA Hardware Development Kit
--
-- Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
--
-- Licensed under the Amazon Software License (the "License"). You may not use
-- this file except in compliance with the License. A copy of the License is
-- located at
--
--    http://aws.amazon.com/asl/
--
-- or in the "license" file accompanying this file. This file is distributed on
-- an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
-- implied. See the License for the specific language governing permissions and
-- limitations under the License.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity uram_ctrl is
  generic ( 
    nb_bit_address : integer := 20
  );
  port ( 
    clk     : in std_logic;
    rst     : in std_logic;
    find    : in std_logic;
    add     : in std_logic;
    del     : in std_logic;
    data_in : in std_logic_vector(31 downto 0);
    find_ok : out std_logic;
    find_ko : out std_logic;
    busy    : out std_logic
  );
 end entity;

architecture rtl of uram_ctrl is

  -- States for the state machine
  type state_type is (state_idle,state_add,state_find,state_del,state_wait_find,state_wait_add);
  signal current_state : state_type;
  
  signal we_uram_a : std_logic := '0';
  signal clk_div2 : std_logic := '0';
  signal clk_div4 : std_logic := '0';
  signal clk_div8 : std_logic := '0';
  
  signal cpt_nb_data_uram : std_logic_vector(nb_bit_address-1 downto 0) := (others=>'0');
  signal addr_uram_a      : std_logic_vector(nb_bit_address-1 downto 0) := (others=>'0');
  signal addr_uram_b      : std_logic_vector(nb_bit_address-1 downto 0) := (others=>'0');
  signal data_to_uram_a   : std_logic_vector(31 downto 0) := (others=>'0');
  signal data_from_uram_0_b : std_logic_vector(31 downto 0) := (others=>'0');
  signal previous_data    : std_logic_vector(31 downto 0) := (others=>'0');
  constant zeros : std_logic_vector(cpt_nb_data_uram'range) := (others => '0');
  
  signal data_from_uram_1_b : std_logic_vector(31 downto 0) := (others=>'0');
  
  signal data_in_control_less : std_logic_vector(31 downto 0);

  component bd_uram
    port (
      URAM_PORTA_clk  : in std_logic;
      URAM_PORTA_we   : in std_logic_vector(0 downto 0);
      URAM_PORTA_en   : in std_logic;
      URAM_PORTA_addr : in std_logic_vector(nb_bit_address-1 downto 0);
      URAM_PORTA_din  : in std_logic_vector(31 downto 0);
      URAM_PORTB_clk  : in std_logic;
      URAM_PORTB_en   : in std_logic;
      URAM_PORTB_addr : in std_logic_vector(nb_bit_address-1 downto 0);
      URAM_PORTB_dout : out std_logic_vector(31 downto 0);
      URAM_PORTA_1_clk  : in std_logic;
      URAM_PORTA_1_we   : in std_logic_vector(0 downto 0);
      URAM_PORTA_1_en   : in std_logic;
      URAM_PORTA_1_addr : in std_logic_vector(nb_bit_address-1 downto 0);
      URAM_PORTA_1_din  : in std_logic_vector(31 downto 0);
      URAM_PORTB_1_clk  : in std_logic;
      URAM_PORTB_1_en   : in std_logic;
      URAM_PORTB_1_addr : in std_logic_vector(nb_bit_address-1 downto 0);
      URAM_PORTB_1_dout : out std_logic_vector(31 downto 0)
    );
  end component bd_uram;

begin

bd_uram_inst: bd_uram
    port map(
      URAM_PORTA_clk   => clk_div8,
      URAM_PORTA_we(0) => we_uram_a,
      URAM_PORTA_en    => '1',
      URAM_PORTA_addr  => addr_uram_a,
      URAM_PORTA_din   => data_to_uram_a,
      URAM_PORTB_clk   => clk_div8,
      URAM_PORTB_en    => '1',
      URAM_PORTB_addr  => addr_uram_b,
      URAM_PORTB_dout  => data_from_uram_0_b,
      URAM_PORTA_1_clk   => clk_div8,
      URAM_PORTA_1_we(0) => we_uram_a,
      URAM_PORTA_1_en    => '1',
      URAM_PORTA_1_addr  => addr_uram_a,
      URAM_PORTA_1_din   => data_to_uram_a,
      URAM_PORTB_1_clk   => clk_div8,
      URAM_PORTB_1_en    => '1',
      URAM_PORTB_1_addr  => addr_uram_b,
      URAM_PORTB_1_dout  => data_from_uram_1_b
    );

  data_in_control_less(28 downto 0) <= data_in(28 downto 0);
  data_in_control_less(31 downto 29) <= "000";
  
  p_clk_div2: process(clk)
  begin
    if(rising_edge(clk)) then
      clk_div2   <= not clk_div2;
    end if;
  end process;
  
  p_clk_div4: process(clk_div2)
  begin
    if(rising_edge(clk_div2)) then
      clk_div4   <= not clk_div4;
    end if;
  end process;
  
  p_clk_div8: process(clk_div4)
  begin
    if(rising_edge(clk_div4)) then
      clk_div8   <= not clk_div8;
    end if;
  end process;
  
  process_ctrl_uram:process(clk_div8)
  begin
    if clk_div8'event and clk_div8 = '1' then
      -- Reset detected, set state_idle and put 0 for the number of data in the uram
      if rst = '0' then
        current_state <= state_idle;
        cpt_nb_data_uram <= (others=>'0');
        find_ok <= '0';
        find_ko <= '0';
        busy <= '0';
        
      -- Reset not detected
      else
        -- By default
        we_uram_a <= '0';
        
        state_machine_uram:case current_state is
          
          -- State_wait_find
          when state_wait_find =>
            -- The read needs one more rising edge of the clk to give back the 1st value 
            -- and therefore compare the 1st value with data_in_control_less in state_find
            current_state <= state_find;
            addr_uram_b   <= std_logic_vector(unsigned(addr_uram_b) + 1);
          
          -- State_wait_add
          when state_wait_add =>
            busy <= '0';
            if (previous_data /= data_in_control_less) or (add = '0') then
              -- We wait a new data to avoid doing continuous add
              current_state <= state_idle;
            end if;
          
          -- State_idle
          when state_idle =>
            busy    <= '0';
            if (find = '1') and (previous_data /= data_in) then
              find_ok <= '0';
              find_ko <= '0';
              busy    <= '1';
              -- Find detected -> New state is state_find
              current_state <= state_wait_find;
              -- Put the read address at the beginning
              addr_uram_b <= (others=>'0');
           elsif add = '1' then
              find_ok <= '0';
              find_ko <= '0';
              busy    <= '1';
              -- Add detected, put the data, the address and the we on the inputs of the uram
              addr_uram_a    <= cpt_nb_data_uram;
              data_to_uram_a <= data_in_control_less;
              previous_data  <= data_in_control_less; -- Store data_in_control_less to compare it later on
              we_uram_a      <= '1';
              -- Increment the number of data inside the uram
              cpt_nb_data_uram <= std_logic_vector(unsigned(cpt_nb_data_uram) + 1);
              current_state    <= state_wait_add;
            end if;
 
          -- State_find
          when state_find =>
            -- uram empty, go back to state_idle
            previous_data  <= data_in;
            if cpt_nb_data_uram = zeros then
              current_state <= state_idle;
              find_ko <= '1';
            -- uram not empty
            -- The data has been found and is located at the address addr_uram_b - 1 (because 2 rising edge in advance)
            elsif (data_from_uram_0_b and data_from_uram_1_b) = data_in_control_less then
              find_ok <= '1'; -- Return find_ok
              
              -- Del detected
              -- Read the data at the following address.
              -- If we have to pull the data up inside the uram, 
              -- we must put the read address on the following data 
              -- not to lose one rising edge of the clk
              if del = '1' then
                -- Decrement the number of data inside the uram
                cpt_nb_data_uram <= std_logic_vector(unsigned(cpt_nb_data_uram) - 1);
                -- If this data is the last one, come back to state_idle
                if cpt_nb_data_uram = addr_uram_b then -- Here, note there is no "addr_uram_b - 1" because cpt_nb_data_uram starts at 1
                  current_state <= state_idle;
                -- Else, this data is not the last one, so read the data at the next address and start the pull up
                else
                  addr_uram_b <= std_logic_vector(unsigned(addr_uram_b) + 1);
                  current_state <= state_del;
                end if;
              -- Del not detected, back to state_idle
              else
                current_state <= state_idle;
              end if;
            -- The data has not been found, 
            -- If some elements remain inside the uram, then increment read address with 1
            -- until reach the end of the data. Else, back to state_idle
            else
              if cpt_nb_data_uram /= addr_uram_b then
                addr_uram_b <= std_logic_vector(unsigned(addr_uram_b) + 1);
              else
                find_ko <= '1';
                current_state <= state_idle;
              end if;
            end if;

          -- State_del
          when state_del =>
            -- The data to delete is located at the address addr_uram_b - 2
            -- The next data has been read and is located at data_from_uram_b
            -- Some elements remain inside the uram
            data_to_uram_a <= (data_from_uram_0_b and data_from_uram_1_b); -- Write the next data in place of the one to delete
            we_uram_a      <= '1';
            addr_uram_a    <= std_logic_vector(unsigned(addr_uram_b) - 2); -- update the read address to the next address
            addr_uram_b    <= std_logic_vector(unsigned(addr_uram_b) + 1); -- Increment the address to point onto the next data to read
            -- No element remains inside the uram
            if std_logic_vector(unsigned(cpt_nb_data_uram) + 1) = addr_uram_b then
              current_state <= state_idle;
            end if;
            
          when others =>
            current_state <= state_idle;
            
        end case;
      end if;
    end if;
  end process;
end rtl;
