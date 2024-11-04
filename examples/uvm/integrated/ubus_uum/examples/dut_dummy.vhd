library ieee;
use ieee.std_logic_1164.all;


entity dut_dummy is
port(	
    ubus_req_master_0 : in std_logic    ;
    ubus_gnt_master_0: out std_logic     ;
    ubus_req_master_1: in std_logic     ;
    ubus_gnt_master_1: out std_logic     ;
    ubus_clock: in std_logic            ;
    ubus_reset: in std_logic            ;
    ubus_addr: in  std_logic_vector (15 downto 0)      ;
    ubus_size: in std_logic_vector (1 downto 0)       ;
    ubus_read: out std_logic             ;
    ubus_write: out std_logic            ;
    ubus_start: out std_logic            ;
    ubus_bip: in std_logic              ;
    ubus_data: inout std_logic_vector (7 downto 0)       ;
    ubus_wait: in std_logic             ;
    ubus_error: in std_logic           

);

end dut_dummy;  

----------------------------------------

architecture behv1 of dut_dummy is

  signal st : std_logic_vector (2 downto 0);
  signal s_ubus_gnt_master_0 : std_logic;
  signal s_ubus_gnt_master_1 : std_logic;
  
begin
  ubus_gnt_master_0 <= s_ubus_gnt_master_0;
  ubus_gnt_master_1 <= s_ubus_gnt_master_1;
  
    process( ubus_clock ,  ubus_reset)
    begin

        if (ubus_reset='1') then
            st <= "000";
        else
        if (ubus_clock'event and ubus_clock ='1') then
          case st is
             when "000" =>
               ubus_start <= '1';
               st <= "011"              ;
             when "011" =>
               ubus_start <= '0';
               if (s_ubus_gnt_master_0='0' and s_ubus_gnt_master_1='0') then
                    st<="100";
                    else
                     st <= "001";
                  end if;   

             when "100" =>
               ubus_start <= '1';
               st <= "011";

             when "001" =>
               st <= "010";
               ubus_start <= '0';
             when "010" =>
                if (ubus_error='1' or ((ubus_bip='0' and ubus_wait='0'))) then
                       st<="011";
                       ubus_start <= '1';
                else
                st <= "010";
                ubus_start <= '0';
                     
                end if;     
             when others => null;
           end case;
        end if;
        end if;

    end process;

  
end behv1;


------------------------------------------

