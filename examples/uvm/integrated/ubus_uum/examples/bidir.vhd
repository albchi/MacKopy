LIBRARY ieee;
USE ieee.std_logic_1164.ALL;

ENTITY bidir IS
    PORT(
        bidir1   : INOUT STD_LOGIC_VECTOR (7 DOWNTO 0);
        oe, clk : IN STD_LOGIC;
        inp     : IN STD_LOGIC_VECTOR (7 DOWNTO 0);
        outp    : OUT STD_LOGIC_VECTOR (7 DOWNTO 0));
END bidir;

ARCHITECTURE maxpld OF bidir IS
SIGNAL  a  : STD_LOGIC_VECTOR (7 DOWNTO 0);  -- DFF that stores 
                                             -- value from input.
SIGNAL  b  : STD_LOGIC_VECTOR (7 DOWNTO 0);  -- DFF that stores 
BEGIN                                        -- feedback value.
    PROCESS(clk)
    BEGIN
    IF clk = '1' AND clk'EVENT THEN  -- Creates the flipflops
        a <= inp;                    
        outp <= b;                  
        END IF;
    END PROCESS;    
    PROCESS (oe, bidir1)          -- Behavioral representation 
        BEGIN                    -- of tri-states.
        IF( oe = '0') THEN
            bidir1 <= "ZZZZZZZZ";
            b <= bidir1;
        ELSE
            bidir1 <= a; 
            b <= bidir1;
        END IF;
    END PROCESS;
END maxpld;

