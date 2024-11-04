/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

`ifndef ROUTER_ENV__SV
`define ROUTER_ENV__SV

`include "./router_agent.sv"
`include "./reset_sequence.sv"
`include "./ms_scoreboard.sv"
`include "./oMonitor.sv"

// Lab 7 - Task 3, Step 2
// Include the host_agent.sv file.
//
// ToDo
`include "./host_agent.sv"

class router_env extends uvm_env;
  router_agent agent[16];
  scoreboard sb;
  oMonitor omon[16];

  typedef uvm_sequencer#() reset_sequencer;
  reset_sequencer r_seqr;

  // Lab 7 - Task 3, Step 3
  // Create an instance of host_agent.  Call it h_agent.
  //
  // ToDo
  host_agent h_agent;

  // Lab 7 - Task 10, Step 2
  // Create an instance of ral_block_host_regmodel call it regmodel.
  //
  // ToDo
  ral_block_host_regmodel regmodel;

  int addr_map_base = 0;  // user configurable
  `uvm_component_utils_begin(router_env)
    `uvm_field_int(addr_map_base, UVM_DEFAULT)
  `uvm_component_utils_end


  function new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    foreach (agent[i]) begin
      agent[i] = router_agent::type_id::create($sformatf("agent[%0d]", i), this);
      uvm_config_db #(int)::set(agent[i], "*", "port_id", i);
      uvm_config_db #(bit[15:0])::set(agent[i], "seqr.*", "sa_enable", 1'b1<<i);
      uvm_config_db #(uvm_object_wrapper)::set(agent[i], "seqr.main_phase", "default_sequence", packet_seq_lib::get_type());
    end

    // Lab 7 - Task 3, Step 4 & 5
    // Construct the host agent object with the factory create() method.
    // Configure the host agent to execute host_bfm_sequence at the configure_phase.
    //
    // ToDo
    h_agent = host_agent::type_id::create("h_agent", this);
    uvm_config_db #(uvm_object_wrapper)::set(h_agent, "seqr.configure_phase", "default_sequence", host_bfm_sequence::get_type());

    sb = scoreboard::type_id::create("sb", this);
    foreach (omon[i]) begin
      omon[i] = oMonitor::type_id::create($sformatf("omon[%0d]",i),this);
      uvm_config_db#(int)::set(omon[i], "", "port_id", i);
    end

    r_seqr = reset_sequencer::type_id::create("r_seqr", this);
    uvm_config_db #(uvm_object_wrapper)::set(this, "r_seqr.reset_phase", "default_sequence", reset_sequence::get_type());


    // Lab 7 - Task 10, Step 3
    // Check to see if regmodel is null.  If yes do the following:
    //
    // 1. Add a string field call it hdl_path.
    //
    // 2. Retrieve the hdl_path string with uvm_config_db.
    //
    // 3. Contruct the regmodel object
    //
    // 4. Call the regmodel's build() method to build the RAL representation.
    //
    // 5. Set the hdl root path by calling the regmodel's set_hdl_path_root() method.
    //
    //
    // if (regmodel == null) begin
    //   string hdl_path;
    //   if (!uvm_config_db #(string)::get(this, "", "hdl_path", hdl_path)) begin
    //     `uvm_warning("HOSTCFG", "HDL path for backdoor not set!");
    //   end
    //   regmodel = ral_block_host_regmodel::type_id::create("regmodel", this);
    //   regmodel.build();
    //   regmodel.set_hdl_path_root(hdl_path);
    // end
    //
    // ToDo
    if (regmodel == null) begin
      string hdl_path;
      if (!uvm_config_db #(string)::get(this, "", "hdl_path", hdl_path)) begin
        `uvm_warning("HOSTCFG", "HDL path for backdoor not set!");
      end
/*
      if (!uvm_config_db #(int)::get(this, "", "addr_map_base", addr_map_base)) 
      begin
        `uvm_warning("HOSTCFG", "Address Map Base Address Defaulting to 0");
      end
*/

      regmodel = ral_block_host_regmodel::type_id::create("regmodel", this);
      // regmodel.build(addr_map_base);
      regmodel.build();
      regmodel.set_hdl_path_root(hdl_path);
      regmodel.lock_model();
    end

  endfunction

  virtual function void connect_phase(uvm_phase phase);

    // Lab 7 - Task 10, Step 4
    // Create and construct an instance of reg2host_adapter call it reg2host.
    //
    // reg2host_adapter reg2host = reg2host_adapter::type_id::create("reg2host", this);
    //
    // ToDo
    reg2host_adapter reg2host = reg2host_adapter::type_id::create("reg2host", this);
    reg2host.provides_responses = 1;


    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    foreach (agent[i]) begin
      agent[i].mon.analysis_port.connect(sb.before_export);
    end
    foreach (omon[i]) begin
      omon[i].analysis_port.connect(sb.after_export);
    end

    // Lab 7 - Task 10, Step 5
    // Tie the regmodel to a sequencer by calling the set_sequencer() method in regmodels default_map member.
    // In the argument of set_sequencer() method, pass in h_agent.seqr and reg2host.
    //
    // regmodel.default_map.set_sequencer(h_agent.seqr, reg2host);
    //
    // ToDo
    regmodel.default_map.set_sequencer(h_agent.seqr, reg2host);

  endfunction
endclass

`endif
