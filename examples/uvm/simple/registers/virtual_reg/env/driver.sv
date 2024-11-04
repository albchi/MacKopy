/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/


`ifndef DRIVER__SV
`define DRIVER__SV

class driver extends uvm_driver #(packet);
  // Lab 4 - Task 2, Step 2 and 3
  // Create the new fields as shown below.
  //
  // ToDo
  virtual router_io sigs;          // DUT virtual interface
  int               port_id = -1;  // Driver's designated port



  // virtual router_io sigs;          // DUT virtual interface
  // int               port_id = -1;  // Driver's designated port
  //
  // The intent of the port_id field is to designate the driver for driving a specific port.
  //
  // If port_id is set in the range of 0 through 15, the driver will only drive
  // the packet it gets from the sequencer through the DUT if the port_id matches the
  // packet's source address (sa) field.  If not, the packet is dropped.
  //
  // If port_id is -1 (the default), the driver will drive all packets it gets from
  // the sequencer through the DUT without checking the packet's source address.
  //
  // Example:  If port_id is 3 and req.sa is also 3,
  // (req is the packet handle that sequencer passed to the driver)
  // The driver will drive the packet through port 3 of DUT: sigs.drvClk.din[req.sa];
  //
  // Example:  If port_id is 3 and req.sa is 7,
  // The driver will drop the packet.
  //
  // Example:  If port_id is -1 and req.sa is 7,
  // The driver will drive the packet through port 7 of DUT: sigs.drvClk.din[req.sa];


  // Lab 4 - Task 2, Step 4
  //
  // Embed the port_id field in the `uvm_component_utils macro.
  // Note: You will need to change the macro to `uvm_component_utils_begin
  //       with a corresponding `uvm_component_utils_end
  //
  // ToDo
  `uvm_component_utils_begin(driver)
    `uvm_field_int(port_id, UVM_DEFAULT | UVM_DEC)
  `uvm_component_utils_end


  function new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction


  function void build_phase(uvm_phase phase);

    // The super.build_phase() call will manage the updating of the fields listed
    // in the uvm_component_utils macro.  Thus, port_id will be automatically 
    // configured without you needing to call get() method to retrieve the value.
    super.build_phase(phase);

    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    // Lab 4 - Task 2, Step 5
    //
    // The DUT virtual interface cannot be listed in the uvm_component_utils macro
    // Therefore you must call the uvm_config_db#(virtual router_io)::get() method
    // to retrieve the handle.
    //
    // Retrieve the DUT virtual interface and store it in the sigs handle.
    // if the virtual interface is not set, terminate simultion with fatal message.
    //
    // if (!uvm_config_db#(virtual router_io)::get(this, "", "router_io", sigs))
    // begin
    //   `uvm_fatal("CFGERR", "Interface for Driver not set");
    // end
    //
    // ToDo
    if (!uvm_config_db#(virtual router_io)::get(this, "", "router_io", sigs)) begin
      `uvm_fatal("CFGERR", "Interface for Driver not set");
    end


  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    forever begin
      seq_item_port.get_next_item(req);

      // Lab 4 - Task 2, Step 6
      //
      // Check port_id to see if the driver should accept or drop the packet.
      // If port_id is -1, or if port_id matches req object's sa field,
      // call send() method to drive the content of the req object through the DUT.
      // Otherwise, drop the req object without processing.  Like the following:
      //
      // if (port_id inside { -1, req.sa }) begin
      //   send(req);
      //   `uvm_info("DRV_RUN", {"\n", req.sprint()}, UVM_MEDIUM);
      // end
      //
      // ToDo
      if (port_id inside { -1, req.sa }) begin
        send(req);
        `uvm_info("DRV_RUN", {"\n", req.sprint()}, UVM_MEDIUM);
      end
      //$tblog(0, "DRIVER_SEQ_ITEM",req.sa, req.da);



      seq_item_port.item_done();
    end
  endtask

  //
  // In the interest of lab time, all device drivers have been done for you:
  //

  virtual task send(packet tr);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    send_address(tr);
    send_pad(tr);
    send_payload(tr);
  endtask: send

  virtual task send_address(packet tr);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    sigs.drvClk.frame_n[tr.sa] <= 1'b0;
    for(int i=0; i<4; i++) begin
      sigs.drvClk.din[tr.sa] <= tr.da[i];
      @(sigs.drvClk);
    end
  endtask: send_address

  virtual task send_pad(packet tr);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    sigs.drvClk.din[tr.sa] <= 1'b1;
    sigs.drvClk.valid_n[tr.sa] <= 1'b1;
    repeat(5) @(sigs.drvClk);
  endtask: send_pad

  virtual task send_payload(packet tr);
    logic [7:0] datum;
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    while(!sigs.drvClk.busy_n[tr.sa]) @(sigs.drvClk);
    foreach(tr.payload[index]) begin
      datum = tr.payload[index];
      for(int i=0; i<$size(tr.payload, 2); i++) begin
        sigs.drvClk.din[tr.sa] <= datum[i];
        sigs.drvClk.valid_n[tr.sa] <= 1'b0;
        sigs.drvClk.frame_n[tr.sa] <= ((tr.payload.size()-1) == index) && (i==7);
        @(sigs.drvClk);
      end
    end
    sigs.drvClk.valid_n[tr.sa] <= 1'b1;
  endtask: send_payload

endclass

`endif
