`ifndef RAL_SYS
`define RAL_SYS

import uvm_pkg::*;

class ral_reg_comp1_regA extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp1_regA");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp1_regA)

endclass : ral_reg_comp1_regA


class ral_reg_comp1_regB extends uvm_reg;
	rand uvm_reg_field fldA;
	rand uvm_reg_field fldB;
	rand uvm_reg_field fldC;

	function new(string name = "comp1_regB");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.fldA = uvm_reg_field::type_id::create("fldA",,get_full_name());
      this.fldA.configure(this, 8, 0, "RW", 0, 8'h0, 0, 0, 1);
      this.fldB = uvm_reg_field::type_id::create("fldB",,get_full_name());
      this.fldB.configure(this, 8, 8, "RW", 0, 8'h0, 0, 0, 1);
      this.fldC = uvm_reg_field::type_id::create("fldC",,get_full_name());
      this.fldC.configure(this, 16, 16, "RW", 0, 16'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp1_regB)

endclass : ral_reg_comp1_regB


class ral_reg_comp1_regC extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp1_regC");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp1_regC)

endclass : ral_reg_comp1_regC


class ral_block_comp1 extends uvm_reg_block;
	rand ral_reg_comp1_regA regA;
	rand ral_reg_comp1_regB regB;
	rand ral_reg_comp1_regC regC;
	rand uvm_reg_field regA_data;
	rand uvm_reg_field regB_fldA;
	rand uvm_reg_field fldA;
	rand uvm_reg_field regB_fldB;
	rand uvm_reg_field fldB;
	rand uvm_reg_field regB_fldC;
	rand uvm_reg_field fldC;
	rand uvm_reg_field regC_data;

	function new(string name = "comp1");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.regA = ral_reg_comp1_regA::type_id::create("regA",,get_full_name());
      this.regA.configure(this, null, "");
      this.regA.build();
      this.default_map.add_reg(this.regA, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.regA_data = this.regA.data;
      this.regB = ral_reg_comp1_regB::type_id::create("regB",,get_full_name());
      this.regB.configure(this, null, "");
      this.regB.build();
      this.default_map.add_reg(this.regB, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.regB_fldA = this.regB.fldA;
		this.fldA = this.regB.fldA;
		this.regB_fldB = this.regB.fldB;
		this.fldB = this.regB.fldB;
		this.regB_fldC = this.regB.fldC;
		this.fldC = this.regB.fldC;
      this.regC = ral_reg_comp1_regC::type_id::create("regC",,get_full_name());
      this.regC.configure(this, null, "");
      this.regC.build();
      this.default_map.add_reg(this.regC, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.regC_data = this.regC.data;
   endfunction : build

	`uvm_object_utils(ral_block_comp1)

endclass : ral_block_comp1


class ral_reg_comp2_regA extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp2_regA");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp2_regA)

endclass : ral_reg_comp2_regA


class ral_reg_comp2_rf1_r0 extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp2_rf1_r0");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp2_rf1_r0)

endclass : ral_reg_comp2_rf1_r0


class ral_reg_comp2_rf1_r1 extends uvm_reg;
	rand uvm_reg_field fA;
	rand uvm_reg_field fB;

	function new(string name = "comp2_rf1_r1");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.fA = uvm_reg_field::type_id::create("fA",,get_full_name());
      this.fA.configure(this, 16, 0, "RW", 0, 16'h0, 0, 0, 1);
      this.fB = uvm_reg_field::type_id::create("fB",,get_full_name());
      this.fB.configure(this, 16, 16, "RW", 0, 16'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp2_rf1_r1)

endclass : ral_reg_comp2_rf1_r1


class ral_reg_comp2_rf1_r2 extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp2_rf1_r2");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp2_rf1_r2)

endclass : ral_reg_comp2_rf1_r2


class ral_regfile_comp2_rf1 extends uvm_reg_file;
	rand ral_reg_comp2_rf1_r0 r0;
	rand ral_reg_comp2_rf1_r1 r1;
	rand ral_reg_comp2_rf1_r2 r2;
	rand uvm_reg_field r0_data;
	rand uvm_reg_field r1_fA;
	rand uvm_reg_field fA;
	rand uvm_reg_field r1_fB;
	rand uvm_reg_field fB;
	rand uvm_reg_field r2_data;


	function new(string name = "comp2_rf1");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.r0 = ral_reg_comp2_rf1_r0::type_id::create("r0",,get_full_name());
		this.r0.configure(get_block(), this, "");
		this.r0.build();
		this.r0_data = this.r0.data;
		this.r1 = ral_reg_comp2_rf1_r1::type_id::create("r1",,get_full_name());
		this.r1.configure(get_block(), this, "");
		this.r1.build();
		this.r1_fA = this.r1.fA;
		this.fA = this.r1.fA;
		this.r1_fB = this.r1.fB;
		this.fB = this.r1.fB;
		this.r2 = ral_reg_comp2_rf1_r2::type_id::create("r2",,get_full_name());
		this.r2.configure(get_block(), this, "");
		this.r2.build();
		this.r2_data = this.r2.data;
	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(r0, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(r1, offset+`UVM_REG_ADDR_WIDTH'h4);
	  mp.add_reg(r2, offset+`UVM_REG_ADDR_WIDTH'h8);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  r0.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  r1.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);
	  r2.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h8);

	endfunction

	`uvm_object_utils(ral_regfile_comp2_rf1)
endclass : ral_regfile_comp2_rf1




class ral_reg_comp2_regE extends uvm_reg;
	rand uvm_reg_field data;

	function new(string name = "comp2_regE");
		super.new(name, 32,build_coverage(UVM_NO_COVERAGE));
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 32, 0, "RW", 0, 32'h0, 0, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_comp2_regE)

endclass : ral_reg_comp2_regE


class ral_block_comp2 extends uvm_reg_block;
	rand ral_reg_comp2_regA regA;
	rand ral_regfile_comp2_rf1 rf1[4];
	rand ral_reg_comp2_regE regE;
	rand uvm_reg_field regA_data;
	rand uvm_reg_field regE_data;

	function new(string name = "comp2");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.regA = ral_reg_comp2_regA::type_id::create("regA",,get_full_name());
      this.regA.configure(this, null, "");
      this.regA.build();
      this.default_map.add_reg(this.regA, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.regA_data = this.regA.data;
      foreach (this.rf1[i]) begin
         int J = i;
         this.rf1[J] = ral_regfile_comp2_rf1::type_id::create($psprintf("rf1[%0d]",J),,get_full_name());
        this.rf1[J].configure(this, null, "");
        this.rf1[J].build();
      this.rf1[J].map(default_map, `UVM_REG_ADDR_WIDTH'h100+`UVM_REG_ADDR_WIDTH'h10 * J);
      end
      this.regE = ral_reg_comp2_regE::type_id::create("regE",,get_full_name());
      this.regE.configure(this, null, "");
      this.regE.build();
      this.default_map.add_reg(this.regE, `UVM_REG_ADDR_WIDTH'h1F0, "RW", 0);
		this.regE_data = this.regE.data;
   endfunction : build

	`uvm_object_utils(ral_block_comp2)

endclass : ral_block_comp2


class ral_sys_sys extends uvm_reg_block;

   rand ral_block_comp1 Comp1a;
   rand ral_block_comp1 Comp1b;
   rand ral_block_comp2 Comp2;

	function new(string name = "sys");
		super.new(name);
	endfunction: new

	function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.Comp1a = ral_block_comp1::type_id::create("Comp1a",,get_full_name());
      this.Comp1a.configure(this, "");
      this.Comp1a.build();
      this.default_map.add_submap(this.Comp1a.default_map, `UVM_REG_ADDR_WIDTH'h1A0000);
      this.Comp1b = ral_block_comp1::type_id::create("Comp1b",,get_full_name());
      this.Comp1b.configure(this, "");
      this.Comp1b.build();
      this.default_map.add_submap(this.Comp1b.default_map, `UVM_REG_ADDR_WIDTH'h1B0000);
      this.Comp2 = ral_block_comp2::type_id::create("Comp2",,get_full_name());
      this.Comp2.configure(this, "");
      this.Comp2.build();
      this.default_map.add_submap(this.Comp2.default_map, `UVM_REG_ADDR_WIDTH'h200000);
	endfunction : build

	`uvm_object_utils(ral_sys_sys)
endclass : ral_sys_sys



`endif
