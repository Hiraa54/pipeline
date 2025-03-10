module pipelined_datapath(
    input logic clk, reset
);
    // Program counter
    logic [31:0] pc_fetch, pc_excute, pc_wr,pc_next;
     
    // ins memory
    logic [31:0] ins_fetch, ins_fetch_dff, ins_excute, ins_wr;

    // Register file
    logic [31:0] readdata1_reg, readdata2_reg, read_data1, read_data2, writedata, writedata_dm;
    logic [4:0] rs1, rs2, rd;
    logic [6:0] opcode;

    // ALU
    logic [31:0] alu_result_excute, alu_result_wr;
    logic [3:0] alu_control;

    // Data memory
    logic [31:0] read_data;

    // Branch condition
    logic [2:0] branch_type;

    // Control unit
    logic [1:0] wb_sel, wb_sel_w;
    logic reg_wr, rd_en, wr_en, br_taken, sel_A, sel_B;
    logic reg_wr_w, rd_en_w, wr_en_w, fwd_A, fwd_B, flush;
    // Immediate Generator
    logic [31:0] extended_imm;

    // Instantiate modules
    Pc pc_0 (
        clk, reset, pc_next, pc_fetch
    );
    Ins_mem inst_mem_0 (
        pc_fetch, ins_fetch_dff
    );
    Dff dff_00 (
        clk, reset, pc_fetch, pc_excute
    );
    Dff dff_01 (
        clk, reset, ins_fetch, ins_excute
    );
    Dff dff_10 (
        clk, reset, pc_excute, pc_wr
    );
    Dff dff_11 (
        clk, reset, alu_result_excute, alu_result_wr
    );
    Dff dff_12 (
        clk, reset, read_data2, writedata_dm
    );
    Dff dff_13 (
        clk, reset, ins_excute, ins_wr
    );
    assign ins_fetch = flush ? 32'h00000013 : ins_fetch_dff;

    reg_file reg_file_0 (
        clk, reset, reg_wr_w, rs1, rs2, ins_wr[11:7], writedata, readdata1_reg, readdata2_reg
    );
    assign read_data1 = fwd_A ? writedata : readdata1_reg;
    assign read_data2 = fwd_B ? writedata : readdata2_reg;
    ALU alu_0 (
        alu_control, sel_A ? read_data1 : pc_excute, sel_B ? extended_imm: read_data2, alu_result_excute
    );
    data_memory data_mem_0 (
        clk, wr_en_w, rd_en_w, alu_result_wr, writedata_dm, read_data
    );
    Branch_cond branch_cond_0 (
        branch_type, read_data1, read_data2, br_taken
    );
    Control_unit control_unit_0 (
        clk, reset, reg_wr, wr_en, rd_en, wb_sel,ins_excute,reg_wr_w, wr_en_w, rd_en_w, wb_sel_w, reg_wr, rd_en, wr_en, sel_A, sel_B, wb_sel, alu_control, branch_type
    );

    Forwarding_unit fwd_unit_0 (
        ins_excute, ins_wr, reg_wr_w, fwd_A, fwd_B
    );
    imd_generator imd_generator_0 (
        ins_excute,extended_imm
    );

    // Assignments
    assign opcode = ins_excute[6:0];
    assign rs1 = ins_excute[19:15];
    assign rs2 = ins_excute[24:20];
    assign rd = ins_wr[11:7];
    assign pc_next = br_taken ? alu_result_excute : pc_fetch + 4;
    assign flush = br_taken ? 1'b1 : 1'b0;

    always_comb begin
         case (wb_sel_w)
            2'b00: writedata = pc_wr + 4;
            2'b01: writedata = alu_result_wr;
            2'b10: writedata = read_data;
        endcase
    end

endmodule

module Pc(
	input logic clk, reset,
	input logic [31:0] pc_next,
	output logic [31:0] pc
);
	
	always_ff @(posedge clk) begin

		if (reset)
			pc <= 32'b0;
		else
			pc <= pc_next;
	end

endmodule

module Ins_mem(
	input logic [31:0] address,
	output logic [31:0] ins
);
	
	logic [31:0] memory [0:1023];

	assign ins = memory[address[11:2]];

endmodule

module Dff(
	input logic clk, reset, [31:0] in,
	output logic [31:0] out
);

always_ff @ (posedge clk)
begin
	if (reset)
		out <= 32'b0;
	else
		out <= in;
end
endmodule

module reg_file(
	input logic clk, reset, reg_write,
	input logic [4:0] rs1, rs2, rd, 
	input logic [31:0] writedata,
	output logic [31:0] read_data1, read_data2
);

	logic [31:0] registers [0:31];


	always_ff @(negedge clk) begin
		registers[0] <= 32'b0;
		if (reg_write)
			registers[rd] <= writedata;
	end

	assign read_data1 = registers[rs1];
	assign read_data2 = registers[rs2];

endmodule

module ALU(
	input logic [3:0] alu_op,
	input logic [31:0] A, B,
	output logic [31:0] C
);

	always_comb begin
        case (alu_op)
            4'b0000: C = A + B; // ADD
            4'b0001: C = A - B; // SUB
            4'b0010: C = A << B[4:0]; // SLL
            4'b0011: C = A >> B[4:0]; // SRL
            4'b0100: C = $signed(A) >>> B[4:0]; // SRA
            4'b0101: C = ($signed(A) < $signed(B)) ? 1 : 0; // SLT
            4'b0110: C = (A < B) ? 1 : 0; // SLTU
            4'b0111: C = A ^ B; // XOR
            4'b1000: C = A | B; // OR
            4'b1001: C = A & B; // AND
            4'b1010: C = B; // Just Pass B
        
            default: C = 32'b0;
        endcase
    end

endmodule

module data_memory (
    input logic clk_i, write_enable, read_enable,
    input logic [31:0] address, write_data,
    output logic [31:0] read_data
);
    
    logic [31:0] memory[0:1023];
    
    always_ff @(negedge clk_i) begin
        if (write_enable)
            memory[address] <= write_data;
    end

    assign read_data = (read_enable) ? memory[address] : 32'b0;

endmodule

module Branch_cond (
    input logic [2:0] branch_type,
    input logic [31:0] read_data1, read_data2,
    output logic br_taken
);

    always_comb begin
        case (branch_type)
            3'b000: br_taken = 0;
            3'b001: br_taken = (read_data1 == read_data2);  // BEQ
            3'b010: br_taken = (read_data1 != read_data2);  // BNE
            3'b011: br_taken = ($signed(read_data1) < $signed(read_data2));  // BLT
            3'b100: br_taken = ($signed(read_data1) >= $signed(read_data2)); // BGE
            3'b101: br_taken = (read_data1 < read_data2);   // BLTU
            3'b110: br_taken = (read_data1 >= read_data2);  // BGEU
            3'b111: br_taken = 1;                   // Unconditional Jump
            default: br_taken = 0;                  // Default case
        endcase
    end

endmodule

module Control_unit (
    input logic clk, reset,
    input logic reg_wr_in, wr_en_in, rd_en_in, // Pipeline register inputs
    input logic [1:0] wb_sel_in, // Pipeline register input
    input logic [31:0] inst,
    output logic reg_wr_out, wr_en_out, rd_en_out, // Pipeline register outputs
    output logic [1:0] wb_sel_out, // Pipeline register output
    output logic reg_wr, rd_en, wr_en, sel_A, sel_B,
    output logic [1:0] wb_sel,
    output logic [3:0] alu_op,
    output logic [2:0] branch_type
);

    logic [4:0] rs1, rs2, rd;
    logic [6:0] opcode, func7;
    logic [2:0] func3;

    assign opcode = inst[6:0];
    assign rd = inst[11:7];
    assign func3 = inst[14:12];
    assign rs1 = inst[19:15];
    assign rs2 = inst[24:20];
    assign func7 = inst[31:25];

    always_comb begin
 
        reg_wr = 0;
        rd_en = 0;
        wr_en = 0;
        sel_A = 0;
        sel_B = 0;
        wb_sel = 2'b00;
        branch_type = 3'b000;
        alu_op = 4'b0000;

        // R-Type
        if (opcode == 7'b0110011) begin
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 1;
            sel_B = 0;
            wb_sel = 2'b01;
            branch_type = 3'b000;
            if (func3 == 3'b000 && func7 == 7'b0000000) // ADD
                alu_op = 4'b0000;
            else if (func3 == 3'b000 && func7 == 7'b0100000) // SUB
                alu_op = 4'b0001;
            else if (func3 == 3'b001 && func7 == 7'b0000000) // SLL
                alu_op = 4'b0010;
            else if (func3 == 3'b101 && func7 == 7'b0000000) // SRL
                alu_op = 4'b0011;
            else if (func3 == 3'b101 && func7 == 7'b0100000) // SRA
                alu_op = 4'b0100;
            else if (func3 == 3'b010 && func7 == 7'b0000000) // SLT
                alu_op = 4'b0101;
            else if (func3 == 3'b011 && func7 == 7'b0000000) // SLTU
                alu_op = 4'b0110;
            else if (func3 == 3'b100 && func7 == 7'b0000000) // XOR
                alu_op = 4'b0111;            
            else if (func3 == 3'b110 && func7 == 7'b0000000) // OR
                alu_op = 4'b1000;
            else if (func3 == 3'b111 && func7 == 7'b0000000) // AND
                alu_op = 4'b1001;
        end

        // I-Type
        else if (opcode == 7'b0010011) begin
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 1;
            sel_B = 1;
            wb_sel = 2'b01;
            branch_type = 3'b000;
            if (func3 == 3'b000) // ADDI
                alu_op = 4'b0000;
            else if (func3 == 3'b001) // SLLI
                alu_op = 4'b0010;
            else if (func3 == 3'b101 && func7 == 7'b0000000) //SRLI
                alu_op = 4'b0011;
            else if (func3 == 3'b101 && func7 == 7'b0100000) //SRAI
                alu_op = 4'b0100;
            else if (func3 == 3'b010) // SLTI
                alu_op = 4'b0101;
            else if (func3 == 3'b011) // SLTIU
                alu_op = 4'b0110;
            else if (func3 == 3'b100) // XOR
                alu_op = 4'b0111;
            else if (func3 == 3'b110) // OR
                alu_op = 4'b1000;
            else if (func3 == 3'b111) // AND
                alu_op = 4'b1001;
        end

        // I-Type (Load)
        else if (opcode == 7'b0000011) begin
            reg_wr = 1;
            rd_en = 1;
            wr_en = 0;
            sel_A = 1;
            sel_B = 1;
            wb_sel = 2'b10;
            branch_type = 3'b000;
            alu_op = 4'b0000;
        end

        // S-Type   
        else if (opcode == 7'b0100011) begin
            reg_wr = 0;
            rd_en = 0;
            wr_en = 1;
            sel_A = 1;
            sel_B = 1;
            wb_sel = 2'b01;
            branch_type = 3'b000;
            alu_op = 4'b0000;
        end

        // B-Type   
        else if (opcode == 7'b1100011) begin
            reg_wr = 0;
            rd_en = 0;
            wr_en = 0;
            sel_A = 0;
            sel_B = 1;
            wb_sel = 2'b01;
            alu_op = 4'b0000;

            if (func3 == 3'b000) // BEQ
                branch_type = 3'b001;
            else if (func3 == 3'b001) // BNE
                branch_type = 3'b010;
            else if (func3 == 3'b100) // BLT
                branch_type = 3'b011;
            else if (func3 == 3'b101) // BGE
                branch_type = 3'b100;
            else if (func3 == 3'b110) // BLTU
                branch_type = 3'b101;
            else if (func3 == 3'b111) // BGEU
                branch_type = 3'b110;
        end

        // U-Type   
        else if (opcode == 7'b0110111) begin // LUI
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 0;
            sel_B = 1;
            wb_sel = 2'b01;
            branch_type = 3'b000;
            alu_op = 4'b1010;
        end
        else if (opcode == 7'b0010111) begin // AUIPC
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 0;
            sel_B = 1;
            wb_sel = 2'b01;
            branch_type = 3'b000;
            alu_op = 4'b0000;
        end

        // J-Type
        else if (opcode == 7'b1101111) begin // JAL
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 0;
            sel_B = 1;
            wb_sel = 2'b00;
            branch_type = 3'b111;
            alu_op = 4'b0000;
        end
        else if (opcode == 7'b1100111) begin // JALR
            reg_wr = 1;
            rd_en = 0;
            wr_en = 0;
            sel_A = 1;
            sel_B = 1;
            wb_sel = 2'b00;
            branch_type = 3'b111;
            alu_op = 4'b0000;
        end
    end

    always_ff @(posedge clk) begin
        if (reset) begin
            reg_wr_out <= 1'b0;
            wr_en_out <= 1'b0;
            rd_en_out <= 1'b0;
            wb_sel_out <= 2'b0;
        end else begin
            reg_wr_out <= reg_wr_in;
            wr_en_out <= wr_en_in;
            rd_en_out <= rd_en_in;
            wb_sel_out <= wb_sel_in;
        end
    end
endmodule

module Forwarding_unit(
    input logic [31:0] ins_excutexecute, ins_wrback,
    input logic reg_wr_wback,
    output logic fwd_A, fwd_B
);
    logic [4:0] rs1_execute, rs2_execute, rd_wback;
    logic [6:0] opcode_execute, opcode_wback;
    
    assign rs1_execute = ins_excutexecute[19:15];
    assign rs2_execute = ins_excutexecute[24:20];
    assign rd_wback = ins_wrback[11:7];
    assign opcode_execute = ins_excutexecute[6:0];
    assign opcode_wback = ins_wrback[6:0];
	always_comb begin
        if (reg_wr_wback && (opcode_wback != 7'b0100011) && (opcode_wback != 7'b1100011)) begin
            if (rs1_execute == rd_wback && (opcode_execute != 7'b0110111) && (opcode_execute != 7'b1101111))
                fwd_A = 1'b1;
            else
                fwd_A = 1'b0;
			if (rs2_execute == rd_wback && (opcode_execute != 7'b0110111) && (opcode_execute != 7'b1101111) && (opcode_execute != 7'b0010011) && (opcode_execute != 7'b0000011))
                fwd_B = 1'b1;
            else
                fwd_B = 1'b0;
        end else begin
            fwd_A = 1'b0;
            fwd_B = 1'b0;
        end
    end
endmodule
module imd_generator (
    input logic [31:0] instruction,
    output logic [31:0] extended_imm
);
    logic [6:0] opcode;
    assign opcode = instruction[6:0];

    always_comb begin

        if (opcode == 7'b0100011) // S-Type
            extended_imm = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
        else if (opcode == 7'b1100011) // B-Type
            extended_imm = {{19{instruction[31]}}, instruction[31], instruction[7], instruction[30:25], instruction[11:8], 1'b0};
        else if (opcode == 7'b0110111 || opcode == 7'b0010111) // U-Type 
            extended_imm = {instruction[31:12], 12'b0};
        else if (opcode == 7'b1101111) // J-Type
            extended_imm = {{11{instruction[31]}}, instruction[31], instruction[19:12], instruction[20], instruction[30:21], 1'b0};
        else
            extended_imm = {{20{instruction[31]}}, instruction[31:20]};

    end

endmodule