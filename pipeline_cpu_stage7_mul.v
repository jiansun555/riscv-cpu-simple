/*
 * ============================================================================
 * 文件名: pipeline_cpu_stage7_mul.v (Final, Syntax-Corrected Version 2)
 * ============================================================================
 */

// 顶层模块
module cpu_pipeline_stage7(input clk, input rst);
    datapath_pipeline dp ( .clk(clk), .rst(rst) );
endmodule

// 数据通路
module datapath_pipeline(input clk, input rst);
    wire pc_write, if_id_write, id_ex_write, if_id_flush;
    wire [31:0] pc_current, pc_next, pc_plus4, pc_branch_target, pc_jump_target;
    wire [31:0] if_instruction;
    wire [1:0]  pc_src;
    wire [31:0] id_pc, id_pc_plus4, id_instruction;
    wire        id_reg_write, id_mem_to_reg, id_mem_read, id_mem_write, id_alu_src, id_branch, id_jump, id_is_mul;
    wire [1:0]  id_alu_op, id_alu_src_a, id_wb_data_sel;
    wire [2:0]  id_mem_op;
    wire [31:0] id_imm_extended, id_reg_read_data1, id_reg_read_data2;
    wire        ex_reg_write, ex_mem_to_reg, ex_mem_read, ex_mem_write, ex_alu_src, ex_branch, ex_jump, ex_is_mul;
    wire [1:0]  ex_alu_op, ex_alu_src_a, ex_wb_data_sel;
    wire [2:0]  ex_mem_op;
    wire [31:0] ex_pc, ex_pc_plus4, ex_reg_read_data1, ex_reg_read_data2, ex_imm_extended;
    wire [4:0]  ex_rs1, ex_rs2, ex_rd;
    wire [2:0]  ex_funct3;
    wire [6:0]  ex_funct7;
    wire [1:0]  forward_a, forward_b;
    wire [31:0] forwarded_data_a, forwarded_data_b, alu_input_a, ex_alu_input_b, ex_alu_result, mul_product, ex_final_result, ex_pc_branch_target;
    wire [3:0]  ex_alu_op_final;
    wire        ex_alu_zero, mul_valid;
    wire        mem_reg_write, mem_mem_to_reg, mem_mem_read, mem_mem_write, mem_branch;
    wire [1:0]  mem_wb_data_sel;
    wire [2:0]  mem_mem_op;
    wire [31:0] mem_pc_plus4, mem_alu_result, mem_store_data;
    wire [4:0]  mem_rd;
    wire [31:0] mem_read_data_raw;
    wire        wb_reg_write, wb_mem_to_reg;
    wire [1:0]  wb_wb_data_sel;
    wire [2:0]  wb_mem_op;
    wire [31:0] wb_pc_plus4, wb_mem_read_data, wb_alu_result;
    wire [4:0]  wb_rd;
    wire [31:0] wb_write_data;

    // IF/ID 阶段
    assign if_id_flush = (pc_src != 2'b00); 
    pc pc_reg ( .clk(clk), .rst(rst), .en(pc_write), .PC_in(pc_next), .PC_out(pc_current) );
    assign pc_plus4 = pc_current + 4;
    assign pc_next = (pc_src == 2'b01) ? pc_branch_target : (pc_src == 2'b10) ? pc_jump_target : pc_plus4;
    instr_mem imem ( .addr(pc_current[7:2]), .instr(if_instruction) );
    if_id_reg if_id_inst ( .clk(clk), .rst(rst), .en(if_id_write), .flush(if_id_flush), .if_pc(pc_current), .if_pc_plus4(pc_plus4), .if_instruction(if_instruction), .id_pc(id_pc), .id_pc_plus4(id_pc_plus4), .id_instruction(id_instruction) );
    
    control_unit cu ( .opcode(id_instruction[6:0]), .funct3(id_instruction[14:12]), .funct7(id_instruction[31:25]), .RegWrite(id_reg_write), .ALUSrc(id_alu_src), .MemRead(id_mem_read), .MemWrite(id_mem_write), .MemtoReg(id_mem_to_reg), .Branch(id_branch), .ALUOp(id_alu_op), .ALUSrcA(id_alu_src_a), .Jump(id_jump), .WBDataSel(id_wb_data_sel), .MemOp(id_mem_op), .IsMul(id_is_mul) );
    hazard_detection_unit hdu ( .id_ex_mem_read(ex_mem_read), .id_ex_rd(ex_rd), .if_id_rs1(id_instruction[19:15]), .if_id_rs2(id_instruction[24:20]), .ex_is_mul(ex_is_mul), .mul_result_valid(mul_valid), .PCWrite(pc_write), .IF_ID_Write(if_id_write), .ID_EX_Write(id_ex_write) );
    reg_file rf ( .clk(clk), .RegWrite(wb_reg_write), .ReadAddr1(id_instruction[19:15]), .ReadAddr2(id_instruction[24:20]), .WriteAddr(wb_rd), .WriteData(wb_write_data), .ReadData1(id_reg_read_data1), .ReadData2(id_reg_read_data2) );
    imm_gen ig ( .instr(id_instruction), .imm_extended(id_imm_extended) );
    
    id_ex_reg id_ex_inst ( .clk(clk), .rst(rst), .en(id_ex_write), .id_reg_write(id_reg_write), .id_mem_to_reg(id_mem_to_reg), .id_mem_read(id_mem_read), .id_mem_write(id_mem_write), .id_alu_src(id_alu_src), .id_branch(id_branch), .id_jump(id_jump), .id_alu_op(id_alu_op), .id_alu_src_a(id_alu_src_a), .id_wb_data_sel(id_wb_data_sel), .id_mem_op(id_mem_op), .id_is_mul(id_is_mul), .id_pc(id_pc), .id_pc_plus4(id_pc_plus4), .id_reg_read_data1(id_reg_read_data1), .id_reg_read_data2(id_reg_read_data2), .id_imm_extended(id_imm_extended), .id_rs1(id_instruction[19:15]), .id_rs2(id_instruction[24:20]), .id_rd(id_instruction[11:7]), .id_funct3(id_instruction[14:12]), .id_funct7(id_instruction[31:25]), .ex_reg_write(ex_reg_write), .ex_mem_to_reg(ex_mem_to_reg), .ex_mem_read(ex_mem_read), .ex_mem_write(ex_mem_write), .ex_alu_src(ex_alu_src), .ex_branch(ex_branch), .ex_jump(ex_jump), .ex_alu_op(ex_alu_op), .ex_alu_src_a(ex_alu_src_a), .ex_wb_data_sel(ex_wb_data_sel), .ex_mem_op(ex_mem_op), .ex_is_mul(ex_is_mul), .ex_pc(ex_pc), .ex_pc_plus4(ex_pc_plus4), .ex_reg_read_data1(ex_reg_read_data1), .ex_reg_read_data2(ex_reg_read_data2), .ex_imm_extended(ex_imm_extended), .ex_rs1(ex_rs1), .ex_rs2(ex_rs2), .ex_rd(ex_rd), .ex_funct3(ex_funct3), .ex_funct7(ex_funct7) );

    // EX 阶段
    forwarding_unit fu ( .id_ex_rs1(ex_rs1), .id_ex_rs2(ex_rs2), .ex_mem_rd(mem_rd), .mem_wb_rd(wb_rd), .ex_mem_reg_write(mem_reg_write), .mem_wb_reg_write(wb_reg_write), .ForwardA(forward_a), .ForwardB(forward_b) );
    assign forwarded_data_a = (forward_a == 2'b10) ? wb_write_data : (forward_a == 2'b01) ? mem_alu_result : ex_reg_read_data1;
    assign forwarded_data_b = (forward_b == 2'b10) ? wb_write_data : (forward_b == 2'b01) ? mem_alu_result : ex_reg_read_data2;
    assign alu_input_a = (ex_alu_src_a == 2'b01) ? ex_pc : (ex_alu_src_a == 2'b10) ? 32'd0 : forwarded_data_a;
    assign ex_alu_input_b = ex_alu_src ? ex_imm_extended : forwarded_data_b;
    alu_control ac ( .ALUOp(ex_alu_op), .funct3(ex_funct3), .funct7(ex_funct7), .ALU_OP(ex_alu_op_final) );
    alu alu_unit ( .A(alu_input_a), .B(ex_alu_input_b), .ALU_OP(ex_alu_op_final), .Result(ex_alu_result), .Zero(ex_alu_zero) );
    pipeline_multiplier mul_unit ( .clk(clk), .rst(rst), .start(ex_is_mul), .A(forwarded_data_a), .B(forwarded_data_b), .valid(mul_valid), .product_out(mul_product) );
    assign ex_final_result = ex_is_mul ? mul_product : ex_alu_result;
    assign ex_pc_branch_target = ex_pc + ex_imm_extended;
    assign pc_jump_target = ex_alu_result;
    assign pc_src = (ex_branch & ex_alu_zero) ? 2'b01 : (ex_jump) ? 2'b10 : 2'b00;

    // EX/MEM, MEM, WB 阶段
    ex_mem_reg ex_mem_inst ( .clk(clk), .rst(rst), .ex_reg_write(ex_reg_write), .ex_mem_to_reg(ex_mem_to_reg), .ex_mem_read(ex_mem_read), .ex_mem_write(ex_mem_write), .ex_branch(ex_branch), .ex_wb_data_sel(ex_wb_data_sel), .ex_mem_op(ex_mem_op), .ex_pc_plus4(ex_pc_plus4), .ex_alu_result(ex_final_result), .ex_store_data(forwarded_data_b), .ex_rd(ex_rd), .mem_reg_write(mem_reg_write), .mem_mem_to_reg(mem_mem_to_reg), .mem_mem_read(mem_mem_read), .mem_mem_write(mem_mem_write), .mem_branch(mem_branch), .mem_wb_data_sel(mem_wb_data_sel), .mem_mem_op(mem_mem_op), .mem_pc_plus4(mem_pc_plus4), .mem_alu_result(mem_alu_result), .mem_store_data(mem_store_data), .mem_rd(mem_rd) );
    data_mem dmem ( .clk(clk), .addr(mem_alu_result), .write_data(mem_store_data), .mem_op(mem_mem_op), .mem_read(mem_mem_read), .mem_write(mem_mem_write), .read_data(mem_read_data_raw) );
    mem_wb_reg mem_wb_inst ( .clk(clk), .rst(rst), .mem_reg_write(mem_reg_write), .mem_mem_to_reg(mem_mem_to_reg), .mem_wb_data_sel(mem_wb_data_sel), .mem_mem_op(mem_mem_op), .mem_pc_plus4(mem_pc_plus4), .mem_read_data(mem_read_data_raw), .mem_alu_result(mem_alu_result), .mem_rd(mem_rd), .wb_reg_write(wb_reg_write), .wb_mem_to_reg(wb_mem_to_reg), .wb_wb_data_sel(wb_wb_data_sel), .wb_mem_op(wb_mem_op), .wb_pc_plus4(wb_pc_plus4), .wb_mem_read_data(wb_mem_read_data), .wb_alu_result(wb_alu_result), .wb_rd(wb_rd) );
    
    reg [31:0] data_from_mem; reg [7:0] byte_to_extend;
    always @(*) begin
        case (wb_alu_result[1:0]) 2'b00: byte_to_extend = wb_mem_read_data[7:0]; 2'b01: byte_to_extend = wb_mem_read_data[15:8]; 2'b10: byte_to_extend = wb_mem_read_data[23:16]; 2'b11: byte_to_extend = wb_mem_read_data[31:24]; default: byte_to_extend = 8'hXX; endcase
        case (wb_mem_op) 3'b010: data_from_mem = wb_mem_read_data; 3'b000: data_from_mem = {{24{byte_to_extend[7]}}, byte_to_extend}; 3'b100: data_from_mem = {{24{1'b0}}, byte_to_extend}; default: data_from_mem = wb_mem_read_data; endcase
    end
	assign wb_write_data = (wb_wb_data_sel == 2'b01) ? data_from_mem : (wb_wb_data_sel == 2'b10) ? wb_pc_plus4 : wb_alu_result;
endmodule

// ============================================================================
// 新增/修改的模块
// ============================================================================

module pipeline_multiplier(input clk, rst, start, input signed [31:0] A, B, output reg valid, output reg signed [31:0] product_out);
    reg signed [31:0] A_reg1, B_reg1; reg signed [63:0] product_reg2; reg signed [31:0] product_reg3; reg valid_reg1, valid_reg2, valid_reg3;
    wire signed [63:0] product_comb = A_reg1 * B_reg1;
    always @(posedge clk or posedge rst) begin
        if (rst) begin A_reg1 <= 0; B_reg1 <= 0; product_reg2 <= 0; product_reg3 <= 0; valid_reg1 <= 1'b0; valid_reg2 <= 1'b0; valid_reg3 <= 1'b0; valid <= 1'b0; product_out <= 0; end
        else begin A_reg1 <= A; B_reg1 <= B; valid_reg1 <= start; product_reg2 <= product_comb; valid_reg2 <= valid_reg1; product_reg3 <= product_reg2[31:0]; valid_reg3 <= valid_reg2; product_out <= product_reg3; valid <= valid_reg3; end
    end
endmodule

module control_unit(input [6:0] opcode, funct7, input [2:0] funct3, output reg RegWrite, output reg [1:0] ALUOp, output reg ALUSrc, output reg [1:0] ALUSrcA, output reg MemRead, MemWrite, MemtoReg, Branch, Jump, output reg [1:0] WBDataSel, output reg [2:0] MemOp, output reg IsMul);
    parameter R=7'b0110011, LOAD=7'b0000011, ADDI=7'b0010011, STORE=7'b0100011, BEQ=7'b1100011, LUI=7'b0110111, AUIPC=7'b0010111, JAL=7'b1101111, JALR=7'b1100111;
    always @(*) begin
        RegWrite=0; ALUOp=2'b00; ALUSrc=0; ALUSrcA=2'b00; MemRead=0; MemWrite=0; MemtoReg=0; Branch=0; Jump=0; WBDataSel=2'b00; MemOp=3'b000; IsMul=0;
        case(opcode) 
            R:begin RegWrite=1;ALUOp=2'b10;if(funct7==7'b1)IsMul=1;end 
            LOAD:begin RegWrite=1;ALUSrc=1;MemRead=1;MemtoReg=1;WBDataSel=2'b01;MemOp=funct3;end 
            ADDI:begin RegWrite=1;ALUSrc=1;end 
            STORE:begin ALUSrc=1;MemWrite=1;MemOp=funct3;end 
            BEQ:begin ALUOp=2'b01;Branch=1;end 
            LUI:begin RegWrite=1;ALUSrc=1;ALUSrcA=2'b10;end 
            AUIPC:begin RegWrite=1;ALUSrc=1;ALUSrcA=2'b01;end 
            JAL:begin RegWrite=1;ALUSrc=1;ALUSrcA=2'b01;Jump=1;WBDataSel=2'b10;end 
            JALR:begin RegWrite=1;ALUSrc=1;Jump=1;WBDataSel=2'b10;end 
        endcase
    end
endmodule

module hazard_detection_unit (input id_ex_mem_read, input [4:0] id_ex_rd, if_id_rs1, if_id_rs2, input ex_is_mul, mul_result_valid, output PCWrite, IF_ID_Write, output ID_EX_Write);
    wire load_use_stall = id_ex_mem_read && (id_ex_rd != 5'd0) && ((id_ex_rd == if_id_rs1) || (id_ex_rd == if_id_rs2));
    wire mul_stall = ex_is_mul && !mul_result_valid;
    wire stall = load_use_stall || mul_stall;
    assign PCWrite = ~stall;
    assign IF_ID_Write = ~stall;
    assign ID_EX_Write = ~stall;
endmodule

module if_id_reg(input clk, rst, en, flush, input [31:0] if_pc, if_pc_plus4, if_instruction, output reg [31:0] id_pc, id_pc_plus4, id_instruction);
    always @(posedge clk or posedge rst) if(rst||flush) {id_pc,id_pc_plus4,id_instruction}<=0; else if(en) {id_pc,id_pc_plus4,id_instruction}<={if_pc,if_pc_plus4,if_instruction};
endmodule

module id_ex_reg(
    input clk, rst, en,
    input id_reg_write, id_mem_to_reg, id_mem_read, id_mem_write, id_alu_src, id_branch, id_jump, id_is_mul,
    input [1:0] id_alu_op, id_alu_src_a, id_wb_data_sel,
    input [2:0] id_mem_op,
    input [31:0] id_pc, id_pc_plus4, id_reg_read_data1, id_reg_read_data2, id_imm_extended,
    input [4:0] id_rs1, id_rs2, id_rd,
    input [2:0] id_funct3, input [6:0] id_funct7,
    output reg ex_reg_write, ex_mem_to_reg, ex_mem_read, ex_mem_write, ex_alu_src, ex_branch, ex_jump, ex_is_mul,
    output reg [1:0] ex_alu_op, ex_alu_src_a, ex_wb_data_sel,
    output reg [2:0] ex_mem_op,
    output reg [31:0] ex_pc, ex_pc_plus4, ex_reg_read_data1, ex_reg_read_data2, ex_imm_extended,
    output reg [4:0] ex_rs1, ex_rs2, ex_rd,
    output reg [2:0] ex_funct3, output reg [6:0] ex_funct7
);
    always @(posedge clk or posedge rst) begin
        if (rst) {ex_reg_write,ex_mem_to_reg,ex_mem_read,ex_mem_write,ex_alu_src,ex_branch,ex_jump,ex_is_mul,ex_alu_op,ex_alu_src_a,ex_wb_data_sel,ex_mem_op,ex_pc,ex_pc_plus4,ex_reg_read_data1,ex_reg_read_data2,ex_imm_extended,ex_rs1,ex_rs2,ex_rd,ex_funct3,ex_funct7} <= 0;
        else if (en) {ex_reg_write,ex_mem_to_reg,ex_mem_read,ex_mem_write,ex_alu_src,ex_branch,ex_jump,ex_is_mul,ex_alu_op,ex_alu_src_a,ex_wb_data_sel,ex_mem_op,ex_pc,ex_pc_plus4,ex_reg_read_data1,ex_reg_read_data2,ex_imm_extended,ex_rs1,ex_rs2,ex_rd,ex_funct3,ex_funct7} <= {id_reg_write,id_mem_to_reg,id_mem_read,id_mem_write,id_alu_src,id_branch,id_jump,id_is_mul,id_alu_op,id_alu_src_a,id_wb_data_sel,id_mem_op,id_pc,id_pc_plus4,id_reg_read_data1,id_reg_read_data2,id_imm_extended,id_rs1,id_rs2,id_rd,id_funct3,id_funct7};
        else if (~en && rst==0) {ex_reg_write,ex_mem_to_reg,ex_mem_read,ex_mem_write,ex_alu_src,ex_branch,ex_jump,ex_is_mul} <= 0; 
    end
endmodule


module ex_mem_reg(
    input clk, rst,
    input ex_reg_write, ex_mem_to_reg, ex_mem_read, ex_mem_write, ex_branch,
    input [1:0] ex_wb_data_sel, input [2:0] ex_mem_op,
    input [31:0] ex_pc_plus4, ex_alu_result, ex_store_data,
    input [4:0] ex_rd,
    output reg mem_reg_write, mem_mem_to_reg, mem_mem_read, mem_mem_write, mem_branch,
    output reg [1:0] mem_wb_data_sel, output reg [2:0] mem_mem_op,
    output reg [31:0] mem_pc_plus4, mem_alu_result, mem_store_data,
    output reg [4:0] mem_rd
);
    always @(posedge clk or posedge rst) if (rst) {mem_reg_write,mem_mem_to_reg,mem_mem_read,mem_mem_write,mem_branch,mem_wb_data_sel,mem_mem_op,mem_pc_plus4,mem_alu_result,mem_store_data,mem_rd}<=0; else {mem_reg_write,mem_mem_to_reg,mem_mem_read,mem_mem_write,mem_branch,mem_wb_data_sel,mem_mem_op,mem_pc_plus4,mem_alu_result,mem_store_data,mem_rd}<={ex_reg_write,ex_mem_to_reg,ex_mem_read,ex_mem_write,ex_branch,ex_wb_data_sel,ex_mem_op,ex_pc_plus4,ex_alu_result,ex_store_data,ex_rd};
endmodule

module mem_wb_reg(input clk, rst, input mem_reg_write, mem_mem_to_reg, input [1:0] mem_wb_data_sel, input [2:0] mem_mem_op, input [31:0] mem_pc_plus4, mem_read_data, mem_alu_result, input [4:0] mem_rd, output reg wb_reg_write, wb_mem_to_reg, output reg [1:0] wb_wb_data_sel, output reg [2:0] wb_mem_op, output reg [31:0] wb_pc_plus4, wb_mem_read_data, wb_alu_result, output reg [4:0] wb_rd);
    always @(posedge clk or posedge rst) if(rst) {wb_reg_write,wb_mem_to_reg,wb_wb_data_sel,wb_mem_op}<=0; else {wb_reg_write,wb_mem_to_reg,wb_wb_data_sel,wb_mem_op,wb_pc_plus4,wb_mem_read_data,wb_alu_result,wb_rd}<={mem_reg_write,mem_mem_to_reg,mem_wb_data_sel,mem_mem_op,mem_pc_plus4,mem_read_data,mem_alu_result,mem_rd};
endmodule

// ** FIXED SYNTAX **
module pc(input clk, rst, en, input [31:0] PC_in, output reg [31:0] PC_out); 
    always @(posedge clk or posedge rst) begin
        if (rst) PC_out <= 32'h0; 
        else if (en) PC_out <= PC_in; 
    end
endmodule

module alu_control(input [1:0] ALUOp, input [2:0] funct3, input [6:0] funct7, output reg [3:0] ALU_OP); 
    parameter ADD=4'b0000,SUB=4'b0001,AND=4'b1001,OR=4'b1000; 
    always @(*) begin
        case(ALUOp) 
            2'b00: ALU_OP=ADD; 
            2'b01: ALU_OP=SUB; 
            2'b10: begin
                case(funct3) 
                    3'b000: if(funct7==7'b1) ALU_OP=ADD; else if(funct7==7'b0100000) ALU_OP=SUB; else ALU_OP=ADD; // for add, sub, mul
                    3'b111: ALU_OP=AND; 
                    3'b110: ALU_OP=OR; 
                    default: ALU_OP=4'bxxxx; 
                endcase
            end
            default: ALU_OP=4'bxxxx; 
        endcase
    end
endmodule

module imm_gen(input [31:0] instr, output reg [31:0] imm_extended); 
    always @(*) begin
        case(instr[6:0]) 
            7'b0000011,7'b0010011,7'b1100111: imm_extended={{20{instr[31]}},instr[31:20]}; 
            7'b0100011: imm_extended={{20{instr[31]}},instr[31:25],instr[11:7]}; 
            7'b1100011: imm_extended={{19{instr[31]}},instr[31],instr[7],instr[30:25],instr[11:8],1'b0}; 
            7'b0110111,7'b0010111: imm_extended={instr[31:12],12'b0}; 
            7'b1101111: imm_extended={{11{instr[31]}},instr[31],instr[19:12],instr[20],instr[30:21],1'b0}; 
            default: imm_extended=32'd0; 
        endcase
    end
endmodule

module alu(input [31:0] A, B, input [3:0] ALU_OP, output reg [31:0] Result, output reg Zero); 
    parameter ADD=4'b0000,SUB=4'b0001,AND=4'b1001,OR=4'b1000; 
    always @(*) begin
        case(ALU_OP) 
            ADD: Result=A+B; 
            SUB: Result=A-B; 
            AND: Result=A&B; 
            OR: Result=A|B; 
            default: Result=32'hdeadbeef; 
        endcase 
        Zero = (Result==0);
    end
endmodule

module reg_file(input clk, RegWrite, input [4:0] ReadAddr1, ReadAddr2, WriteAddr, input [31:0] WriteData, output [31:0] ReadData1, ReadData2); 
    reg [31:0] registers [0:31]; 
    integer i; 
    initial for(i=0;i<32;i=i+1) registers[i]=0; 
    assign ReadData1 = (ReadAddr1 == 0) ? 32'b0 : registers[ReadAddr1]; 
    assign ReadData2 = (ReadAddr2 == 0) ? 32'b0 : registers[ReadAddr2]; 
    always @(posedge clk) if (RegWrite && (WriteAddr != 0)) registers[WriteAddr] <= WriteData; 
endmodule

module instr_mem(input [5:0] addr, output [31:0] instr); 
    reg [31:0] rom[0:63]; 
    initial $readmemh("instr.mem", rom); 
    assign instr = rom[addr]; 
endmodule

module data_mem(input clk, input [31:0] addr, write_data, input [2:0] mem_op, input mem_read, mem_write, output [31:0] read_data); 
    reg [7:0] ram [0:4095]; 
    integer i; 
    initial for(i=0;i<4096;i=i+1) ram[i]=8'b0; 
    assign read_data={ram[{addr[31:2],2'b11}],ram[{addr[31:2],2'b10}],ram[{addr[31:2],2'b01}],ram[{addr[31:2],2'b00}]}; 
    always @(posedge clk) if(mem_write) case(mem_op[1:0]) 2'b00:ram[addr]<=write_data[7:0]; 2'b10:begin ram[addr]<=write_data[7:0];ram[addr+1]<=write_data[15:8];ram[addr+2]<=write_data[23:16];ram[addr+3]<=write_data[31:24];end endcase 
endmodule

module forwarding_unit(input [4:0] id_ex_rs1, id_ex_rs2, ex_mem_rd, mem_wb_rd, input ex_mem_reg_write, mem_wb_reg_write, output reg [1:0] ForwardA, ForwardB); 
    always @(*) begin
        if(ex_mem_reg_write&&(ex_mem_rd!=5'b0)&&(ex_mem_rd==id_ex_rs1)) ForwardA=2'b01; 
        else if(mem_wb_reg_write&&(mem_wb_rd!=5'b0)&&(mem_wb_rd==id_ex_rs1)) ForwardA=2'b10; 
        else ForwardA=2'b00; 
        
        if(ex_mem_reg_write&&(ex_mem_rd!=5'b0)&&(ex_mem_rd==id_ex_rs2)) ForwardB=2'b01; 
        else if(mem_wb_reg_write&&(mem_wb_rd!=5'b0)&&(mem_wb_rd==id_ex_rs2)) ForwardB=2'b10; 
        else ForwardB=2'b00; 
    end
endmodule