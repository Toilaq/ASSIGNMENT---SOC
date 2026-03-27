`timescale 1ns / 1ns

`define REG_SIZE 31
`define INST_SIZE 31
`define OPCODE_SIZE 6

// =============================================================================
// MODULE: REGISTER FILE (NEGEDGE Triggered)
// =============================================================================
module RegFile (
  input      [4:0] rd,
  input      [`REG_SIZE:0] rd_data,
  input      [4:0] rs1,
  output reg [`REG_SIZE:0] rs1_data,
  input      [4:0] rs2,
  output reg [`REG_SIZE:0] rs2_data,
  input      clk,
  input      we,
  input      rst
);
  localparam NumRegs = 32;
  reg [`REG_SIZE:0] regs[0:NumRegs-1];
  integer i;

  // [NEGEDGE] Bắt buộc để khớp timing với Testbench
  always @(negedge clk) begin
    if (rst) begin
      for (i = 0; i < NumRegs; i = i + 1) regs[i] <= 0;
    end else if (we && (rd != 0)) begin
      regs[rd] <= rd_data;
    end
  end

  always @(*) begin
    rs1_data = (rs1 == 0) ? 32'd0 : regs[rs1];
    rs2_data = (rs2 == 0) ? 32'd0 : regs[rs2];
  end
endmodule

// =============================================================================
// MODULE: DATAPATH PIPELINED (Serialized Divider)
// =============================================================================
module DatapathPipelined (
  input                     clk,
  input                     rst,
  output     [`REG_SIZE:0]  pc_to_imem,
  input      [`INST_SIZE:0] inst_from_imem,
  output reg [`REG_SIZE:0]  addr_to_dmem,
  input      [`REG_SIZE:0]  load_data_from_dmem,
  output reg [`REG_SIZE:0]  store_data_to_dmem,
  output reg [3:0]          store_we_to_dmem,
  output reg                halt,
  output reg [`REG_SIZE:0]  trace_writeback_pc,
  output reg [`INST_SIZE:0] trace_writeback_inst
);

  localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;
  
  localparam [`INST_SIZE:0] NOP_INST = 32'h00000013;

  reg [`REG_SIZE:0] cycles_current;
  always @(posedge clk) begin
    if (rst) cycles_current <= 0;
    else cycles_current <= cycles_current + 1;
  end

  // --- Signals ---
  reg  [`REG_SIZE:0] f_pc;
  wire [`REG_SIZE:0] f_pc_next;
  wire stall;
  wire pc_src; 
  wire [`REG_SIZE:0] x_target_pc;

  reg [`REG_SIZE:0] d_pc;
  reg [`INST_SIZE:0] d_inst;
  
  reg [`REG_SIZE:0] x_pc, x_rs1_data, x_rs2_data, x_imm;
  reg [`INST_SIZE:0] x_inst;
  reg [4:0] x_rd, x_rs1, x_rs2;
  reg [6:0] x_opcode, x_funct7;
  reg [2:0] x_funct3;
  reg x_reg_write, x_mem_read, x_mem_write, x_branch, x_jal, x_jalr, x_halt;
  
  reg [`REG_SIZE:0] m_pc, m_alu_result, m_rs2_data;
  reg [`INST_SIZE:0] m_inst;
  reg [4:0] m_rd;
  reg [2:0] m_funct3;
  reg m_reg_write, m_mem_read, m_mem_write, m_halt;

  reg [`REG_SIZE:0] w_pc, w_alu_result, w_mem_read_data;
  reg [`INST_SIZE:0] w_inst;
  reg [4:0] w_rd;
  reg w_reg_write, w_mem_read, w_halt;
  wire [`REG_SIZE:0] w_final_data;

reg [4:0] div_rd_fifo [0:7];
  reg div_valid_fifo [0:7];
  reg div_rem_fifo [0:7];
  
  // ===========================================================================
  // 1. FETCH STAGE
  // ===========================================================================
  assign f_pc_next = pc_src ? x_target_pc : (f_pc + 4);
  assign pc_to_imem = f_pc;

  always @(posedge clk) begin
    if (rst) f_pc <= 0;
    else if (!stall) f_pc <= f_pc_next;
  end

  always @(posedge clk) begin
    if (rst) begin
      d_pc <= 0; d_inst <= NOP_INST;
    end else if (pc_src) begin 
      d_pc <= 0; d_inst <= NOP_INST; // Flush
    end else if (!stall) begin
      d_pc <= f_pc; d_inst <= inst_from_imem;
    end
  end

  // ===========================================================================
  // 2. DECODE STAGE
  // ===========================================================================
  wire [6:0] d_opcode = d_inst[6:0];
  wire [4:0] d_rd     = d_inst[11:7];
  wire [2:0] d_funct3 = d_inst[14:12];
  wire [4:0] d_rs1    = d_inst[19:15];
  wire [4:0] d_rs2    = d_inst[24:20];
  wire [6:0] d_funct7 = d_inst[31:25];
  wire [`REG_SIZE:0] rf_rs1_data, rf_rs2_data;

  RegFile rf (
    .rd(w_rd), .rd_data(w_final_data), .we(w_reg_write),
    .rs1(d_rs1), .rs1_data(rf_rs1_data),
    .rs2(d_rs2), .rs2_data(rf_rs2_data),
    .clk(clk), .rst(rst)
  );

  // WD Bypass
  wire [`REG_SIZE:0] d_rs1_val = (w_reg_write && w_rd != 0 && w_rd == d_rs1) ? w_final_data : rf_rs1_data;
  wire [`REG_SIZE:0] d_rs2_val = (w_reg_write && w_rd != 0 && w_rd == d_rs2) ? w_final_data : rf_rs2_data;

  reg [`REG_SIZE:0] d_imm;
  always @(*) begin
    case (d_opcode)
      OpcodeStore:  d_imm = { {20{d_inst[31]}}, d_inst[31:25], d_inst[11:7] };
      OpcodeBranch: d_imm = { {20{d_inst[31]}}, d_inst[7], d_inst[30:25], d_inst[11:8], 1'b0 };
      OpcodeJal:    d_imm = { {12{d_inst[31]}}, d_inst[19:12], d_inst[20], d_inst[30:21], 1'b0 };
      OpcodeLui, OpcodeAuipc: d_imm = { d_inst[31:12], 12'b0 };
      default:      d_imm = { {20{d_inst[31]}}, d_inst[31:20] };
    endcase
  end

  wire d_uses_rs1 = (d_opcode != OpcodeLui && d_opcode != OpcodeAuipc && d_opcode != OpcodeJal);
  wire d_uses_rs2 = (d_opcode == OpcodeRegReg || d_opcode == OpcodeStore || d_opcode == OpcodeBranch);

  wire d_mem_read  = (d_opcode == OpcodeLoad);
  
  // --- HAZARD LOGIC ---
  wire div_busy; // From Divider FIFO
  wire load_use_hazard = (x_mem_read && x_rd != 0 && 
                         ((d_uses_rs1 && d_rs1 == x_rd) || (d_uses_rs2 && d_rs2 == x_rd)));
  
  // RAW hazard with DIV: Stall if instruction needs result from:
  // 1) DIV currently in EX stage - will enter FIFO next cycle
  // 2) DIV in FIFO stages 0-7 - still computing or waiting to inject
  wire [4:0] div_rd_in_fifo [0:7];
  assign div_rd_in_fifo[0] = (div_valid_fifo[0]) ? div_rd_fifo[0] : 5'b0;
  assign div_rd_in_fifo[1] = (div_valid_fifo[1]) ? div_rd_fifo[1] : 5'b0;
  assign div_rd_in_fifo[2] = (div_valid_fifo[2]) ? div_rd_fifo[2] : 5'b0;
  assign div_rd_in_fifo[3] = (div_valid_fifo[3]) ? div_rd_fifo[3] : 5'b0;
  assign div_rd_in_fifo[4] = (div_valid_fifo[4]) ? div_rd_fifo[4] : 5'b0;
  assign div_rd_in_fifo[5] = (div_valid_fifo[5]) ? div_rd_fifo[5] : 5'b0;
  assign div_rd_in_fifo[6] = (div_valid_fifo[6]) ? div_rd_fifo[6] : 5'b0;
  assign div_rd_in_fifo[7] = (div_valid_fifo[7]) ? div_rd_fifo[7] : 5'b0;
  
  // Check EX stage for DIV that will enter FIFO next cycle
wire x_is_div = (x_opcode == OpcodeRegReg) && (x_funct7 == 7'b0000001) && x_funct3[2];
  wire div_in_ex = x_is_div && x_reg_write && (x_rd != 0);
  
  // RAW hazard: Check FIFO stages 0-6 only (not 7, because 7 is injecting to MEM this cycle)
  wire div_raw_hazard = (d_uses_rs1 && d_rs1 != 0 && 
                        (div_in_ex && d_rs1 == x_rd ||
                         d_rs1 == div_rd_in_fifo[0] || d_rs1 == div_rd_in_fifo[1] ||
                         d_rs1 == div_rd_in_fifo[2] || d_rs1 == div_rd_in_fifo[3] ||
                         d_rs1 == div_rd_in_fifo[4] || d_rs1 == div_rd_in_fifo[5] ||
                         d_rs1 == div_rd_in_fifo[6])) ||
                       (d_uses_rs2 && d_rs2 != 0 &&
                        (div_in_ex && d_rs2 == x_rd ||
                         d_rs2 == div_rd_in_fifo[0] || d_rs2 == div_rd_in_fifo[1] ||
                         d_rs2 == div_rd_in_fifo[2] || d_rs2 == div_rd_in_fifo[3] ||
                         d_rs2 == div_rd_in_fifo[4] || d_rs2 == div_rd_in_fifo[5] ||
                         d_rs2 == div_rd_in_fifo[6]));
  
  // Structural hazard: non-DIV register-writing instructions must wait for DIV
  // Check DIV in EX stage + FIFO stages [0-6] (not 7, since 7 is about to complete)
  wire d_is_div = (d_opcode == OpcodeRegReg) && (d_funct7 == 7'b0000001);
  wire d_writes_reg = (d_opcode != OpcodeStore && d_opcode != OpcodeBranch) && (d_rd != 0);
  wire div_struct_hazard = (div_in_ex || div_valid_fifo[0] || div_valid_fifo[1] || 
                            div_valid_fifo[2] || div_valid_fifo[3] || div_valid_fifo[4] || 
                            div_valid_fifo[5] || div_valid_fifo[6]) && d_writes_reg && !d_is_div;
  
  assign stall = load_use_hazard || div_raw_hazard || div_struct_hazard;
  
  // Debug: Monitor hazards
  always @(posedge clk) begin
    if (!rst) begin
      if (div_raw_hazard) begin
        $display("[RAW] Cycle %0d: Stall ID (PC=%h) waiting for DIV result x%0d (rs1=%0d:%b rs2=%0d:%b)", 
                 cycles_current, d_pc, 
                 d_uses_rs1 && (div_in_ex && d_rs1 == x_rd || d_rs1 == div_rd_in_fifo[0] || d_rs1 == div_rd_in_fifo[1] || d_rs1 == div_rd_in_fifo[2] || d_rs1 == div_rd_in_fifo[3] || d_rs1 == div_rd_in_fifo[4] || d_rs1 == div_rd_in_fifo[5] || d_rs1 == div_rd_in_fifo[6] || d_rs1 == div_rd_in_fifo[7]) ? d_rs1 : d_rs2,
                 d_rs1, d_uses_rs1,
                 d_rs2, d_uses_rs2);
        $display("      EX: div_in_ex=%0b x_rd=%0d, FIFO: [0]=%0d:x%0d [1]=%0d:x%0d [2]=%0d:x%0d [3]=%0d:x%0d [4]=%0d:x%0d [5]=%0d:x%0d [6]=%0d:x%0d [7]=%0d:x%0d",
                 div_in_ex, x_rd,
                 div_valid_fifo[0], div_rd_fifo[0], div_valid_fifo[1], div_rd_fifo[1],
                 div_valid_fifo[2], div_rd_fifo[2], div_valid_fifo[3], div_rd_fifo[3],
                 div_valid_fifo[4], div_rd_fifo[4], div_valid_fifo[5], div_rd_fifo[5],
                 div_valid_fifo[6], div_rd_fifo[6], div_valid_fifo[7], div_rd_fifo[7]);
      end
    end
  end

  always @(posedge clk) begin
    if (rst) begin
      x_pc <= 0; x_inst <= NOP_INST; x_rd <= 0; x_rs1 <= 0; x_rs2 <= 0;
      x_rs1_data <= 0; x_rs2_data <= 0; x_imm <= 0; x_opcode <= 0; x_funct3 <= 0; x_funct7 <= 0;
      x_reg_write <= 0; x_mem_read <= 0; x_mem_write <= 0; x_branch <= 0; x_jal <= 0; x_jalr <= 0; x_halt <= 0;
    end 
    else if (stall || pc_src) begin // Flush EX on stall or branch - prevents new instr from entering
      x_pc <= 0; x_inst <= NOP_INST; x_rd <= 0; x_reg_write <= 0; x_mem_read <= 0; x_mem_write <= 0;
      x_branch <= 0; x_jal <= 0; x_jalr <= 0; x_halt <= 0;
      x_rs1 <= 0; x_rs2 <= 0; x_opcode <= 0; x_funct3 <= 0; x_funct7 <= 0;
    end 
    else begin
      x_pc <= d_pc; x_inst <= d_inst; x_rd <= d_rd; x_rs1 <= d_rs1; x_rs2 <= d_rs2;
      x_rs1_data <= d_rs1_val; x_rs2_data <= d_rs2_val; x_imm <= d_imm;
      x_opcode <= d_opcode; x_funct3 <= d_funct3; x_funct7 <= d_funct7;
      x_reg_write <= (d_opcode != OpcodeStore && d_opcode != OpcodeBranch);
      x_mem_read <= d_mem_read; x_mem_write <= (d_opcode == OpcodeStore);
      x_branch <= (d_opcode == OpcodeBranch); x_jal <= (d_opcode == OpcodeJal); 
      x_jalr <= (d_opcode == OpcodeJalr); x_halt <= (d_opcode == OpcodeEnviron);
    end
  end

  // ===========================================================================
  // 3. EXECUTE STAGE
  // ===========================================================================
  reg [`REG_SIZE:0] fwd_a_val, fwd_b_val;
  
  always @(*) begin
    fwd_a_val = x_rs1_data;
    if (m_reg_write && m_rd != 0 && m_rd == x_rs1)      fwd_a_val = m_alu_result;
    else if (w_reg_write && w_rd != 0 && w_rd == x_rs1) fwd_a_val = w_final_data;

    fwd_b_val = x_rs2_data;
    if (m_reg_write && m_rd != 0 && m_rd == x_rs2)      fwd_b_val = m_alu_result;
    else if (w_reg_write && w_rd != 0 && w_rd == x_rs2) fwd_b_val = w_final_data;
  end
  
  // Debug: Monitor forwarding
  always @(posedge clk) begin
    if (!rst && (x_opcode != 7'b0)) begin
      if (m_reg_write && m_rd != 0 && (m_rd == x_rs1 || m_rd == x_rs2)) begin
        $display("[FWD-MX] Cycle %0d: Forward from MEM x%0d=%h to EX (rs1=%0d rs2=%0d)", 
                 cycles_current, m_rd, m_alu_result, x_rs1, x_rs2);
      end
      if (w_reg_write && w_rd != 0 && (w_rd == x_rs1 || w_rd == x_rs2)) begin
        $display("[FWD-WX] Cycle %0d: Forward from WB x%0d=%h to EX (rs1=%0d rs2=%0d)", 
                 cycles_current, w_rd, w_final_data, x_rs1, x_rs2);
      end
    end
  end

  wire [`REG_SIZE:0] alu_op1 = fwd_a_val;
  wire [`REG_SIZE:0] alu_op2 = (x_opcode == OpcodeRegImm || x_opcode == OpcodeLoad || x_opcode == OpcodeStore || 
                                x_opcode == OpcodeJalr || x_opcode == OpcodeAuipc || x_opcode == OpcodeLui) ? x_imm : fwd_b_val;
  
  reg [`REG_SIZE:0] alu_res;
  always @(*) begin
    case (x_opcode)
      OpcodeLui:   alu_res = x_imm;
      OpcodeAuipc: alu_res = x_pc + x_imm;
      OpcodeJal, OpcodeJalr: alu_res = x_pc + 4;
      OpcodeLoad, OpcodeStore: alu_res = alu_op1 + alu_op2;
      OpcodeRegImm, OpcodeRegReg: begin
        case (x_funct3)
          3'b000: alu_res = (x_opcode == OpcodeRegReg && x_funct7[5]) ? (alu_op1 - alu_op2) : (alu_op1 + alu_op2);
          3'b001: alu_res = alu_op1 << alu_op2[4:0];
          3'b010: alu_res = ($signed(alu_op1) < $signed(alu_op2)) ? 1 : 0;
          3'b011: alu_res = (alu_op1 < alu_op2) ? 1 : 0;
          3'b100: alu_res = alu_op1 ^ alu_op2;
          3'b101: alu_res = x_funct7[5] ? ($signed(alu_op1) >>> alu_op2[4:0]) : (alu_op1 >> alu_op2[4:0]);
          3'b110: alu_res = alu_op1 | alu_op2;
          3'b111: alu_res = alu_op1 & alu_op2;
          default: alu_res = 0;
        endcase
      end
      default: alu_res = 0;
    endcase
  end

  // Branch
  reg taken;
  always @(*) begin
    case (x_funct3)
      3'b000: taken = (fwd_a_val == fwd_b_val);
      3'b001: taken = (fwd_a_val != fwd_b_val);
      3'b100: taken = ($signed(fwd_a_val) < $signed(fwd_b_val));
      3'b101: taken = ($signed(fwd_a_val) >= $signed(fwd_b_val));
      3'b110: taken = (fwd_a_val < fwd_b_val);
      3'b111: taken = (fwd_a_val >= fwd_b_val);
      default: taken = 0;
    endcase
  end

  assign pc_src = (x_branch && taken) || x_jal || x_jalr;
  assign x_target_pc = (x_opcode == OpcodeJalr) ? (fwd_a_val + x_imm) : (x_pc + x_imm);

  // --- DIVIDER UNIT ---
  wire [31:0] div_quotient;
  wire [31:0] div_remainder;
 // wire x_is_div = (x_opcode == OpcodeRegReg) && (x_funct7 == 7'b0000001) && x_funct3[2];
  
  // Debug: Monitor DIV entering FIFO
  always @(posedge clk) begin
    if (!rst && x_is_div && !stall && !pc_src) begin
      $display("[DIV-IN] Cycle %0d: DIV x%0d = %h / %h (fwd_a=%h fwd_b=%h) [rem=%b]", 
               cycles_current, x_rd, fwd_a_val, fwd_b_val, fwd_a_val, fwd_b_val, x_funct3[1]);
    end
  end
  
  // Use forwarded values
  DividerUnsignedPipelined u_div_pipe (
    .clk (clk), .rst (rst), .stall (1'b0), 
    .i_dividend (fwd_a_val), .i_divisor  (fwd_b_val),
    .o_quotient (div_quotient), .o_remainder (div_remainder)
  );

  // Divider FIFO
  /*reg [4:0] div_rd_fifo [0:7];
  reg div_valid_fifo [0:7];
  reg div_rem_fifo [0:7];*/
  integer k; 

  always @(posedge clk) begin
    if (rst) begin
      for (k = 0; k < 8; k = k + 1) begin
        div_valid_fifo[k] <= 0; div_rd_fifo[k] <= 0; div_rem_fifo[k] <= 0;
      end
    end else begin
      // Push DIV to FIFO[0] if DIV in EX (before it gets flushed)
      div_valid_fifo[0] <= x_is_div && !pc_src;
      div_rd_fifo[0]    <= x_rd;
      div_rem_fifo[0]   <= x_funct3[1];
      
      // Shift all stages normally
      for (k = 1; k < 8; k = k + 1) begin
        div_valid_fifo[k] <= div_valid_fifo[k-1];
        div_rd_fifo[k]    <= div_rd_fifo[k-1];
        div_rem_fifo[k]   <= div_rem_fifo[k-1];
      end
    end
  end
  
  // DIV BUSY Logic
  assign div_busy = div_valid_fifo[0] || div_valid_fifo[1] || div_valid_fifo[2] || 
                    div_valid_fifo[3] || div_valid_fifo[4] || div_valid_fifo[5] || 
                    div_valid_fifo[6] || div_valid_fifo[7];
  
  wire div_done = div_valid_fifo[7];

  // EX -> MEM
  always @(posedge clk) begin
    if (rst) begin
      m_pc <= 0; m_inst <= NOP_INST; m_alu_result <= 0; m_rs2_data <= 0; m_rd <= 0;
      m_funct3 <= 0; m_reg_write <= 0; m_mem_read <= 0; m_mem_write <= 0; m_halt <= 0;
    end else begin
      m_pc <= x_pc; m_inst <= x_inst; m_rs2_data <= fwd_b_val; m_funct3 <= x_funct3;
      m_mem_read <= x_mem_read; m_mem_write <= x_mem_write; m_halt <= x_halt;
      
      if (div_done) begin
        m_alu_result <= div_rem_fifo[7] ? div_remainder : div_quotient;
        m_rd         <= div_rd_fifo[7];
        m_reg_write  <= 1;
        $display("[DIV-OUT] Cycle %0d: DIV result x%0d = %h (rem=%b) injected to MEM (overwrite EX x%0d=%h)", 
                 cycles_current, div_rd_fifo[7], 
                 div_rem_fifo[7] ? div_remainder : div_quotient,
                 div_rem_fifo[7], x_rd, alu_res);
      end else begin
        m_alu_result <= alu_res;
        m_rd         <= x_rd;
        m_reg_write  <= x_reg_write && !x_is_div;  // DIV writes via div_done only
      end
    end
  end

  // ===========================================================================
  // 4. MEMORY STAGE
  // ===========================================================================
  wire [1:0] byte_offset = m_alu_result[1:0];
  reg [31:0] shifted_store_data;
  reg [3:0] store_mask;
  
  always @(*) begin
    case (m_funct3[1:0]) // SB=00, SH=01, SW=10
      2'b00: begin // SB
        case (byte_offset)
          2'b00: begin shifted_store_data = {24'b0, m_rs2_data[7:0]};        store_mask = 4'b0001; end
          2'b01: begin shifted_store_data = {16'b0, m_rs2_data[7:0], 8'b0};  store_mask = 4'b0010; end
          2'b10: begin shifted_store_data = {8'b0, m_rs2_data[7:0], 16'b0};  store_mask = 4'b0100; end
          2'b11: begin shifted_store_data = {m_rs2_data[7:0], 24'b0};        store_mask = 4'b1000; end
        endcase
      end
      2'b01: begin // SH
        case (byte_offset[1])
          1'b0: begin shifted_store_data = {16'b0, m_rs2_data[15:0]};        store_mask = 4'b0011; end
          1'b1: begin shifted_store_data = {m_rs2_data[15:0], 16'b0};        store_mask = 4'b1100; end
        endcase
      end
      default: begin // SW
        shifted_store_data = m_rs2_data;
        store_mask = 4'b1111;
      end
    endcase
  end
  
  always @(*) begin
    addr_to_dmem       = m_alu_result;
    store_data_to_dmem = shifted_store_data;
    store_we_to_dmem   = m_mem_write ? store_mask : 4'b0000;
  end

  // MEM -> WB
  always @(posedge clk) begin
    if (rst) begin
      w_pc <= 0; w_inst <= NOP_INST; w_alu_result <= 0; w_mem_read_data <= 0; w_rd <= 0;
      w_reg_write <= 0; w_mem_read <= 0; w_halt <= 0;
    end else begin
      w_pc <= m_pc; w_inst <= m_inst; w_alu_result <= m_alu_result;
      w_mem_read_data <= load_data_from_dmem; w_rd <= m_rd;
      w_reg_write <= m_reg_write; w_mem_read <= m_mem_read; w_halt <= m_halt;
    end
  end

  // ===========================================================================
  // 5. WRITEBACK STAGE
  // ===========================================================================
  assign w_final_data = w_mem_read ? w_mem_read_data : w_alu_result;
  
  // Debug: Monitor writeback
  always @(posedge clk) begin
    if (!rst && w_reg_write && w_rd != 0) begin
      $display("[WB] Cycle %0d: Write x%0d = %h (from %s)", 
               cycles_current, w_rd, w_final_data, w_mem_read ? "MEM" : "ALU");
    end
  end

  always @(*) begin
    trace_writeback_pc   = w_pc;
    trace_writeback_inst = w_inst;
    halt                 = w_halt;
  end

endmodule

// =============================================================================
// MODULE: MEMORY & PROCESSOR WRAPPERS
// =============================================================================
module MemorySingleCycle #(
  parameter NUM_WORDS = 512
) (
  input                     rst,
  input                     clk,
  input      [`REG_SIZE:0]  pc_to_imem,
  output reg [`REG_SIZE:0]  inst_from_imem,
  input      [`REG_SIZE:0]  addr_to_dmem,
  output reg [`REG_SIZE:0]  load_data_from_dmem,
  input      [`REG_SIZE:0]  store_data_to_dmem,
  input      [3:0]          store_we_to_dmem
);

  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];
  integer k;

  initial begin
    for (k=0; k<NUM_WORDS; k=k+1) mem_array[k] = 0;
    $readmemh("/mnt/c/Users/Windows/Downloads/05_pipelined/mem_initial_contents.hex", mem_array, 0, NUM_WORDS-1);
  end
  
  always @(negedge rst) begin
    if (rst == 0) $readmemh("/mnt/c/Users/Windows/Downloads/05_pipelined/mem_initial_contents.hex", mem_array, 0, NUM_WORDS-1);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  // Read instruction memory
  always @(*) begin
    inst_from_imem = mem_array[pc_to_imem[AddrMsb:AddrLsb]];
  end

  // Data memory access
  always @(negedge clk) begin
    if (store_we_to_dmem[0]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0]   <= store_data_to_dmem[7:0];
    if (store_we_to_dmem[1]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8]  <= store_data_to_dmem[15:8];
    if (store_we_to_dmem[2]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    if (store_we_to_dmem[3]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    
    load_data_from_dmem <= mem_array[addr_to_dmem[AddrMsb:AddrLsb]];
  end
endmodule

module Processor (
  input                 clk,
  input                 rst,
  output                halt,
  input  [(8*32)-1:0]   test_case,
  output [`REG_SIZE:0]  trace_writeback_pc,
  output [`INST_SIZE:0] trace_writeback_inst
);

  wire [`INST_SIZE:0] inst_from_imem;
  wire [`REG_SIZE:0]  pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0]          mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clk                 (clk),
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
  );

  DatapathPipelined datapath (
    .clk                  (clk),
    .rst                  (rst),
    .pc_to_imem           (pc_to_imem),
    .inst_from_imem       (inst_from_imem),
    .addr_to_dmem         (mem_data_addr),
    .store_data_to_dmem   (mem_data_to_write),
    .store_we_to_dmem     (mem_data_we),
    .load_data_from_dmem  (mem_data_loaded_value),
    .halt                 (halt),
    .trace_writeback_pc   (trace_writeback_pc),
    .trace_writeback_inst (trace_writeback_inst)
  );

endmodule
