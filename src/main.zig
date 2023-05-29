const std = @import("std");

const FormatType = enum {
    R,
    I,
    S,
    B,
    U,
    J,
};

const Opcode = enum {
    const Self = @This();

    // I
    LUI,
    AUIPC,
    JAL,
    JALR,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    ADDI,
    SLTI,
    SLTIU,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND,
    FENCE,
    ECALL,
    EBREAK,

    // “Zicsr”, Control and Status Register (CSR) Instructions, Version 2.0
    CSRRW,
    CSRRS,
    CSRRC,
    CSRRWI,
    CSRRSI,
    CSRRCI,

    fn format_type(self: Self) FormatType {
        return switch (self) {
            .LUI, .AUIPC => FormatType.U,
            .JAL => FormatType.J,
            .JALR => FormatType.I,
            .BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU => FormatType.B,
            .LB, .LH, .LW, .LBU, .LHU => FormatType.I,
            .SB, .SH, .SW => FormatType.S,
            .ADDI, .SLTI, .SLTIU, .XORI, .ORI, .ANDI => FormatType.I,
            .SLLI, .SRLI, .SRAI => FormatType.I,
            .ADD, .SUB, .SLL, .SLT, .SLTU, .XOR, .SRL, .SRA, .OR, .AND => FormatType.R,
            .FENCE, .ECALL, .EBREAK, .CSRRW, .CSRRS, .CSRRC, .CSRRWI, .CSRRSI, .CSRRCI => FormatType.I,
        };
    }

    fn str(self: Self) []const u8 {
        return switch (self) {
            .LUI => "LUI",
            .AUIPC => "AUIPC",
            .JAL => "JAL",
            .JALR => "JALR",
            .BEQ => "BEQ",
            .BNE => "BNE",
            .BLT => "BLT",
            .BGE => "BGE",
            .BLTU => "BLTU",
            .BGEU => "BGEU",
            .LB => "LB",
            .LH => "LH",
            .LW => "LW",
            .LBU => "LBU",
            .LHU => "LHU",
            .SB => "SB",
            .SH => "SH",
            .SW => "SW",
            .ADDI => "ADDI",
            .SLTI => "SLTI",
            .SLTIU => "SLTIU",
            .XORI => "XORI",
            .ORI => "ORI",
            .ANDI => "ANDI",
            .SLLI => "SLLI",
            .SRLI => "SRLI",
            .SRAI => "SRAI",
            .ADD => "ADD",
            .SUB => "SUB",
            .SLL => "SLL",
            .SLT => "SLT",
            .SLTU => "SLTU",
            .XOR => "XOR",
            .SRL => "SRL",
            .SRA => "SRA",
            .OR => "OR",
            .AND => "AND",
            .FENCE => "FENCE",
            .ECALL => "ECALL",
            .EBREAK => "EBREAK",
            .CSRRW => "CSRRW",
            .CSRRS => "CSRRS",
            .CSRRC => "CSRRC",
            .CSRRWI => "CSRRWI",
            .CSRRSI => "CSRRSI",
            .CSRRCI => "CSRRCI",
        };
    }
};

const Instruction = struct {
    const Self = @This();

    op: Opcode,
    rd: u8,
    rs1: u8,
    rs2: u8,
    imm: i32,

    pub fn format(
        self: Self,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        const format_type = self.op.format_type();
        try writer.print("{s}", .{
            self.op.str(),
        });
        switch (format_type) {
            .R => {
                try writer.print(" x{} x{} x{}", .{ self.rd, self.rs1, self.rs2 });
            },
            .I => {
                try writer.print(" x{} x{} 0x{x}", .{ self.rd, self.rs1, self.imm });
            },
            .S => {
                try writer.print(" x{} x{} 0x{x}", .{ self.rs1, self.rs2, self.imm });
            },
            .B => {
                try writer.print(" x{} x{} 0x{x}", .{ self.rs1, self.rs2, self.imm });
            },
            .U => {
                try writer.print(" x{}  0x{x}", .{ self.rd, self.imm });
            },
            .J => {
                try writer.print(" x{}  0x{x}", .{ self.rd, self.imm });
            },
        }
    }
};

const MASK_OPCODE: u32 = 0b00000000000000000000000001111111;
const MASK_FUNCT3: u32 = 0b00000000000000000111000000000000;
const SHIFT_FUNCT3: u5 = 12;
const MASK_IMM_HI: u32 = 0b11111110000000000000000000000000;
const SHIFT_IMM_HI: u5 = 25;
const MASK_7_31: u32 = 0b11111111111111111111111100000000;

const RV32I_OPCODE = enum(u32) {
    LUI = 0b0110111,
    AUIPC = 0b001011,
    JAL = 0b1101111,
    JALR = 0b1100111,
    // Conditional Branches
    BRANCH = 0b1100011, // BEQ, BNE, BLT, BGE, BLTU, BGEU
    LOAD = 0b0000011, // LB, LH, LW, LBU, LHU
    STORE = 0b0100011, // SB, SH, SW
    // Integer Register-Immediate Instructions
    OPIMM = 0b0010011, // ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI
    // Integer Register Register Operations
    OP = 0b0110011, // ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
    FENCE = 0b0001111,
    SYSTEM = 0b1110011, // ECALL, EBREAK, CSR*
};

const JALR_FUNCT3: u32 = 0b000;

const BRANCH_FUNCT3 = enum(u32) {
    BEQ = 0b000,
    BNE = 0b001,
    BLT = 0b100,
    BGE = 0b101,
    BLTU = 0b110,
    BGEU = 0b111,
};

const LOAD_FUNCT3 = enum(u32) {
    LB = 0b000,
    LH = 0b001,
    LW = 0b010,
    LBU = 0b100,
    LHU = 0b101,
};

const STORE_FUNCT3 = enum(u32) {
    SB = 0b000,
    SH = 0b001,
    SW = 0b010,
};

const OPIMM_FUNCT3 = enum(u32) {
    ADDI = 0b000,
    SLTI = 0b010,
    SLTIU = 0b011,
    XORI = 0b100,
    ORI = 0b110,
    ANDI = 0b111,
    SLLI = 0b001,
    SRI = 0b101, // SRLI, SRAI
};

const SLLI_IMM_HI: u32 = 0b0000000;

const SRI_IMM_HI = enum(u32) {
    SRLI = 0b0000000,
    SRAI = 0b0100000,
};

const OP_FUNCT3 = enum(u32) {
    ADDSUB = 0b000,
    SLL = 0b001,
    SLT = 0b010,
    SLTU = 0b11,
    XOR = 0b100,
    SR = 0b101,
    OR = 0b110,
    AND = 0b111,
};

const ADDSUB_IMM_HI = enum(u32) {
    ADD = 0b0000000,
    SUB = 0b0100000,
};

const SR_IMM_HI = enum(u32) {
    SRL = 0b0000000,
    SRA = 0b0100000,
};

const SYSTEM_FUNCT3 = enum(u32) {
    PRIV = 0b000,
    CSRRW = 0b001,
    CSRRS = 0b010,
    CSRRC = 0b011,
    CSRRWI = 0b101,
    CSRRSI = 0b110,
    CSRRCI = 0b111,
};

const PRIV_7_31 = enum(u32) {
    ECALL = 0b00000000000000000000000000000000,
    EBREAK = 0b00000000000100000000000000000000,
};

fn decode_opcode(ins: u32) u8 {
    return @intCast(u8, ins & 0b00000000000000000000000001111111);
}
// 'rd' is register destination
fn decode_rd(ins: u32) u8 {
    return @intCast(u8, (ins & 0b00000000000000000000111110000000) >> 7);
}
fn decode_funct3(ins: u32) u8 {
    return @intCast(u8, (ins & 0b00000000000000000111000000000000) >> 12);
}
// 'rs1' is register source 1
fn decode_rs1(ins: u32) u8 {
    return @intCast(u8, (ins & 0b00000000000011111000000000000000) >> 15);
}
// 'rs1' is register source 2
fn decode_rs2(ins: u32) u8 {
    return @intCast(u8, (ins & 0b00000001111100000000000000000000) >> 20);
}
fn decode_funct7(ins: u32) u8 {
    return @intCast(u8, (ins & 0b11111110000000000000000000000000) >> 25);
}
// 12 bits, sign-extended
fn decode_i_imm(ins: u32) i32 {
    @setRuntimeSafety(false);
    return @intCast(i32, ins & 0b11111111111100000000000000000000) >> 20;
}
// 5 bits
fn decode_i_imm_lo(ins: u32) u8 {
    @setRuntimeSafety(false);
    return @intCast(u8, @intCast(u32, ins & 0b00000001111100000000000000000000) >> 20);
}
// 12 bits, sign-extended
fn decode_s_imm(ins: u32) i32 {
    @setRuntimeSafety(false);
    return @intCast(i32, ins & 0b11111110000000000000000000000000) >> (25 - 5) |
        @intCast(i32, ins & 0b00000000000000000000111110000000) >> 7;
}
// 32 bits, sign-extended
fn decode_u_imm(ins: u32) i32 {
    @setRuntimeSafety(false);
    return @intCast(i32, ins & 0b11111111111111111111000000000000);
}
// 12 bits, sign-extended
fn decode_b_imm(ins: u32) i32 {
    @setRuntimeSafety(false);
    return @intCast(i32, ins & 0b10000000000000000000000000000000) >> (31 - 12) |
        @intCast(i32, ins & 0b01111110000000000000000000000000) >> (25 - 5) |
        @intCast(i32, ins & 0b00000000000000000000111100000000) >> (8 - 1) |
        @intCast(i32, ins & 0b00000000000000000000000010000000) << -(7 - 11);
}
// 32 bits, sign-extended
fn decode_j_imm(ins: u32) i32 {
    @setRuntimeSafety(false);
    return @intCast(i32, ins & 0b10000000000000000000000000000000) >> (31 - 20) |
        @intCast(i32, ins & 0b01111111111000000000000000000000) >> (21 - 1) |
        @intCast(i32, ins & 0b00000000000100000000000000000000) >> (20 - 11) |
        @intCast(i32, ins & 0b00000000000011111111000000000000) >> (12 - 12);
}

fn decode(comptime T: type, self: *T, ins: u32) T.ReturnType {
    switch (ins & MASK_OPCODE) {
        @enumToInt(RV32I_OPCODE.LUI) => {
            // U-Type
            const rd = decode_rd(ins);
            const imm = decode_u_imm(ins);
            return self.op_lui(rd, imm);
        },
        @enumToInt(RV32I_OPCODE.AUIPC) => {
            // U-Type
            const rd = decode_rd(ins);
            const imm = decode_u_imm(ins);
            return self.op_auipc(rd, imm);
        },
        @enumToInt(RV32I_OPCODE.JAL) => {
            // J-Type
            const rd = decode_rd(ins);
            const imm = decode_j_imm(ins);
            return self.op_jal(rd, imm);
        },
        @enumToInt(RV32I_OPCODE.JALR) => {
            // I-Type
            const rd = decode_rd(ins);
            const rs1 = decode_rs1(ins);
            const imm = decode_i_imm(ins);
            return switch (ins & MASK_FUNCT3) {
                JALR_FUNCT3 << SHIFT_FUNCT3 => self.op_jalr(rd, rs1, imm),
                else => @import("std").debug.panic("Invalid", .{}),
            };
        },
        @enumToInt(RV32I_OPCODE.BRANCH) => {
            // B-Type
            const rs1 = decode_rs1(ins);
            const rs2 = decode_rs2(ins);
            const imm = decode_b_imm(ins);
            return switch (ins & MASK_FUNCT3) {
                @enumToInt(BRANCH_FUNCT3.BEQ) << SHIFT_FUNCT3 => self.op_beq(rs1, rs2, imm),
                @enumToInt(BRANCH_FUNCT3.BNE) << SHIFT_FUNCT3 => self.op_bne(rs1, rs2, imm),
                @enumToInt(BRANCH_FUNCT3.BLT) << SHIFT_FUNCT3 => self.op_blt(rs1, rs2, imm),
                @enumToInt(BRANCH_FUNCT3.BGE) << SHIFT_FUNCT3 => self.op_bge(rs1, rs2, imm),
                @enumToInt(BRANCH_FUNCT3.BLTU) << SHIFT_FUNCT3 => self.op_bltu(rs1, rs2, imm),
                @enumToInt(BRANCH_FUNCT3.BGEU) << SHIFT_FUNCT3 => self.op_bgeu(rs1, rs2, imm),
                else => @import("std").debug.panic("Invalid", .{}),
            };
        },
        @enumToInt(RV32I_OPCODE.LOAD) => {
            // I-Type
            const rd = decode_rd(ins);
            const rs1 = decode_rs1(ins);
            const imm = decode_i_imm(ins);
            return switch (ins & MASK_FUNCT3) {
                @enumToInt(LOAD_FUNCT3.LB) << SHIFT_FUNCT3 => self.op_lb(rd, rs1, imm),
                @enumToInt(LOAD_FUNCT3.LH) << SHIFT_FUNCT3 => self.op_lh(rd, rs1, imm),
                @enumToInt(LOAD_FUNCT3.LW) << SHIFT_FUNCT3 => self.op_lw(rd, rs1, imm),
                @enumToInt(LOAD_FUNCT3.LBU) << SHIFT_FUNCT3 => self.op_lbu(rd, rs1, imm),
                @enumToInt(LOAD_FUNCT3.LHU) << SHIFT_FUNCT3 => self.op_lhu(rd, rs1, imm),
                else => @import("std").debug.panic("Invalid", .{}),
            };
        },
        @enumToInt(RV32I_OPCODE.STORE) => {
            // B-Type
            const rs1 = decode_rs1(ins);
            const rs2 = decode_rs2(ins);
            const imm = decode_b_imm(ins);
            return switch (ins & MASK_FUNCT3) {
                @enumToInt(STORE_FUNCT3.SB) << SHIFT_FUNCT3 => self.op_sb(rs1, rs2, imm),
                @enumToInt(STORE_FUNCT3.SH) << SHIFT_FUNCT3 => self.op_sh(rs1, rs2, imm),
                @enumToInt(STORE_FUNCT3.SW) << SHIFT_FUNCT3 => self.op_sw(rs1, rs2, imm),
                else => @import("std").debug.panic("Invalid", .{}),
            };
        },
        @enumToInt(RV32I_OPCODE.OPIMM) => {
            // I-Type
            const rd = decode_rd(ins);
            const rs1 = decode_rs1(ins);
            switch (ins & MASK_FUNCT3) {
                @enumToInt(OPIMM_FUNCT3.ADDI) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_addi(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.SLTI) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_slti(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.SLTIU) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_sltiu(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.XORI) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_xori(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.ORI) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_ori(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.ANDI) << SHIFT_FUNCT3 => {
                    const imm = decode_i_imm(ins);
                    return self.op_andi(rd, rs1, imm);
                },
                @enumToInt(OPIMM_FUNCT3.SLLI) << SHIFT_FUNCT3 => {
                    switch (ins & MASK_IMM_HI) {
                        SLLI_IMM_HI << SHIFT_IMM_HI => {
                            const imm = decode_i_imm_lo(ins);
                            return self.op_slli(rd, rs1, imm);
                        },
                        else => @import("std").debug.panic("Invalid", .{}),
                    }
                },
                @enumToInt(OPIMM_FUNCT3.SRI) => {
                    switch (ins & MASK_IMM_HI) {
                        @enumToInt(SRI_IMM_HI.SRLI) << SHIFT_IMM_HI => {
                            const imm = decode_i_imm_lo(ins);
                            return self.op_srli(rd, rs1, imm);
                        },
                        @enumToInt(SRI_IMM_HI.SRAI) << SHIFT_IMM_HI => {
                            const imm = decode_i_imm_lo(ins);
                            return self.op_srai(rd, rs1, imm);
                        },
                        else => @import("std").debug.panic("Invalid", .{}),
                    }
                },
                else => @import("std").debug.panic("Invalid", .{}),
            }
        },
        @enumToInt(RV32I_OPCODE.OP) => {
            // R-Type
            const rd = decode_rd(ins);
            const rs1 = decode_rs1(ins);
            const rs2 = decode_rs2(ins);
            return switch (ins & MASK_FUNCT3) {
                @enumToInt(OP_FUNCT3.ADDSUB) << SHIFT_FUNCT3 => {
                    return switch (ins & MASK_IMM_HI) {
                        @enumToInt(ADDSUB_IMM_HI.ADD) << SHIFT_IMM_HI => self.op_add(rd, rs1, rs2),
                        @enumToInt(ADDSUB_IMM_HI.SUB) << SHIFT_IMM_HI => self.op_sub(rd, rs1, rs2),
                        else => @import("std").debug.panic("Invalid", .{}),
                    };
                },
                @enumToInt(OP_FUNCT3.SLL) << SHIFT_FUNCT3 => self.op_sll(rd, rs1, rs2),
                @enumToInt(OP_FUNCT3.SLT) << SHIFT_FUNCT3 => self.op_slt(rd, rs1, rs2),
                @enumToInt(OP_FUNCT3.SLTU) << SHIFT_FUNCT3 => self.op_sltu(rd, rs1, rs2),
                @enumToInt(OP_FUNCT3.XOR) << SHIFT_FUNCT3 => self.op_xor(rd, rs1, rs2),
                @enumToInt(OP_FUNCT3.SR) << SHIFT_FUNCT3 => {
                    return switch (ins & MASK_IMM_HI) {
                        @enumToInt(SR_IMM_HI.SRL) << SHIFT_IMM_HI => self.op_srl(rd, rs1, rs2),
                        @enumToInt(SR_IMM_HI.SRA) << SHIFT_IMM_HI => self.op_sra(rd, rs1, rs2),
                        else => @import("std").debug.panic("Invalid", .{}),
                    };
                },
                @enumToInt(OP_FUNCT3.OR) << SHIFT_FUNCT3 => self.op_or(rd, rs1, rs2),
                @enumToInt(OP_FUNCT3.AND) << SHIFT_FUNCT3 => self.op_and(rd, rs1, rs2),
                else => @import("std").debug.panic("Invalid", .{}),
            };
        },
        @enumToInt(RV32I_OPCODE.FENCE) => {
            @import("std").debug.panic("Unimplemented", .{});
        },
        @enumToInt(RV32I_OPCODE.SYSTEM) => {
            // I-Type
            const rd = decode_rd(ins);
            const rs1 = decode_rs1(ins);
            const imm = decode_i_imm(ins);
            return switch (ins & MASK_FUNCT3) {
                @enumToInt(SYSTEM_FUNCT3.PRIV) << SHIFT_FUNCT3 => {
                    return switch (ins & MASK_7_31) {
                        @enumToInt(PRIV_7_31.ECALL) << 7 => self.op_ecall(),
                        @enumToInt(PRIV_7_31.EBREAK) << 7 => self.op_ebreak(),
                        else => @import("std").debug.panic("Invalid", .{}),
                    };
                },
                @enumToInt(SYSTEM_FUNCT3.CSRRW) << SHIFT_FUNCT3 => self.op_csrrw(rd, rs1, imm),
                @enumToInt(SYSTEM_FUNCT3.CSRRS) << SHIFT_FUNCT3 => self.op_csrrs(rd, rs1, imm),
                @enumToInt(SYSTEM_FUNCT3.CSRRC) << SHIFT_FUNCT3 => self.op_csrrc(rd, rs1, imm),
                @enumToInt(SYSTEM_FUNCT3.CSRRWI) << SHIFT_FUNCT3 => self.op_csrrwi(rd, rs1, imm),
                @enumToInt(SYSTEM_FUNCT3.CSRRSI) << SHIFT_FUNCT3 => self.op_csrrsi(rd, rs1, imm),
                @enumToInt(SYSTEM_FUNCT3.CSRRCI) << SHIFT_FUNCT3 => self.op_csrrci(rd, rs1, imm),
                else => @import("std").debug.panic("Invalid {b:0>3}", .{(ins & MASK_FUNCT3) >> SHIFT_FUNCT3}),
            };
        },
        else => {
            @import("std").debug.panic("Invalid {b:0>7}", .{ins & MASK_OPCODE});
        },
    }
    @import("std").debug.panic("Unreachable", .{});
}

const Decoder = struct {
    const Self = @This();
    const ReturnType = Instruction;

    fn i_type(op: Opcode, rd: u8, rs1: u8, imm: i32) Instruction {
        return Instruction{ .op = op, .rd = rd, .rs1 = rs1, .rs2 = 0, .imm = imm };
    }
    fn u_type(op: Opcode, rd: u8, imm: i32) Instruction {
        return Instruction{ .op = op, .rd = rd, .rs1 = 0, .rs2 = 0, .imm = imm };
    }
    fn r_type(op: Opcode, rd: u8, rs1: u8, rs2: u8) Instruction {
        return Instruction{ .op = op, .rd = rd, .rs1 = rs1, .rs2 = rs2, .imm = 0 };
    }
    fn j_type(op: Opcode, rd: u8, imm: i32) Instruction {
        return Instruction{ .op = op, .rd = rd, .rs1 = 0, .rs2 = 0, .imm = imm };
    }
    fn b_type(op: Opcode, rs1: u8, rs2: u8, imm: i32) Instruction {
        return Instruction{ .op = op, .rd = 0, .rs1 = rs1, .rs2 = rs2, .imm = imm };
    }
    fn s_type(op: Opcode, rs1: u8, rs2: u8, imm: i32) Instruction {
        return Instruction{ .op = op, .rd = 0, .rs1 = rs1, .rs2 = rs2, .imm = imm };
    }

    fn op_addi(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.ADDI, rd, rs1, imm);
    }
    fn op_slti(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.SLTI, rd, rs1, imm);
    }
    fn op_sltiu(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.SLTIU, rd, rs1, imm);
    }
    fn op_andi(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.ANDI, rd, rs1, imm);
    }
    fn op_ori(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.ORI, rd, rs1, imm);
    }
    fn op_xori(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.XORI, rd, rs1, imm);
    }
    fn op_slli(self: *Self, rd: u8, rs1: u8, shamt: u8) Instruction {
        _ = self;
        return i_type(.SLLI, rd, rs1, @intCast(i32, shamt));
    }
    fn op_srli(self: *Self, rd: u8, rs1: u8, shamt: u8) Instruction {
        _ = self;
        return i_type(.SRLI, rd, rs1, @intCast(i32, shamt));
    }
    fn op_srai(self: *Self, rd: u8, rs1: u8, shamt: u8) Instruction {
        _ = self;
        return i_type(.SRAI, rd, rs1, @intCast(i32, shamt));
    }
    fn op_lui(self: *Self, rd: u8, imm: i32) Instruction {
        _ = self;
        return u_type(.LUI, rd, imm);
    }
    fn op_auipc(self: *Self, rd: u8, imm: i32) Instruction {
        _ = self;
        return u_type(.AUIPC, rd, imm);
    }
    fn op_add(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.ADD, rd, rs1, rs2);
    }
    fn op_sub(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SUB, rd, rs1, rs2);
    }
    fn op_slt(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SLT, rd, rs1, rs2);
    }
    fn op_sltu(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SLTU, rd, rs1, rs2);
    }
    fn op_and(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.AND, rd, rs1, rs2);
    }
    fn op_or(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.OR, rd, rs1, rs2);
    }
    fn op_xor(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.XOR, rd, rs1, rs2);
    }
    fn op_sll(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SLL, rd, rs1, rs2);
    }
    fn op_srl(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SRL, rd, rs1, rs2);
    }
    fn op_sra(self: *Self, rd: u8, rs1: u8, rs2: u8) Instruction {
        _ = self;
        return r_type(.SRA, rd, rs1, rs2);
    }
    fn op_jal(self: *Self, rd: u8, imm: i32) Instruction {
        _ = self;
        return j_type(.JAL, rd, imm);
    }
    fn op_jalr(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.JALR, rd, rs1, imm);
    }
    fn op_beq(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_bne(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_blt(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_bltu(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_bge(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_bgeu(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return b_type(.BEQ, rs1, rs2, imm);
    }
    fn op_lw(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.BEQ, rd, rs1, imm);
    }
    fn op_lh(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.BEQ, rd, rs1, imm);
    }
    fn op_lhu(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.BEQ, rd, rs1, imm);
    }
    fn op_lb(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.BEQ, rd, rs1, imm);
    }
    fn op_lbu(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.BEQ, rd, rs1, imm);
    }
    fn op_sw(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return s_type(.BEQ, rs1, rs2, imm);
    }
    fn op_sh(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return s_type(.BEQ, rs1, rs2, imm);
    }
    fn op_sb(self: *Self, rs1: u8, rs2: u8, imm: i32) Instruction {
        _ = self;
        return s_type(.BEQ, rs1, rs2, imm);
    }
    fn op_ecall(self: *Self) Instruction {
        _ = self;
        return Instruction{ .op = .ECALL, .rd = 0, .rs1 = 0, .rs2 = 0, .imm = 0 };
    }
    fn op_ebreak(self: *Self) Instruction {
        _ = self;
        return Instruction{ .op = .EBREAK, .rd = 0, .rs1 = 0, .rs2 = 0, .imm = 0 };
    }
    fn op_csrrw(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRW, rd, rs1, imm);
    }
    fn op_csrrs(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRS, rd, rs1, imm);
    }
    fn op_csrrc(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRC, rd, rs1, imm);
    }
    fn op_csrrwi(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRWI, rd, rs1, imm);
    }
    fn op_csrrsi(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRSI, rd, rs1, imm);
    }
    fn op_csrrci(self: *Self, rd: u8, rs1: u8, imm: i32) Instruction {
        _ = self;
        return i_type(.CSRRCI, rd, rs1, imm);
    }
};

const Cpu = struct {
    const Self = @This();
    const ReturnType = void;

    // Registers from x0-x31.
    // 'zero' is an alias to x0 and it is hardwired to the value '0'.
    // Standard calling conventions:
    // - x1: return address for a call
    // - x2: stack pointer
    // - x5: alternative link register
    x: [32]u32,
    // Program counter
    pc: u32,

    pub fn init() Self {
        var self = Self{
            .x = [_]u32{0} ** 32,
            .pc = 0,
        };
        return self;
    }

    fn decode_ins(ins: u32) Instruction {
        var decoder = Decoder{};
        return decode(Decoder, &decoder, ins);
    }

    fn decode_exec(self: *Self, ins: u32) void {
        return decode(Self, self, ins);
    }

    fn mem_read_8(self: *Self, addr: u32) u8 {
        _ = self;
        _ = addr;
        return 0;
    }
    fn mem_read_16(self: *Self, addr: u32) u16 {
        _ = self;
        _ = addr;
        return 0;
    }
    fn mem_read_32(self: *Self, addr: u32) u32 {
        _ = self;
        _ = addr;
        return 0;
    }
    fn mem_write_8(self: *Self, addr: u32, value: u8) void {
        _ = self;
        _ = addr;
        _ = value;
    }
    fn mem_write_16(self: *Self, addr: u32, value: u16) void {
        _ = self;
        _ = addr;
        _ = value;
    }
    fn mem_write_32(self: *Self, addr: u32, value: u32) void {
        _ = self;
        _ = addr;
        _ = value;
    }

    fn op_addi(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] + @intCast(u32, imm);
        self.pc += 4;
    }

    fn op_slti(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = if (@intCast(i32, self.x[rs1]) < imm) 1 else 0;
        self.pc += 4;
    }
    fn op_sltiu(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = if (self.x[rs1] < @intCast(u32, imm)) 1 else 0;
        self.pc += 4;
    }

    fn op_andi(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] & @intCast(u32, imm);
        self.pc += 4;
    }
    fn op_ori(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] | @intCast(u32, imm);
        self.pc += 4;
    }
    fn op_xori(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] ^ @intCast(u32, imm);
        self.pc += 4;
    }

    fn op_slli(self: *Self, rd: u8, rs1: u8, shamt: u8) void {
        self.x[rd] = self.x[rs1] << @intCast(u5, shamt);
        self.pc += 4;
    }
    fn op_srli(self: *Self, rd: u8, rs1: u8, shamt: u8) void {
        self.x[rd] = self.x[rs1] >> @intCast(u5, shamt);
        self.pc += 4;
    }
    fn op_srai(self: *Self, rd: u8, rs1: u8, shamt: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, @intCast(i32, self.x[rs1]) >> @intCast(u5, shamt));
        self.pc += 4;
    }

    fn op_lui(self: *Self, rd: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, imm);
        self.pc += 4;
    }
    fn op_auipc(self: *Self, rd: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, @intCast(i32, self.pc) + imm);
        self.pc += 4;
    }

    fn op_add(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] + self.x[rs2];
        self.pc += 4;
    }
    fn op_sub(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] - self.x[rs2];
        self.pc += 4;
    }
    fn op_slt(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = if (@intCast(i32, self.x[rs1]) < @intCast(i32, self.x[rs2])) 1 else 0;
        self.pc += 4;
    }
    fn op_sltu(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = if (self.x[rs1] < self.x[rs2]) 1 else 0;
        self.pc += 4;
    }
    fn op_and(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] & self.x[rs2];
        self.pc += 4;
    }
    fn op_or(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] | self.x[rs2];
        self.pc += 4;
    }
    fn op_xor(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.x[rs1] ^ self.x[rs2];
        self.pc += 4;
    }

    fn op_sll(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        self.x[rd] = self.x[rs1] << @intCast(u5, self.x[rs2] & 0b11111);
        self.pc += 4;
    }
    fn op_srl(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        self.x[rd] = self.x[rs1] >> @intCast(u5, self.x[rs2] & 0b11111);
        self.pc += 4;
    }
    fn op_sra(self: *Self, rd: u8, rs1: u8, rs2: u8) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, @intCast(i32, self.x[rs1]) >> @intCast(u5, self.x[rs2] & 0b11111));
        self.pc += 4;
    }

    fn op_jal(self: *Self, rd: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.pc + 4;
        self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
    }
    fn op_jalr(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.pc + 4;
        self.pc = @intCast(u32, @intCast(i32, self.x[rs1]) + imm) & 0b11111111111111111111111111111110;
    }

    fn op_beq(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (self.x[rs1] == self.x[rs2]) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }
    fn op_bne(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (self.x[rs1] != self.x[rs2]) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }
    fn op_blt(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (@intCast(i32, self.x[rs1]) < @intCast(i32, self.x[rs2])) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }
    fn op_bltu(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (self.x[rs1] < self.x[rs2]) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }
    fn op_bge(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (@intCast(i32, self.x[rs1]) >= @intCast(i32, self.x[rs2])) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }
    fn op_bgeu(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        @setRuntimeSafety(false);
        if (self.x[rs1] >= self.x[rs2]) {
            self.pc = @intCast(u32, @intCast(i32, self.pc) + imm);
        } else {
            self.pc += 4;
        }
    }

    fn op_lw(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = self.mem_read_32(@intCast(u32, @intCast(i32, self.x[rs1]) + imm));
    }
    fn op_lh(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, @intCast(i32, @intCast(i16, self.mem_read_16(@intCast(u32, @intCast(i32, self.x[rs1]) + imm)))));
    }
    fn op_lhu(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, self.mem_read_16(@intCast(u32, @intCast(i32, self.x[rs1]) + imm)));
    }
    fn op_lb(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, @intCast(i32, @intCast(i8, self.mem_read_8(@intCast(u32, @intCast(i32, self.x[rs1]) + imm)))));
    }
    fn op_lbu(self: *Self, rd: u8, rs1: u8, imm: i32) void {
        @setRuntimeSafety(false);
        self.x[rd] = @intCast(u32, self.mem_read_8(@intCast(u32, @intCast(i32, self.x[rs1]) + imm)));
    }

    fn op_sw(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        self.mem_write_32(@intCast(u32, @intCast(i32, self.x[rs1]) + imm), self.x[rs2]);
    }
    fn op_sh(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        self.mem_write_16(@intCast(u32, @intCast(i32, self.x[rs1]) + imm), @intCast(u16, self.x[rs2] & 0x0000ffff));
    }
    fn op_sb(self: *Self, rs1: u8, rs2: u8, imm: i32) void {
        self.mem_write_8(@intCast(u32, @intCast(i32, self.x[rs1]) + imm), @intCast(u8, self.x[rs2] & 0x000000ff));
    }

    // TODO: op_fence
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    std.debug.print("Arguments: {s}\n", .{args});

    const rom_path = args[1];
    var rom_file = try std.fs.cwd().openFile(rom_path, .{ .mode = .read_only });
    defer rom_file.close();

    var buf: [4]u8 = undefined;
    try rom_file.seekTo(0);
    while (true) {
        const read = try rom_file.read(&buf);
        if (read != buf.len) {
            break;
        }
        const word = std.mem.readInt(u32, &buf, .Little);
        std.debug.print("0b{b:0>32} ", .{word});
        const ins = Cpu.decode_ins(word);
        std.debug.print("{}\n", .{ins});
    }
}

const expectEqual = std.testing.expectEqual;

test "decode imm" {
    @setRuntimeSafety(false);
    var v: u32 = undefined;
    v = 0b00000000000000000000011111111111;
    try expectEqual(@intCast(i32, v), Cpu.decode_i_imm(0b01111111111100000000000000000000));
    v = 0b11111111111111111111111111111111;
    try expectEqual(@intCast(i32, v), Cpu.decode_i_imm(0b11111111111100000000000000000000));

    v = 0b00000000000000000000011111111111;
    try expectEqual(@intCast(i32, v), Cpu.decode_s_imm(0b01111110000000000000111110000000));
    v = 0b00000000000000000000011111011111;
    try expectEqual(@intCast(i32, v), Cpu.decode_s_imm(0b01111100000000000000111110000000));
    v = 0b11111111111111111111111111111111;
    try expectEqual(@intCast(i32, v), Cpu.decode_s_imm(0b11111110000000000000111110000000));

    v = 0b11111111111111111111000000000000;
    try expectEqual(@intCast(i32, v), Cpu.decode_u_imm(0b11111111111111111111000000000000));
    v = 0b01111111111111111111000000000000;
    try expectEqual(@intCast(i32, v), Cpu.decode_u_imm(0b01111111111111111111000000000000));

    v = 0b11111111111111111111111111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_b_imm(0b11111110000000000000111110000000));
    v = 0b00000000000000000000111111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_b_imm(0b01111110000000000000111110000000));
    v = 0b00000000000000000000011111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_b_imm(0b01111110000000000000111100000000));
    v = 0b00000000000000000000011111111100;
    try expectEqual(@intCast(i32, v), Cpu.decode_b_imm(0b01111110000000000000111000000000));
    v = 0b00000000000000000000011111011100;
    try expectEqual(@intCast(i32, v), Cpu.decode_b_imm(0b01111100000000000000111000000000));

    v = 0b11111111111111111111111111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_j_imm(0b11111111111111111111000000000000));
    v = 0b00000000000011111111111111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_j_imm(0b01111111111111111111000000000000));
    v = 0b00000000000001111111111111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_j_imm(0b01111111111101111111000000000000));
    v = 0b00000000000001111111011111111110;
    try expectEqual(@intCast(i32, v), Cpu.decode_j_imm(0b01111111111001111111000000000000));
    v = 0b00000000000001111111011111111100;
    try expectEqual(@intCast(i32, v), Cpu.decode_j_imm(0b01111111110001111111000000000000));
}

test "instructions" {
    var cpu = Cpu.init();
    cpu.x[2] = 2;
    cpu.op_addi(1, 2, 3);
    try expectEqual(@as(u32, 5), cpu.x[1]);

    cpu.op_srai(1, 2, 3);
}

test "decode_exec" {
    var cpu = Cpu.init();
    cpu.decode_exec(123);
}

test "decode0" {
    const ins = Cpu.decode_ins(0b00000000011001000000000110110011);
    std.debug.print("{}\n", .{ins});
}
