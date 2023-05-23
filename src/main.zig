const std = @import("std");

const Cpu = struct {
    const Self = @This();

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

    fn decode_opcode(ins: u32) u8 {
        return @intCast(ins & 0b00000000000000000000000001111111, u8);
    }
    // 'rd' is register destination
    fn decode_rd(ins: u32) u8 {
        return @intCast(ins & 0b00000000000000000000111110000000 >> 6, u8);
    }
    fn decode_funct3(ins: u32) u8 {
        return @intCast(ins & 0b00000000000000000111000000000000 >> 11, u8);
    }
    // 'rs1' is register source 1
    fn decode_rs1(ins: u32) u8 {
        return @intCast(ins & 0b00000000000011111000000000000000 >> 14, u8);
    }
    // 'rs1' is register source 2
    fn decode_rs2(ins: u32) u8 {
        return @intCast(ins & 0b00000001111100000000000000000000 >> 19, u8);
    }
    fn decode_funct7(ins: u32) u8 {
        return @intCast(ins & 0b11111110000000000000000000000000 >> 24, u8);
    }
    // 12 bits, sign-extended
    fn decode_i_imm(ins: u32) i32 {
        @setRuntimeSafety(false);
        return @intCast(i32, ins & 0b11111111111100000000000000000000) >> (19 + 1);
    }
    // 12 bits, sign-extended
    fn decode_s_imm(ins: u32) i32 {
        @setRuntimeSafety(false);
        return @intCast(i32, ins & 0b11111110000000000000000000000000) >> (24 - 5 + 1) |
            @intCast(i32, ins & 0b00000000000000000000111110000000) >> 6 + 1;
    }
    // 32 bits, sign-extended
    fn decode_u_imm(ins: u32) i32 {
        @setRuntimeSafety(false);
        return @intCast(i32, ins & 0b11111111111111111111000000000000);
    }
    // 12 bits, sign-extended
    fn decode_b_imm(ins: u32) i32 {
        @setRuntimeSafety(false);
        return @intCast(i32, ins & 0b10000000000000000000000000000000) >> (30 - 12 + 1) |
            @intCast(i32, ins & 0b01111110000000000000000000000000) >> (24 - 5 + 1) |
            @intCast(i32, ins & 0b00000000000000000000111100000000) >> (7 - 1 + 1) |
            @intCast(i32, ins & 0b00000000000000000000000010000000) << -(6 - 11 + 1);
    }
    // 32 bits, sign-extended
    fn decode_j_imm(ins: u32) i32 {
        @setRuntimeSafety(false);
        return @intCast(i32, ins & 0b10000000000000000000000000000000) >> (30 - 20 + 1) |
            @intCast(i32, ins & 0b01111111111000000000000000000000) >> (20 - 1 + 1) |
            @intCast(i32, ins & 0b00000000000100000000000000000000) >> (19 - 11 + 1) |
            @intCast(i32, ins & 0b00000000000011111111000000000000) >> (11 - 12 + 1);
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
};

pub fn main() !void {
    {
        @setRuntimeSafety(false);
        // var a: u32 = 0b11111110000000000000000000000000;
        var a: u32 = 0b11000000000000000000000000000000;
        var b: u32 = 0b11110000000000000000000000000000;
        std.debug.print("Hello, {d}!\n", .{@intCast(i32, a) & 0b01000000000000000000000000000000});
        std.debug.print("Hello, {d}!\n", .{@intCast(i32, b)});
        std.debug.print("Hello, {d}!\n", .{@intCast(i32, a) >> 2});
        // std.debug.print("Hello, {b}!\n", .{@ptrCast(*i32, &a).* >> 0});
        // std.debug.print("Hello, {b}!\n", .{@ptrCast(*i32, &a).* >> 1});
        // std.debug.print("Hello, {b}!\n", .{@ptrCast(*i32, &a).* >> 2});
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
