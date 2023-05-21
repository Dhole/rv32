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
    fn decode_rd(ins: u32) u8 {
        return @intCast(ins & 0b00000000000000000000111110000000 >> 6, u8);
    }
    fn decode_funct3(ins: u32) u8 {
        return @intCast(ins & 0b00000000000000000111000000000000 >> 11, u8);
    }
    fn decode_rs1(ins: u32) u8 {
        return @intCast(ins & 0b00000000000011111000000000000000 >> 14, u8);
    }
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
