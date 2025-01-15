package main

import "base:intrinsics"
import "core:fmt"
import "core:log"
import "core:math"
import "core:mem"
import "core:slice"
import "core:strconv"
import "core:testing"

@(test)
test_stop :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{u8(Opcode.STOP)}
	memory := [dynamic]byte{}
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)
	assert(run(&vm) == .Stop)
}

@(test)
test_add :: proc(t: ^testing.T) {
	push32_addend: [32]byte = 0xff

	bytecode: [dynamic]byte
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0x0a)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0x0a)
	append(&bytecode, u8(Opcode.ADD))
	append(&bytecode, u8(Opcode.PUSH32))
	append(&bytecode, ..push32_addend[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.ADD))
	append(&bytecode, u8(Opcode.STOP))

	memory := [dynamic]byte{}
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)
	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)

	res := stack_pop(&vm.stack)

	assert(res == U256{0, 0, 0, 0})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 20})
}

@(test)
test_push :: proc(t: ^testing.T) {

	push1_test: [1]byte = 1
	push2_test: [2]byte = 1
	push4_test: [4]byte = 1
	push16_test: [16]byte = 1
	push32_test: [32]byte = 1

	Push_Test :: struct {
		opcode:   Opcode,
		to_push:  []byte,
		expected: U256,
	}

	tests := []Push_Test {
		{Opcode.PUSH1, push1_test[:], U256{0, 0, 0, 0x1}},
		{Opcode.PUSH2, push2_test[:], U256{0, 0, 0, 0x0101}},
		{Opcode.PUSH4, push4_test[:], U256{0, 0, 0, 0x01010101}},
		{Opcode.PUSH16, push16_test[:], U256{0, 0, 0x0101010101010101, 0x0101010101010101}},
		{
			Opcode.PUSH32,
			push32_test[:],
			U256{0x0101010101010101, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101},
		},
	}


	for test in tests {
		bytecode := [dynamic]byte{}
		append(&bytecode, u8(test.opcode))
		append(&bytecode, ..test.to_push)
		append(&bytecode, u8(Opcode.STOP))


		memory := [dynamic]byte{}
		vm := make_vm(bytecode[:], memory)
		defer destroy(&vm)

		assert(run(&vm) == .Stop)
		assert(vm.gas_used == 21003)
		assert(stack_pop(&vm.stack) == test.expected)
	}

}

@(test)
test_dup :: proc(t: ^testing.T) {
	//Each DUPN test consists of a single (PUSH1, 1) instruction and (N-1) (PUSH1, 0) instructions.
	gen_dup_bytecode :: proc(n: int) -> [dynamic]byte {
		bytecode := [dynamic]byte{}
		append(&bytecode, u8(Opcode.PUSH1))
		append(&bytecode, 1)
		for i in 0 ..< n - 1 {
			append(&bytecode, u8(Opcode.PUSH1))
			append(&bytecode, 0)
		}

		return bytecode
	}

	Dup_Test :: struct {
		opcode: Opcode,
		n:      int,
	}

	tests := []Dup_Test {
		{Opcode.DUP1, 1},
		{Opcode.DUP2, 2},
		{Opcode.DUP8, 8},
		{Opcode.DUP12, 12},
		{Opcode.DUP16, 16},
	}

	for test in tests {
		bytecode := [dynamic]byte{}
		gen_dup_bytecode := gen_dup_bytecode(test.n)
		defer delete(gen_dup_bytecode)
		append(&bytecode, ..gen_dup_bytecode[:])
		append(&bytecode, u8(test.opcode))
		append(&bytecode, u8(Opcode.STOP))

		vm := make_vm(bytecode[:], {})
		defer destroy(&vm)

		expected_gas_used := vm.gas_used + verylow + verylow * (test.n)
		assert(run(&vm) == .Stop)
		assert(vm.gas_used == expected_gas_used)
		assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
	}

}


@(test)
test_swap :: proc(t: ^testing.T) {

	Swap_Test :: struct {
		opcode: Opcode,
		n:      int,
	}

	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 2)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.SWAP4))
	append(&bytecode, u8(Opcode.STOP))

	memory := [dynamic]byte{}
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)
	assert(vm.stack.data[len(vm.stack.data) - 5] == U256{0, 0, 0, 1})
	assert(vm.stack.data[len(vm.stack.data) - 1] == U256{0, 0, 0, 2})

}

@(test)
test_byte :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0xff)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 31)
	append(&bytecode, u8(Opcode.BYTE))
	append(&bytecode, u8(Opcode.PUSH2))
	append(&bytecode, ..[]byte{0x00, 0xff})
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 30)
	append(&bytecode, u8(Opcode.BYTE))
	append(&bytecode, u8(Opcode.STOP))

	memory := [dynamic]byte{}
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)

	v := stack_pop(&vm.stack)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0xff})
}


@(test)
test_mload :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}
	push32: [32]byte = {
		0 ..< 31   = 0,
		31 = 0xff,
	}
	append(&bytecode, u8(Opcode.PUSH32))
	append_elems(&bytecode, ..push32[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MSTORE))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MLOAD))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.MLOAD))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21027)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0xff00})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0xff})

}

@(test)
test_mstore :: proc(t: ^testing.T) {
	expected_memory: [64]byte = {
		0 ..= 31   = 0,
		32 = 0xFF,
		33 ..< 64   = 0,
	}

	bytecode := [dynamic]byte{}
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0xff)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MSTORE))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0xff)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.MSTORE))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte

	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21024)
	assert(slice.equal(vm.memory[:], expected_memory[:]))


}

@(test)
test_mstore8 :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	expected_memory: [32]byte = {
		0 ..= 1 = 0xFF,
		2 ..= 31 = 0,
	}
	append(&bytecode, u8(Opcode.PUSH2))
	append(&bytecode, ..[]byte{0xFF, 0xFF})
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MSTORE8))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0xFF)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.MSTORE8))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte

	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21021)
	assert(slice.equal(vm.memory[:], expected_memory[:]))

	clear(&bytecode)
}

@(test)
test_mcopy :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}
	expected := hex("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
	append(&bytecode, u8(Opcode.PUSH32))
	append(&bytecode, ..expected[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 32)
	append(&bytecode, u8(Opcode.MSTORE))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 32)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 32)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MCOPY))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte

	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21030)
	assert(slice.equal(vm.memory[0:32], expected[:]))
	assert(slice.equal(vm.memory[32:64], expected[:]))

	clear(&bytecode)

}

@(test)
test_div :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.DIV))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 2)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.DIV))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21022)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})

}

@(test)
test_sdiv :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.SDIV))

	bytes_1: [32]byte = 0xff
	bytes_2: [32]byte = {
		0 ..= 30   = 0xff,
		31 = 0xfe,
	}
	append(&bytecode, u8(Opcode.PUSH32))
	append_elems(&bytecode, ..bytes_1[:])
	append(&bytecode, u8(Opcode.PUSH32))
	append_elems(&bytecode, ..bytes_2[:])
	append(&bytecode, u8(Opcode.SDIV))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21022)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 2})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
}


@(test)
test_mod :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 3)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.MOD))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 5)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 17)
	append(&bytecode, u8(Opcode.MOD))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21022)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 2})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
}

@(test)
test_smod :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 3)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 10)
	append(&bytecode, u8(Opcode.SMOD))
	append(&bytecode, u8(Opcode.PUSH32))

	bytes1: [32]byte = {
		0 ..= 30   = 0xff,
		31 = 0xfd,
	}
	append(&bytecode, ..bytes1[:])
	append(&bytecode, u8(Opcode.PUSH32))
	bytes2: [32]byte = {
		0 ..= 30   = 0xff,
		31 = 0xf8,
	}
	append(&bytecode, ..bytes2[:])
	append(&bytecode, u8(Opcode.SMOD))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21022)
	assert(stack_pop(&vm.stack) == U256{max(u64), max(u64), max(u64), 0xfffffffffffffffe})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
}

@(test)
test_shl :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.SHL))
	push32: [32]byte = {
		0 = 0xff,
		1 ..= 31  = 0,
	}
	append(&bytecode, u8(Opcode.PUSH32))
	append_elems(&bytecode, ..push32[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 4)
	append(&bytecode, u8(Opcode.SHL))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)
	assert(stack_pop(&vm.stack) == U256{0xf000000000000000, 0, 0, 0})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 2})
}

@(test)
test_shr :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 2)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.SHR))
	append(&bytecode, u8(Opcode.PUSH1))
	append_elems(&bytecode, 0xff)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 4)
	append(&bytecode, u8(Opcode.SHR))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0xf})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
}

@(test)
test_sar :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 2)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 1)
	append(&bytecode, u8(Opcode.SAR))
	push32: [32]byte = {
		0 ..= 30   = 0xff,
		31 = 0xf0,
	}
	append(&bytecode, u8(Opcode.PUSH32))
	append_elems(&bytecode, ..push32[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 4)
	append(&bytecode, u8(Opcode.SAR))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)
	assert(stack_pop(&vm.stack) == max_U256())
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
}

@(test)
test_keccak :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.PUSH32))
	push32: [32]byte = {
		0 ..= 3 = 0xff,
		4 ..= 31 = 0x00,
	}
	append_elems(&bytecode, ..push32[:])
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.MSTORE))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 4)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.KECCAK256))

	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21054)
	assert(
		stack_pop(&vm.stack) ==
		U256{0x29045a592007d0c2, 0x46ef02c2223570da, 0x9522d0cf0f73282c, 0x79a1bc8f0bb2c238},
	)
}

@(test)
test_address :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.ADDRESS))
	append(&bytecode, u8(Opcode.STOP))

	vm := make_vm(bytecode[:], {})
	defer destroy(&vm)
	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21002)
	assert(stack_pop(&vm.stack) == U256{0, 0x69696969, 0x6969696969696969, 0x6969696969696969})
}

@(test)
test_balance :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.ADDRESS))
	append(&bytecode, u8(Opcode.BALANCE))
	append(&bytecode, u8(Opcode.STOP))

	vm := make_vm(bytecode[:], {})
	defer destroy(&vm)
	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21102)
	assert(stack_pop(&vm.stack) == 69)
}

@(test)
test_call_data_load :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	call_data := Call_Data {
		0 ..= 31 = 0xFF,
	}

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.CALLDATALOAD))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 31)
	append(&bytecode, u8(Opcode.CALLDATALOAD))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	tx_env := Transaction_Context {
		call_data = call_data,
		gas_price = 1,
	}
	vm := make_vm(bytecode[:], memory, 200_000, tx_env = tx_env)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21524)
	assert(stack_pop(&vm.stack) == U256{0xff00000000000000, 0, 0, 0})
	assert(stack_pop(&vm.stack) == max_U256())

}

@(test)
test_call_data_size :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	call_data := Call_Data{0xFF}

	append(&bytecode, u8(Opcode.CALLDATASIZE))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	tx_env := Transaction_Context {
		call_data = call_data,
		gas_price = 1,
	}
	vm := make_vm(bytecode[:], memory, 200_000, tx_env = tx_env)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21018)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})

}

@(test)
test_call_data_copy :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	call_data := Call_Data {
		0 ..= 31 = 0xFF,
	}
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 32)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.CALLDATACOPY))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 8)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 31)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.CALLDATACOPY))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	tx_env := Transaction_Context {
		call_data = call_data,
		gas_price = 1,
	}
	vm := make_vm(bytecode[:], memory, 200_000, tx_env = tx_env)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21545)
	assert(slice.equal(vm.memory[:], []byte{0 = 0xff, 1 ..= 7 = 0, 8 ..= 31 = 0xff}))
}

@(test)
test_code_size :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}
	memory: [dynamic]byte

	code := [?]byte {
		0 ..< 29 = 0,
	}
	append(&bytecode, u8(Opcode.PUSH29))
	append(&bytecode, ..code[:])
	append(&bytecode, u8(Opcode.CODESIZE))
	append(&bytecode, u8(Opcode.STOP))
	vm := make_vm(bytecode[:], memory, 200_000)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21005)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0x20})
}

@(test)
test_code_copy :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}
	memory: [dynamic]byte

	code_1 := [30]byte {
		0 ..< 30 = 0xFF,
	}
	append(&bytecode, u8(Opcode.PUSH30))
	append(&bytecode, ..code_1[:])
	code_2 := [?]byte {
		0 ..< 32 = 0,
	}
	append(&bytecode, u8(Opcode.PUSH32))
	append(&bytecode, ..code_2[:])
	append(&bytecode, u8(Opcode.POP))
	append(&bytecode, u8(Opcode.POP))

	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 32)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.CODECOPY))
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 8)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 31)
	append(&bytecode, u8(Opcode.PUSH1))
	append(&bytecode, 0)
	append(&bytecode, u8(Opcode.CODECOPY))
	append(&bytecode, u8(Opcode.STOP))

	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)
	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21043, "Wrong gas calculation")
	assert(slice.equal(vm.memory[:], []byte{0 = 0x7f, 1 ..= 7 = 0, 8 ..< 31 = 0xff, 31 = 0x7f}))
}

test_gas :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	bytes: [3]byte
	copy(bytes[:], mem.any_to_bytes(21000))

	append(&bytecode, u8(Opcode.GAS))
	append(&bytecode, u8(Opcode.PUSH3))
	append(&bytecode, ..bytes[:])
	append(&bytecode, u8(Opcode.GASLIMIT))
	append(&bytecode, u8(Opcode.SUB))
	append(&bytecode, u8(Opcode.SUB))
	append(&bytecode, u8(Opcode.STOP))

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21013)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 2})

}


@(test)
test_gas_limit :: proc(t: ^testing.T) {
	bytecode := [dynamic]byte{}

	append(&bytecode, u8(Opcode.GASLIMIT))
	append(&bytecode, u8(Opcode.STOP))
	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21002)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, u64(DEFAULT_GAS_LIMIT)})
}

@(test)
test_jump :: proc(t: ^testing.T) {
	Jump_Test :: struct {
		description: string,
		bytecode:    []byte,
		err:         Error,
		gas_used:    int,
	}

	tests := []Jump_Test {
		{
			description = "valid jump",
			bytecode = []byte {
				u8(Opcode.PUSH1),
				4,
				u8(Opcode.JUMP),
				u8(Opcode.INVALID),
				u8(Opcode.JUMPDEST),
				u8(Opcode.PUSH1),
				1,
				u8(Opcode.STOP),
			},
			err = .Stop,
			gas_used = 21015,
		},
		{
			description = "invalid jump",
			bytecode = []byte {
				u8(Opcode.PUSH1),
				3,
				u8(Opcode.JUMP),
				u8(Opcode.MSIZE),
				u8(Opcode.INVALID),
				u8(Opcode.STOP),
			},
			err = .InvalidJump,
			gas_used = 21011,
		},
	}


	for test in tests {
		bytecode := [dynamic]byte{}
		for byte in test.bytecode {
			append(&bytecode, byte)
		}
		memory: [dynamic]byte
		vm := make_vm(bytecode[:], memory)
		defer destroy(&vm)

		assert(run(&vm) == test.err)
		assert(vm.gas_used == test.gas_used)
	}
}

@(test)
test_jumpi :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.PUSH1),
		10,
		u8(Opcode.JUMPI),
		u8(Opcode.PUSH1),
		1,
		u8(Opcode.PUSH1),
		12,
		u8(Opcode.JUMPI),
		u8(Opcode.JUMPDEST),
		u8(Opcode.INVALID),
		u8(Opcode.JUMPDEST),
		u8(Opcode.PUSH1),
		1,
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21036)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})

	clear(&bytecode)
}

@(test)
test_pc :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PC),
		u8(Opcode.PC),
		u8(Opcode.JUMPDEST),
		u8(Opcode.PC),
		u8(Opcode.PUSH1),
		1,
		u8(Opcode.PC),
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)

	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21012)
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 6})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 3})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 1})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0})

	clear(&bytecode)
}


@(test)
test_sstore :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PUSH2),
		0xff,
		0xff,
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.SSTORE),
		u8(Opcode.PUSH2),
		0,
		0xff,
		u8(Opcode.PUSH2),
		0x23,
		0x05,
		u8(Opcode.SSTORE),
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)


	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 65212)
	expected := [32]byte {
		0 ..= 29 = 0,
		30 ..= 31 = 0xff,
	}
	assert(vm.storage[cast(Slot)[32]byte{0 ..= 31 = 0}] == be_bytes_to_U256(expected[:]))
	expected = [32]byte {
		0 ..= 30   = 0,
		31 = 0xff,
	}
	assert(
		vm.storage[cast(Slot)[32]byte{0 ..= 29 = 0, 30 = 0x23, 31 = 0x05}] ==
		be_bytes_to_U256(expected[:]),
	)

	clear(&bytecode)
}

@(test)
test_sload :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PUSH1),
		46,
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.SSTORE),
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.SLOAD),
		u8(Opcode.PUSH1),
		1,
		u8(Opcode.SLOAD),
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)


	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 45312)
	clear(&bytecode)
	assert(stack_pop(&vm.stack) == U256{})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0x2e})
}

@(test)
test_tstore :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PUSH2),
		0xff,
		0xff,
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.TSTORE),
		u8(Opcode.PUSH2),
		0,
		0xff,
		u8(Opcode.PUSH2),
		0x23,
		0x05,
		u8(Opcode.TSTORE),
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)


	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21212)
	expected := [32]byte {
		0 ..= 29 = 0,
		30 ..= 31 = 0xff,
	}
	assert(
		vm.tx_env.transient_storage[cast(Address)[20]byte{0 ..= 19 = 0}] ==
		be_bytes_to_U256(expected[:]),
	)
	expected = [32]byte {
		0 ..= 30   = 0,
		31 = 0xff,
	}
	assert(
		vm.tx_env.transient_storage[cast(Address)[20]byte{0 ..= 17 = 0, 18 = 0x23, 19 = 0x05}] ==
		be_bytes_to_U256(expected[:]),
	)

	clear(&bytecode)
}

@(test)
test_tload :: proc(t: ^testing.T) {
	bytes := []byte {
		u8(Opcode.PUSH1),
		46,
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.TSTORE),
		u8(Opcode.PUSH1),
		0,
		u8(Opcode.TLOAD),
		u8(Opcode.PUSH1),
		1,
		u8(Opcode.TLOAD),
		u8(Opcode.STOP),
	}

	bytecode := [dynamic]byte{}
	for byte in bytes {
		append(&bytecode, byte)
	}

	memory: [dynamic]byte
	vm := make_vm(bytecode[:], memory)
	defer destroy(&vm)


	assert(run(&vm) == .Stop)
	assert(vm.gas_used == 21312)
	assert(stack_pop(&vm.stack) == U256{})
	assert(stack_pop(&vm.stack) == U256{0, 0, 0, 0x2e})

	clear(&bytecode)
}

// Prints the stack. Helpful for debugging.
print_stack :: proc(vm: ^EVM) {
	log.infof("Stack:")
	for value, i in vm.stack.data {
		log.infof("[{}] %x", i, value)
	}
	log.infof("*** END OF STACK ***\n")
}

// Prints the storage. Helpful for debugging.
print_storage :: proc(vm: ^EVM) {
	for key in vm.storage {
		key_str := ""
		log.infof("%x: %x\n", key, vm.storage[key])
	}
}
