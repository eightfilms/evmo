package main

import "base:intrinsics"
import "core:crypto/legacy/keccak"
import "core:encoding/endian"
import "core:fmt"
import "core:log"
import "core:math"
import "core:mem"
import "core:slice"
import "core:strconv"
import "core:testing"

STACK_LIMIT :: 1024

// A list of 32-byte elements used to store smart contract instruction inputs and outputs
// A single stack is created and destroyed per call context. Has a maximum of `STACK_LIMIT` items.
Stack :: struct {
	data: [dynamic]U256,
}

make_stack :: proc() -> Stack {
	data := make([dynamic]U256, 0, STACK_LIMIT)
	return Stack{data = data}

}

/// Pops the next `U256` off the `Stack`.
///
/// `pop()` panicks based on how dynamic arrays work in Odin;
/// i.e. panics if len(array) == 0.
stack_pop :: proc(stack: ^Stack) -> U256 {
	item := pop(&stack.data)
	return item
}

// Pushes a `U256` onto the `Stack`. Errors if stack overflows.
push :: proc(stack: ^Stack, item: U256) -> (err: Error) {
	if (len(stack.data) >= STACK_LIMIT) {
		return .StackOverflow
	}
	append(&stack.data, item)

	return
}

@(test)
test_stack_overflow :: proc(t: ^testing.T) {
	stack := Stack{}
	defer delete(stack.data)
	err: Error = .None
	for i in 0 ..= STACK_LIMIT {
		err = push(&stack, U256{0, 0, 0, u64(i)})
	}
	assert(err == .StackOverflow)
}

Error :: enum {
	None,
	Stop,
	OutOfGas,
	// Stack has a maximum size of `STACK_LIMIT`.
	StackOverflow,
	// An invalid jump happens when a `JUMP` instruction leads to an instruction that is not a `JUMPDEST`.
	InvalidJump,
}

// The World Computer 
EVM :: struct {
	stack:         Stack,
	// Slice of the bytecode. The EVM does not own this bytecode but merely references it.
	bytecode:      []byte,
	memory:        [dynamic]byte,
	ip:            uint,
	gas:           u64,
	gas_limit:     u64,
	gas_used:      int,
	// Transaction context. Contains things that are per-call.
	tx_env:        Transaction_Context,
	block_context: Block_Context,
	storage:       Storage,
	state_db:      State_DB,
}

// A `StateAccount` is the Ethereum consensus representation of accounts.
// These objects are stored in the main account trie.
// 
// References:
// https://github.com/ethereum/go-ethereum/blob/82e963e5c981e36dc4b607dd0685c64cf4aabea8/core/types/state_account.go#L27-L36
// https://ethereum.org/en/developers/docs/accounts/#an-account-examined
State_Account :: struct {
	nonce:        u64,
	balance:      U256,
	//AKA storage hash, a 256-bit hash of the root node of a Merkle Patricia trie
	//that encodes storage contents of the account.
	storage_root: Hash,
	//A hash that maps to the code of an account on the EVM.
	//
	//For EOAs, this is the hash of an empty string.
	code_hash:    Hash,
}

// A `State_Object` is an Ethereum account which is being modified. This is a simpler version // of a `stateObject` type found in go-ethereum.
//
// Adapted from: https://github.com/ethereum/go-ethereum/blob/82e963e5c981e36dc4b607dd0685c64cf4aabea8/core/state/state_object.go#L41-L46
State_Object :: struct {
	//Address of the Ethereum account
	address:      Address,
	//Hash of the address of the Ethereum account
	address_hash: Hash,
	//Hash of the address of the Ethereum account
	data:         State_Account,
}

// Stores anything within the merkle trie. Serves as the general query interface
// for contracts and accounts.
//
// geth requires more complex operations to interact with its state DB, but since we're
// doing a toy EVM we can mock the things here.
//
// Adapted from: https://github.com/ethereum/go-ethereum/blob/82e963e5c981e36dc4b607dd0685c64cf4aabea8/core/state/statedb.go#L68-L78
State_DB :: struct {
	state_objects: map[Address]State_Object,
}

// transientStorage is a representation of EIP-1153 "Transient Storage".
Transient_Storage :: map[Address]U256

Call_Data :: distinct []byte

Slot :: distinct [32]byte

Hash :: distinct [32]byte

Storage :: distinct map[Slot]U256

Address :: distinct [20]byte

Transaction_Context :: struct {
	address:               Address,
	value:                 u64,
	gas_price:             u64,
	call_data:             Call_Data,
	access_list_storage:   [dynamic]Slot,
	access_list_addresses: [dynamic]Address,
	transient_storage:     Transient_Storage,
}

//Contains read-only information about a block.
//Reference: https://github.com/ethereum/go-ethereum/blob/c0882429f032da58620bcaa610007939aa7e0adb/core/vm/evm.go#L48-L68
Block_Context :: struct {
	coinbase:      Address,
	block_number:  U256,
	time:          u64,
	base_fee:      U256,
	blob_base_fee: U256,
	random:        Hash,
}

//Converts a hex string into a byte array.
//
//Useful for some test cases eg. PUSH32 that appends long hex strings to the bytecode.
hex :: #force_inline proc(s: string) -> [32]byte {
	bytes: [32]byte
	assert(len(s) % 2 == 0)
	for i := 0; i < 32; i += 1 {
		b, ok := strconv.parse_int(s[i:i + 2], 16)
		assert(ok)
		assert(0 <= b && b <= 255)
		bytes[i] = byte(b)
	}
	return bytes
}
MOCK_HASH: Hash = cast(Hash)hex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
MOCK_ADDRESS: Address : Address{0 ..= 19 = 0x69}
MOCK_ACCOUNT: State_Account = State_Account {
	nonce        = 69,
	balance      = 69,
	storage_root = MOCK_HASH,
	code_hash    = MOCK_HASH,
}
MOCK_OBJECT: State_Object = State_Object {
	address = MOCK_ADDRESS,
	data    = MOCK_ACCOUNT,
}

DEFAULT_GAS_LIMIT: u64 : 500_000

// Each transaction has an intrinsic cost of 21000 gas.
INTRINSIC_GAS: int : 21_000

make_vm :: proc(
	bytecode: []byte,
	memory: [dynamic]byte,
	gas: u64 = DEFAULT_GAS_LIMIT,
	gas_limit: u64 = DEFAULT_GAS_LIMIT,
	tx_env: Transaction_Context = Transaction_Context{address = MOCK_ADDRESS},
) -> EVM {
	stack := make_stack()
	ip: uint = 0
	gas_used: int = INTRINSIC_GAS
	storage: Storage = Storage{}
	state_objects := map[Address]State_Object {
		MOCK_ADDRESS = MOCK_OBJECT,
	}
	state_db: State_DB = State_DB {
		state_objects = state_objects,
	}

	return EVM {
		stack,
		bytecode,
		memory,
		ip,
		gas,
		gas_limit,
		gas_used,
		tx_env,
		// Odin zero-inits by default. Do that here since we don't have actual blocks.
		Block_Context{},
		storage,
		state_db,
	}
}

// Frees all memory allocated for the `EVM` instance.
destroy :: proc(evm: ^EVM) {
	delete(evm.stack.data)
	delete(evm.memory)
	delete(evm.bytecode)
	delete(evm.storage)
	delete(evm.state_db.state_objects)
	delete(evm.tx_env.access_list_storage)
	delete(evm.tx_env.access_list_addresses)
	delete(evm.tx_env.transient_storage)
}


add :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_add(op0, op1)) or_return
	return
}

sub :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_sub(op0, op1)) or_return
	return
}

mul :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_mul(op0, op1)) or_return
	return
}

div :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, low) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_div(op0, op1)) or_return
	return
}

sdiv :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, low) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_sdiv(op0, op1)) or_return
	return
}

mod :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, low) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_mod(op0, op1)) or_return
	return
}

smod :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, low) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	res := U256_smod(op0, op1)
	push(&vm.stack, res) or_return
	return
}

addmod :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, mid) or_return

	op0, op1, op2 := stack_pop(&vm.stack), stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_addmod(op0, op1, op2)) or_return
	return
}

mulmod :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, mid) or_return

	op0, op1, op2 := stack_pop(&vm.stack), stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_mulmod(op0, op1, op2)) or_return
	return
}

exponent :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, high) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	push(&vm.stack, U256_exp(op0, op1)) or_return
	return
}

signextend :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, low) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)

	// no-op if size >= 31
	if (U256_gt(op0, U256{0, 0, 0, 31}) == U256{0, 0, 0, 1}) {
		push(&vm.stack, op0) or_return
		return
	}

	size := U256_to_bytes(op0)
	x := U256_to_bytes(op1)

	sign_bit := x[3] >> 7

	res := U256{}
	push(&vm.stack, res) or_return
	return
}

lt :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_lt(op0, op1)
	return
}

gt :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_gt(op0, op1)
	return
}

slt :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_slt(op0, op1)
	return
}

sgt :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_sgt(op0, op1)
	return
}

eq :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_eq(op0, op1)
	return
}

is_zero :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	res := U256{0, 0, 0, 0}

	op := stack_pop(&vm.stack)
	if (op[0] == 0 && op[1] == 0) {
		res = U256{0, 0, 0, 1}
	}
	return
}

and :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_and(op0, op1)
	return
}

or :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_or(op0, op1)
	return
}

xor :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op0, op1 := stack_pop(&vm.stack), stack_pop(&vm.stack)
	U256_xor(op0, op1)
	return
}

not :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	op := stack_pop(&vm.stack)
	U256_not(op)
	return
}

byte_op :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	i, x := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)
	bytes := U256_to_bytes(x)
	res: U256

	if i < 32 {
		res = U256{0, 0, 0, u64(bytes[i])}
	} else {
		res = U256{0, 0, 0, 0}
	}
	push(&vm.stack, res) or_return
	return
}

shl :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	shift, v := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)
	// Truncate to u8, since shift > 255 returns 0 anyway
	// NOTE: In Odin there is no need to mask with 0xff like in C.
	// gingerbill: That's just something people do in C because of C's implicit type conversions.
	// Just cast it to u8 and truncation happens.

	v_bytes := U256_to_bytes(v)
	for i in 0 ..= 31 {
		v_bytes[i] <<= shift
	}

	v = be_bytes_to_U256(v_bytes[:])
	push(&vm.stack, v) or_return
	return
}

shr :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	shift, v := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)
	// Truncate to u8, since shift > 255 returns 0 anyway
	// NOTE: In Odin there is no need to mask with 0xff like in C.
	// gingerbill: That's just something people do in C because of C's implicit type conversions.
	// Just cast it to u8 and truncation happens.

	v_bytes := U256_to_bytes(v)
	for i in 0 ..= 31 {
		v_bytes[i] >>= shift
	}

	v = be_bytes_to_U256(v_bytes[:])
	push(&vm.stack, v) or_return
	return
}

sar :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return

	shift, value := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)

	num_full_shifts := shift / (size_of(shift) * 8)
	remaining_bits := shift % (size_of(shift) * 8)


	if num_full_shifts > 3 {
		push(&vm.stack, U256{0, 0, 0, 0}) or_return
		return
	}

	result: U256 = value
	msb := value[0] >> 63

	// If full shifts they are copies of the bytes to the next byte
	for i in 0 ..< num_full_shifts {
		for j in 1 ..= 3 {
			result[4 - j] = value[3 - j]
		}
	}

	// Handle bit shifts
	for j in 1 ..= 3 {
		overflow_bits := result[3 - j] << remaining_bits
		result[4 - j] >>= remaining_bits
		result[4 - j] |= overflow_bits
	}

	push(&vm.stack, result) or_return
	return
}

keccak_ctx := keccak.Context{}

keccak_ :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, keccak256) or_return
	digest: [32]byte

	offset, size := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3]

	dynamic_gas := 6 * minimum_word_size(int(size))
	if ((offset + size) > u64(len(vm.memory))) {
		record_gas(vm, expand_memory(vm, offset, size))

	}
	record_gas(vm, dynamic_gas) or_return

	data: []u8 = vm.memory[offset:offset + size]
	keccak.init_256(&keccak_ctx)
	keccak.update(&keccak_ctx, data)
	keccak.final(&keccak_ctx, digest[:])

	result := be_bytes_to_U256(digest[:])
	push(&vm.stack, result) or_return
	return
}

block_hash :: proc(vm: ^EVM) -> (err: Error) {
	digest: [32]byte
	keccak.init_256(&keccak_ctx)
	keccak.update(&keccak_ctx, {})
	keccak.final(&keccak_ctx, digest[:])
	push(&vm.stack, bytes_to_U256(digest[:])) or_return

	return
}

push_zero :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	push(&vm.stack, 0) or_return

	return
}

address :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	address := bytes_to_U256(vm.tx_env.address[:])
	push(&vm.stack, address) or_return

	return
}

balance :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, warmaccess) or_return

	address := U256_to_address(stack_pop(&vm.stack))
	push(&vm.stack, vm.state_db.state_objects[address].data.balance) or_return

	return
}

origin :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	// Mock that origin is same as address from tx_env.
	address := bytes_to_U256(vm.tx_env.address[:])
	push(&vm.stack, address) or_return

	return
}

call_value :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	push(&vm.stack, U256{0, 0, 0, vm.tx_env.value}) or_return

	return
}

call_data_load :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	offset := stack_pop(&vm.stack)[3]

	call_data_len := math.min(len(vm.tx_env.call_data), int(offset + 32))
	call_data_slice := vm.tx_env.call_data[offset:call_data_len]

	data: [32]u8 = 0
	for i in 0 ..< len(call_data_slice) {
		data[i] = call_data_slice[i]
	}

	push(&vm.stack, be_bytes_to_U256(mem.any_to_bytes(data))) or_return

	return
}

call_data_size :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	size := bytes_to_U256(mem.any_to_bytes(len(vm.tx_env.call_data)))
	push(&vm.stack, size) or_return

	return
}

call_data_copy :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	dst_offset, src_offset, size :=
		stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3]


	words_to_copy := minimum_word_size(int(size))
	record_gas(vm, int(3 * words_to_copy))

	if ((dst_offset + size) > u64(len(vm.memory))) {
		record_gas(vm, expand_memory(vm, src_offset, size))
	}

	for i in 0 ..< size {
		if (uint(src_offset + i) >= len(vm.tx_env.call_data)) {
			vm.memory[dst_offset + i] = 0
		} else {
			vm.memory[dst_offset + i] = cast(byte)vm.tx_env.call_data[src_offset + i]
		}
	}
	return
}

code_size :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	size_bytes := mem.any_to_bytes(len(vm.bytecode))
	size := bytes_to_U256(size_bytes[:])

	push(&vm.stack, size) or_return
	return
}

code_copy :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	dst_offset, src_offset, size :=
		stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3]
	cost := 0

	if ((dst_offset + size) > u64(len(vm.memory))) {
		cost = expand_memory(vm, src_offset, size)
	}
	for i in 0 ..< size {
		if (uint(src_offset + i) >= len(vm.bytecode)) {
			vm.memory[dst_offset + i] = 0
		} else {
			vm.memory[dst_offset + i] = cast(byte)vm.bytecode[src_offset + i]
		}
	}

	dynamic_gas := verylow * minimum_word_size(int(size)) + cost
	record_gas(vm, dynamic_gas) or_return

	return
}

gas_price :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	push(&vm.stack, U256{0, 0, 0, vm.tx_env.gas_price}) or_return
	return
}

calculate_memory_cost :: proc(memory_byte_size: int) -> int {
	memory_size_word := minimum_word_size(memory_byte_size)
	return int(u64(math.pow(f32(memory_size_word), 2))) / 512 + (3 * memory_size_word)
}

minimum_word_size :: proc(size: int) -> int {
	return (size + 31) / 32
}

expand_memory :: proc(vm: ^EVM, offset, mem_len: u64) -> int {
	log.debug("Expanding memory")
	last_memory_cost := calculate_memory_cost(len(vm.memory))

	new_len: int = math.max(len(vm.memory), 32)
	offset := offset + u64(new_len)
	for offset > u64(new_len) {
		new_len += 32
	}
	resize(&vm.memory, new_len)
	new_memory_cost := calculate_memory_cost(len(vm.memory))

	cost := new_memory_cost - last_memory_cost

	return cost
}

mcopy :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	// Assume we use only max u64
	dst_offset, src_offset, size :=
		stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3]

	words_to_copy := size / 32
	record_gas(vm, int(3 * words_to_copy))

	if (len(vm.memory) < int(src_offset + size) || len(vm.memory) < int(dst_offset + size)) {
		record_gas(vm, expand_memory(vm, dst_offset, 32))
	}

	mem.copy(
		raw_data(vm.memory[dst_offset:dst_offset + size]),
		raw_data(vm.memory[src_offset:src_offset + size]),
		32,
	)

	return
}

mload :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	// Assume we use only max u64
	offset := stack_pop(&vm.stack)[3]

	if ((offset + 32) > u64(len(vm.memory))) {
		record_gas(vm, expand_memory(vm, offset, 32))
	}

	read: []u8 = vm.memory[offset:offset + 32]

	push(&vm.stack, be_bytes_to_U256(read)) or_return

	return
}


mstore :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	// Assume we use only max u64
	offset, value := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)

	if ((offset + 32) > u64(len(vm.memory))) {
		record_gas(vm, expand_memory(vm, offset, 32))
	}

	bytes := U256_to_bytes(value)
	mem.copy(raw_data(vm.memory[offset:offset + 32]), &bytes, 32)

	return
}

//offset: offset in memory in bytes (starting from least significant)
//value: 1-byte value to write in the memory
mstore8 :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, verylow) or_return
	// Assume we use only max u64
	offset := stack_pop(&vm.stack)[3]
	popped := stack_pop(&vm.stack)[3]
	value := cast(u8)popped

	bytes: [32]u8

	if (offset > u64(len(vm.memory)) || len(vm.memory) == 0) {
		record_gas(vm, expand_memory(vm, offset, 1))
	}

	vm.memory[offset] = value
	return
}

msize :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	// Assume we use only max u64
	offset := stack_pop(&vm.stack)[1]
	value := cast(u8)stack_pop(&vm.stack)[1]

	if ((offset + 32) > u64(len(vm.memory))) {
		expand_memory(vm, offset, 1)
	}

	vm.memory[offset] = value

	return
}

is_slot_cold :: proc(vm: ^EVM, slot: Slot) -> bool {
	return !slice.contains(vm.tx_env.access_list_storage[:], slot)
}

// `Original value`: This is the value of the storage if a reversion happens on the current transaction.
// Current value: Value of storage slot before SSTORE
// New value: Value of storage slot after SSTORE
//
// Source: https://eips.ethereum.org/EIPS/eip-1283
sstore :: proc(vm: ^EVM) -> (err: Error) {
	key, value := stack_pop(&vm.stack), stack_pop(&vm.stack)
	key_bytes := U256_to_bytes(key)

	slot := cast(Slot)key_bytes
	current_value := vm.storage[slot]

	base_dynamic_gas := 100

	if (current_value == U256{}) {
		base_dynamic_gas = 20000
	} else {
		base_dynamic_gas = 2900
	}

	if is_slot_cold(vm, slot) {
		base_dynamic_gas += 2100
	}

	record_gas(vm, base_dynamic_gas) or_return
	vm.storage[slot] = value

	append(&vm.tx_env.access_list_storage, slot)

	return
}

sload :: proc(vm: ^EVM) -> (err: Error) {
	key := stack_pop(&vm.stack)
	key_bytes := U256_to_bytes(key)
	base_dynamic_gas: int

	slot := cast(Slot)key_bytes

	if is_slot_cold(vm, slot) {
		base_dynamic_gas = 2100
	} else {
		base_dynamic_gas = 100
	}

	record_gas(vm, base_dynamic_gas) or_return
	current_value, ok := vm.storage[slot]
	if !ok {
		current_value = U256{}
	}
	push(&vm.stack, current_value) or_return
	append(&vm.tx_env.access_list_storage, slot)

	return
}

tstore :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, warmaccess) or_return
	key, value := stack_pop(&vm.stack), stack_pop(&vm.stack)
	address := U256_to_address(key)

	vm.tx_env.transient_storage[address] = value
	gas := mem.any_to_bytes(vm.gas)
	push(&vm.stack, bytes_to_U256(gas)) or_return
	return
}

tload :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, warmaccess) or_return
	key := stack_pop(&vm.stack)
	address := U256_to_address(key)

	value, ok := vm.tx_env.transient_storage[address]
	if !ok {value = U256{}}
	push(&vm.stack, value) or_return
	return
}

gas :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	gas := mem.any_to_bytes(vm.gas)
	push(&vm.stack, bytes_to_U256(gas)) or_return
	return
}

gas_limit :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	push(&vm.stack, U256{0, 0, 0, u64(vm.gas_limit)}) or_return
	return
}


jump :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, mid) or_return // haha mid
	counter := stack_pop(&vm.stack)[3]

	vm.ip = uint(counter)
	target_opcode := Opcode(vm.bytecode[vm.ip])

	if (target_opcode != .JUMPDEST) {
		return .InvalidJump
	}

	return
}

jumpi :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, high) or_return
	counter, b := stack_pop(&vm.stack)[3], stack_pop(&vm.stack)[3]

	if b == 0 {return}
	vm.ip = uint(counter)
	target_opcode := Opcode(vm.bytecode[vm.ip])

	if (target_opcode != .JUMPDEST) {
		return .InvalidJump
	}

	return
}

pc :: proc(vm: ^EVM) -> (err: Error) {
	record_gas(vm, base) or_return
	push(&vm.stack, U256{0, 0, 0, u64(vm.ip - 1)}) or_return

	return
}

dup_n :: proc(vm: ^EVM, $N: uint) -> (err: Error) {
	assert(N != 0 && N <= 16, "invalid DUP instruction")
	record_gas(vm, verylow) or_return
	to_dup := vm.stack.data[uint(len(vm.stack.data)) - N]
	push(&vm.stack, to_dup) or_return

	return
}

push_n :: proc(vm: ^EVM, $N: uint) -> (err: Error) {
	assert(N != 0 && N <= 32, "invalid PUSH instruction")
	record_gas(vm, verylow) or_return
	to_push: [32]u8 = 0
	raw := vm.bytecode[vm.ip:vm.ip + N]
	for i in 0 ..< len(raw) {
		to_push[31 - i] = raw[len(raw) - 1 - i]
	}
	vm.ip += N
	push(&vm.stack, be_bytes_to_U256(to_push[:])) or_return

	return
}

swap_n :: proc(vm: ^EVM, $N: int) -> (err: Error) {
	record_gas(vm, verylow) or_return
	vm.stack.data[len(vm.stack.data) - 1], vm.stack.data[len(vm.stack.data) - 1 - N] =
		vm.stack.data[len(vm.stack.data) - 1 - N], vm.stack.data[len(vm.stack.data) - 1]
	return
}

// Runs a single cycle of the EVM.
step :: proc(vm: ^EVM) -> (err: Error = .None) {
	opcode := Opcode(vm.bytecode[vm.ip])
	vm.ip += 1

	switch opcode {
	case .STOP:
		return .Stop
	case .ADD:
		add(vm) or_return
	case .MUL:
		mul(vm) or_return
	case .SUB:
		sub(vm) or_return
	case .DIV:
		div(vm) or_return
	case .SDIV:
		sdiv(vm) or_return
	case .MOD:
		mod(vm) or_return
	case .SMOD:
		smod(vm) or_return
	case .ADDMOD:
		addmod(vm) or_return
	case .MULMOD:
		mulmod(vm) or_return
	case .EXP:
		exponent(vm) or_return
	case .SIGNEXTEND:
		signextend(vm) or_return
	case .LT:
		lt(vm) or_return
	case .GT:
		gt(vm) or_return
	case .SLT:
		slt(vm) or_return
	case .SGT:
		sgt(vm) or_return
	case .EQ:
		eq(vm) or_return
	case .ISZERO:
		is_zero(vm) or_return
	case .AND:
		and(vm) or_return
	case .OR:
		or(vm) or_return
	case .XOR:
		xor(vm) or_return
	case .NOT:
		not(vm) or_return
	case .BYTE:
		byte_op(vm) or_return
	case .SHL:
		shl(vm) or_return
	case .SHR:
		shr(vm) or_return
	case .SAR:
		sar(vm) or_return
	case .KECCAK256:
		keccak_(vm) or_return
	case .ADDRESS:
		address(vm) or_return
	case .BALANCE:
		balance(vm) or_return
	case .ORIGIN:
		origin(vm) or_return
	case .CALLER:
		panic("unimplemented because there's no contract caller to return")
	case .CALLVALUE:
		call_value(vm) or_return
	case .CALLDATALOAD:
		call_data_load(vm) or_return
	case .CALLDATASIZE:
		call_data_size(vm) or_return
	case .CALLDATACOPY:
		call_data_copy(vm) or_return
	case .CODESIZE:
		code_size(vm) or_return
	case .CODECOPY:
		code_copy(vm) or_return
	case .GASPRICE:
		panic("unimplemented because there's no transactions to record the gas price of")
	case .EXTCODESIZE:
		panic("contract logic is unsupported")
	case .EXTCODECOPY:
		panic("contract logic is unsupported")
	case .RETURNDATASIZE:
		panic("there is no return data because contract logic is unsupported")
	case .RETURNDATACOPY:
		panic("there is no return data because contract logic is unsupported")
	case .EXTCODEHASH:
		panic("contract logic is unsupported")
	case .BLOCKHASH:
		block_hash(vm) or_return
	case .COINBASE:
		push(&vm.stack, bytes_to_U256(vm.block_context.coinbase[0:20])) or_return
	case .TIMESTAMP:
		push(&vm.stack, U256{0, 0, 0, vm.block_context.time}) or_return
	case .NUMBER:
		push(&vm.stack, vm.block_context.block_number) or_return
	case .PREVRANDAO:
		random := cast([32]byte)(vm.block_context.random)
		push(&vm.stack, bytes_to_U256(random[:])) or_return
	case .GASLIMIT:
		gas_limit(vm) or_return
	case .CHAINID:
		// 1 = mainnet
		push(&vm.stack, U256{0, 0, 0, 1}) or_return
	case .BASEFEE:
		panic("unimplemented because there is no block production")
	case .BLOBHASH, .BLOBBASEFEE:
		panic("EIP-4844 is unsupported")
	case .POP:
		top := pop(&vm.stack.data)
		record_gas(vm, base)
		return
	case .MLOAD:
		mload(vm) or_return
	case .MSTORE:
		mstore(vm) or_return
	case .MSTORE8:
		mstore8(vm) or_return
	case .SLOAD:
		sload(vm) or_return
	case .SSTORE:
		sstore(vm) or_return
	case .JUMP:
		jump(vm) or_return
	case .JUMPI:
		jumpi(vm) or_return
	case .PC:
		pc(vm) or_return
	case .MSIZE:
		msize(vm) or_return
	case .GAS:
		gas(vm) or_return
	case .JUMPDEST:
		// no-op: just record gas
		record_gas(vm, jumpdest)
	case .TLOAD:
		tload(vm) or_return
	case .TSTORE:
		tstore(vm) or_return
	case .MCOPY:
		mcopy(vm) or_return
	case .PUSH0:
		push_zero(vm) or_return
	case .PUSH1:
		push_n(vm, 1) or_return
	case .PUSH2:
		push_n(vm, 2) or_return
	case .PUSH3:
		push_n(vm, 3) or_return
	case .PUSH4:
		push_n(vm, 4) or_return
	case .PUSH5:
		push_n(vm, 5) or_return
	case .PUSH6:
		push_n(vm, 6) or_return
	case .PUSH7:
		push_n(vm, 7) or_return
	case .PUSH8:
		push_n(vm, 8) or_return
	case .PUSH9:
		push_n(vm, 9) or_return
	case .PUSH10:
		push_n(vm, 10) or_return
	case .PUSH11:
		push_n(vm, 11) or_return
	case .PUSH12:
		push_n(vm, 12) or_return
	case .PUSH13:
		push_n(vm, 13) or_return
	case .PUSH14:
		push_n(vm, 14) or_return
	case .PUSH15:
		push_n(vm, 15) or_return
	case .PUSH16:
		push_n(vm, 16) or_return
	case .PUSH17:
		push_n(vm, 17) or_return
	case .PUSH18:
		push_n(vm, 18) or_return
	case .PUSH19:
		push_n(vm, 19) or_return
	case .PUSH20:
		push_n(vm, 20) or_return
	case .PUSH21:
		push_n(vm, 21) or_return
	case .PUSH22:
		push_n(vm, 22) or_return
	case .PUSH23:
		push_n(vm, 23) or_return
	case .PUSH24:
		push_n(vm, 24) or_return
	case .PUSH25:
		push_n(vm, 25) or_return
	case .PUSH26:
		push_n(vm, 26) or_return
	case .PUSH27:
		push_n(vm, 27) or_return
	case .PUSH28:
		push_n(vm, 28) or_return
	case .PUSH29:
		push_n(vm, 29) or_return
	case .PUSH30:
		push_n(vm, 30) or_return
	case .PUSH31:
		push_n(vm, 31) or_return
	case .PUSH32:
		push_n(vm, 32) or_return
	case .DUP1:
		dup_n(vm, 1) or_return
	case .DUP2:
		dup_n(vm, 2) or_return
	case .DUP3:
		dup_n(vm, 3) or_return
	case .DUP4:
		dup_n(vm, 4) or_return
	case .DUP5:
		dup_n(vm, 5) or_return
	case .DUP6:
		dup_n(vm, 6) or_return
	case .DUP7:
		dup_n(vm, 7) or_return
	case .DUP8:
		dup_n(vm, 8) or_return
	case .DUP9:
		dup_n(vm, 9) or_return
	case .DUP10:
		dup_n(vm, 10) or_return
	case .DUP11:
		dup_n(vm, 11) or_return
	case .DUP12:
		dup_n(vm, 12) or_return
	case .DUP13:
		dup_n(vm, 13) or_return
	case .DUP14:
		dup_n(vm, 14) or_return
	case .DUP15:
		dup_n(vm, 15) or_return
	case .DUP16:
		dup_n(vm, 16) or_return
	case .SWAP1:
		swap_n(vm, 1)
	case .SWAP2:
		swap_n(vm, 2)
	case .SWAP3:
		swap_n(vm, 3)
	case .SWAP4:
		swap_n(vm, 4)
	case .SWAP5:
		swap_n(vm, 5)
	case .SWAP6:
		swap_n(vm, 6)
	case .SWAP7:
		swap_n(vm, 7)
	case .SWAP8:
		swap_n(vm, 8)
	case .SWAP9:
		swap_n(vm, 9)
	case .SWAP10:
		swap_n(vm, 10)
	case .SWAP11:
		swap_n(vm, 11)
	case .SWAP12:
		swap_n(vm, 12)
	case .SWAP13:
		swap_n(vm, 13)
	case .SWAP14:
		swap_n(vm, 14)
	case .SWAP15:
		swap_n(vm, 15)
	case .SWAP16:
		swap_n(vm, 16)
	case .SELFBALANCE,
	     .LOG0,
	     .LOG1,
	     .LOG2,
	     .LOG3,
	     .LOG4,
	     .CREATE,
	     .CALL,
	     .CALLCODE,
	     .RETURN,
	     .DELEGATECALL,
	     .CREATE2,
	     .STATICCALL,
	     .REVERT,
	     .INVALID,
	     .SELFDESTRUCT:
		panic("Unsupported :(")
	}
	return
}


run :: proc(vm: ^EVM) -> (err: Error = .None) {
	c := 0
	for b in vm.tx_env.call_data {
		if b == 0 {
			vm.gas_used += 4
		} else {
			vm.gas_used += 16
		}
	}

	for (c < 10_000) {
		err = step(vm)
		when ODIN_DEBUG {
			fmt.eprintf("c = %i\n", c)
		}
		if err == .Stop || err == .InvalidJump {
			break
		}
		if err == .OutOfGas {
			panic("Ran out of gas")
		}

		c += 1
	}
	return
}
