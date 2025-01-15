package main

import "base:intrinsics"
import "core:fmt"
import "core:log"
import "core:math"
import "core:math/big"
import "core:mem"
import "core:slice"
import "core:strconv"
import "core:testing"

U256 :: [4]u64

max_U256 :: proc() -> U256 {
	return U256{max(u64), max(u64), max(u64), max(u64)}
}

U256_add :: proc(a, b: U256) -> U256 {
	result: U256
	carry: bool

	for i in 0 ..= 3 {
		result[3 - i] = a[3 - i] + b[3 - i] + u64(carry)
		c := result[3 - i] < a[3 - i] || result[3 - i] < b[3 - i]
		carry = c
	}
	return result
}

@(test)
test_U256_add :: proc(t: ^testing.T) {
	U256_Add_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Add_Test {
		{U256{0, 0, 60, 400}, U256{0, 0, 9, 20}, U256{0, 0, 69, 420}}, // no overflow
		{U256{0, 0, 0, max(u64) - 1}, U256{0, 0, 0, 4}, U256{0, 0, 1, 2}}, // overflow
		{U256{max(u64), max(u64), max(u64), max(u64)}, U256{0, 0, 0, 1}, U256{0, 0, 0, 0}}, // overflow hi
		{U256{max(u64), max(u64), max(u64), max(u64)}, U256{0, 0, 0, 2}, U256{0, 0, 0, 1}}, // overflow hi
	}

	for test in tests {
		actual := U256_add(test.a, test.b)
		testing.expect(t, actual == test.expected)
	}
}

U256_sub :: proc(a, b: U256) -> U256 {
	result: U256
	borrow: bool
	for i in 0 ..< 4 {
		res: u64 = a[3 - i]
		br: bool
		if (borrow) {
			res, br = intrinsics.overflow_sub(a[3 - i], 1)
		}
		result[3 - i], borrow = intrinsics.overflow_sub(res, b[3 - i])
		borrow = borrow || br
	}
	return result
}

@(test)
test_U256_sub :: proc(t: ^testing.T) {
	U256_Sub_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Sub_Test {
		{U256{0, 0, 69, 420}, U256{0, 0, 9, 20}, U256{0, 0, 60, 400}},
		{U256{0, 0, 1, 1}, U256{0, 0, 0, max(u64)}, U256{0, 0, 0, 2}},
		{U256{0, 0, 2, 6}, U256{0, 0, 1, 5}, U256{0, 0, 1, 1}},
		{U256{0, 0, 0, 0}, U256{0, 0, 0, 1}, U256{max(u64), max(u64), max(u64), max(u64)}},
	}

	for test in tests {
		got := U256_sub(test.a, test.b)
		testing.expectf(t, got == test.expected, "expected = {:x}\ngot = {:x}", test.expected, got)
	}
}

/// Most significant byte is in bytes[0]
U256_to_bytes :: proc(value: U256) -> [32]u8 {
	bytes: [32]u8

	for i in 0 ..= 3 {
		value_bytes: [8]u8 = transmute([size_of(value[i])]u8)value[i]
		slice.reverse(value_bytes[:])
		mem.copy(raw_data(bytes[i * 8:(i + 1) * 8]), raw_data(value_bytes[:]), 8)
	}

	return bytes
}

// Most significant byte is in bytes[0]
U256_to_address :: proc(value: U256) -> Address {
	address: Address

	bytes := U256_to_bytes(value)
	copy_slice(address[:], bytes[12:32])
	return address
}

U256_to_big_int :: proc(dst: ^big.Int, src: U256, signed: bool = false) {
	bytes: [32]byte = U256_to_bytes(src)
	big.int_from_bytes_big(dst, bytes[:], signed = signed)
}

U256_mul :: proc(a, b: U256) -> U256 {
	temp: [8]u64
	carry: u64

	for i in 0 ..< 4 {
		c: u64 = 0
		for j in 0 ..< 4 {
			if (i + j >= 4) do break
			product := u128(a[3 - i]) * u128(b[3 - j]) + u128(c) + u128(temp[i + j])
			temp[i + j] = u64(product)
			c = u64(product >> 64)
		}
	}
	result := U256{temp[3], temp[2], temp[1], temp[0]}
	return result
}

@(test)
test_U256_mul :: proc(t: ^testing.T) {
	U256_Mul_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Mul_Test {
		{U256{0, 0, 0, max(u64)}, U256{0, 0, 0, 0x2}, U256{0, 0, 0x1, max(u64) - 1}}, // overflow hi
		{U256{0, 0, 0, max(u64)}, U256{0, 0, 0, 0x4}, U256{0, 0, 0x3, 0xFFFFFFFFFFFFFFFC}}, // overflow hi
		{U256{0, 0, 0, max(u64)}, U256{0, 0, 0, max(u64)}, U256{0, 0, max(u64) - 1, 1}}, // overflow hi
		{
			U256{max(u64), max(u64), max(u64), max(u64)},
			U256{max(u64), max(u64), max(u64), max(u64)},
			U256{0, 0, 0, 1},
		}, // overflow hi
	}


	for test in tests {
		testing.expect(t, U256_mul(test.a, test.b) == test.expected)
	}
}

U256_div :: proc(num, den: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	q, num_big, den_big := big.Int{}, big.Int{}, big.Int{}

	U256_to_big_int(&den_big, den)
	defer big.destroy(&den_big)

	// If denominator is zero, return 0
	den_is_zero, _ := big.is_zero(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}

	U256_to_big_int(&num_big, num)
	defer big.destroy(&num_big)

	bytes: [32]byte
	big.div(&q, &num_big, &den_big)
	defer big.destroy(&q)

	big.int_to_bytes_big(&q, bytes[:])
	res := be_bytes_to_U256(bytes[:])

	return res
}

// Interpret `num` and `den` as two's complement signed integers,
// does a signed division on the two operands.
U256_sdiv :: proc(num, den: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	q, num_big, den_big := big.Int{}, big.Int{}, big.Int{}

	den := U256_sub(U256{0, 0, 0, 0}, den)
	U256_to_big_int(&den_big, den, signed = true)
	defer big.destroy(&den_big)

	den_is_zero, _ := big.is_zero(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}

	num := U256_sub(U256{0, 0, 0, 0}, num)
	U256_to_big_int(&num_big, num, signed = true)
	defer big.destroy(&num_big)

	bytes: [32]byte
	big.div(&q, &num_big, &den_big)
	defer big.destroy(&q)

	big.int_to_bytes_big(&q, bytes[:])
	res := be_bytes_to_U256(bytes[:])


	return res
}

U256_mod :: proc(num, den: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	q, num_big, den_big := big.Int{}, big.Int{}, big.Int{}

	U256_to_big_int(&den_big, den)
	defer big.destroy(&den_big)
	// If denominator is zero, return 0
	den_is_zero, _ := big.is_zero(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}

	U256_to_big_int(&num_big, num)
	defer big.destroy(&num_big)
	big.mod(&q, &num_big, &den_big)
	defer big.destroy(&q)
	bytes: [32]byte

	big.int_to_bytes_big(&q, bytes[:])
	res := be_bytes_to_U256(bytes[:])


	return res
}

U256_smod :: proc(num, den: U256) -> U256 {
	// Sorry i don't want to deal with limbs here.
	// Relying on big ints it is.
	r, num_big, den_big := big.Int{}, big.Int{}, big.Int{}
	num_is_neg := num[0] >> 7 & 1 == 1

	den := den
	if (den[0] >> 7 & 1 == 1) {
		den = U256_sub(max_U256(), den)
	}
	U256_to_big_int(&den_big, den, signed = true)
	defer big.destroy(&den_big)
	den_is_zero, _ := big.is_zero(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}

	num := num
	if (num_is_neg) {
		num = U256_sub(max_U256(), num)
	}
	U256_to_big_int(&num_big, num, signed = true)
	defer big.destroy(&num_big)
	big.mod(&r, &num_big, &den_big)
	defer big.destroy(&r)
	bytes: [32]byte


	big.int_to_bytes_big(&r, bytes[:])
	res := be_bytes_to_U256(bytes[:])

	// Why...
	if (num_is_neg) {res = U256_sub(max_U256(), res)}

	return res
}

U256_addmod :: proc(num, den, mod: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	r, num_big, den_big, mod_big := big.Int{}, big.Int{}, big.Int{}, big.Int{}

	U256_to_big_int(&den_big, den, signed = true)
	// If denominator is zero, return 0
	den_is_zero, _ := big.is_zero(&den_big)
	defer big.destroy(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}

	U256_to_big_int(&num_big, num, signed = true)
	U256_to_big_int(&mod_big, mod, signed = true)
	defer big.destroy(&num_big)
	defer big.destroy(&mod_big)

	big.addmod(&r, &num_big, &den_big, &mod_big)

	bytes: [32]byte
	big.int_to_bytes_big(&r, bytes[:])
	defer big.destroy(&r)
	res := be_bytes_to_U256(bytes[:])

	return res
}

U256_mulmod :: proc(num, den, mod: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	r, num_big, den_big, mod_big := big.Int{}, big.Int{}, big.Int{}, big.Int{}
	// If denominator is zero, return 0
	den_is_zero, _ := big.is_zero(&den_big)
	U256_to_big_int(&den_big, den)
	defer big.destroy(&den_big)
	if (den_is_zero) {return U256{0, 0, 0, 0}}


	U256_to_big_int(&num_big, num)
	U256_to_big_int(&mod_big, mod)
	defer big.destroy(&num_big)
	defer big.destroy(&mod_big)

	big.mulmod(&r, &num_big, &den_big, &mod_big)

	bytes: [32]byte
	big.int_to_bytes_big(&r, bytes[:])
	defer big.destroy(&r)
	res := be_bytes_to_U256(bytes[:])

	return res
}

U256_exp :: proc(base, power: U256) -> U256 {
	// Sorry i don't want to deal with limb mults here.
	// Relying on big ints it is.
	r, base_big, den_big := big.Int{}, big.Int{}, big.Int{}
	U256_to_big_int(&den_big, power)
	defer big.destroy(&den_big)
	den_is_zero, _ := big.is_zero(&den_big)
	// If denominator is zero, return 0
	if (den_is_zero) {
		return U256{0, 0, 0, 0}
	}

	U256_to_big_int(&base_big, base)
	defer big.destroy(&base_big)

	big.exp(&r, &base_big, 2)

	bytes: [32]byte
	big.int_to_bytes_big(&r, bytes[:])
	defer big.destroy(&r)
	res := be_bytes_to_U256(bytes[:])

	return res
}


U256_lt :: proc(a, b: U256) -> U256 {
	for i in 0 ..< 4 {
		if (a[i] < b[i]) {return U256{0, 0, 0, 1}}
		if (a[i] > b[i]) {return U256{0, 0, 0, 0}}
	}

	return U256{0, 0, 0, 0}
}

@(test)
test_U256_lt :: proc(t: ^testing.T) {
	U256_Less_Than_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Less_Than_Test {
		{U256{0, 0, 0, 10}, U256{0, 0, 1, 0}, U256{0, 0, 0, 1}},
		{U256{0, 0, 1, 0}, U256{0, 0, 0, 10}, U256{0, 0, 0, 0}},
		{U256{0, 0, 1, 0}, U256{0, 0, 1, 10}, U256{0, 0, 0, 1}},
		{U256{0, 0, 1, 10}, U256{0, 0, 1, 0}, U256{0, 0, 0, 0}},
	}

	for test in tests {
		testing.expect(t, U256_lt(test.a, test.b) == test.expected)
	}
}

U256_gt :: proc(a, b: U256) -> U256 {
	for i in 0 ..< 4 {
		if (a[i] > b[i]) {return U256{0, 0, 0, 1}}
		if (a[i] < b[i]) {return U256{0, 0, 0, 0}}
	}

	return U256{0, 0, 0, 0}
}

@(test)
test_U256_gt :: proc(t: ^testing.T) {
	U256_Greater_Than_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Greater_Than_Test {
		{U256{0, 0, 0, 10}, U256{0, 0, 1, 0}, U256{0, 0, 0, 0}},
		{U256{0, 0, 1, 0}, U256{0, 0, 0, 10}, U256{0, 0, 0, 1}},
		{U256{0, 0, 1, 0}, U256{0, 0, 1, 10}, U256{0, 0, 0, 0}},
		{U256{0, 0, 1, 10}, U256{0, 0, 1, 0}, U256{0, 0, 0, 1}},
	}

	for test in tests {
		testing.expect(t, U256_gt(test.a, test.b) == test.expected)
	}
}

// Returns 1 if a < b, 0 otherwise.
U256_slt :: proc(a, b: U256) -> U256 {
	a_hi := i64(a[0])
	b_hi := i64(b[0])

	a_sign, b_sign := (a_hi >> 63) & 1, (b_hi >> 63) & 1

	if (a_sign != b_sign) {
		return U256{0, 0, 0, a_sign == 1}
	}

	for i in 0 ..< 4 {
		if a[i] != b[i] {
			if (a_sign == 1) {
				return U256{0, 0, 0, a[i] > b[i]}
			} else {
				return U256{0, 0, 0, a[i] < b[i]}
			}
		}

	}

	return U256{0, 0, 0, 0}
}


@(test)
test_U256_slt :: proc(t: ^testing.T) {
	U256_Signed_Less_Than_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Signed_Less_Than_Test {
		{U256{max(u64), max(u64), max(u64), max(u64)}, U256{0, 0, 0, 0}, U256{0, 0, 0, 1}}, // a(neg) < b
		{
			U256{max(u64), max(u64), max(u64), max(u64)},
			U256{max(u64), max(u64), max(u64), 0},
			U256{0, 0, 0, 1},
		}, // a(neg) < b(neg)
		{U256{0, 0, 0, max(u64)}, U256{0, 0, 0, 0}, U256{0, 0, 0, 0}}, // a > b
	}

	for test in tests {
		testing.expect(t, U256_slt(test.a, test.b) == test.expected)
	}
}

/// Return 1 if a > b, 0 otherwise.
U256_sgt :: proc(a, b: U256) -> U256 {
	a_hi := i64(a[0])
	b_hi := i64(b[0])

	a_sign, b_sign := (a_hi >> 63) & 1, (b_hi >> 63) & 1

	if (a_sign != b_sign) {
		return U256{0, 0, 0, a_sign != 1}
	}

	for i in 0 ..< 4 {
		if a[i] != b[i] {
			if (a_sign == 1) {
				return U256{0, 0, 0, a[i] < b[i]}
			} else {
				return U256{0, 0, 0, a[i] > b[i]}
			}
		}
	}

	return U256{0, 0, 0, 0}
}

@(test)
test_U256_sgt :: proc(t: ^testing.T) {
	U256_Signed_Less_Than_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Signed_Less_Than_Test {
		{U256{max(u64), max(u64), max(u64), max(u64)}, U256{0, 0, 0, 0}, U256{0, 0, 0, 0}}, // a(neg) < b
		{
			U256{max(u64), max(u64), max(u64), max(u64)},
			U256{max(u64), max(u64), max(u64), 0},
			U256{0, 0, 0, 0},
		}, // a(neg) < b(neg)
		{U256{0, 0, 0, max(u64)}, U256{0, 0, 0, 0}, U256{0, 0, 0, 1}}, // a > b
	}

	for test in tests {
		testing.expect(t, U256_sgt(test.a, test.b) == test.expected)
	}
}

U256_eq :: proc(a, b: U256) -> U256 {
	return U256{0, 0, 0, a[0] == b[0] && a[1] == b[1] && a[2] == b[2] && a[3] == b[3]}
}

@(test)
test_U256_eq :: proc(t: ^testing.T) {
	U256_Eq_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_Eq_Test {
		{U256{0, 0, 0, 0}, U256{0, 0, 0, 0}, U256{0, 0, 0, 1}},
		{U256{0, 0, max(u64), 0}, U256{0, 0, max(u64), 0}, U256{0, 0, 0, 1}},
		{U256{0, 0, 1, 0}, U256{0, 0, 0, 10}, U256{0, 0, 0, 0}},
		{U256{0, 0, max(u64) - 1, 0}, U256{0, 0, max(u64) - 1, 0}, U256{0, 0, 0, 1}},
	}

	for test in tests {
		testing.expect(t, U256_eq(test.a, test.b) == test.expected)
	}
}

U256_and :: proc(a, b: U256) -> U256 {
	return U256{a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]}
}

@(test)
test_U256_and :: proc(t: ^testing.T) {
	U256_And_Test :: struct {
		a:        U256,
		b:        U256,
		expected: U256,
	}

	tests :: []U256_And_Test {
		{U256{0, 0, 0, 0x1010}, U256{0, 0, 0, 0x1010}, U256{0, 0, 0, 0x1010}},
		{U256{0, 0, max(u64), 0}, U256{0, 0, max(u64), 0}, U256{0, 0, max(u64), 0}},
	}

	for test in tests {
		testing.expect(t, U256_and(test.a, test.b) == test.expected)
	}
}

U256_or :: proc(a, b: U256) -> U256 {
	return U256{a[0] | b[0], a[1] | b[1], a[2] | b[2], a[3] | b[3]}
}

@(test)
test_U256_or :: proc(t: ^testing.T) {
	testing.expect(
		t,
		U256_or(U256{0, 0, 0, 0x1010}, U256{0, 0, 0, 0x0101}) == U256{0, 0, 0, 0x1111},
	)
}

U256_xor :: proc(a, b: U256) -> U256 {
	return U256{a[0] ~ b[0], a[1] ~ b[1], a[2] ~ b[2], a[3] ~ b[3]}
}

@(test)
test_U256_xor :: proc(t: ^testing.T) {
	testing.expect(
		t,
		U256_xor(U256{0, 0, 0, 0x1010}, U256{0, 0, 0, 0x1101}) == U256{0, 0, 0, 0x111},
	)
}

U256_not :: proc(a: U256) -> U256 {
	return U256{~a[0], ~a[1], ~a[2], ~a[3]}
}

@(test)
test_U256_not :: proc(t: ^testing.T) {
	testing.expect(
		t,
		U256_not(U256{0, 1, max(u64) - 1, max(u64)}) == U256{max(u64), max(u64) - 1, 1, 0},
	)
}

// Bytes in EVM's bytecode is in big endian, i.e. most significant byte first.
// Biggest is bytes[0]...
be_bytes_to_U256 :: proc(bytes: []u8) -> U256 {
	assert(len(bytes) <= 32, "Cannot convert byte array of length >256 to U256")

	limbs_bytes: [32]u8
	copy_slice(limbs_bytes[:], bytes)
	slice.reverse(limbs_bytes[:])

	limb0, limb1, limb2, limb3: u64
	limb0 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[0:8]))^
	limb1 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[8:16]))^
	limb2 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[16:24]))^
	limb3 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[24:32]))^

	res := U256{limb3, limb2, limb1, limb0}
	return res
}

bytes_to_U256 :: proc(bytes: []u8) -> U256 {
	assert(len(bytes) <= 32, "Cannot convert byte array of length >256 to U256")

	limbs_bytes: [32]u8
	copy_slice(limbs_bytes[:], bytes)

	limb0, limb1, limb2, limb3: u64
	limb0 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[0:8]))^
	limb1 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[8:16]))^
	limb2 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[16:24]))^
	limb3 = transmute(u64)(^[8]byte)(raw_data(limbs_bytes[24:32]))^

	res := U256{limb3, limb2, limb1, limb0}
	return res
}
