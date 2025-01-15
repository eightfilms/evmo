package main

import "base:intrinsics"
import "core:log"

// Nothing paid for operations of the set `W_zero`.
zero: int : 0
// Amount of gas to pay for a `JUMPDEST` operation.
jumpdest: int : 1
// Amount of gas to pay for operations of the set `W_base`.
base: int : 2
// Amount of gas to pay for operations of the set `W_verylow`.
verylow: int : 3
// Amount of gas to pay for operations of the set `W_low`.
low: int : 5
// Amount of gas to pay for operations of the set `W_mid`.
mid: int : 8
// Amount of gas to pay for operations of the set `W_high`.
high: int : 10
// Cost of a warm account or storage access.
warmaccess: int : 100
// Cost of warming up an account with the access list.
accesslistaddress: int : 2400
// Cost of warming up a storage with the access list.
accessliststorage: int : 1900
// Cost of a cold account access.
coldaccountaccess: int : 2600
// Cost of a cold storage access.
coldsload: int : 2100
// Paid for an `SSTORE` operation when the storage value is set to non-zero from zero.
sset: int : 20000
// Paid for an `SSTORE` operation when the storage value's zeroness remains unchanged or
// is set to zero.
sreset: int : 2900
// Refund given (added into refund counter) when the storage value is set to zero from
// non-zero.
sclear: int : 4800
// Amount of gas to pay for a `SELFDESTRUCT` operation.
selfdestruct: int : 5000
// Paid for a `CREATE` operation.
create: int : 32000
// Paid per byte for a `CREATE` operation to succeed in placing code into state.
codedeposit: int : 200
// Paid for a non-zero value transfer as part of the `CALL` operation.
callvalue: int : 9000
// A stipend for the called contract subtracted from `callvalue` for a non-zero value transfer.
callstipend: int : 2300
// Paid for a `CALL` or `SELFDESTRUCT` operation which creates an account.
newaccount: int : 25000
// Partial payment for an `EXP` operation.
exp: int : 10
// Partial payment when multiplied by the number of bytes in the exponent for the `EXP` operation.
expbyte: int : 50
// Paid for every additional word when expanding memory.
memory: int : 3
// Paid by all contract-creating transactions after the `Homestead` transition.
txcreate: int : 32000
// Paid for every zero byte of data or code for a transaction.
txdatazero: int : 4
// Paid for every non-zero byte of data or code for a transaction.
txdatanonzero: int : 16
// Paid for every transaction.
transaction: int : 21000
// Partial payment for a `LOG` operation.
log: int : 375
// Paid for each byte in a `LOG` operation's data.
logdata: int : 8
// Paid for each topic of a `LOG` operation.
logtopic: int : 375
// Paid for each `KECCAK256` operation.
keccak256: int : 30
// Paid for each word (rounded up) for input data to a `KECCAK256` operation.
keccak256word: int : 6
// Partial payment for `*COPY` operations, multiplied by words copied, rounded up.
copy_: int : 3
// Payment for each `BLOCKHASH` operation.
blockhash: int : 20

// Records gas. Returns `Error.OutOfGas` if an overflow occurred.
record_gas :: proc(vm: ^EVM, cost: int) -> (err: Error = .None) {
	res, did_overflow := intrinsics.overflow_sub(vm.gas, cost)
	if (did_overflow) {return .OutOfGas}
	vm.gas = res
	vm.gas_used += cost
	log.debugf("gas used: %i", vm.gas_used)
	return
}
