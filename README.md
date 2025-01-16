# evmo

A toy **EVM** written in [**O**din](https://odin-lang.org).

- Supports 122 out of 148 opcodes found on [evm.codes](https://evm.codes)
- No external dependencies. Just ~2.5K LoC of Odin and its standard library
- Tests the basic examples found on [evm.codes](https://evm.codes)

Some opcodes were left unimplemented because I didn't think it made sense to implement them given that this is a toy evm and I have accomplished what I set out to do for this implementation

## Test

You will need [Odin](https://odin-lang.org/docs/install/) installed.

Run all tests:

```sh
$ odin test .
```

To run specific tests, define key-value pair of `ODIN_TEST_NAMES` and a comma-separated string of test names as a environment variable:

```sh
$ odin test . -define:ODIN_TEST_NAMES=test_add,test_mstore 
```

## Acknowledgements

Acknowledging some resources which I used as reference to write this, thanks!

- [evm.codes](https://evm.codes)
- https://github.com/ethereum/go-ethereum
- https://github.com/ethereum/evmone
- https://github.com/chfast/intx
- https://github.com/Jesserc/gevm
