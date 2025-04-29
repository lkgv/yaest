# Ethereum to Solana

Welcome to Ethereum to Solana, a new Ethereum transpiler to Solana.

## How to execute

```
cargo build
./target/debug/solang compile --target evm examples/erc20/ERC20.sol
```

Driver program: `src/bin/solang.rs`.

Entrance to the transpile process: function `visit_ns` in `src/translate/mod.rs`.

Pointer analysis: `/src/translate/analysis/pointers.rs` (TODOs have been listed here).

The solidity files to be tested are mainly `examples/erc20` and `examples/openzeppelin`.
