# cryptolib4
Implementation of [JoeyLupo's cryptolib](https://github.com/JoeyLupo/cryptolib) in Lean4.

This project aims to implement the game-based semantically secure and proof of correctness of the ElGamal public key encryption scheme.

## Getting started
### Add mathlib4 dependency
- Add to `lakefile.lean`:
```
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
```
- run `lake update` in the terminal
  - There might be some warnings about package configuration errors. This will be fixed in the next step.
  
- In the terminal, run `cp lake-packages/mathlib/lean-toolchain .` to make sure current Lean version matches mathlib4's.

- Run `lake update` again, there should not be any errors now.

- (Optionally) run `lake exe cache get` in the terminal to save time compiling mathlib and its dependencies

- Run `lake build` in the terminal

- Restart your instance of your IDE (VSCode, Emacs...)