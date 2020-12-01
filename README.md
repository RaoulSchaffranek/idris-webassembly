# WebAssembly Model

This project aims to provide a model of the WebAssembly specification for Idris.
It is at a very early stage, there isn't much to spot here yet.

Possible use cases:

- Prove meta-theorems about the WebAssembly specification, i.e. decidability of type-checking.
- Prove properties of specific WebAssembly programs, i.e. termination.
- Generate WebAssembly ByteCode for (verified) compilers.
- Statically analyze WebAssembly programs to uncover bugs.
- Interactively analyze WebAssembly programs with time-travel debugging.
- Serve as an orcacle for test-suites of WebAssembly implementations.

## Progress

[x] Structure
  [x] Values
  [x] Types
  [x] Instructions
  [x] Modules
[ ] Validation
  [ ] Types
  [ ] Instructions
  [ ] Modules
[ ] Execution
  [ ] Runtime Structure
  [ ] Numerics
  [ ] Instructions
  [ ] Modules
[ ] Binary Format
  [ ] Values
  [ ] Types
  [ ] Instructions
  [ ] Modules
[ ] Text Format
  [ ] Values
  [ ] Types
  [ ] Insructions
  [ ] Modules
