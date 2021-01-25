# Idris WebAssembly

This project aims to provide an [Idris](http://docs.idris-lang.org/en/latest/)-model of the [WebAssembly specification](https://webassembly.github.io/spec/core/).
It is at a very early stage; there isn't much to spot yet.

Possible use cases:

- Prove meta-theorems about the WebAssembly specification, for example, decidability of type-checking.
- Prove properties of specific WebAssembly programs, for example, termination.
- Generate WebAssembly bytecode for (verified) compilers.
- Statically analyze WebAssembly programs to uncover bugs.
- Serve as an oracle for test-suites of WebAssembly implementations.

## Progress

- [x] Structure
  - [x] Values
  - [x] Types
  - [x] Instructions
  - [x] Modules
- [ ] Validation
  - [x] Types
  - [x] Instructions
  - [ ] Modules
- [ ] Execution
  - [ ] Runtime Structure
  - [ ] Numerics
  - [ ] Instructions
  - [ ] Modules
- [ ] Binary Format
  - [ ] Values
  - [ ] Types
  - [ ] Instructions
  - [ ] Modules
- [ ] Text Format
  - [ ] Values
  - [ ] Types
  - [ ] Insructions
  - [ ] Modules


## Commands

Typecheck Package: `idris --checkpkg .\WebAssembly.ipkg`
Generate Documentation: `idris --mkdoc .\WebAssembly.ipkg`
