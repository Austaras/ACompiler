Test out various compiler technology with a toy compiler for a toy language **in between** rust and OCaml. Referenced source including but not limited to:

- _Modern Compiler Implementation in ML_
- _Engineering a Compiler_
- _OCaml Programming: Correct + Efficient + Beautiful_

### Design Decision

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call, = for assign, == for equal, != for not equal, |a, b| a + b for closure
   - not whitespace sensitive, but without mandatory semicolons
   - variant has their own namespace
   - also break/continue/return
   - struct/enum keyword
   - .\_0 for tuple access
2. ML semantic with Rust characteristics
   - HM type inference with trait and operator overloading
   - c style function declaration that are hoisted and can only refer to values in outer scope
   - internal mutable
   - no auto boxing, provide general reference type(s) tracked by GC
   - user can roll their own container like in Rust
   - impl block, but user need to import that module to work
3. Compiler Architecture
   - Hand written recursive descendant parser
4. suffix is .adf which stands for Advanced Dominance Fighter
5. Major TODO
   - [ ] f-string
   - [ ] effect system. Algebraic effect?
   - [ ] const generic
   - [ ] try trait
   - [ ] GC
   - [ ] macro
   - [ ] HKT
   - [ ] curry and pipe
   - [ ] IR. How many? What kind?
