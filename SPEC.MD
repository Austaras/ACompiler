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
   - all functions are mutually recursive
   - internal mutable
   - no auto boxing, provide generic reference type(s) tracked by GC
   - user can roll their own container as in Rust
3. suffix is .adf which stands for Advanced Dominance Fighter
4. Major TODO
   - [ ] f-string
   - [ ] module system and linking
   - [ ] effect system
   - [ ] orphan rule, specification
   - [ ] const generic
   - [ ] try trait
   - [ ] GC
   - [ ] macro
   - [ ] HKT
   - [ ] IR. How many? What kind?

### Syntax Construct

See AST and parser

### Semantic

As one would normally imagine
