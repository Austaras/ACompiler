Test out various compiler technology with a toy compiler for a toy language **in between** rust and OCaml. Referenced source including but not limited to:

- _Modern Compiler Implementation in ML_
- _Engineering a Compiler_
- _OCaml Programming: Correct + Efficient + Beautiful_

### Design Decisions

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call, = for assign, == for equal, != for not equal, |a, b| a + b for closure
   - not whitespace sensitive, but without mandatory semicolons; if there's ambiguity, **prefer line break**
   - variant has their own namespace
   - break/continue/return/struct/enum keyword
2. ML semantic with Rust characteristics
   - HM type inference with trait and operator overloading
   - c style function declaration that are hoisted and can only refer to values in outer scope
   - internal mutable
   - impl block, but user need to import that module to work
   - string is UTF8 and char is UTF32
3. Pratically functional
   - provide immutable std lib and tail call optimization
   - but also mutable std lib and control keyword
4. Focus on performance and optimization
   - no auto boxing, provide general reference type(s) tracked by GC
   - user can roll their own container like in Rust
5. suffix is .adf which stands for **A**dvanced **D**ominance **F**unctional language
6. Major decisions TODO
   - [ ] template string
   - [ ] effect system. Algebraic effect?
   - [ ] const generic
   - [ ] refinement type
   - [ ] ABI
   - [ ] GC
   - [ ] macro
   - [ ] curry and pipe
   - [ ] IR. How many? What kind?
   - [ ] Fn trait?
   - [ ] Immtuable mark?
