### Design Decisions

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call, = for assign, == for equal, != for not equal, |a, b| a + b for closure
   - not whitespace sensitive, but without mandatory semicolons; if there's ambiguity, **prefer line break**
   - break/continue/return/struct/enum keyword
2. ML semantic with Rust characteristics
   - HM type inference with trait and operator overloading
   - c style function declaration that are hoisted and cannot capture environment
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
   - [ ] effect system, immtuable, pure, lazy
   - [ ] const generic
   - [ ] refinement type
   - [ ] ABI
   - [ ] GC
   - [ ] macro
   - [ ] curry and pipe
   - [ ] Fn trait
