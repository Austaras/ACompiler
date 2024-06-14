Test out various compiler technology with a toy compiler for a toy language **in between** rust and OCaml.

### Reference Material

#### Book

- _Modern Compiler Implementation in ML_
- _Engineering a Compiler_
- _Programming Language Concepts_
- _Compilers: Principles, Techniques, and Tools_

#### Paper

- _Typing Haskell in Haskell_
- _Type classes: an exploration of the design space_
- _Type Classes with Functional Dependencies_

### Design Decisions

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call, = for assign, == for equal, != for not equal, |a, b| a + b for closure
   - not whitespace sensitive, but without mandatory semicolons; if there's ambiguity, **prefer line break**
   - break/continue/return/struct/enum keyword
2. ML semantic with Rust characteristics
   - HM type inference with trait and operator overloading
   - c style function declaration that are hoisted and cannot capture environment
   - internal mutable
   - impl block and trait, but user need to import them
   - string is UTF8 and char is UTF32
3. Pratically functional
   - provide immutable std lib and tail call optimization
   - but also mutable std lib and control keyword
4. Focus on performance and optimization
   - no auto boxing, provide general reference type(s) tracked by GC
   - no object header, no object identity
   - rust doesn't assume anything, ADF assumes memory allocation tracked by GC
   - user can roll their own container like in Rust
5. suffix is .adf which stands for **A**dvanced **D**ominance **F**unctional language

### Major TODO

#### Design decisions

- [ ] effect system, immtuable, pure, lazy
- [ ] region
- [ ] const generic
- [ ] refinement type
- [ ] ABI
- [ ] GC
- [ ] macro
- [ ] Fn trait

#### Implementation

- [ ] cross module type check
- [x] type class
  - [ ] multi parameter type class
  - [ ] functional dependency
  - [ ] existential type
- [ ] fixed size array
- [ ] IR lowering
  - [ ] SSA
  - [ ] generic

### Code Architecture

1. plain ADT for AST

   [AST](./src/Syntax/Library.fs)

2. hand written recursive descendant parser

   [Parser](./src/Syntax/Parser.fs)

3. HM type inference with trait

   [Semantic](./src/Semantic)

4. FLIR, which stands for First Linear Intermediate Representation

   [FLIR](./src/Optimize/Library.fs)

   - three address code, basic block, SSA
   - eliminates ADT, operator overloading, assign operator and pattern
   - lambda lifting
   - monotyped

### Syntax Construct

```hs
Module :: [ModuleItem]
ModuleItem :: <Visbility> Declaration
Visibility :: pub | intl
Declaration :: Function | Let | Const | Struct | Enum | TypeAlias | Use
Function :: fn IDENTIFIER ( [Argument, ] ) < -> Type > Block
Statement :: Declaration | Expression
Let :: let Pattern < : Type > = Expression
Const :: const IDENTIFIER < : Type > = Expression
Struct :: struct IDENTIFIER { [ IDENTIFIER: Type ] }
Enum :: enum IDENTIFIER { [ IDENTIFIER < ( [Type, ] ) > ] }
TypeAlias :: type IDENTIFIER = Type
Expression :: If | Match | Call | Binary | Unary | Field | Index | Assign
            | Closure | StructInit | Tuple | Array | Block
            | Range | For | While | Continue | Break | Return
            | Identifier | Literal | Path | Self
Block :: { [Statement (; | NewLine ) ] }
If :: if IfCond Block [else if Condition Block] <else Block>
Condition :: Expression | let Pattern = Expression
Match :: match { [ Pattern <if Expression> => Expression, ] }
Call :: Expression ( [Expression, ] )
Binary :: Expression BinaryOp Expression
Unary :: UNARY Expression
Field :: Expression . IDENTIFIER
Index :: Expression [ Expression ]
Assign :: LValue ASSIGN Expression
Closure :: < <[ TypeParam, ]> > | [ Argument, ] | < -> Type > Expression
StructInit :: IDENTIFIER { [ IDENTIFIER: Expression, ] < ...Expression > }
Tuple :: ( [ Expression, ] )
Array :: [ [ Expression, ] ] | [ Expression; Expression ]
Range :: <Expression>..<Expression>
For :: for <Pattner> in <Expression> Block
While :: While Condition Block
Continue :: continue
Break :: break
Return :: return < Expression >
Identifier :: IDENTIFIER
Literal :: IntLiteral | FloatLiteral | BoolLiteral | StringLiteral | CharLiteral
Self :: self

IDENTIFIER :: \uXID_Start[\uXID_Continue]
ASSIGN :: += -= *= /= &= |= ^= <<= >>=
BINARY :: + - * / & | ^ && || << >> == >= <= != < > |> as
Unary :: - * &
```
