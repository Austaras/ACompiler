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
   - impl block, but user need to import that module to work
3. suffix is .adf which stands for Advanced Dominance Fighter
4. Major TODO
   - [ ] f-string
   - [ ] effect systemd. Algebraic effect?
   - [ ] const generic
   - [ ] try trait
   - [ ] GC
   - [ ] macro
   - [ ] HKT
   - [ ] IR. How many? What kind?

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
ASSIGN :: += -= *= /= &= |= ^= &&= ||= <<= >>=
BINARY :: + - * / & | ^ && || << >> == >= <= != < > |> as
Unary :: - * &
```

### Semantic

As one would normally imagine

#### Type System
