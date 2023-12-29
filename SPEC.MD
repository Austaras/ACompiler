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

### Semantic

As one would normally imagine

#### Type System

#### ABI
