### Design Decision

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call, = for assign, == for equal, != for not equal
   - not whitespace sensitive, but without mandatory semicolons
   - variant has their own namespace
   - also break/continue/return
2. suffix is .adf which stands for Advanced Dominance Fighter

### Syntax Construct

<> means optional, [] means array

```
Boolean:: true | false

String:: "[\*]"

Char:: '[\*]'

Literal:: Boolean | Int | Float | String

Expr:: AssignExpr | BinExpr | BlockExpr | CallExpr | Identifier | IfExpr | Litreal | MemberExpr | RangeExpr | UnaryExpr

Identifier:: starts with \_ or a-zA-Z, and contains only number or alphabet

BlockExpr:: { [Expr (\n|;)] }

IfExpr:: if Expr then BlockExpr \<else BlockExpr\>

ArithmeticOp:: + - * / % ** & | ^ && ||

AssignOp:: ArithmeticOrLogicalOp= | =

BinaryOp:: ArithmeticOrLogicalOp | == != > < >= <= |>

AssignExpr:: Expr AssignOp Expr

BinExpr:: Expr BinaryOp Expr

CallExpr:: Expr<::<[Expr, ]+>>( [Expr, ] )

MemberExpr:: Expr .Identifier | .Int | [Expr]

RangeExpr:: Expr ..|..= Expr

UnaryExpr:: Op Expr

Stmt:: ExprStmt | LetStmt | UseStmt | FnStmt
```

### Semantic

As one would normally imagine
