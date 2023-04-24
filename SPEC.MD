### Design Decision

1. ML syntax with Rust characteristics
   - That means, {} for block, => for pattern match, fn for function, () for function call
   - not whitespace sensitive, but without mandatory semicolons
   - = for assign, == for equal, allows arbitary infix operator with an alphabet of `<=>&|+-*/%!` except `->` and `=>`
   - variant has their own namespace
   - also break/continue/return
2. suffix is .adf which stands for Advanced Dominance Fighter

### Syntax Construct

<> means optional, [] means array

Boolean:: true | false

String:: "[\*]" | '[\*]'

Literal:: Boolean | Int | Float | String

Expr:: BinExpr | CallExpr | BlockExpr | Identifier | IfExpr | Litreal

Identifier:: starts with \_ or a-zA-Z, and contains only number or alphabet

BlockExpr:: { [Expr (\n|;)] }

IfExpr:: if Expr then BlockExpr \<else BlockExpr\>

BinOp:: + - \* / < > | & or their combination

BinExpr:: Expr BinOp Expr

CallExpr:: Expr( [Expr, ] )

### Semantic

As one would normally imagine
