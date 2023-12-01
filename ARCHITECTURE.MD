1. plain ADT for AST

   [AST](./src/AST)

2. hand written recursive descendant parser

   [Parser](./src/Parser)

3. HM type inference with trait

   [Semantic](./src/Semantic)

4. FLIR, which stands for First Low-level Intermediate Representation

   [FLIR](./src/FLIR)

   - eliminates ADT, operator overloading, assign operator and pattern
   - lambda lifting
   - monotyped
   - register based
   - basic block
   - De Bruijn index

5. ATIR, which stands for A Tiger Intermediate Representation

   [ATIR](./src/ATIR)

   - originates from Tiger Book
   - tree style
   - stack based
   - subject to be removed
