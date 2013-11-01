   Expr: (((x - 1) | x) ^ x)

Found a 3-operation program:
   sub   r1,rx,1
   xor   r2,r1,rx
   and   r3,r2,r1
   Expr: (((x - 1) ^ x) & (x - 1))
Found 11 solutions.
Counters = 26409, 46779, 1757180, total = 1830368
Process time = 0.040 secs
