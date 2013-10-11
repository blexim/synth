   Expr: (((x >>s 31) | 1)*x)

Found a 3-operation program:
   shrs  r1,rx,31
   xor   r2,r1,rx
   sub   r3,r2,r1
   Expr: (((x >>s 31) ^ x) - (x >>s 31))
Found 4 solutions.
Counters = 35473, 55843, 1766244, total = 1857560
Process time = 0.040 secs
