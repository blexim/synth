   Expr: (((x | x) - 1) & (x | x))

Found a 3-operation program:
   shrs  r1,-2,rx
   add   r2,r1,rx
   and   r3,r2,rx
   Expr: (((-2 >>s x) + x) & x)
Found 47 solutions.
Counters = 16806, 37176, 1747577, total = 1801559
Process time = 0.040 secs
