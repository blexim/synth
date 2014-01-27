
Found a 4-operation program:
   shrs  r1,rx,31
   shrs  r2,rx,r1
   divu  r3,r2,rx
   or    r4,r3,r1
   Expr: (((x >>s (x >>s 31)) /u x) | (x >>s 31))
Found 48 solutions.
Counters = 31236757, 31257127, 38236374, 557606966, total = 658337224
Process time = 11.840 secs
