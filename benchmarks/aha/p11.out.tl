   Expr: (1 << ((y >>s y) >>s (y >>s y)))

Found a 3-operation program:
   shrs  r1,ry,ry
   shrs  r2,r1,r1
   shr   r3,1,r2
   Expr: (1 >>u ((y >>s y) >>s (y >>s y)))
Found 398302 solutions.
Counters = 211, 72162, 5426498, total = 5498871
Process time = 2.210 secs
