   Expr: ((y >>s y) >>s ((y >>s y) >>s (y >>s y)))

Found a 3-operation program:
   shrs  r1,ry,ry
   shrs  r2,r1,r1
   shrs  r3,r2,r2
   Expr: (((y >>s y) >>s (y >>s y)) >>s ((y >>s y) >>s (y >>s y)))
Found 2284262 solutions.
Counters = 211, 72162, 5426498, total = 5498871
Process time = 11.980 secs
