
Found a 4-operation program:
   shl   r1,rx,1
   and   r2,r1,rx
   mul   r3,rx,-2
   and   r4,r3,r2
   Expr: ((x*-2) & ((x << 1) & x))
Found 68 solutions.
Counters = 6225486, 6245856, 13225103, 532595695, total = 558292140
Process time = 10.460 secs
