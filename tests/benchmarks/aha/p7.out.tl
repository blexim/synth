   Expr: (((-2 - x) & x) + 1)

Found a 3-operation program:
   sub   r1,-2,rx
   or    r2,r1,rx
   not   r3,r2
   Expr: ~(((-2 - x) | x))
Found 11 solutions.
Counters = 8469, 28839, 1739240, total = 1776548
Process time = 0.030 secs
