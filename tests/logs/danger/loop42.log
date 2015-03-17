Running with args: ['./kalashnikov.py', '--seed=1337', '--strategy=evolve', '-v', '--nondet=2', '-P3', '--evars', '4', '-a4', '../../tests/loops/danger.c', '/tmp/loop42.c', '--varnames', 'nondet0', 'nondet1', 'x', 'y']
Using seed: 1337
[]
Fastest checker: genetic
Evars: 1, 0, 7, 7
Program 0:
t1 = ~(nondet1);
res1 = 0x1 / y;
Program 1:
t1 = ~(0x0);
t2 = y ==> y;
res1 = t1 s< 0x1;
Program 2:
res1 = nondet0 >> 0x1;

Fastest checker: explicit
Fails for (0, 0, 0, 0)

[]
Fastest checker: genetic
Evars: 6, 4, 1, 2
Program 0:
t1 = 0x1 & 0x0;
res1 = x == nondet0;
Program 1:
t1 = nondet1 <= nondet1;
t2 = 0x1 ? nondet0 : nondet0;
res1 = y ? 0x1 : t1;
Program 2:
t1 = -(y);
t2 = y <= x;
res1 = y s<= nondet0;

Fastest checker: explicit
Fails for (0, 0, 0, 3)

[]
Fastest checker: genetic
Evars: 6, 2, 4, 6
Program 0:
t1 = nondet1 != 0x1;
res1 = 0x1 == y;
Program 1:
t1 = ~(x);
res1 = t1 ^ y;
Program 2:
t1 = y ? x : x;
t2 = 0x1 ^ t1;
res1 = y / y;

Fastest checker: explicit
Fails for (0, 0, 0, 1)

[]
Fastest checker: genetic
Evars: 7, 7, 3, 0
Program 0:
t1 = x ==> nondet0;
t2 = y <= 0x1;
res1 = x ? 0x0 : y;
Program 1:
t1 = x >>> nondet1;
res1 = x s<= t1;
Program 2:
t1 = 0x0 - y;
t2 = 0x0 + 0x0;
res1 = 0x0 + 0x0;

Fastest checker: explicit
Fails for (0, 0, 0, 7)

[]
Fastest checker: genetic
Evars: 3, 1, 5, 3
Program 0:
res1 = 0x1 == y;
Program 1:
t1 = 0x1 + 0x1;
res1 = 0x0 + 0x0;
Program 2:
t1 = -(0x0);
t2 = ~(nondet0);
res1 = x ==> t1;

Fastest checker: explicit
Fails for (0, 0, 1, 1)

[]
Fastest checker: genetic
Evars: 3, 1, 0, 4
Program 0:
res1 = y != x;
Program 1:
t1 = nondet0 != y;
t2 = 0x1 + nondet1;
res1 = -(0x1);
Program 2:
t1 = nondet1 - y;
res1 = nondet0 - y;

Fastest checker: explicit
Fails for (0, 0, 1, 0)

[]
Fastest checker: genetic
Evars: 7, 5, 4, 5
Program 0:
res1 = 0x1 == y;
Program 1:
t1 = 0x0 <= nondet0;
t2 = 0x1 & y;
res1 = -(nondet0);
Program 2:
t1 = ~(x);
res1 = nondet1 + nondet1;

Fastest checker: explicit
Correct for wordlen=3
Fastest checker: cbmc
Also correct for wordlen=32!







Finished in 7.40s

Evars: 7, 5, 4, 5
Program 0:
res1 = 0x1 == y;
Program 1:
t1 = 0x0 <= nondet0;
t2 = 0x1 & y;
res1 = -(nondet0);
Program 2:
t1 = ~(x);
res1 = nondet1 + nondet1;


Perf counters:
{'genetic': 7, 'cbmc': 1, 'explicit': 7, 'iterations': 7}
Perf timers:
verify: 4.47s
checker: 7.38s
gcc: 3.32s
_: 7.40s
synth: 2.93s
