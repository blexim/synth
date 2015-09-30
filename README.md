The Kalashnikov Program Synthesiser
===================================

Kalashnikov is a fully automatic program synthesiser and second-order SAT solver.  As well
as a program synthesiser, Kalashnikov is a decision procedure for an NEXPTIME-complete logic,
which means you can use it for a very wide class of problems, including:

* Synthesising C programs from a specification (the specification is also given as a C program).
* Superoptimisation (producing optimal code that does the same thing as some other code).
* Finding bugs in C programs with no false alarms.
* Proving safety for C programs.
* Proving termination and non-termination of C programs.
* Automatic refactoring.
* Automatically finding complexity bounds.

Installation
------------

Currently the only operating system we support is Linux.

0. Make sure you have Python and the standard C toolchain installed, including `gcc`.
1. Download and install [CBMC](http://www.cprover.org/cbmc/).  Make sure to add it to your `PATH`.
2. Clone this repository.
3. Set the `KALASHNIKOVDIR` environment variable to point to the directory you just cloned into.
4. Add `$KALASHNIKOVDIR/src` to your `PATH`.
5. Run some examples!

### Example Installation in Ubuntu:

```
sudo apt-get install cbmc gcc python
git clone https://github.com/blexim/synth ~/kalashnikov
export KALASHNIKOVDIR=~/kalashnikov
export PATH=$PATH:$KALASHNIKOVDIR/src/kalashnikov
kalashnikov.py --help
```

Papers
------

* [Second-Order Propositional Satisfiability](http://arxiv.org/pdf/1409.4925): describes the synthesiser
itself, how it works, the problem it solves and the underlying theory.
* [Using Program Synthesis for Program Analysis](http://arxiv.org/abs/1508.07829): describes how Kalashnikov is optimised specifically for building program analyses.
* [Unrestricted Termination and Non-Termination Arguments for Bit-Vector Programs](http://arxiv.org/pdf/1410.5089): we used Kalashnikov to prove termination and non-termination for C programs.  The
tool we built for this paper is [Juggernaut](https://github.com/blexim/synth/blob/master/src/frontends/termination.py), which is slow but unstoppable.
* [Propositional Reasoning about Safety and Termination of Heap-Manipulating Programs](http://arxiv.org/pdf/1410.5088): this is a logic & associated decision procedure we made in order to use Kalashnikov
for reasoning about programs with linked lists.  The associated tool is [Shakira](https://github.com/blexim/synth/blob/master/src/shakira/shakira.sh), which checks that heaps don't lie.
* [Danger Invariants](http://arxiv.org/pdf/1503.05445): Kalashnikov can be used for finding very deep
bugs in C programs without false positives by searching for Danger Invariants.  The associated
tool is [Dangerzone](https://github.com/blexim/synth/blob/master/src/frontends/dangerzone.py).
