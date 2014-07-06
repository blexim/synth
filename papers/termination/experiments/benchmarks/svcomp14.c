/*
 * Name:           SVCOMP-GulwaniJainKoskinen-PLDI2009
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/pldi/GulwaniJK09
 */
//#Termination
/*
 * Program from Fig.1a of
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 *
 * Date: 9.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main()
{
  int id = nondet();
  int maxId = nondet();

  if (0 > id || id >= maxId) {
    return 0;
  }


  int tmp = id + 1;
  while (tmp != id && nondet()) {
    if (tmp <= maxId) {
      tmp = tmp + 1;
    } else {
      tmp = 0;
    }
  }


  return 0;
}
