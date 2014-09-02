/*
 * Name:           SVCOMP-ChenFlurMukhopadhyay-SAS12
 * Linear-program: true
 * Linear-rank:    unk
 * Conditional:    false
 * Float:          false
 * Bitvector:      unk
 * Lexicographic:  unk
 * Terminates:     true
 * Bibtex:         Chen:2012:TPL:2414936.2414966
 */

/*
 * Program from Fig.1 of
 * 2012SAS - Chen,Flur,Mukhopadhyay - Termination Proofs for Linear Simple Loops
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main()
{
  int x, y, z;

  while (x > 0) {
    x = x + y;
    y = z;
    z = -z - 1;
  }
}
