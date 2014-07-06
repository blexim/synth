/*
 * Name:           SVCOMP-BradleyMannaSipma-2005CAV-1
 * Linear-program: true
 * Linear-rank:    unk
 * Conditional:    true
 * Float:          false
 * Bitvector:      unk
 * Lexicographic:  unk
 * Terminates:     false
 * Bibtex:         DBLP:conf/cav/BradleyMS05
 */

int main(void)
{
  int y1, y2;

  if (y1 <= 0 || y2 <= 0) {
    return 0;
  }

  while (y1 != y2) {
    if (y1 > y2) {
      y1 = y1 - y2;
    } else {
      y2 = y2 - y2;
    }
  }
}
