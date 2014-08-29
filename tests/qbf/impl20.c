
#include "synth.h"

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];
  word_t eargs[NARGS];
  int i;
  int ret = 0;

  word_t x1 = sol->evars[0];
  word_t x2 = sol->evars[1];
  word_t x3 = sol->evars[2];
  word_t x4 = args[0];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  exec(&sol->progs[3], eargs, res);
  word_t x5 = res[0];
  exec(&sol->progs[4], eargs, res);
  word_t x6 = res[0];
  exec(&sol->progs[5], eargs, res);
  word_t x7 = res[0];
  word_t x8 = args[1];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  exec(&sol->progs[6], eargs, res);
  word_t x9 = res[0];
  exec(&sol->progs[7], eargs, res);
  word_t x10 = res[0];
  exec(&sol->progs[8], eargs, res);
  word_t x11 = res[0];
  word_t x12 = args[2];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  exec(&sol->progs[9], eargs, res);
  word_t x13 = res[0];
  exec(&sol->progs[10], eargs, res);
  word_t x14 = res[0];
  exec(&sol->progs[11], eargs, res);
  word_t x15 = res[0];
  word_t x16 = args[3];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  exec(&sol->progs[12], eargs, res);
  word_t x17 = res[0];
  exec(&sol->progs[13], eargs, res);
  word_t x18 = res[0];
  exec(&sol->progs[14], eargs, res);
  word_t x19 = res[0];
  word_t x20 = args[4];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  exec(&sol->progs[15], eargs, res);
  word_t x21 = res[0];
  exec(&sol->progs[16], eargs, res);
  word_t x22 = res[0];
  exec(&sol->progs[17], eargs, res);
  word_t x23 = res[0];
  word_t x24 = args[5];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  exec(&sol->progs[18], eargs, res);
  word_t x25 = res[0];
  exec(&sol->progs[19], eargs, res);
  word_t x26 = res[0];
  exec(&sol->progs[20], eargs, res);
  word_t x27 = res[0];
  word_t x28 = args[6];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  exec(&sol->progs[21], eargs, res);
  word_t x29 = res[0];
  exec(&sol->progs[22], eargs, res);
  word_t x30 = res[0];
  exec(&sol->progs[23], eargs, res);
  word_t x31 = res[0];
  word_t x32 = args[7];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  exec(&sol->progs[24], eargs, res);
  word_t x33 = res[0];
  exec(&sol->progs[25], eargs, res);
  word_t x34 = res[0];
  exec(&sol->progs[26], eargs, res);
  word_t x35 = res[0];
  word_t x36 = args[8];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  exec(&sol->progs[27], eargs, res);
  word_t x37 = res[0];
  exec(&sol->progs[28], eargs, res);
  word_t x38 = res[0];
  exec(&sol->progs[29], eargs, res);
  word_t x39 = res[0];
  word_t x40 = args[9];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  exec(&sol->progs[30], eargs, res);
  word_t x41 = res[0];
  exec(&sol->progs[31], eargs, res);
  word_t x42 = res[0];
  exec(&sol->progs[32], eargs, res);
  word_t x43 = res[0];
  word_t x44 = args[10];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  exec(&sol->progs[33], eargs, res);
  word_t x45 = res[0];
  exec(&sol->progs[34], eargs, res);
  word_t x46 = res[0];
  exec(&sol->progs[35], eargs, res);
  word_t x47 = res[0];
  word_t x48 = args[11];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  exec(&sol->progs[36], eargs, res);
  word_t x49 = res[0];
  exec(&sol->progs[37], eargs, res);
  word_t x50 = res[0];
  exec(&sol->progs[38], eargs, res);
  word_t x51 = res[0];
  word_t x52 = args[12];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  exec(&sol->progs[39], eargs, res);
  word_t x53 = res[0];
  exec(&sol->progs[40], eargs, res);
  word_t x54 = res[0];
  exec(&sol->progs[41], eargs, res);
  word_t x55 = res[0];
  word_t x56 = args[13];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  exec(&sol->progs[42], eargs, res);
  word_t x57 = res[0];
  exec(&sol->progs[43], eargs, res);
  word_t x58 = res[0];
  exec(&sol->progs[44], eargs, res);
  word_t x59 = res[0];
  word_t x60 = args[14];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  exec(&sol->progs[45], eargs, res);
  word_t x61 = res[0];
  exec(&sol->progs[46], eargs, res);
  word_t x62 = res[0];
  exec(&sol->progs[47], eargs, res);
  word_t x63 = res[0];
  word_t x64 = args[15];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  eargs[15] = x64;
  exec(&sol->progs[48], eargs, res);
  word_t x65 = res[0];
  exec(&sol->progs[49], eargs, res);
  word_t x66 = res[0];
  exec(&sol->progs[50], eargs, res);
  word_t x67 = res[0];
  word_t x68 = args[16];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  eargs[15] = x64;
  eargs[16] = x68;
  exec(&sol->progs[51], eargs, res);
  word_t x69 = res[0];
  exec(&sol->progs[52], eargs, res);
  word_t x70 = res[0];
  exec(&sol->progs[53], eargs, res);
  word_t x71 = res[0];
  word_t x72 = args[17];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  eargs[15] = x64;
  eargs[16] = x68;
  eargs[17] = x72;
  exec(&sol->progs[54], eargs, res);
  word_t x73 = res[0];
  exec(&sol->progs[55], eargs, res);
  word_t x74 = res[0];
  exec(&sol->progs[56], eargs, res);
  word_t x75 = res[0];
  word_t x76 = args[18];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  eargs[15] = x64;
  eargs[16] = x68;
  eargs[17] = x72;
  eargs[18] = x76;
  exec(&sol->progs[57], eargs, res);
  word_t x77 = res[0];
  exec(&sol->progs[58], eargs, res);
  word_t x78 = res[0];
  exec(&sol->progs[59], eargs, res);
  word_t x79 = res[0];
  word_t x80 = args[19];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  eargs[2] = x12;
  eargs[3] = x16;
  eargs[4] = x20;
  eargs[5] = x24;
  eargs[6] = x28;
  eargs[7] = x32;
  eargs[8] = x36;
  eargs[9] = x40;
  eargs[10] = x44;
  eargs[11] = x48;
  eargs[12] = x52;
  eargs[13] = x56;
  eargs[14] = x60;
  eargs[15] = x64;
  eargs[16] = x68;
  eargs[17] = x72;
  eargs[18] = x76;
  eargs[19] = x80;
  exec(&sol->progs[60], eargs, res);
  word_t x81 = res[0];
  exec(&sol->progs[61], eargs, res);
  word_t x82 = res[0];
  if (x1) ret += 1;
  if (x4 || x5 || !x1) ret += 1;
  if (x4 || x1 || !x5) ret += 1;
  if (x4 || x6 || !x3) ret += 1;
  if (x4 || x3 || !x6) ret += 1;
  if (x5 || !x4 || !x3) ret += 1;
  if (x3 || !x4 || !x5) ret += 1;
  if (x6 || !x4 || !x2) ret += 1;
  if (x2 || !x4 || !x6) ret += 1;
  if (x9 || !x8 || !x5) ret += 1;
  if (x5 || !x8 || !x9) ret += 1;
  if (x10 || !x8 || !x7) ret += 1;
  if (x7 || !x8 || !x10) ret += 1;
  if (x8 || x9 || !x7) ret += 1;
  if (x8 || x7 || !x9) ret += 1;
  if (x8 || x10 || !x6) ret += 1;
  if (x8 || x6 || !x10) ret += 1;
  if (x12 || x13 || !x9) ret += 1;
  if (x12 || x9 || !x13) ret += 1;
  if (x12 || x14 || !x11) ret += 1;
  if (x12 || x11 || !x14) ret += 1;
  if (x13 || !x12 || !x11) ret += 1;
  if (x11 || !x12 || !x13) ret += 1;
  if (x14 || !x12 || !x10) ret += 1;
  if (x10 || !x12 || !x14) ret += 1;
  if (x17 || !x16 || !x13) ret += 1;
  if (x13 || !x16 || !x17) ret += 1;
  if (x18 || !x16 || !x15) ret += 1;
  if (x15 || !x16 || !x18) ret += 1;
  if (x16 || x17 || !x15) ret += 1;
  if (x16 || x15 || !x17) ret += 1;
  if (x16 || x18 || !x14) ret += 1;
  if (x16 || x14 || !x18) ret += 1;
  if (x20 || x21 || !x17) ret += 1;
  if (x20 || x17 || !x21) ret += 1;
  if (x20 || x22 || !x19) ret += 1;
  if (x20 || x19 || !x22) ret += 1;
  if (x21 || !x20 || !x19) ret += 1;
  if (x19 || !x20 || !x21) ret += 1;
  if (x22 || !x20 || !x18) ret += 1;
  if (x18 || !x20 || !x22) ret += 1;
  if (x25 || !x24 || !x21) ret += 1;
  if (x21 || !x24 || !x25) ret += 1;
  if (x26 || !x24 || !x23) ret += 1;
  if (x23 || !x24 || !x26) ret += 1;
  if (x24 || x25 || !x23) ret += 1;
  if (x24 || x23 || !x25) ret += 1;
  if (x24 || x26 || !x22) ret += 1;
  if (x24 || x22 || !x26) ret += 1;
  if (x28 || x29 || !x25) ret += 1;
  if (x28 || x25 || !x29) ret += 1;
  if (x28 || x30 || !x27) ret += 1;
  if (x28 || x27 || !x30) ret += 1;
  if (x29 || !x28 || !x27) ret += 1;
  if (x27 || !x28 || !x29) ret += 1;
  if (x30 || !x28 || !x26) ret += 1;
  if (x26 || !x28 || !x30) ret += 1;
  if (x33 || !x32 || !x29) ret += 1;
  if (x29 || !x32 || !x33) ret += 1;
  if (x34 || !x32 || !x31) ret += 1;
  if (x31 || !x32 || !x34) ret += 1;
  if (x32 || x33 || !x31) ret += 1;
  if (x32 || x31 || !x33) ret += 1;
  if (x32 || x34 || !x30) ret += 1;
  if (x32 || x30 || !x34) ret += 1;
  if (x36 || x37 || !x33) ret += 1;
  if (x36 || x33 || !x37) ret += 1;
  if (x36 || x38 || !x35) ret += 1;
  if (x36 || x35 || !x38) ret += 1;
  if (x37 || !x36 || !x35) ret += 1;
  if (x35 || !x36 || !x37) ret += 1;
  if (x38 || !x36 || !x34) ret += 1;
  if (x34 || !x36 || !x38) ret += 1;
  if (x41 || !x40 || !x37) ret += 1;
  if (x37 || !x40 || !x41) ret += 1;
  if (x42 || !x40 || !x39) ret += 1;
  if (x39 || !x40 || !x42) ret += 1;
  if (x40 || x41 || !x39) ret += 1;
  if (x40 || x39 || !x41) ret += 1;
  if (x40 || x42 || !x38) ret += 1;
  if (x40 || x38 || !x42) ret += 1;
  if (x44 || x45 || !x41) ret += 1;
  if (x44 || x41 || !x45) ret += 1;
  if (x44 || x46 || !x43) ret += 1;
  if (x44 || x43 || !x46) ret += 1;
  if (x45 || !x44 || !x43) ret += 1;
  if (x43 || !x44 || !x45) ret += 1;
  if (x46 || !x44 || !x42) ret += 1;
  if (x42 || !x44 || !x46) ret += 1;
  if (x49 || !x48 || !x45) ret += 1;
  if (x45 || !x48 || !x49) ret += 1;
  if (x50 || !x48 || !x47) ret += 1;
  if (x47 || !x48 || !x50) ret += 1;
  if (x48 || x49 || !x47) ret += 1;
  if (x48 || x47 || !x49) ret += 1;
  if (x48 || x50 || !x46) ret += 1;
  if (x48 || x46 || !x50) ret += 1;
  if (x52 || x53 || !x49) ret += 1;
  if (x52 || x49 || !x53) ret += 1;
  if (x52 || x54 || !x51) ret += 1;
  if (x52 || x51 || !x54) ret += 1;
  if (x53 || !x52 || !x51) ret += 1;
  if (x51 || !x52 || !x53) ret += 1;
  if (x54 || !x52 || !x50) ret += 1;
  if (x50 || !x52 || !x54) ret += 1;
  if (x57 || !x56 || !x53) ret += 1;
  if (x53 || !x56 || !x57) ret += 1;
  if (x58 || !x56 || !x55) ret += 1;
  if (x55 || !x56 || !x58) ret += 1;
  if (x56 || x57 || !x55) ret += 1;
  if (x56 || x55 || !x57) ret += 1;
  if (x56 || x58 || !x54) ret += 1;
  if (x56 || x54 || !x58) ret += 1;
  if (x60 || x61 || !x57) ret += 1;
  if (x60 || x57 || !x61) ret += 1;
  if (x60 || x62 || !x59) ret += 1;
  if (x60 || x59 || !x62) ret += 1;
  if (x61 || !x60 || !x59) ret += 1;
  if (x59 || !x60 || !x61) ret += 1;
  if (x62 || !x60 || !x58) ret += 1;
  if (x58 || !x60 || !x62) ret += 1;
  if (x65 || !x64 || !x61) ret += 1;
  if (x61 || !x64 || !x65) ret += 1;
  if (x66 || !x64 || !x63) ret += 1;
  if (x63 || !x64 || !x66) ret += 1;
  if (x64 || x65 || !x63) ret += 1;
  if (x64 || x63 || !x65) ret += 1;
  if (x64 || x66 || !x62) ret += 1;
  if (x64 || x62 || !x66) ret += 1;
  if (x68 || x69 || !x65) ret += 1;
  if (x68 || x65 || !x69) ret += 1;
  if (x68 || x70 || !x67) ret += 1;
  if (x68 || x67 || !x70) ret += 1;
  if (x69 || !x68 || !x67) ret += 1;
  if (x67 || !x68 || !x69) ret += 1;
  if (x70 || !x68 || !x66) ret += 1;
  if (x66 || !x68 || !x70) ret += 1;
  if (x73 || !x72 || !x69) ret += 1;
  if (x69 || !x72 || !x73) ret += 1;
  if (x74 || !x72 || !x71) ret += 1;
  if (x71 || !x72 || !x74) ret += 1;
  if (x72 || x73 || !x71) ret += 1;
  if (x72 || x71 || !x73) ret += 1;
  if (x72 || x74 || !x70) ret += 1;
  if (x72 || x70 || !x74) ret += 1;
  if (x76 || x77 || !x73) ret += 1;
  if (x76 || x73 || !x77) ret += 1;
  if (x76 || x78 || !x75) ret += 1;
  if (x76 || x75 || !x78) ret += 1;
  if (x77 || !x76 || !x75) ret += 1;
  if (x75 || !x76 || !x77) ret += 1;
  if (x78 || !x76 || !x74) ret += 1;
  if (x74 || !x76 || !x78) ret += 1;
  if (x81 || !x80 || !x77) ret += 1;
  if (x77 || !x80 || !x81) ret += 1;
  if (x82 || !x80 || !x79) ret += 1;
  if (x79 || !x80 || !x82) ret += 1;
  if (x80 || x81 || !x79) ret += 1;
  if (x80 || x79 || !x81) ret += 1;
  if (x80 || x82 || !x78) ret += 1;
  if (x80 || x78 || !x82) ret += 1;
  if (x82 || !x81) ret += 1;

  return ret;
}
