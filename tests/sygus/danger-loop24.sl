(set-logic BV)

(declare-var a (BitVec 32))
(declare-var c (BitVec 32))
(declare-var i (BitVec 32))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((i (BitVec 32)))
              Bool
              (bvult i #x00010003))

(define-fun B_c ((c (BitVec 32)) (i (BitVec 32)))
                (BitVec 32)
                (bvadd c i))

(define-fun B_i ((i (BitVec 32)))
                (BitVec 32)
                (bvadd i #x00000001))


(define-fun A ((a (BitVec 32)))
              Bool
              (bvugt a #x00000000))


(synth-fun D ((i (BitVec 32)) (c (BitVec 32)) (a (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
   i
   c
   a
             (bvxor Start Start)
             (bvand Start Start)
             (bvor Start Start)
             (bvnot Start)
             (bvneg Start)
             (bvadd Start Start)
             (bvmul Start Start)
             (bvudiv Start Start)
             (bvurem Start Start)
             (bvlshr Start Start)
             (bvashr Start Start)
             (bvshl Start Start)
             (bvsdiv Start Start)
             (bvsrem Start Start)
             (bvsub Start Start)
             (if0 Start Start Start)
             (expand (bvule Start Start))
             (expand (bvult Start Start))
             (expand (bvuge Start Start))
             (expand (bvugt Start Start))
             (expand (bvsle Start Start))
             (expand (bvslt Start Start))
             (expand (bvsgt Start Start))
             (expand (= Start Start))
             (expand (not (= Start Start)))
             #x00000001
             #x00000000
             #xFFFFFFFF
             ))))

(synth-fun R ((i (BitVec 32)) (c (BitVec 32)) (a (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
   i
   c
   a
             (bvxor Start Start)
             (bvand Start Start)
             (bvor Start Start)
             (bvnot Start)
             (bvneg Start)
             (bvadd Start Start)
             (bvmul Start Start)
             (bvudiv Start Start)
             (bvurem Start Start)
             (bvlshr Start Start)
             (bvashr Start Start)
             (bvshl Start Start)
             (bvsdiv Start Start)
             (bvsrem Start Start)
             (bvsub Start Start)
             (if0 Start Start Start)
             (expand (bvule Start Start))
             (expand (bvult Start Start))
             (expand (bvuge Start Start))
             (expand (bvugt Start Start))
             (expand (bvsle Start Start))
             (expand (bvslt Start Start))
             (expand (bvsgt Start Start))
             (expand (= Start Start))
             (expand (not (= Start Start)))
             #x00000001
             #x00000000
             #xFFFFFFFF
             ))))

(synth-fun a0 ((i (BitVec 32)) (c (BitVec 32)) (a (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
             (bvxor Start Start)
             (bvand Start Start)
             (bvor Start Start)
             (bvnot Start)
             (bvneg Start)
             (bvadd Start Start)
             (bvmul Start Start)
             (bvudiv Start Start)
             (bvurem Start Start)
             (bvlshr Start Start)
             (bvashr Start Start)
             (bvshl Start Start)
             (bvsdiv Start Start)
             (bvsrem Start Start)
             (bvsub Start Start)
             (if0 Start Start Start)
             (expand (bvule Start Start))
             (expand (bvult Start Start))
             (expand (bvuge Start Start))
             (expand (bvugt Start Start))
             (expand (bvsle Start Start))
             (expand (bvslt Start Start))
             (expand (bvsgt Start Start))
             (expand (= Start Start))
             (expand (not (= Start Start)))
             #x00000001
             #x00000000
             #xFFFFFFFF
             ))))

(constraint (implies
             (and (not (= (D i c a) #x00000000)) (G i))
             (and
              (bvugt (R i c a) #x00000000)
              (and
               (bvugt (R i c a) (R (B_i i) (B_c i c) a))
               (not (= (D (B_i i) (B_c i c) a) #x00000000))))))

(constraint (implies
             (and (not (= (D i c a) #x00000000)) (not (G i)))
             (not (A a))))

(constraint (not (= (D #x00000000 #x00000000 (a0 i c a)) #x00000000)))

(check-synth)
