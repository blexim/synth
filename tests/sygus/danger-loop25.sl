(set-logic BV)

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(declare-var lockstate (BitVec 32))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32)))
                (BitVec 32)
                (ite (= x #x00000000) z y))

(define-fun expand ((x Bool))
                   (BitVec 32)
                   (ite x #x00000001 #x00000000))

(define-fun contract ((x (BitVec 32)))
                     Bool
                     (not (= x #x00000000)))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((x (BitVec 32)) (y (BitVec 32)))
              Bool
              (not (= x y)))

(define-fun B_x ((y (BitVec 32)))
                (BitVec 32)
                y)

(define-fun B_y ((y (BitVec 32)) (n (BitVec 32)))
                (BitVec 32)
                (if0 n y (bvadd y #x00000001)))

(define-fun B_lockstate ((n (BitVec 32)))
                        (BitVec 32)
                        (if0 n #x00000000 #x00000001))

(define-fun A ((lockstate (BitVec 32)))
              Bool
              (= lockstate #x00000000))


(synth-fun D ((x (BitVec 32)) (y (BitVec 32)) (lockstate (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
    lockstate
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

(synth-fun R ((x (BitVec 32)) (y (BitVec 32)) (lockstate (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
    lockstate
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

(synth-fun S ((x (BitVec 32)) (y (BitVec 32)) (lockstate (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
    lockstate
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

(synth-fun y0 ((x (BitVec 32)) (y (BitVec 32)) (lockstate (BitVec 32))) (BitVec 32)
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

(synth-fun n0 ((x (BitVec 32)) (y (BitVec 32)) (lockstate (BitVec 32))) (BitVec 32)
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

(define-fun x0 ((y (BitVec 32))) (BitVec 32) y)

(define-fun lockstate0 ((n (BitVec 32)))
                       (BitVec 32)
                       (if0 n #x00000001 #x00000000))

(define-fun y1 ((y (BitVec 32)) (n (BitVec 32)))
               (BitVec 32)
               (if0 n y (bvadd y #x00000001)))

(constraint (implies
             (and (contract (D x y lockstate)) (G x y))
             (and
              (bvugt (R x y lockstate) #x00000000)
              (and
               (bvugt (R x y lockstate) (R (B_x y) (B_y y (S x y lockstate)) (B_lockstate (S x y lockstate))))
               (contract (D (B_x y) (B_y y (S x y lockstate)) (B_lockstate (S x y lockstate))))))))

(constraint (implies
             (and (not (= (D x y lockstate) #x00000000)) (not (G x y)))
             (not (A lockstate))))

(constraint (contract (D (x0 (y0 x y lockstate)) (y1 (y0 x y lockstate) (n0 x y lockstate)) (lockstate0 (n0 x y lockstate)))))

(check-synth)
