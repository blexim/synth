(set-logic BV)

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32)))
                (BitVec 32)
                (ite (= x #x00000000) y z))

(define-fun expand ((x Bool))
                   (BitVec 32)
                   (ite x #x00000001 #x00000000))

(define-fun contract ((x (BitVec 32)))
                     Bool
                     (not (= x #x00000000)))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((x (BitVec 32)))
              Bool
              (bvult x #x00010003))

(define-fun B_x ((x (BitVec 32)) (n (BitVec 32)))
                (BitVec 32)
                (if0 n
                     x
                     (bvadd x #x00000001)))

(define-fun B_y ((y (BitVec 32)) (n (BitVec 32)))
                (BitVec 32)
                (if0 n
                     y
                     (bvadd y #x00000001)))

(define-fun A ((x (BitVec 32)) (y (BitVec 32)))
              Bool
              (not (= x y)))


(synth-fun D ((x (BitVec 32)) (y (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
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

(synth-fun R ((x (BitVec 32)) (y (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
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

(synth-fun S1 ((x (BitVec 32)) (y (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
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

(synth-fun S2 ((x (BitVec 32)) (y (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    y
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

(define-fun x0 () (BitVec 32) #x00000000)
(define-fun y0 () (BitVec 32) #x00000000)

(constraint (implies
             (and (contract (D x y)) (G x))
             (and
              (bvugt (R x y) #x00000000)
              (and
               (bvugt (R x y) (R (B_x x (S1 x y)) (B_y y (S2 x y))))
               (contract (D (B_x x (S1 x y)) (B_y y (S2 x y))))))))

(constraint (implies
             (and (contract (D x y)) (not (G x)))
             (not (A x y))))

(constraint (contract (D x0 y0)))

(check-synth)
