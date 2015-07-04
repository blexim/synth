(set-logic BV)

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((x (BitVec 32)))
              Bool
              (bvult x #x00000006))

(define-fun B_x ((x (BitVec 32)))
                (BitVec 32)
                (bvadd x #x00000001))

(define-fun B_y ((y (BitVec 32)))
                (BitVec 32)
                (bvmul y #x00000002))

(define-fun A ((x (BitVec 32)))
              Bool
              (not (= x #x00000006)))


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

(constraint (implies
             (and (not (= (D x y) #x00000000)) (G x))
             (and
              (bvugt (R x y) #x00000000)
              (and
               (bvugt (R x y) (R (B_x x) (B_y y)))
               (not (= (D (B_x x) (B_y y)) #x00000000))))))

(constraint (implies
             (and (not (= (D x y) #x00000000)) (not (G x)))
             (not (A x))))

(constraint (not (= (D #x00000000 #x00000001) #x00000000)))

(check-synth)
