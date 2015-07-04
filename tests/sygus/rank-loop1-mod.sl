(set-logic BV)

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))

(declare-var x (BitVec 32))

(define-fun G ((x (BitVec 32)))
              Bool
              (bvugt x #x00000000))

(define-fun B_x ((x (BitVec 32)))
                (BitVec 32)
                (bvmul x #x00000002))


(synth-fun R ((x (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
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
             (G x)
             (bvugt (R x) #x00000000)))

(constraint (implies
             (G x)
             (bvugt (R x)
                    (R (B_x x)))))

(check-synth)
