(set-logic BV)

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))

(declare-var i (BitVec 32))
(declare-var j (BitVec 32))

(define-fun G ((i (BitVec 32)) (j (BitVec 32)))
              Bool
              (bvsgt (bvsub i j) #x00000000))

(define-fun B_i ((i (BitVec 32)))
                (BitVec 32)
                (bvsub i #x00000001))

(define-fun B_j ((j (BitVec 32)))
                (BitVec 32)
                (bvadd j #x00000001))


(synth-fun R ((i (BitVec 32)) (j (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    i
    j
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

(synth-fun I ((i (BitVec 32)) (j (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    i
    j
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
             (and (not (= (I i j) #x00000000)) (G i j))
             (and
              (and
               (bvugt (R i j) #x00000000)
               (bvugt (R i j)
                      (R (B_i i) (B_j j))))
              (not (= (I (B_i i) (B_j j)) #x00000000)))))

(constraint (not (= (I #x00000100 #x00000001) #x00000000)))


(check-synth)
