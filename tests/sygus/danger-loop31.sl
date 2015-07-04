(set-logic BV)

(declare-var x (BitVec 32))
(declare-var N (BitVec 16))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((x (BitVec 32)) (N (BitVec 16)))
              Bool
              (bvult x (bvconcat #x0000 N)))

(define-fun B_x ((x (BitVec 32)))
                (BitVec 32)
                (bvadd x #x00000002))

(define-fun A ((x (BitVec 32)))
              Bool
              (not (= (bvurem x #x00000002) #x00000000)))



(synth-fun D ((x (BitVec 32)) (N (BitVec 16))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    (bvconcat #x0000 N)
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

(synth-fun R ((x (BitVec 32)) (N (BitVec 16))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    (bvconcat #x0000 N)
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

(synth-fun N0 ((x (BitVec 32)) (N (BitVec 16))) (BitVec 16)
  ((Start (BitVec 16)
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
             (expand (bvule Start Start))
             (expand (bvult Start Start))
             (expand (bvuge Start Start))
             (expand (bvugt Start Start))
             (expand (bvsle Start Start))
             (expand (bvslt Start Start))
             (expand (bvsgt Start Start))
             (expand (= Start Start))
             (expand (not (= Start Start)))
             #x0001
             #x0000
             #xFFFF
             ))))

(constraint (implies
             (and (not (= (D x N) #x00000000)) (G x N))
             (and
              (bvugt (R x N) #x00000000)
              (and
               (bvugt (R x N) (R (B_x x) N))
               (not (= (D (B_x x) N) #x00000000))))))

(constraint (implies
             (and (not (= (D x N) #x00000000)) (not (G x N)))
             (not (A x))))

(constraint (not (= (D #x00000000 (N0 x N)) #x00000000)))

(check-synth)
