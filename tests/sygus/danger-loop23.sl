(set-logic BV)

(declare-var x (BitVec 32))
(declare-var len (BitVec 32))
(declare-var i (BitVec 32))

(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000000) z y))

(define-fun expand ((x Bool)) (BitVec 32)
 (ite x #x00000001 #x00000000))

(define-fun implies ((a Bool) (b Bool)) Bool
  (or (not a) b))


(define-fun G ((x (BitVec 32)) (len (BitVec 32)) (i (BitVec 32)))
              Bool
              (and
               (bvult (bvmul i #x00000004) len)
               (bvult i x)))

(define-fun B_i ((i (BitVec 32)))
                (BitVec 32)
                (bvadd i #x00000001))

(define-fun A ((x (BitVec 32)) (len (BitVec 32)) (i (BitVec 32)))
              Bool
              (or
               (bvult (bvmul i #x00000004) len)
               (bvuge i x)))

(synth-fun D ((x (BitVec 32)) (len (BitVec 32)) (i (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    len
    i
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

(synth-fun R ((x (BitVec 32)) (len (BitVec 32)) (i (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32)
   (
    x
    len
    i
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

(synth-fun x0 ((x (BitVec 32)) (len (BitVec 32)) (i (BitVec 32))) (BitVec 32)
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
             (and (not (= (D x len i) #x00000000)) (G x len i))
             (and
              (bvugt (R x len i) #x00000000)
              (and
               (bvugt (R x len i) (R x len (B_i i)))
               (not (= (D x len (B_i i)) #x00000000))))))

(constraint (implies
             (and (not (= (D x len i) #x00000000)) (not (G x len i)))
             (not (A x len i))))

(constraint (not (= (D (x0 x len i)
                       (bvmul (x0 x len i) #x00000004)
                       #x00000000) #x00000000)))

(check-synth)
