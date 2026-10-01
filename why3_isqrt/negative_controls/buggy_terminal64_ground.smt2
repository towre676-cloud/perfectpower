; benchmark generated from python API
(set-info :status unknown)
(declare-fun m () (_ BitVec 64))
(declare-fun bits_g () (_ BitVec 64))
(declare-fun bits () (_ BitVec 64))
(declare-fun res_g () (_ BitVec 64))
(declare-fun res () (_ BitVec 64))
(declare-fun x () (_ BitVec 64))
(declare-fun num () (_ BitVec 64))
(assert
 (bvule m (_ bv32 64)))
(assert
 (= bits_g (ite (= m (_ bv0 64)) (_ bv0 64) (bvshl (_ bv1 64) (bvsub m (_ bv1 64))))))
(assert
 (= bits (bvmul bits_g bits_g)))
(assert
 (= (bvand res_g (bvsub (bvshl (_ bv1 64) m) (_ bv1 64))) (_ bv0 64)))
(assert
 (bvult res_g (_ bv4294967296 64)))
(assert
 (= res (bvadd res_g (_ bv1 64))))
(assert
 (bvule num x))
(assert
 (let ((?x153 (bvmul res_g res_g)))
 (= (bvsub x num) ?x153)))
(assert
 (let ((?x140 (bvshl (_ bv1 64) m)))
 (let ((?x155 (bvadd res_g ?x140)))
 (bvule ?x155 (_ bv4294967296 64)))))
(assert
 (let ((?x140 (bvshl (_ bv1 64) m)))
 (let ((?x155 (bvadd res_g ?x140)))
 (bvule x (bvsub (bvmul ?x155 ?x155) (_ bv1 64))))))
(assert
 (= bits (_ bv0 64)))
(assert
 (= m (_ bv0 64)))
(assert
 (= bits (_ bv0 64)))
(assert
 (= x (_ bv0 64)))
(assert
 (= num (_ bv0 64)))
(assert
 (= res_g (_ bv0 64)))
(assert
 (= res (_ bv1 64)))
(assert
 (= m (_ bv0 64)))
(assert
 (= bits_g (_ bv0 64)))
(assert
 (= bits (_ bv0 64)))
(assert
 (not (bvule (bvmul res res) x)))
(check-sat)
