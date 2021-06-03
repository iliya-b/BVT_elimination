(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(assert (bvule a x))
(assert (bvult x b))
(assert (= ((_ extract 7 7) x) #b0))

