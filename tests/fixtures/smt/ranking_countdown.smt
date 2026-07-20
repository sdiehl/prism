-- count termination #0 (entry: measure >= 0) --
prism-smt-query-v1
logic QF_LIA
digest 03e24cd0d2d81e21350eebb91d40a9406d9fad52dd0bcb0353ef3f0f3acbad48
--
(set-logic QF_LIA)
(declare-const x0 Int)
(assert (>= x0 0))
(assert (not (>= x0 0)))
(check-sat)

-- count termination #1 (edge #0: measure >= 0) --
prism-smt-query-v1
logic QF_LIA
digest 7a76489cacd8649a6408f2b8fe60c397015f61dcb328d11bab6aa16d302892d6
--
(set-logic QF_LIA)
(declare-const x0 Int)
(assert (>= x0 0))
(assert (not (= x0 0)))
(assert (not (>= (- x0 1) 0)))
(check-sat)

-- count termination #2 (edge #0: measure decreases) --
prism-smt-query-v1
logic QF_LIA
digest 3813e05dbab2cae541fb79bd6ad198700a249c0742b7d4f38f8ad9ac6fcfacfb
--
(set-logic QF_LIA)
(declare-const x0 Int)
(assert (>= x0 0))
(assert (not (= x0 0)))
(assert (not (< (- x0 1) x0)))
(check-sat)

