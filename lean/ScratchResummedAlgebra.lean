import YMGap.Continuum.Z4StrongCouplingParametricAnchor

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

theorem test (a x y : Q') :
    (x*x + (x*y)*a + (y*x)*a + y*y) ≈
      ((1 : Q') + -a) * (x*x + y*y) + a*((x+y)*(x+y)) := by
  ring_qeqv

theorem test2 (a x y : Q') :
    (x*x + (x*y)*a + (y*x)*a + y*y) ≈
      (((1 : Q') + -a) * (x*x) + ((1 : Q') + -a) * (y*y)) +
        (a*(x*x) + (a*(x*y) + (a*(y*x) + a*(y*y)))) := by
  ring_qeqv
