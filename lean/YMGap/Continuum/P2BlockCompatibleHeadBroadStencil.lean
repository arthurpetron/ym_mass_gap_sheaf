/-
Track 11.7-fusion / R3n -- a four-coefficient broad-peak stencil.

The distance-two energy comparison is local.  For four positive coefficients
`x,y,z,t`, log-concavity, the reverse-curvature factor `7/8`, and the mild
successor cap `2z <= 3y` force

  3 (z-y)^2 <= (z-x)^2 + (t-y)^2.

The proof is division-free.  It splits only on the decidable relative sizes
of `y` and `z`, then pays the square by fixed rational span factors.  Thus the
large physical cutoff never enters kernel reduction.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadLocalEnergyCompiler
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.P2BlockCompatibleHeadBroadStencil

set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3
private def q4 : Q' := Q'.ofNat 4
private def q5 : Q' := Q'.ofNat 5
private def q6 : Q' := Q'.ofNat 6
private def q7 : Q' := Q'.ofNat 7
private def q8 : Q' := Q'.ofNat 8
private def q9 : Q' := Q'.ofNat 9
private def q10 : Q' := Q'.ofNat 10
private def q15 : Q' := Q'.ofNat 15
private def q21 : Q' := Q'.ofNat 21
private def q22 : Q' := Q'.ofNat 22
private def q54 : Q' := Q'.ofNat 54
private def q72 : Q' := Q'.ofNat 72
private def q1e2 : Q' := Q'.mkPos 1 2 (by decide)
private def q1e3 : Q' := Q'.mkPos 1 3 (by decide)
private def q1e4 : Q' := Q'.mkPos 1 4 (by decide)
private def q1e8 : Q' := Q'.mkPos 1 8 (by decide)
private def q7e8 : Q' := Q'.mkPos 7 8 (by decide)
private def q3e4 : Q' := Q'.mkPos 3 4 (by decide)
private def q5e3 : Q' := Q'.mkPos 5 3 (by decide)
private def q7e4 : Q' := Q'.mkPos 7 4 (by decide)
private def q3e2 : Q' := Q'.mkPos 3 2 (by decide)
private def q15e8 : Q' := Q'.mkPos 15 8 (by decide)

/-! The six nonlinear decompositions below are kernel-certified through the
constructive reflective normaliser.  They are deliberately denominator-free:
the order proof cancels the positive integer scale only after reflection. -/

private def increasingLowL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.const 4) (.add (.mul y y) (.neg (.mul x z))))
    (.mul (.add z (.neg y))
      (.add (.mul (.const 4) y) (.neg (.mul (.const 3) z))))

private def increasingLowR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .mul z
    (.add (.mul (.const 4) (.add z (.neg x)))
      (.neg (.mul (.const 7) (.add z (.neg y)))))

private theorem increasingLow_normal :
    RingNormaliser.normalize increasingLowL =
      RingNormaliser.normalize increasingLowR := by decide

private theorem increasingLow_eqv (x y z : Q') :
    q4 * (y * y + (-(x * z))) +
        (z + (-y)) * (q4 * y + (-(q3 * z))) ≈
      z * (q4 * (z + (-x)) + (-(q7 * (z + (-y))))) := by
  simpa [increasingLowL, increasingLowR, RingNormaliser.eval,
    q3, q4, q7,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 7 = Q'.ofNat 7 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      increasingLowL increasingLowR increasingLow_normal
      (fun | 0 => x | 1 => y | _ => z))

private def increasingHighLeftL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.const 3) (.add (.mul y y) (.neg (.mul x z))))
    (.mul (.add z (.neg y))
      (.add (.mul (.const 3) y) (.neg (.mul (.const 2) z))))

private def increasingHighLeftR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .mul z
    (.add (.mul (.const 3) (.add z (.neg x)))
      (.neg (.mul (.const 5) (.add z (.neg y)))))

private theorem increasingHighLeft_normal :
    RingNormaliser.normalize increasingHighLeftL =
      RingNormaliser.normalize increasingHighLeftR := by decide

private theorem increasingHighLeft_eqv (x y z : Q') :
    q3 * (y * y + (-(x * z))) +
        (z + (-y)) * (q3 * y + (-(q2 * z))) ≈
      z * (q3 * (z + (-x)) + (-(q5 * (z + (-y))))) := by
  simpa [increasingHighLeftL, increasingHighLeftR, RingNormaliser.eval,
    q2, q3, q5,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 5 = Q'.ofNat 5 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      increasingHighLeftL increasingHighLeftR increasingHighLeft_normal
      (fun | 0 => x | 1 => y | _ => z))

private def increasingHighRightL : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.const 9)
      (.add (.mul (.const 8) (.mul y t))
        (.neg (.mul (.const 7) (.mul z z)))))
    (.add
      (.mul
        (.add (.mul (.const 3) z) (.neg (.mul (.const 4) y)))
        (.add (.mul (.const 21) z) (.mul (.const 10) y)))
      (.mul (.const 22) (.mul y y)))

private def increasingHighRightR : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .mul y
    (.add (.mul (.const 72) (.add t (.neg y)))
      (.neg (.mul (.const 54) (.add z (.neg y)))))

private theorem increasingHighRight_normal :
    RingNormaliser.normalize increasingHighRightL =
      RingNormaliser.normalize increasingHighRightR := by decide

private theorem increasingHighRight_eqv (y z t : Q') :
    q9 * (q8 * (y * t) + (-(q7 * (z * z)))) +
        ((q3 * z + (-(q4 * y))) * (q21 * z + q10 * y) +
          q22 * (y * y)) ≈
      y * (q72 * (t + (-y)) + (-(q54 * (z + (-y))))) := by
  simpa [increasingHighRightL, increasingHighRightR, RingNormaliser.eval,
    q3, q4, q7, q8, q9, q10, q21, q22, q54, q72,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 7 = Q'.ofNat 7 from rfl,
    show Q'.ofInt 8 = Q'.ofNat 8 from rfl,
    show Q'.ofInt 9 = Q'.ofNat 9 from rfl,
    show Q'.ofInt 10 = Q'.ofNat 10 from rfl,
    show Q'.ofInt 21 = Q'.ofNat 21 from rfl,
    show Q'.ofInt 22 = Q'.ofNat 22 from rfl,
    show Q'.ofInt 54 = Q'.ofNat 54 from rfl,
    show Q'.ofInt 72 = Q'.ofNat 72 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      increasingHighRightL increasingHighRightR increasingHighRight_normal
      (fun | 0 => y | 1 => z | _ => t))

private def decreasingLowL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .add
    (.add (.mul (.const 8) (.mul x z))
      (.neg (.mul (.const 7) (.mul y y))))
    (.add
      (.mul
        (.add y (.neg (.mul (.const 2) z)))
        (.add (.mul (.const 7) y) (.neg (.mul (.const 2) z))))
      (.mul (.const 4) (.mul z z)))

private def decreasingLowR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .mul (.const 8)
    (.mul z
      (.add (.add x (.neg z))
        (.neg (.mul (.const 2) (.add y (.neg z))))))

private theorem decreasingLow_normal :
    RingNormaliser.normalize decreasingLowL =
      RingNormaliser.normalize decreasingLowR := by decide

private theorem decreasingLow_eqv (x y z : Q') :
    (q8 * (x * z) + (-(q7 * (y * y)))) +
        ((y + (-(q2 * z))) * (q7 * y + (-(q2 * z))) +
          q4 * (z * z)) ≈
      q8 * (z * ((x + (-z)) + (-(q2 * (y + (-z)))))) := by
  simpa [decreasingLowL, decreasingLowR, RingNormaliser.eval,
    q2, q4, q7, q8,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 7 = Q'.ofNat 7 from rfl,
    show Q'.ofInt 8 = Q'.ofNat 8 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      decreasingLowL decreasingLowR decreasingLow_normal
      (fun | 0 => x | 1 => y | _ => z))

private def decreasingMiddleL : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.const 2) (.add (.mul z z) (.neg (.mul y t))))
    (.mul (.add y (.neg z))
      (.add (.mul (.const 2) z) (.neg y)))

private def decreasingMiddleR : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .mul y
    (.add (.mul (.const 2) (.add y (.neg t)))
      (.neg (.mul (.const 3) (.add y (.neg z)))))

private theorem decreasingMiddle_normal :
    RingNormaliser.normalize decreasingMiddleL =
      RingNormaliser.normalize decreasingMiddleR := by decide

private theorem decreasingMiddle_eqv (y z t : Q') :
    q2 * (z * z + (-(y * t))) +
        (y + (-z)) * (q2 * z + (-y)) ≈
      y * (q2 * (y + (-t)) + (-(q3 * (y + (-z))))) := by
  simpa [decreasingMiddleL, decreasingMiddleR, RingNormaliser.eval,
    q2, q3,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      decreasingMiddleL decreasingMiddleR decreasingMiddle_normal
      (fun | 0 => y | 1 => z | _ => t))

private def decreasingHighL : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .add
    (.mul (.const 8) (.add (.mul z z) (.neg (.mul y t))))
    (.mul (.add y (.neg z))
      (.add (.mul (.const 8) z) (.neg (.mul (.const 7) y))))

private def decreasingHighR : RingNormaliser.PolyExpr :=
  let y := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  .mul y
    (.add (.mul (.const 8) (.add y (.neg t)))
      (.neg (.mul (.const 15) (.add y (.neg z)))))

private theorem decreasingHigh_normal :
    RingNormaliser.normalize decreasingHighL =
      RingNormaliser.normalize decreasingHighR := by decide

private theorem decreasingHigh_eqv (y z t : Q') :
    q8 * (z * z + (-(y * t))) +
        (y + (-z)) * (q8 * z + (-(q7 * y))) ≈
      y * (q8 * (y + (-t)) + (-(q15 * (y + (-z))))) := by
  simpa [decreasingHighL, decreasingHighR, RingNormaliser.eval,
    q7, q8, q15,
    show Q'.ofInt 7 = Q'.ofNat 7 from rfl,
    show Q'.ofInt 8 = Q'.ofNat 8 from rfl,
    show Q'.ofInt 15 = Q'.ofNat 15 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      decreasingHighL decreasingHighR decreasingHigh_normal
      (fun | 0 => y | 1 => z | _ => t))

private theorem span_seven_fourths {d L : Q'}
    (h : q7 * d <= q4 * L) : q7e4 * d <= L := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q1e4 h (by decide)
  have hleft : q1e4 * (q7 * d) ≈ q7e4 * d := by
    unfold q1e4 q7 q7e4
    ring_qeqv
  have hright : q1e4 * (q4 * L) ≈ L := by
    unfold q1e4 q4
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

private theorem span_five_thirds {d L : Q'}
    (h : q5 * d <= q3 * L) : q5e3 * d <= L := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q1e3 h (by decide)
  have hleft : q1e3 * (q5 * d) ≈ q5e3 * d := by
    unfold q1e3 q5 q5e3
    ring_qeqv
  have hright : q1e3 * (q3 * L) ≈ L := by
    unfold q1e3 q3
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

private theorem span_three_fourths {d R : Q'}
    (h : q54 * d <= q72 * R) : q3e4 * d <= R := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q1e8 h (by decide)
  have hleft : q1e8 * (q54 * d) ≈ q3e4 * (Q'.ofNat 9 * d) := by
    unfold q1e8 q54 q3e4
    ring_qeqv
  have hright : q1e8 * (q72 * R) ≈ Q'.ofNat 9 * R := by
    unfold q1e8 q72
    ring_qeqv
  have hscaled : q3e4 * (Q'.ofNat 9 * d) <= Q'.ofNat 9 * R :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))
  have hreL : Q'.ofNat 9 * (q3e4 * d) ≈
      q3e4 * (Q'.ofNat 9 * d) := by ring_qeqv
  have hscaled' : Q'.ofNat 9 * (q3e4 * d) <= Q'.ofNat 9 * R :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hreL) hscaled
  exact Q'.le_of_mul_le_mul_left hscaled' (by decide)

private theorem span_three_halves {d R : Q'}
    (h : q3 * d <= q2 * R) : q3e2 * d <= R := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q1e2 h (by decide)
  have hleft : q1e2 * (q3 * d) ≈ q3e2 * d := by
    unfold q1e2 q3 q3e2
    ring_qeqv
  have hright : q1e2 * (q2 * R) ≈ R := by
    unfold q1e2 q2
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

private theorem span_fifteen_eighths {d R : Q'}
    (h : q15 * d <= q8 * R) : q15e8 * d <= R := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q1e8 h (by decide)
  have hleft : q1e8 * (q15 * d) ≈ q15e8 * d := by
    unfold q1e8 q15 q15e8
    ring_qeqv
  have hright : q1e8 * (q8 * R) ≈ R := by
    unfold q1e8 q8
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

private theorem scaled_slack_cancel {c a b : Q'} (hc : (0 : Q') < c)
    (h : (0 : Q') <= c * (b + (-a))) : a <= b := by
  have hre : c * (b + (-a)) ≈ c * b + (-(c * a)) := by
    ring_qeqv
  have hsub : (0 : Q') <= c * b + (-(c * a)) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv hre)
  exact Q'.le_of_mul_le_mul_left (Q'.le_of_sub_nonneg hsub) hc

private theorem square_budget {d L R a b : Q'}
    (hd : (0 : Q') <= d) (hL : (0 : Q') <= L)
    (hR : (0 : Q') <= R) (ha : (0 : Q') <= a)
    (hb : (0 : Q') <= b)
    (hconst : q3 <= a * a + b * b)
    (hspanL : a * d <= L) (hspanR : b * d <= R) :
    q3 * (d * d) <= L * L + R * R := by
  have hadd0 : (0 : Q') <= a * a + b * b :=
    Q'.zero_le_add _ _ (q_mul_self_nonneg a) (q_mul_self_nonneg b)
  have hdd0 : (0 : Q') <= d * d := q_mul_self_nonneg d
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ (d * d)
    hconst hdd0
  have had0 : (0 : Q') <= a * d := Q'.mul_nonneg _ _ ha hd
  have hbd0 : (0 : Q') <= b * d := Q'.mul_nonneg _ _ hb hd
  have hLL := Q'.mul_le_mul_of_nonneg hspanL hspanL hL had0
  have hRR := Q'.mul_le_mul_of_nonneg hspanR hspanR hR hbd0
  have hsquares := Q'.add_le_add hLL hRR
  have hre :
      (a * a + b * b) * (d * d) ≈
        (a * d) * (a * d) + (b * d) * (b * d) := by
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) hsquares)

private theorem square_budget_left {d L R a : Q'}
    (hd : (0 : Q') <= d) (hL : (0 : Q') <= L)
    (ha : (0 : Q') <= a) (hconst : q3 <= a * a)
    (hspan : a * d <= L) :
    q3 * (d * d) <= L * L + R * R := by
  have hdd0 : (0 : Q') <= d * d := q_mul_self_nonneg d
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ (d * d)
    hconst hdd0
  have had0 : (0 : Q') <= a * d := Q'.mul_nonneg _ _ ha hd
  have hLL := Q'.mul_le_mul_of_nonneg hspan hspan hL had0
  have hRR0 : (0 : Q') <= R * R := q_mul_self_nonneg R
  have hplus := Q'.add_le_self_of_nonneg (L * L) (R * R) hRR0
  have hre : (a * a) * (d * d) ≈ (a * d) * (a * d) := by
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
      (Q'.le_trans' _ _ _ hLL hplus))

private theorem square_budget_right {d L R b : Q'}
    (hd : (0 : Q') <= d) (hR : (0 : Q') <= R)
    (hb : (0 : Q') <= b) (hconst : q3 <= b * b)
    (hspan : b * d <= R) :
    q3 * (d * d) <= L * L + R * R := by
  have hdd0 : (0 : Q') <= d * d := q_mul_self_nonneg d
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ (d * d)
    hconst hdd0
  have hbd0 : (0 : Q') <= b * d := Q'.mul_nonneg _ _ hb hd
  have hRR := Q'.mul_le_mul_of_nonneg hspan hspan hR hbd0
  have hLL0 : (0 : Q') <= L * L := q_mul_self_nonneg L
  have hplus := Q'.add_le_self_of_nonneg (R * R) (L * L) hLL0
  have hre : (b * b) * (d * d) ≈ (b * d) * (b * d) := by
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
      (Q'.le_trans' _ _ _ hRR
        (Q'.le_trans' _ _ _ hplus
          (Q'.le_of_eqv (Q'.add_comm_eqv (R * R) (L * L))))))

private theorem dirichlet_stencil_of_squares (x y z t : Q')
    (h : q3 * ((z + (-y)) * (z + (-y))) <=
      (z + (-x)) * (z + (-x)) + (t + (-y)) * (t + (-y))) :
    q3 * dirichletTerm y z <=
      dirichletTerm x z + dirichletTerm y t := by
  have hleft : q3 * dirichletTerm y z ≈
      q3 * ((z + (-y)) * (z + (-y))) := by
    refine Q'.mul_eqv_congr_left q3 _ _ ?_
    refine Q'.eqv_trans _ ((y + (-z)) * (y + (-z))) _
      (dirichletTerm_eqv_sq y z) ?_
    ring_qeqv
  have hright :
      (z + (-x)) * (z + (-x)) + (t + (-y)) * (t + (-y)) ≈
        dirichletTerm x z + dirichletTerm y t := by
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ ((x + (-z)) * (x + (-z))) _
        (by ring_qeqv) (Q'.eqv_symm (dirichletTerm_eqv_sq x z)))
      (Q'.eqv_trans _ ((y + (-t)) * (y + (-t))) _
        (by ring_qeqv) (Q'.eqv_symm (dirichletTerm_eqv_sq y t)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

private theorem dirichlet_stencil_of_reverse_squares (x y z t : Q')
    (h : q3 * ((y + (-z)) * (y + (-z))) <=
      (x + (-z)) * (x + (-z)) + (y + (-t)) * (y + (-t))) :
    q3 * dirichletTerm y z <=
      dirichletTerm x z + dirichletTerm y t := by
  have hleft : q3 * dirichletTerm y z ≈
      q3 * ((y + (-z)) * (y + (-z))) :=
    Q'.mul_eqv_congr_left q3 _ _ (dirichletTerm_eqv_sq y z)
  have hright :
      (x + (-z)) * (x + (-z)) + (y + (-t)) * (y + (-t)) ≈
        dirichletTerm x z + dirichletTerm y t :=
    Q'.add_eqv_congr'
      (Q'.eqv_symm (dirichletTerm_eqv_sq x z))
      (Q'.eqv_symm (dirichletTerm_eqv_sq y t))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- A division-free broad-peak stencil for four positive coefficients. -/
theorem broadPeak_local_stencil {x y z t : Q'}
    (hx0 : (0 : Q') <= x) (hy : (0 : Q') < y)
    (hz : (0 : Q') < z) (ht0 : (0 : Q') <= t)
    (hlogL : x * z <= y * y) (hlogR : y * t <= z * z)
    (hrevL : q7e8 * (y * y) <= x * z)
    (hrevR : q7e8 * (z * z) <= y * t)
    (hratio : q2 * z <= q3 * y) :
    q3 * dirichletTerm y z <=
      dirichletTerm x z + dirichletTerm y t := by
  have hy0 : (0 : Q') <= y := Q'.le_of_lt hy
  have hz0 : (0 : Q') <= z := Q'.le_of_lt hz
  by_cases hyz : y <= z
  · let d := z + (-y)
    let L := z + (-x)
    let R := t + (-y)
    have hd : (0 : Q') <= d := Q'.sub_nonneg_of_le hyz
    have hxy : x <= y := by
      have hxyScaled : x * y <= y * y :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ x hyz hx0) hlogL
      have hxyScaled' : y * x <= y * y :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv y x)) hxyScaled
      exact Q'.le_of_mul_le_mul_left hxyScaled' hy
    have hxz : x <= z := Q'.le_trans' _ _ _ hxy hyz
    have hL : (0 : Q') <= L := Q'.sub_nonneg_of_le hxz
    by_cases hlow : q3 * z <= q4 * y
    · have hspan : q7e4 * d <= L := by
        have hgap : (0 : Q') <= q4 * y + (-(q3 * z)) :=
          Q'.sub_nonneg_of_le hlow
        have hlogGap : (0 : Q') <= y * y + (-(x * z)) :=
          Q'.sub_nonneg_of_le hlogL
        have hlogScaled : (0 : Q') <=
            q4 * (y * y + (-(x * z))) :=
          Q'.mul_nonneg _ _ (by decide) hlogGap
        have hprod : (0 : Q') <=
            (z + (-y)) * (q4 * y + (-(q3 * z))) :=
          Q'.mul_nonneg _ _ hd hgap
        have hsum := Q'.zero_le_add _ _ hlogScaled hprod
        have hinter : q7 * d <= q4 * L := by
          apply scaled_slack_cancel hz
          exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
            dsimp only [d, L]
            exact increasingLow_eqv x y z))
        exact span_seven_fourths hinter
      have hsquares := square_budget_left (R := R) hd hL (by decide)
        (by decide : q3 <= q7e4 * q7e4) hspan
      exact dirichlet_stencil_of_squares x y z t (by
        simpa only [d, L, R] using hsquares)
    · have hhigh : q4 * y <= q3 * z := Q'.le_of_not_le hlow
      have hspanL : q5e3 * d <= L := by
        have hratioGap : (0 : Q') <= q3 * y + (-(q2 * z)) :=
          Q'.sub_nonneg_of_le hratio
        have hlogGap : (0 : Q') <= y * y + (-(x * z)) :=
          Q'.sub_nonneg_of_le hlogL
        have hlogScaled : (0 : Q') <=
            q3 * (y * y + (-(x * z))) :=
          Q'.mul_nonneg _ _ (by decide) hlogGap
        have hprod : (0 : Q') <=
            (z + (-y)) * (q3 * y + (-(q2 * z))) :=
          Q'.mul_nonneg _ _ hd hratioGap
        have hsum := Q'.zero_le_add _ _ hlogScaled hprod
        have hinter : q5 * d <= q3 * L := by
          apply scaled_slack_cancel hz
          exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
            dsimp only [d, L]
            exact increasingHighLeft_eqv x y z))
        exact span_five_thirds hinter
      have hspanR : q3e4 * d <= R := by
        have hhighGap : (0 : Q') <= q3 * z + (-(q4 * y)) :=
          Q'.sub_nonneg_of_le hhigh
        have hlin0 : (0 : Q') <=
            q21 * z + q10 * y :=
          Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (by decide) hz0)
            (Q'.mul_nonneg _ _ (by decide) hy0)
        have hpositive : (0 : Q') <=
            q22 * (y * y) :=
          Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg y)
        have hpoly := Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ hhighGap hlin0) hpositive
        have hrevScaled := Q'.mul_le_mul_of_nonneg_left _ _ q8 hrevR
          (by decide)
        have hrevLeft : q8 * (q7e8 * (z * z)) ≈ q7 * (z * z) := by
          unfold q8 q7e8 q7
          ring_qeqv
        have hrevInt : q7 * (z * z) <= q8 * (y * t) :=
          Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrevLeft) hrevScaled
        have hrevGap : (0 : Q') <=
            q8 * (y * t) + (-(q7 * (z * z))) :=
          Q'.sub_nonneg_of_le hrevInt
        have hrevNine : (0 : Q') <=
            q9 * (q8 * (y * t) + (-(q7 * (z * z)))) :=
          Q'.mul_nonneg _ _ (by decide) hrevGap
        have hsum := Q'.zero_le_add _ _ hrevNine hpoly
        have hinter : q54 * d <= q72 * R := by
          apply scaled_slack_cancel hy
          exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
            dsimp only [d, R]
            exact increasingHighRight_eqv y z t))
        exact span_three_fourths hinter
      have hR : (0 : Q') <= R :=
        Q'.le_trans' _ _ _
          (Q'.mul_nonneg _ _ (by decide) hd) hspanR
      have hsquares := square_budget hd hL hR
        (by decide) (by decide)
        (by decide : q3 <= q5e3 * q5e3 + q3e4 * q3e4)
        hspanL hspanR
      exact dirichlet_stencil_of_squares x y z t (by
        simpa only [d, L, R] using hsquares)
  · have hzy : z <= y := Q'.le_of_not_le hyz
    let d := y + (-z)
    let L := x + (-z)
    let R := y + (-t)
    have hd : (0 : Q') <= d := Q'.sub_nonneg_of_le hzy
    have htz : t <= z := by
      have htzScaled : z * t <= z * z :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ t hzy ht0)
          hlogR
      exact Q'.le_of_mul_le_mul_left htzScaled hz
    have hty : t <= y := Q'.le_trans' _ _ _ htz hzy
    have hR : (0 : Q') <= R := Q'.sub_nonneg_of_le hty
    by_cases hlow : q2 * z <= y
    · have hspan : q2 * d <= L := by
        have hlowGap : (0 : Q') <= y + (-(q2 * z)) :=
          Q'.sub_nonneg_of_le hlow
        have hlin0 : (0 : Q') <=
            Q'.ofNat 7 * y + (-(q2 * z)) := by
          have hc : (1 : Q') <= Q'.ofNat 7 := by decide
          have hy7 : y <= Q'.ofNat 7 * y := by
            have hs := Q'.mul_le_mul_of_nonneg_right _ _ y hc hy0
            exact Q'.le_trans' _ _ _
              (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv y))) hs
          have hraw : q2 * z <= Q'.ofNat 7 * y :=
            Q'.le_trans' _ _ _ hlow hy7
          exact Q'.sub_nonneg_of_le hraw
        have hprod : (0 : Q') <=
            (y + (-(q2 * z))) *
              (Q'.ofNat 7 * y + (-(q2 * z))) :=
          Q'.mul_nonneg _ _ hlowGap hlin0
        have hzsq : (0 : Q') <= Q'.ofNat 4 * (z * z) :=
          Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg z)
        have hpoly := Q'.zero_le_add _ _ hprod hzsq
        have hrevScaled := Q'.mul_le_mul_of_nonneg_left _ _ q8 hrevL
          (by decide)
        have hrevLeft : q8 * (q7e8 * (y * y)) ≈ q7 * (y * y) := by
          unfold q8 q7e8 q7
          ring_qeqv
        have hrevInt : q7 * (y * y) <= q8 * (x * z) :=
          Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrevLeft) hrevScaled
        have hrevGap : (0 : Q') <=
            q8 * (x * z) + (-(q7 * (y * y))) :=
          Q'.sub_nonneg_of_le hrevInt
        have hsum := Q'.zero_le_add _ _ hrevGap hpoly
        have hc : (0 : Q') < q8 * z := Q'.mul_pos (by decide) hz
        apply scaled_slack_cancel hc
        have hre := decreasingLow_eqv x y z
        have hre' :
            q8 * (z * (L + (-(q2 * d)))) ≈
              (q8 * z) * (L + (-(q2 * d))) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv q8 z (L + (-(q2 * d))))
        exact Q'.le_trans' _ _ _ hsum
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (by
            dsimp only [d, L]
            exact hre) hre'))
      have hL : (0 : Q') <= L :=
        Q'.le_trans' _ _ _
          (Q'.mul_nonneg _ _ (by decide) hd) hspan
      have hsquares := square_budget_left (R := R) hd hL (by decide)
        (by decide : q3 <= q2 * q2) hspan
      exact dirichlet_stencil_of_reverse_squares x y z t (by
        simpa only [d, L, R] using hsquares)
    · have hmidLow : y <= q2 * z := Q'.le_of_not_le hlow
      by_cases hmid : Q'.ofNat 8 * z <= Q'.ofNat 7 * y
      · have hspanL : (1 : Q') * d <= L := by
          have hmidScaled := Q'.mul_le_mul_of_nonneg_left _ _ y hmid hy0
          have hmidInt : q8 * (y * z) <= q7 * (y * y) := by
            have hleft : y * (Q'.ofNat 8 * z) ≈ q8 * (y * z) := by
              unfold q8
              ring_qeqv
            have hright : y * (Q'.ofNat 7 * y) ≈ q7 * (y * y) := by
              unfold q7
              ring_qeqv
            exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
              (Q'.le_trans' _ _ _ hmidScaled (Q'.le_of_eqv hright))
          have hrevScaled := Q'.mul_le_mul_of_nonneg_left _ _ q8 hrevL
            (by decide)
          have hrevLeft : q8 * (q7e8 * (y * y)) ≈ q7 * (y * y) := by
            unfold q8 q7e8 q7
            ring_qeqv
          have hrevInt : q7 * (y * y) <= q8 * (x * z) :=
            Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrevLeft) hrevScaled
          have hq8 : q8 * (y * z) <= q8 * (x * z) :=
            Q'.le_trans' _ _ _ hmidInt hrevInt
          have hxz_ge_yz : y * z <= x * z :=
            Q'.le_of_mul_le_mul_left hq8 (by decide)
          have hxy : y <= x := by
            have hcomm : z * y <= z * x :=
              Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_comm_eqv y z))
                (Q'.le_trans' _ _ _ hxz_ge_yz
                  (Q'.le_of_eqv (Q'.mul_comm_eqv x z)))
            exact Q'.le_of_mul_le_mul_left hcomm hz
          have hraw := Q'.add_le_add_right _ _ (-z) hxy
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.one_mul_eqv d)) (by
              dsimp only [d, L]
              exact hraw)
        have hL : (0 : Q') <= L :=
          Q'.le_trans' _ _ _
            (Q'.mul_nonneg _ _ (by decide) hd) hspanL
        have hspanR : q3e2 * d <= R := by
          have hlogGap : (0 : Q') <= z * z + (-(y * t)) :=
            Q'.sub_nonneg_of_le hlogR
          have hmidGap : (0 : Q') <= q2 * z + (-y) :=
            Q'.sub_nonneg_of_le hmidLow
          have hlogScaled : (0 : Q') <=
              q2 * (z * z + (-(y * t))) :=
            Q'.mul_nonneg _ _ (by decide) hlogGap
          have hprod : (0 : Q') <=
              (y + (-z)) * (q2 * z + (-y)) :=
            Q'.mul_nonneg _ _ hd hmidGap
          have hsum := Q'.zero_le_add _ _ hlogScaled hprod
          have hinter : q3 * d <= q2 * R := by
            apply scaled_slack_cancel hy
            exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
              dsimp only [d, R]
              exact decreasingMiddle_eqv y z t))
          exact span_three_halves hinter
        have hsquares := square_budget hd hL hR
          (by decide) (by decide)
          (by decide : q3 <= (1 : Q') * 1 + q3e2 * q3e2)
          hspanL hspanR
        exact dirichlet_stencil_of_reverse_squares x y z t (by
          simpa only [d, L, R] using hsquares)
      · have hhigh : Q'.ofNat 7 * y <= Q'.ofNat 8 * z :=
          Q'.le_of_not_le hmid
        have hspan : q15e8 * d <= R := by
          have hlogGap : (0 : Q') <= z * z + (-(y * t)) :=
            Q'.sub_nonneg_of_le hlogR
          have hhighGap : (0 : Q') <=
              Q'.ofNat 8 * z + (-(Q'.ofNat 7 * y)) :=
            Q'.sub_nonneg_of_le hhigh
          have hlogScaled : (0 : Q') <=
              q8 * (z * z + (-(y * t))) :=
            Q'.mul_nonneg _ _ (by decide) hlogGap
          have hprod : (0 : Q') <=
              (y + (-z)) * (q8 * z + (-(q7 * y))) :=
            Q'.mul_nonneg _ _ hd hhighGap
          have hsum := Q'.zero_le_add _ _ hlogScaled hprod
          have hinter : q15 * d <= q8 * R := by
            apply scaled_slack_cancel hy
            exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
              dsimp only [d, R]
              exact decreasingHigh_eqv y z t))
          exact span_fifteen_eighths hinter
        have hsquares := square_budget_right (L := L) hd hR (by decide)
          (by decide : q3 <= q15e8 * q15e8) hspan
        exact dirichlet_stencil_of_reverse_squares x y z t (by
          simpa only [d, L, R] using hsquares)

/-- The increasing high-side half of `broadPeak_local_stencil`.  This is the
one-sided form needed at the first physical interior cell, where the left
reverse-curvature estimate is intentionally unavailable. -/
theorem broadPeak_increasing_high_stencil {x y z t : Q'}
    (hx0 : (0 : Q') <= x) (hy : (0 : Q') < y)
    (hz : (0 : Q') < z)
    (hyz : y <= z) (hhigh : q4 * y <= q3 * z)
    (hlogL : x * z <= y * y)
    (hrevR : q7e8 * (z * z) <= y * t)
    (hratio : q2 * z <= q3 * y) :
    q3 * dirichletTerm y z <=
      dirichletTerm x z + dirichletTerm y t := by
  let d := z + (-y)
  let L := z + (-x)
  let R := t + (-y)
  have hy0 : (0 : Q') <= y := Q'.le_of_lt hy
  have hz0 : (0 : Q') <= z := Q'.le_of_lt hz
  have hd : (0 : Q') <= d := Q'.sub_nonneg_of_le hyz
  have hxy : x <= y := by
    have hxyScaled : x * y <= y * y :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ x hyz hx0) hlogL
    have hxyScaled' : y * x <= y * y :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv y x)) hxyScaled
    exact Q'.le_of_mul_le_mul_left hxyScaled' hy
  have hL : (0 : Q') <= L :=
    Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hxy hyz)
  have hspanL : q5e3 * d <= L := by
    have hratioGap : (0 : Q') <= q3 * y + (-(q2 * z)) :=
      Q'.sub_nonneg_of_le hratio
    have hlogGap : (0 : Q') <= y * y + (-(x * z)) :=
      Q'.sub_nonneg_of_le hlogL
    have hlogScaled : (0 : Q') <=
        q3 * (y * y + (-(x * z))) :=
      Q'.mul_nonneg _ _ (by decide) hlogGap
    have hprod : (0 : Q') <=
        (z + (-y)) * (q3 * y + (-(q2 * z))) :=
      Q'.mul_nonneg _ _ hd hratioGap
    have hsum := Q'.zero_le_add _ _ hlogScaled hprod
    have hinter : q5 * d <= q3 * L := by
      apply scaled_slack_cancel hz
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
        dsimp only [d, L]
        exact increasingHighLeft_eqv x y z))
    exact span_five_thirds hinter
  have hspanR : q3e4 * d <= R := by
    have hhighGap : (0 : Q') <= q3 * z + (-(q4 * y)) :=
      Q'.sub_nonneg_of_le hhigh
    have hlin0 : (0 : Q') <= q21 * z + q10 * y :=
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hz0)
        (Q'.mul_nonneg _ _ (by decide) hy0)
    have hpositive : (0 : Q') <= q22 * (y * y) :=
      Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg y)
    have hpoly := Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ hhighGap hlin0) hpositive
    have hrevScaled := Q'.mul_le_mul_of_nonneg_left _ _ q8 hrevR
      (by decide)
    have hrevLeft : q8 * (q7e8 * (z * z)) ≈ q7 * (z * z) := by
      unfold q8 q7e8 q7
      ring_qeqv
    have hrevInt : q7 * (z * z) <= q8 * (y * t) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrevLeft) hrevScaled
    have hrevGap : (0 : Q') <=
        q8 * (y * t) + (-(q7 * (z * z))) :=
      Q'.sub_nonneg_of_le hrevInt
    have hrevNine : (0 : Q') <=
        q9 * (q8 * (y * t) + (-(q7 * (z * z)))) :=
      Q'.mul_nonneg _ _ (by decide) hrevGap
    have hsum := Q'.zero_le_add _ _ hrevNine hpoly
    have hinter : q54 * d <= q72 * R := by
      apply scaled_slack_cancel hy
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by
        dsimp only [d, R]
        exact increasingHighRight_eqv y z t))
    exact span_three_fourths hinter
  have hR : (0 : Q') <= R :=
    Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (by decide) hd) hspanR
  have hsquares := square_budget hd hL hR
    (by decide) (by decide)
    (by decide : q3 <= q5e3 * q5e3 + q3e4 * q3e4)
    hspanL hspanR
  exact dirichlet_stencil_of_squares x y z t (by
    simpa only [d, L, R] using hsquares)

/-- A `7/4` forward span pays the first adjacent edge with its unique
distance-two edge. -/
theorem forward_endpoint_stencil {x y z : Q'}
    (hxy : x <= y) (hxz : x <= z)
    (hspan : q7e4 * (y + (-x)) <= z + (-x)) :
    q3 * dirichletTerm x y <= dirichletTerm x z := by
  let d := y + (-x)
  let L := z + (-x)
  have hd : (0 : Q') <= d := Q'.sub_nonneg_of_le hxy
  have hL : (0 : Q') <= L := Q'.sub_nonneg_of_le hxz
  have hsquares := square_budget_left (R := 0) hd hL (by decide)
    (by decide : q3 <= q7e4 * q7e4) (by
      simpa only [d, L] using hspan)
  have hleft : q3 * dirichletTerm x y ≈ q3 * (d * d) := by
    refine Q'.mul_eqv_congr_left q3 _ _ ?_
    exact Q'.eqv_trans _ ((x + (-y)) * (x + (-y))) _
      (dirichletTerm_eqv_sq x y) (by
        dsimp only [d]
        ring_qeqv)
  have hright : L * L + (0 : Q') * 0 ≈ dirichletTerm x z := by
    refine Q'.eqv_trans _ (L * L) _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
    exact Q'.eqv_trans _ ((x + (-z)) * (x + (-z))) _
      (by
        dsimp only [L]
        ring_qeqv)
      (Q'.eqv_symm (dirichletTerm_eqv_sq x z))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsquares (Q'.le_of_eqv hright))

/-- A `7/4` backward span pays the final adjacent edge with its unique
distance-two edge. -/
theorem backward_endpoint_stencil {x y z : Q'}
    (hzy : z <= y) (hzx : z <= x)
    (hspan : q7e4 * (y + (-z)) <= x + (-z)) :
    q3 * dirichletTerm y z <= dirichletTerm x z := by
  let d := y + (-z)
  let L := x + (-z)
  have hd : (0 : Q') <= d := Q'.sub_nonneg_of_le hzy
  have hL : (0 : Q') <= L := Q'.sub_nonneg_of_le hzx
  have hsquares := square_budget_left (R := 0) hd hL (by decide)
    (by decide : q3 <= q7e4 * q7e4) (by
      simpa only [d, L] using hspan)
  have hleft : q3 * dirichletTerm y z ≈ q3 * (d * d) :=
    Q'.mul_eqv_congr_left q3 _ _ (by
      exact Q'.eqv_trans _ ((y + (-z)) * (y + (-z))) _
        (dirichletTerm_eqv_sq y z) (Q'.eqv_refl _))
  have hright : L * L + (0 : Q') * 0 ≈ dirichletTerm x z := by
    refine Q'.eqv_trans _ (L * L) _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
    dsimp only [L]
    exact Q'.eqv_symm (dirichletTerm_eqv_sq x z)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsquares (Q'.le_of_eqv hright))

#print axioms broadPeak_local_stencil
#print axioms broadPeak_increasing_high_stencil
#print axioms forward_endpoint_stencil
#print axioms backward_endpoint_stencil

end YMGap.Continuum.P2BlockCompatibleHeadBroadStencil
