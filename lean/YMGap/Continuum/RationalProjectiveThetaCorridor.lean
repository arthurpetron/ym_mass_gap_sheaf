import YMGap.Constructive.RatNat
import YMGap.Continuum.HarmonicThetaPascalBridge

namespace YMGap.Continuum.RationalProjectiveThetaCorridor

set_option maxHeartbeats 4000000
set_option maxRecDepth 50000

open YMGap.Constructive
open YMGap.Constructive.RatNat
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.HarmonicThetaPascalBridge

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem ofInt_num_cast (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem ofInt_den_cast (z : Int) : ((Q'.ofInt z).den : Int) = 1 := rfl
private theorem one_den_cast : (((1 : Q').den : Int)) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

local macro "integer_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               ofInt_num_cast, ofInt_den_cast, one_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.natCast_one,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem pow_mono_nonneg {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) : ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right x y (x ^ n) hxy
          (Q'.pow_nonneg x hx n))
        (Q'.mul_le_mul_of_nonneg_left (x ^ n) (y ^ n) y
          (pow_mono_nonneg hx hxy n) hy)

private theorem mul_antitone_of_nonpos_left {c x y : Q'}
    (hc : c ≤ (0 : Q')) (hxy : x ≤ y) : c * y ≤ c * x := by
  have hn : (0 : Q') ≤ -c := Q'.nonneg_neg_of_nonpos hc
  have hm : (-c) * x ≤ (-c) * y :=
    Q'.mul_le_mul_of_nonneg_left x y (-c) hxy hn
  have hneg := Q'.neg_le_neg hm
  have hL : -((-c) * y) ≈ c * y := by
    refine Q'.eqv_trans _ ((-(-c)) * y) _
      (Q'.eqv_symm (Q'.neg_mul_eqv (-c) y)) ?_
    exact Q'.mul_eqv_congr_right _ _ y (Q'.neg_neg_eqv c)
  have hR : -((-c) * x) ≈ c * x := by
    refine Q'.eqv_trans _ ((-(-c)) * x) _
      (Q'.eqv_symm (Q'.neg_mul_eqv (-c) x)) ?_
    exact Q'.mul_eqv_congr_right _ _ x (Q'.neg_neg_eqv c)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv hR))

private theorem ofInt_nonpos {z : Int} (hz : z ≤ 0) :
    Q'.ofInt z ≤ (0 : Q') := by
  show z * (1 : Int) ≤ (0 : Int) * (1 : Int)
  simpa using hz

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem scaled_boundary_bracket_eqv (m t : Nat) :
    Q'.ofNat 30 * growingHeadBoundaryBracketQ m t ≈
      Q'.ofInt (growingHeadBoundary30 m t) := by
  have h1 : 2 * m * m + 1 - 1 = 2 * m * m := by omega
  have h2 : 2 * m * m + 1 - 2 = 2 * m * m - 1 := by omega
  have h3 : 2 * m * m + 1 - 3 = 2 * m * m - 2 := by omega
  dsimp only [growingHeadBoundaryBracketQ, growingHeadBoundary30]
  rw [h1, h2, h3]
  simp only [Q'.pow_succ, Q'.pow_zero]
  integer_qeqv

private theorem harmonic_boundary_bracket_nonnegative (t : Nat) :
    (0 : Q') ≤ growingHeadBoundaryBracketQ (2 * t + 4) t := by
  let m := 2 * t + 4
  have hscaled : (0 : Q') ≤
      Q'.ofNat 30 * growingHeadBoundaryBracketQ m t :=
    Q'.le_trans' _ _ _
      (ofInt_nonnegative (growing_head_boundary30_harmonic_nonnegative t))
      (Q'.ge_of_eqv (scaled_boundary_bracket_eqv m t))
  have hmul : Q'.ofNat 30 * (0 : Q') ≤
      Q'.ofNat 30 * growingHeadBoundaryBracketQ m t :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 30))) hscaled
  exact Q'.le_of_mul_le_mul_left hmul (Q'.ofNat_succ_pos 29)

private theorem boundary_coeff_zero_nonpos (t : Nat) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    Q'.ofInt (growingHeadThetaBernCoeff D m D) ≤ (0 : Q') := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  apply ofInt_nonpos
  change growingHeadThetaBernCoeff (2 * m * m + 1) m
    (2 * m * m + 1) ≤ 0
  rw [growing_head_deficit_zero m (by dsimp [m]; omega)]
  have hprod : (0 : Int) ≤ 4 * (m : Int) * ((m : Int) - 1) := Int.mul_nonneg
    (Int.mul_nonneg (by decide) (Int.natCast_nonneg m)) (by omega)
  omega

private theorem boundary_coeff_one_nonpos (t : Nat) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    Q'.ofInt (growingHeadThetaBernCoeff D m (D - 1)) ≤ (0 : Q') := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  apply ofInt_nonpos
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hidx : D - 1 = 2 * m * m := by dsimp [D]
  rw [hidx, growing_head_deficit_one m hm, Int.sub_eq_add_neg]
  apply Int.add_nonpos
  · have hprod : (0 : Int) ≤
        2 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 5) :=
      Int.mul_nonneg
      (Int.mul_nonneg
        (Int.mul_nonneg (by decide) (Int.natCast_nonneg m)) (by omega))
      (by dsimp [m]; omega)
    omega
  · have hprod : (0 : Int) ≤ 12 * (m : Int) * (m : Int) := Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg m))
      (Int.natCast_nonneg m)
    omega

private theorem boundary_coeff_two_nonpos (t : Nat) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    Q'.ofInt (growingHeadThetaBernCoeff D m (D - 2)) ≤ (0 : Q') := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  apply ofInt_nonpos
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmm : 1 ≤ m * m := Nat.mul_pos (by omega) (by omega)
  have htwo : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have hidx : D - 2 = 2 * m * m - 1 := by dsimp [D]; omega
  rw [hidx, growing_head_deficit_two m hm, Int.sub_eq_add_neg]
  apply Int.add_nonpos
  · have hprod : (0 : Int) ≤
        3 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 3) :=
      Int.mul_nonneg
      (Int.mul_nonneg
        (Int.mul_nonneg (by decide) (Int.natCast_nonneg m)) (by omega))
      (by dsimp [m]; omega)
    omega
  · have hprod : (0 : Int) ≤ 6 * (m : Int) * (m : Int) := Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg m))
      (Int.natCast_nonneg m)
    omega

theorem projective_boundary_bracket_nonnegative_below_nat
    (t : Nat) {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hxt : x ≤ Q'.ofNat t) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    (0 : Q') ≤ projectiveBoundaryBracket D
      (growingHeadThetaBernCoeff D m) x := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  let T := Q'.ofNat t
  let c0 := Q'.ofInt (growingHeadThetaBernCoeff D m D)
  let c1 := Q'.ofInt (growingHeadThetaBernCoeff D m (D - 1))
  let c2 := Q'.ofInt (growingHeadThetaBernCoeff D m (D - 2))
  let c3 := Q'.ofInt (growingHeadThetaBernCoeff D m (D - 3))
  have hp1 : x ≤ T := hxt
  have hp2 : x ^ 2 ≤ T ^ 2 := pow_mono_nonneg hx0 hxt 2
  have hp3 : x ^ 3 ≤ T ^ 3 := pow_mono_nonneg hx0 hxt 3
  have hc0 : c0 ≤ (0 : Q') := boundary_coeff_zero_nonpos t
  have hc1 : c1 ≤ (0 : Q') := boundary_coeff_one_nonpos t
  have hc2 : c2 ≤ (0 : Q') := boundary_coeff_two_nonpos t
  have h0 : c0 * T ^ 3 ≤ c0 * x ^ 3 :=
    mul_antitone_of_nonpos_left hc0 hp3
  have h1 : c1 * T ^ 2 ≤ c1 * x ^ 2 :=
    mul_antitone_of_nonpos_left hc1 hp2
  have h2 : c2 * T ≤ c2 * x :=
    mul_antitone_of_nonpos_left hc2 hp1
  have hbracket :
      c0 * T ^ 3 + (c1 * T ^ 2 + (c2 * T + c3)) ≤
        c0 * x ^ 3 + (c1 * x ^ 2 + (c2 * x + c3)) :=
    Q'.add_le_add h0 (Q'.add_le_add h1
      (Q'.add_le_add h2 (Q'.le_refl' c3)))
  have hT : (0 : Q') ≤
      c0 * T ^ 3 + (c1 * T ^ 2 + (c2 * T + c3)) := by
    dsimp only [c0, c1, c2, c3, T, D, m]
    exact harmonic_boundary_bracket_nonnegative t
  exact Q'.le_trans' _ _ _ hT (Q'.le_trans' _ _ _ hbracket
    (Q'.le_of_eqv (by
      unfold projectiveBoundaryBracket
      exact Q'.eqv_refl _)))

theorem growing_head_projective_deficit_nonnegative_below_nat
    (t : Nat) {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hxt : x ≤ Q'.ofNat t) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    (0 : Q') ≤ projectiveDeficitEval D
      (growingHeadThetaBernCoeff D m) x := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmm : 1 ≤ m * m := Nat.mul_pos (by dsimp [m]; omega) (by dsimp [m]; omega)
  have htwice : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have hD : 3 ≤ D := by dsimp [D]; omega
  have hbracket := projective_boundary_bracket_nonnegative_below_nat t hx0 hxt
  have hfactor := projectiveBoundaryFour_eqv_factor D
    (growingHeadThetaBernCoeff D m) x hD
  have hproduct : (0 : Q') ≤ x ^ (D - 3) *
      projectiveBoundaryBracket D (growingHeadThetaBernCoeff D m) x :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg x hx0 (D - 3)) hbracket
  have hboundary : (0 : Q') ≤ projectiveBoundaryFour D
      (growingHeadThetaBernCoeff D m) x :=
    Q'.le_trans' _ _ _ hproduct (Q'.ge_of_eqv hfactor)
  exact projectiveDeficitEval_nonnegative_of_boundary_bulk D
    (growingHeadThetaBernCoeff D m) x hD hx0 hboundary
    (fun r hr hrD => by
      dsimp [D]
      exact growing_head_bulk_coefficient_nonnegative m r hm hr (by
        simpa [D] using hrD))

theorem growing_head_projective_deficit_nonnegative_rational
    {x : Q'} (hx0 : (0 : Q') ≤ x) :
    let t := x.num.toNat
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    (0 : Q') ≤ projectiveDeficitEval D
      (growingHeadThetaBernCoeff D m) x := by
  exact growing_head_projective_deficit_nonnegative_below_nat
    x.num.toNat hx0 (le_ofNat_toNat x hx0)

end YMGap.Continuum.RationalProjectiveThetaCorridor

#print axioms YMGap.Continuum.RationalProjectiveThetaCorridor.projective_boundary_bracket_nonnegative_below_nat
#print axioms YMGap.Continuum.RationalProjectiveThetaCorridor.growing_head_projective_deficit_nonnegative_below_nat
#print axioms YMGap.Continuum.RationalProjectiveThetaCorridor.growing_head_projective_deficit_nonnegative_rational
