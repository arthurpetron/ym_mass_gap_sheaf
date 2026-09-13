/-
# Strict positivity of the original SU(2) heat series, with finite cutoffs

The positive theta floor and the first positive logarithmic-derivative term
give S(q,x)>=q/2 and K(q,x)>=thetaFloor(q)/4. Thus the actual original
completed heat kernel has the computable positive floor E_q(K(q))^2/16.
The existing differentiated finite-error estimate also supplies a computed
cutoff beyond which every original character prefix is >= half this floor.

All statements are uniform in rational x in [-1,1], at the NAMED rational
0<q<1. The constants and cutoffs depend on q. This is not an interacting
Haar-product lower bound, stationary vacuum, transfer gap, or continuum claim.
-/

import YMGap.Continuum.ThetaProductStrictFloor
import YMGap.Continuum.JacobiDifferentiatedIdentityOnBox

namespace YMGap.Continuum.SU2PointwiseHeatStrictFloor

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast]; ac_rfl))

/-- The first positive S term already bounds q/2, uniformly over x<=1. -/
theorem half_nome_le_sTerm_zero {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    q * HalfPow.half ≤ HKConv.sTerm q x 0 := by
  let f := HKPos.factor (HKPos.geoAmp q 0) x
  have hf0 : (0 : Q') < f := HKPos.factor_pos
    (Q'.pow_nonneg q (Q'.le_of_lt hq0) _) (HKPos.pow_succ_pos_lt_one hq0 hq1 0).2 hxLower
  have hf4 : f ≤ ThetaConv.four := ThetaConv.factor_le_four
    (Q'.pow_nonneg q (Q'.le_of_lt hq0) _) (HKPos.pow_succ_pos_lt_one hq0 hq1 0).2 hxUpper
  have hnum : HKConv.sTerm q x 0 * f ≈ HKPos.two q := by
    calc HKConv.sTerm q x 0 * f
        ≈ HKPos.two (HKPos.geoAmp q 0) := HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hf0)
      _ ≈ HKPos.two q * (q * q) ^ 0 := HKConv.two_geoAmp_eqv q 0
      _ ≈ HKPos.two q := Q'.mul_one_eqv _
  have hfour : (q * HalfPow.half) * ThetaConv.four ≈ HKPos.two q := by
    calc (q * HalfPow.half) * ThetaConv.four
        ≈ q * (HalfPow.half * ThetaConv.four) := Q'.mul_assoc_eqv _ _ _
      _ ≈ q * ((1 : Q') + 1) := Q'.mul_eqv_congr_left _ _ _ (by decide)
      _ ≈ q * 1 + q * 1 := Q'.mul_add_eqv _ _ _
      _ ≈ q + q := Cheb.add_eqv_congr _ _ _ _ (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)
  apply HKConvGen.mul_le_mul_left_cancel hf0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hf4
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hq0) HalfPow.half_nonneg))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfour
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hnum) (Q'.mul_comm_eqv _ _)))))

/-- Every nonempty actual S partial sum retains its first positive term. -/
theorem sTerm_zero_le_Spart {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (N : Nat) :
    HKConv.sTerm q x 0 ≤ HKConv.Spart q x (N + 1) := by
  induction N with
  | zero => exact Q'.ge_of_eqv (QPoly.q_zero_add_eqv _)
  | succ N ih =>
      exact Q'.le_trans' _ _ _ ih
        (Q'.add_le_self_of_nonneg _ _ (HKConv.sTerm_nonneg hq0 hq1 hxLower _))

/-- Uniform in the named class coordinate x and positive truncation length. -/
theorem half_nome_le_Spart {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) (N : Nat) (hN : 1 ≤ N) :
    q * HalfPow.half ≤ HKConv.Spart q x N := by
  cases N with
  | zero => omega
  | succ N =>
      exact Q'.le_trans' _ _ _
        (half_nome_le_sTerm_zero hq0 hq1 hxLower hxUpper) (sTerm_zero_le_Spart hq0 hq1 hxLower N)

/-- Computable original heat floor: thetaFloor(q)/4 = E_q(K(q))^2/16. -/
def floor (q : Q') : Q' := ThetaProductStrictFloor.floor q * (HalfPow.half * HalfPow.half)

theorem floor_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (0 : Q') < floor q :=
  HKPos.q_mul_pos (ThetaProductStrictFloor.floor_pos hq0 hq1) (by decide)

/-- At every nonempty truncation, the ACTUAL half-normalized derivative
product is at least q times the heat floor. -/
theorem nome_floor_le_Rhalf_approx {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) (N : Nat) (hN : 1 ≤ N) :
    q * floor q ≤ (JTPIdentity.Rhalf hq0 hq1 hxLower hxUpper).approx N := by
  have he : q * floor q ≈ HalfPow.half * (ThetaProductStrictFloor.floor q * (q * HalfPow.half)) := by
    unfold floor
    mul_ring
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
  apply Q'.mul_le_mul_of_nonneg_left _ _ _ _ HalfPow.half_nonneg
  exact HKConv.mul_le_mul' (Q'.le_of_lt (ThetaProductStrictFloor.floor_pos hq0 hq1))
    (HKConv.Spart_nonneg hq0 hq1 hxLower N)
    (ThetaProductStrictFloor.floor_le_Ppart hq0 hq1 hxLower N)
    (half_nome_le_Spart hq0 hq1 hxLower hxUpper N hN)

/-- The original differentiated heat series has a strict rational floor. -/
theorem dSeriesCReal_geRat_nome_floor {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal hq0 hq1 hxLower hxUpper) (q * floor q) :=
  SU3CharFactor.geRat_of_equiv (JacobiDifferentiatedIdentityOnBox.diffJTP hq0 hq1 hxLower hxUpper)
    (ExpPos.geRat_of_eventually ⟨1, fun N hN => nome_floor_le_Rhalf_approx hq0 hq1 hxLower hxUpper N hN⟩)

/-- Strict positivity of the EXISTING original completed SU(2) heat kernel.
The positive bound is uniform in x in [-1,1], with q-dependence explicit. -/
theorem pointwiseHeatCReal_geRat_floor {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    ExpPos.geRat (pointwiseHeatCReal hq0 hq1 hxLower hxUpper) (floor q) := by
  have h := SU3CharFactor.geRat_smul_nonneg (inverseNome_nonnegative q)
    (dSeriesCReal_geRat_nome_floor hq0 hq1 hxLower hxUpper)
  have he : inverseNome q * (q * floor q) ≈ floor q := by
    calc inverseNome q * (q * floor q)
        ≈ (inverseNome q * q) * floor q := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (1 : Q') * floor q := Q'.mul_eqv_congr_right _ _ _ (inverseNome_mul_nome_eqv hq0)
      _ ≈ floor q := Q'.one_mul_eqv _
  exact SU3CharFactor.geRat_of_equiv
    (pointwiseHeatCReal_equiv_inverseNome_mul_dSeriesCReal hq0 hq1 hxLower hxUpper)
    (ExpPos.geRat_mono h (Q'.ge_of_eqv he))

/-- Retain half the completed heat floor for the original finite prefixes. -/
def finiteFloor (q : Q') : Q' := floor q * HalfPow.half

theorem finiteFloor_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (0 : Q') < finiteFloor q := HKPos.q_mul_pos (floor_pos hq0 hq1) (by decide)

/-- Actual label-count cutoff; the nome-scaled error budget is positive.
This is data, independent of x, not an index extracted from geRat. -/
def finiteCutoff (q : Q') : Nat :=
  max 1 (FiniteJacobiDerivativeComparison.derivativeCutoff q (q * finiteFloor q))

/-- All sufficiently long ORIGINAL signed character prefixes are positive,
with a supplied nome-dependent cutoff and floor, uniformly on the real box. -/
theorem finiteFloor_le_standardPointwiseHeatPartial {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (N : Nat) (hN : finiteCutoff q ≤ N) :
    finiteFloor q ≤ standardPointwiseHeatPartial q x N := by
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hNd : FiniteJacobiDerivativeComparison.derivativeCutoff q (q * finiteFloor q) ≤ N :=
    Nat.le_trans (Nat.le_max_right _ _) hN
  have hε : (0 : Q') < q * finiteFloor q := HKPos.q_mul_pos hq0 (finiteFloor_pos hq0 hq1)
  have hclose := JacobiDifferentiatedIdentityOnBox.Rhalf_sub_dSeries_close
    hq0 hq1 hxUpper hxLower hε N hNd
  have hnear : (JTPIdentity.Rhalf hq0 hq1 hxLower hxUpper).approx N
      ≤ JTPIdentity.dPartial q x N + q * finiteFloor q := ExpNeg.le_add_of_abs_sub_le hclose
  have hbound := Q'.le_trans' _ _ _ (nome_floor_le_Rhalf_approx hq0 hq1 hxLower hxUpper N hN1) hnear
  have hsplit : q * floor q ≈ q * finiteFloor q + q * finiteFloor q := by
    unfold finiteFloor
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_eqv_congr_left _ _ _ (ExpNeg.two_halves (floor q))))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Cheb.add_eqv_congr _ _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))))
  have hcancel : q * finiteFloor q ≤ JTPIdentity.dPartial q x N := by
    have hsub := Q'.sub_le_of_le_add
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    have he : q * finiteFloor q ≈ q * floor q + -(q * finiteFloor q) := by
      calc q * finiteFloor q
          ≈ q * finiteFloor q + (q * finiteFloor q + -(q * finiteFloor q)) :=
            Q'.add_sub_cancel_eqv _ _
        _ ≈ (q * finiteFloor q + q * finiteFloor q) + -(q * finiteFloor q) :=
            Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
        _ ≈ q * floor q + -(q * finiteFloor q) :=
            Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsplit)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hsub
  apply HKConvGen.mul_le_mul_left_cancel hq0
  exact Q'.le_trans' _ _ _ hcancel
    (Q'.ge_of_eqv (nome_mul_standardPointwiseHeatPartial_eqv_dPartial q x N))

end YMGap.Continuum.SU2PointwiseHeatStrictFloor

#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.half_nome_le_sTerm_zero
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.sTerm_zero_le_Spart
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.half_nome_le_Spart
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.floor
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.floor_pos
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.nome_floor_le_Rhalf_approx
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.dSeriesCReal_geRat_nome_floor
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.pointwiseHeatCReal_geRat_floor
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.finiteFloor
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.finiteFloor_pos
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.finiteCutoff
#print axioms YMGap.Continuum.SU2PointwiseHeatStrictFloor.finiteFloor_le_standardPointwiseHeatPartial
