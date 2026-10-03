/-
# Necessary rate compatibility for the SAME dyadic filtered budget

The original all-nome one-step gap forces the even-lag filtered drop to
cost at least the constructed kinetic comparison fraction. Strict response
positivity comes from the EXISTING finite-nome geometric floor. Thus a
supplied relative filtered budget necessarily satisfies m*mixFraction<=C.

The literal original half-smoothed finite budget has the same consequence:
its checked cost/variance limits retain BOTH chronological partitions and
the actual OWN mean; the EXISTING original norm is then cancelled using
its pointwise positive floor. No uniform norm floor or new normalizer is
assumed. This is a necessary compatibility condition, not production of
an analytic budget or a changing-family/continuum claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeOneStepGap
import YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredRateConstraint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixFraction)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareResponseFraction squareResponseFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_symm unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitResponse dyadicUnitResponse_pin
    dyadicUnitResponse_geometric_floor dyadicOriginalNorm dyadicOriginalNorm_floor)
open YMGap.Continuum.BF4WilsonAllNomeOneStepGap (completed_even_filtered_form_gap)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
  (originalOwnBlockCost originalOwnBlockVariance originalOwnBlockCost_converges
    originalOwnBlockVariance_converges)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

attribute [local irreducible] dyadicUnitResponse dyadicOriginalNorm
  originalOwnBlockCost originalOwnBlockVariance

private theorem drop_lower (fraction : Q') (even odd : CReal)
    (h : leEv odd (mul (ofQ' (1 + -fraction)) even)) :
    leEv (mul (ofQ' fraction) even) (sub even odd) := by
  intro epsilon he
  obtain ⟨index, hindex⟩ := h epsilon he
  refine ⟨index, fun k hk => ?_⟩
  have hnegative := Q'.neg_le_neg_add (hindex k hk)
  have hsum := Q'.add_le_add_left (even.approx k) _ _ hnegative
  change fraction*even.approx k ≤ (even.approx k + -odd.approx k)+epsilon
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.var 1))
      (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
      (by decide) (fun | 0 => fraction | _ => even.approx k)))
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))))

private theorem rational_scale_cancel {X : CReal} (floor : Q')
    (hfloor0 : (0 : Q') < floor) (hfloor : leEv (ofQ' floor) X)
    (a b : Q') (h : leEv (mul (ofQ' a) X) (mul (ofQ' b) X)) : a ≤ b := by
  have hc := leEv_cancel_mul_right_posEv ⟨floor,hfloor0,hfloor⟩ h
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

private theorem scale_norm_commute (scalar : Q') (norm moment : CReal) :
    Equiv (mul (ofQ' scalar) (mul norm moment))
      (mul (mul (ofQ' scalar) moment) norm) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k => poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => scalar | 1 => norm.approx k | _ => moment.approx k))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation:max "Response" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag
local notation "Norm" => dyadicOriginalNorm hw0 hw1 scale width hwidth

/-- The actual even-lag drop pays the original kinetic fraction, not a bare
fundamental eigenvalue or a supplied response comparison. -/
theorem dyadicUnitResponse_even_filtered_lower (t : Nat) :
    leEv (mul (ofQ' (mixFraction hw0 hw1 width)) (Response (2*t)))
      (sub (Response (2*t)) (Response (2*t+1))) := by
  let u := Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
  have hu : completedInner hw0 hw1 u (unitState hw0 hw1 width) = RCzero := by
    rw [completedInner_symm]
    exact (dyadicUnitExcitation hw0 hw1 scale width hwidth).property
  have h := completed_even_filtered_form_gap hw0 hw1 u hu t
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin, RCscale_mk] at h
  change leEv (Response (2*t+1))
    (mul (ofQ' (1 + -mixFraction hw0 hw1 width)) (Response (2*t))) at h
  exact drop_lower (mixFraction hw0 hw1 width) (Response (2*t)) (Response (2*t+1)) h

/-- Necessary compatibility for a supplied budget on this SAME response.
The floor used for cancellation is positive at each fixed nome/scale only. -/
theorem filtered_budget_rate_constraint (t : Nat) (m C : Q')
    (hm : (0 : Q') ≤ m)
    (hbudget : leEv (mul (ofQ' m) (sub (Response (2*t)) (Response (2*t+1))))
      (mul (ofQ' C) (Response (2*t)))) :
    m*mixFraction hw0 hw1 width ≤ C := by
  have hraw := leEv_trans
    (leEv_smul_nonneg hm
      (dyadicUnitResponse_even_filtered_lower hw0 hw1 scale width hwidth t)) hbudget
  have hassoc : Equiv
      (mul (ofQ' m) (mul (ofQ' (mixFraction hw0 hw1 width)) (Response (2*t))))
      (mul (ofQ' (m*mixFraction hw0 hw1 width)) (Response (2*t))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.eqv_symm
      (Q'.mul_assoc_eqv m (mixFraction hw0 hw1 width) ((Response (2*t)).approx k)))
  have hscaled := leEv_trans (leEv_of_equiv hassoc.symm) hraw
  exact rational_scale_cancel
    ((squareResponseFraction hw0 hw1 scale)^(2*t))
    (HKPos.pow_pos (squareResponseFraction_positive hw0 hw1 scale) (2*t))
    (dyadicUnitResponse_geometric_floor hw0 hw1 scale width hwidth (2*t))
    (m*mixFraction hw0 hw1 width) C hscaled

/-- A literal late-stage ORIGINAL finite budget must obey the same necessary
rate constraint after the checked OWN-centered cost/variance limits. Both
finite partitions and the existing original norm remain unchanged. -/
theorem originalOwnBlock_budget_rate_constraint (t : Nat) (m C : Q')
    (hm : (0 : Q') ≤ m) (start : Nat)
    (hbudget : ∀ k : Nat, start ≤ k →
      m*originalOwnBlockCost hw0 hw1 scale width hwidth k t ≤
        C*originalOwnBlockVariance hw0 hw1 scale width hwidth k t) :
    m*mixFraction hw0 hw1 width ≤ C := by
  have hlimit : leEv
      (mul (ofQ' m) (mul Norm (sub (Response (2*t)) (Response (2*t+1)))))
      (mul (ofQ' C) (mul Norm (Response (2*t)))) :=
    BF4ExactSlabThermodynamicScalarRows.limit_le_of_eventual
      (convergesTo_mul_general (convergesTo_const (ofQ' m))
        (originalOwnBlockCost_converges hw0 hw1 scale width hwidth t))
      (convergesTo_mul_general (convergesTo_const (ofQ' C))
        (originalOwnBlockVariance_converges hw0 hw1 scale width hwidth t))
      start (fun k hk epsilon he => by
        refine ⟨0, fun _ _ => ?_⟩
        change m*originalOwnBlockCost hw0 hw1 scale width hwidth k t ≤
          C*originalOwnBlockVariance hw0 hw1 scale width hwidth k t+epsilon
        exact Q'.le_trans' _ _ _ (hbudget k hk)
          (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he)))
  have hcleared := (leEv_congr
    (scale_norm_commute m Norm (sub (Response (2*t)) (Response (2*t+1))))
    (scale_norm_commute C Norm (Response (2*t)))).mp hlimit
  have hnormalized := leEv_cancel_mul_right_posEv
    ⟨starRatio w,starRatio_positive hw0 hw1,
      dyadicOriginalNorm_floor hw0 hw1 scale width hwidth⟩ hcleared
  exact filtered_budget_rate_constraint hw0 hw1 scale width hwidth t m C hm hnormalized

#print axioms dyadicUnitResponse_even_filtered_lower
#print axioms filtered_budget_rate_constraint
#print axioms originalOwnBlock_budget_rate_constraint

end YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredRateConstraint
