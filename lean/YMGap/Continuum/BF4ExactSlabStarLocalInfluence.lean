/-
# Strict local influence on free-link-centered inputs

The original conditional projection has a strict squared-norm bound on
polynomials orthogonal to exterior probes in the star-deleted form. Every
input has an explicitly constructed free-link residual in this sector. The factor is
1-L(w)/U(w), with the actual six-face comparison constants. Every finite
exterior approximation leaves at least L times the star-deleted input norm
in its residual. That floor passes directly through the constructed Cauchy
representative, and the exact projection identity subtracts it from the
original full-action input norm.

This is a directional one-link estimate, not a contraction on the entire
vacuum complement, a multi-link influence bound, spatial decay, or an OS
transfer/Hamiltonian gap. All norms retain the original action; the deleted
action is used only in the proved comparison. No coupling-uniform margin or
physical-scale conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabStarFreeCentering
import YMGap.Continuum.BF4ExactSlabStarConditionalProjection

namespace YMGap.Continuum.BF4ExactSlabStarLocalInfluence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarFreeCentering
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev rc (q : Q') : CReal.RC := Quotient.mk CReal.crealSetoid (CReal.ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "R" => deletedData hw0 hw1 K extent hK link hl
local notation "J" => probeMap hw0 hw1 K extent hK link hl
local notation "N" => numeratorMap hw0 hw1 K extent hK link hl
local notation "Q" => conditionalUpdate hw0 hw1 K extent hK link hl

/-- The two actual forms share their supported polynomial carrier. -/
theorem actual_deleted_form_bounds (p : (F).V) :
    lowerFactor w * (R).B p p ≤ (F).B p p ∧
      (F).B p p ≤ upperFactor w * (R).B p p :=
  original_star_bounds hw0 hw1 K extent hK link (.square p.val p.property)

/-- No exterior polynomial can remove the free-centered input's residual
floor. The normalized fraction uses only the LOCAL six-face constants. -/
theorem probe_residual_lower (p : (F).V) (r : (G).V)
    (hcenter : ∀ a : (G).V, (R).B p (J a) ≈ 0) :
    starRatio w * (F).B p p ≤ (F).distSqQ p (J r) := by
  have hscale : starRatio w * (F).B p p ≤ lowerFactor w * (R).B p p := by
    have hu := Q'.mul_le_mul_of_nonneg_left _ _ _
      (actual_deleted_form_bounds hw0 hw1 K extent hK link hl p).2
      (Q'.le_of_lt (starRatio_positive hw0 hw1))
    have he : starRatio w * (upperFactor w * (R).B p p) ≈
        lowerFactor w * (R).B p p :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _
          (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))))
    exact Q'.le_trans' _ _ _ hu (Q'.le_of_eqv he)
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (deleted_sub_norm_lower hw0 hw1 K extent hK link hl p r (hcenter r))
        (Q'.le_of_lt (lowerFactor_positive hw0 hw1)))
      (actual_deleted_form_bounds hw0 hw1 K extent hK link hl ((F).sub p (J r))).1)

/-- The floor holds at every index of the ACTUAL completed conditional
vector's residual; no change of limit, measure or completion is used. -/
theorem conditional_residual_lower (p : (F).V)
    (hcenter : ∀ a : (G).V, (R).B p (J a) ≈ 0) :
    CReal.RCle (rc (starRatio w * (F).B p p))
      ((F).cinnerCompl ((F).cSub (embedV F p) (Q p)) ((F).cSub (embedV F p) (Q p))) := by
  change CReal.leEv (CReal.ofQ' (starRatio w * (F).B p p))
    ((F).cinnerRep
      ((F).subCauchy (constCauchy F p)
        (probeCauchy hw0 hw1 K extent hK link hl (inverseCauchy hw0 hw1 K extent hK link hl (N p))))
      ((F).subCauchy (constCauchy F p)
        (probeCauchy hw0 hw1 K extent hK link hl (inverseCauchy hw0 hw1 K extent hK link hl (N p)))))
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  exact probe_residual_lower hw0 hw1 K extent hK link hl p _ hcenter

/-- Strict squared-norm control of the actual conditional vector on the
free-link-centered sector. `inverseRate w = 1 - starRatio w`; this is NOT
a full vacuum-complement gap or a spatial mixing estimate. -/
theorem conditionalUpdate_freeCentered_norm (p : (F).V)
    (hcenter : ∀ a : (G).V, (R).B p (J a) ≈ 0) :
    CReal.RCle ((F).cinnerCompl (Q p) (Q p)) (rc (inverseRate w * (F).B p p)) := by
  have h := GNSPairingNormBound.norm_le_of_residual_floor F (Q p) (embedV F p)
    (rc (starRatio w * (F).B p p))
    (conditionalUpdate_self_pairing hw0 hw1 K extent hK link hl p)
    (conditional_residual_lower hw0 hw1 K extent hK link hl p hcenter)
  have he : CReal.RCsub ((F).cinnerCompl (embedV F p) (embedV F p))
      (rc (starRatio w * (F).B p p)) = rc (inverseRate w * (F).B p p) := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (by decide)
      (fun | 0 => (F).B p p | _ => starRatio w)
  rw [he] at h
  exact h

/-- The strict local estimate belongs to the constructed ORIGINAL operator,
on embedded free-centered inputs, not to a replacement heat-bath model. -/
theorem conditionalProjection_freeCentered_norm (p : (F).V)
    (hcenter : ∀ a : (G).V, (R).B p (J a) ≈ 0) :
    let C := conditionalProjection hw0 hw1 K extent hK link hl
    CReal.RCle ((F).cinnerCompl (C (embedV F p)) (C (embedV F p)))
      (rc (inverseRate w * (F).B p p)) := by
  dsimp only
  rw [conditionalProjection_embed]
  exact conditionalUpdate_freeCentered_norm hw0 hw1 K extent hK link hl p hcenter

/-- Every original polynomial gives an explicit input in the controlled
sector: subtract its computed free-link average on the same carrier. -/
theorem conditionalProjection_freeResidual_norm (p : (F).V) :
    let r := freeResidual hw0 hw1 K extent hK link hl p
    let C := conditionalProjection hw0 hw1 K extent hK link hl
    CReal.RCle ((F).cinnerCompl (C (embedV F r)) (C (embedV F r)))
      (rc (inverseRate w * (F).B r r)) :=
  conditionalProjection_freeCentered_norm hw0 hw1 K extent hK link hl _
    (freeResidual_pair_zero hw0 hw1 K extent hK link hl p)

end YMGap.Continuum.BF4ExactSlabStarLocalInfluence

#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.actual_deleted_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.probe_residual_lower
#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.conditional_residual_lower
#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.conditionalUpdate_freeCentered_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.conditionalProjection_freeCentered_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarLocalInfluence.conditionalProjection_freeResidual_norm
