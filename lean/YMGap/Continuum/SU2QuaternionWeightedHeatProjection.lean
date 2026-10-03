/-
# Actual normalized selected-link projection in its joint heat law

The update integrates only the selected input i against heatAt(i,j).
The surrounding factor R is independent of i, but may depend on the existing
output j and every other spectator. Original Haar normalization proves exact
weighted residual orthogonality and Pythagoras; constructed heat/R positivity
then gives square contraction with coefficient ONE. No free-polynomial unit
identity, headMap identification, conditional gap, variance inverse or
interacting/scaling conclusion is assumed or asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionWeightedProjectionSweep

namespace YMGap.Continuum.SU2QuaternionWeightedHeatProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv

/-- Literal in-place selected update; no spectator is discarded. -/
def heatUpdate (i j : Nat) (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  project i (polyMul (heatAt i j w K) p)

/-- The unchanged joint law, with the heat factor appearing exactly once. -/
def heatJointWeight (i j : Nat) (w : Q') (K : Nat) (R : RatPoly) : RatPoly :=
  polyMul (heatAt i j w K) R

/-- Literal conditionally centered residual on the original ambient carrier. -/
def heatResidual (i j : Nat) (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (heatUpdate i j w K p))

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem heatUpdate_supported {blocks i j : Nat} (hi : i < blocks) (hj : j < blocks)
    (w : Q') (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (heatUpdate i j w K p) :=
  project_supported i (supported_polyMul (heat_supported hi hj w K) hp)

theorem heatUpdate_independent (i j : Nat) (w : Q') (K : Nat) (p : RatPoly) :
    QuaternionBlockIndependent i (heatUpdate i j w K p) :=
  project_independent i _

theorem heatResidual_supported {blocks i j : Nat} (hi : i < blocks) (hj : j < blocks)
    (w : Q') (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (heatResidual i j w K p) :=
  supported_add hp (supported_neg (heatUpdate_supported hi hj w K hp))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::ps =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks ps))
        (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_neg (blocks : Nat) (W p : RatPoly) :
    quaternionHaar blocks (polyMul W (polyNeg p)) ≈
      -quaternionHaar blocks (polyMul W p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => W | _ => p))) (haar_neg blocks _)

/-- Every independent test has the SAME pairing before and after the actual
normalized heat update. No positivity or nome/cutoff restriction is needed. -/
theorem heatUpdate_weighted_pairing (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (R p z : RatPoly) (hR : SupportedQuaternionBlocks (tail+1) R)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hz : SupportedQuaternionBlocks (tail+1) z)
    (hRi : QuaternionBlockIndependent i.val R) (hzi : QuaternionBlockIndependent i.val z) :
    quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R) (polyMul p z)) ≈
      quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R)
        (polyMul (heatUpdate i.val j.val w K p) z)) := by
  let U := heatAt i.val j.val w K
  let E := heatUpdate i.val j.val w K p
  have hE := heatUpdate_supported i.isLt j.isLt w K hp
  have hEi := heatUpdate_independent i.val j.val w K p
  have hRz := quaternionBlockIndependent_polyMul hRi hzi
  have hproject : quaternionHaar (tail+1) (polyMul E (polyMul R z)) ≈
      quaternionHaar (tail+1) (polyMul (polyMul U p) (polyMul R z)) :=
    Q'.eqv_trans _ _ _ (project_selfAdjoint (tail+1) i.val i.isLt _ _)
      (haar_of_coeff ((project_fixed i.val (polyMul R z) hRz).mul_left (polyMul U p)))
  have hfirst : quaternionHaar (tail+1)
      (polyMul (heatJointWeight i.val j.val w K R) (polyMul p z)) ≈
      quaternionHaar (tail+1) (polyMul R (polyMul E z)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => U
          | 1 => R
          | 2 => p
          | _ => z)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hproject)
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => E | 1 => R | _ => z))))
  have hremove : quaternionHaar (tail+1)
      (polyMul (heatJointWeight i.val j.val w K R) (polyMul E z)) ≈
      quaternionHaar (tail+1) (polyMul R (polyMul E z)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc U R (polyMul E z)))
      (pair_vacuum tail ht i j hij w K (polyMul R (polyMul E z))
        (supported_polyMul hR (supported_polyMul hE hz))
        (independent_has_degree_zero
          (quaternionBlockIndependent_polyMul hRi
            (quaternionBlockIndependent_polyMul hEi hzi))))
  exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_symm hremove)

/-- Conditional centering is orthogonal to every independent test in the
ORIGINAL joint heat law, including tests depending on its output j. -/
theorem heatResidual_weighted_orthogonal (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (R p z : RatPoly) (hR : SupportedQuaternionBlocks (tail+1) R)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hz : SupportedQuaternionBlocks (tail+1) z)
    (hRi : QuaternionBlockIndependent i.val R) (hzi : QuaternionBlockIndependent i.val z) :
    quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R)
      (polyMul (heatResidual i.val j.val w K p) z)) ≈ 0 := by
  let W := heatJointWeight i.val j.val w K R
  let E := heatUpdate i.val j.val w K p
  have hpair := heatUpdate_weighted_pairing tail ht i j hij w K R p z hR hp hz hRi hzi
  have hex : RatPolyCoeffEqv (polyMul (heatResidual i.val j.val w K p) z)
      (polyAdd (polyMul p z) (polyNeg (polyMul E z))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => p | 1 => E | _ => z)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hex.mul_left W))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (tail+1) W _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hpair (weighted_neg (tail+1) W _))
        (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
          (by decide) (fun _ => quaternionHaar (tail+1) (polyMul W (polyMul E z))))))

/-- Exact joint-weight Pythagoras. R may be signed; it is only required to
be independent of the selected input. The heat prefix itself is unchanged. -/
theorem heatUpdate_weighted_square_decomposition (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (R p : RatPoly) (hR : SupportedQuaternionBlocks (tail+1) R)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hRi : QuaternionBlockIndependent i.val R) :
    quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R) (polyMul p p)) ≈
      quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R)
        (polyMul (heatUpdate i.val j.val w K p) (heatUpdate i.val j.val w K p))) +
      quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R)
        (polyMul (heatResidual i.val j.val w K p) (heatResidual i.val j.val w K p))) := by
  let W := heatJointWeight i.val j.val w K R
  let E := heatUpdate i.val j.val w K p
  let F := heatResidual i.val j.val w K p
  have hc : quaternionHaar (tail+1) (polyMul W (polyMul E F)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm E F).mul_left W))
      (heatResidual_weighted_orthogonal tail ht i j hij w K R p E hR hp
        (heatUpdate_supported i.isLt j.isLt w K hp) hRi
        (heatUpdate_independent i.val j.val w K p))
  have halg : RatPolyCoeffEqv (polyMul p p)
      (polyAdd (polyMul E E) (polyAdd (polyMul F F)
        (polyAdd (polyMul E F) (polyMul E F)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => p | _ => E)
  have hz : quaternionHaar (tail+1)
      (polyMul W (polyAdd (polyMul E F) (polyMul E F))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (tail+1) W _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc) (by decide : (0 : Q')+0 ≈ 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (halg.mul_left W))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (tail+1) W _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (tail+1) W _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- Actual positive joint weight at the existing all-nome head guard. No
normalizer or square-norm estimate is supplied as a premise. -/
def heatJointCertificate {blocks i j : Nat} (hi : i < blocks) (hj : j < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) {R : RatPoly} (PR : Certificate blocks R) :
    Certificate blocks (heatJointWeight i j w K R) := by
  have PU : Certificate blocks (heatAt i j w K) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
      (fun | 0 => heatAt i j w K | _ => cap (headFloor w)))
      ((heatAt_floorCertificate hi hj hw0 hw1 K hK).add
        (.constant blocks (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))
  exact PU.mul PR

/-- Jensen contraction in the SAME joint law. The coefficient is ONE and
there is no output-independence requirement on p or R. Zero norms are included. -/
theorem heatUpdate_weighted_square_le (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (R p : RatPoly) (hR : SupportedQuaternionBlocks (tail+1) R)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hRi : QuaternionBlockIndependent i.val R)
    (PR : Certificate (tail+1) R) :
    quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R)
      (polyMul (heatUpdate i.val j.val w K p) (heatUpdate i.val j.val w K p))) ≤
      quaternionHaar (tail+1) (polyMul (heatJointWeight i.val j.val w K R) (polyMul p p)) := by
  have P := heatJointCertificate i.isLt j.isLt hw0 hw1 K hK PR
  have hnonneg : (0 : Q') ≤ quaternionHaar (tail+1)
      (polyMul (heatJointWeight i.val j.val w K R)
        (polyMul (heatResidual i.val j.val w K p) (heatResidual i.val j.val w K p))) :=
    (P.mul (.square _ (heatResidual_supported i.isLt j.isLt w K hp))).haar_nonnegative
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hnonneg)
    (Q'.ge_of_eqv (heatUpdate_weighted_square_decomposition tail ht i j hij w K R p hR hp hRi))

end YMGap.Continuum.SU2QuaternionWeightedHeatProjection

#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatJointWeight
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatResidual
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate_supported
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate_independent
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatResidual_supported
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate_weighted_pairing
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatResidual_weighted_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate_weighted_square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatJointCertificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatProjection.heatUpdate_weighted_square_le
