/-
# Original slot-0/1 conditional angular Poincare bound

The selected input is the original block 0 and the retained output is the
original block 1. In-place Haar projection, not a headMap identification,
is pinned under every original insertion to conditionalHeat. Arbitrary
certified weights independent of the INPUT block retain the output and all
other spectators. The cutoff is computed from the actual signed source.

This bounded join does not claim arbitrary-pair permutation transport,
product tensorization, an interacting relative cost, or scaling/QFT closure.
-/

import YMGap.Continuum.SU2QuaternionConditionalAngularPoincare
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.SU2QuaternionHaarKernelBound
import YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadLinearHaar (liftHead_mul)
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalAngularPoincare
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Literal selected projection on the ORIGINAL carrier; output 1 remains. -/
def selectedMean (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  project 0 (polyMul (heatAt 0 1 w K) p)

def selectedVariance (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (selectedMean w K (polyMul p p))
    (polyNeg (polyMul (selectedMean w K p) (selectedMean w K p)))

private theorem degree_zero_partial {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (partialHaarHead p) (dropHeadPolynomial p) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead p) (dropHeadPolynomial p) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        have hd := hp t List.mem_cons_self
        have hz : exponentAt t.1 0 = 0 ∧ exponentAt t.1 1 = 0 ∧
            exponentAt t.1 2 = 0 ∧ exponentAt t.1 3 = 0 := by
          change exponentAt t.1 0 + exponentAt t.1 1 + exponentAt t.1 2 +
            exponentAt t.1 3 = 0 at hd
          have h012 := Nat.eq_zero_of_add_eq_zero hd
          have h01 := Nat.eq_zero_of_add_eq_zero h012.1
          have h0 := Nat.eq_zero_of_add_eq_zero h01.1
          exact ⟨h0.1, h0.2, h01.2, h012.2⟩
        have hm : headQuaternionMoment t.1 ≈ (1 : Q') := by
          unfold headQuaternionMoment
          rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
          decide +kernel
        exact ⟨rfl, Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
          (Q'.mul_one_eqv _), ih (fun s hs => hp s (List.mem_cons_of_mem t hs))⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem lift_neg (p : RatPoly) :
    liftHead (polyNeg p) = polyNeg (liftHead p) := by
  simp only [liftHead, polyNeg, List.map_map]
  rfl

private theorem lift_add (p q : RatPoly) :
    liftHead (polyAdd p q) = polyAdd (liftHead p) (liftHead q) :=
  List.map_append

/-- All surviving insertions are retained: this is NOT an eigenpin or the
refuted selected-link universal headMap identification. -/
theorem selectedMean_conditional_pin (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) :
    HaarCarrierEqv (tail+1) (selectedMean w K p)
      (liftHead (conditionalHeat w K p)) := by
  let q := polyMul (heatAt 0 1 w K) p
  have hi : HeadQuaternionIndependent (project 0 q) :=
    independent_has_degree_zero (project_independent 0 q)
  intro insertion
  have h := independent_to_lift tail insertion (project 0 q) hi
  have hd : dropHeadPolynomial (project 0 q) = conditionalHeat w K p := by
    rw [drop_project_head]
    rfl
  change quaternionHaar (tail+1) (polyMul insertion (project 0 q)) ≈ _
  rw [hd] at h
  exact h

theorem selectedVariance_conditional_pin (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) :
    HaarCarrierEqv (tail+1) (selectedVariance w K p)
      (liftHead (heatVariance w K p)) := by
  have hm := selectedMean_conditional_pin tail w K p
  have hs := HaarCarrierEqv.add
    (selectedMean_conditional_pin tail w K (polyMul p p))
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul hm hm))
  simpa only [selectedVariance, heatVariance, liftHead_mul, lift_neg,
    lift_add] using hs

private theorem independent_lift_pair (tail : Nat) (W q : RatPoly)
    (hW : HeadQuaternionIndependent W) :
    quaternionHaar (tail+1) (polyMul W (liftHead q)) ≈
      quaternionHaar tail (polyMul (dropHeadPolynomial W) q) := by
  have hl : RatPolyCoeffEqv (partialHaarHead (liftHead q)) q :=
    partialHaarHeads_liftBoundary 1 q
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_headIndependent tail (liftHead q) W hW)
      (haar_of_coeff ((hl.mul_right (dropHeadPolynomial W)).trans
        (RatPolyCoeffEqv.mul_comm _ _))))

/-- Exact ORIGINAL variance pairing, with the same output-dependent weight. -/
theorem selectedVariance_weighted_pin (tail : Nat) (w : Q') (K : Nat)
    (p W : RatPoly) (hW : QuaternionBlockIndependent 0 W) :
    quaternionHaar (tail+1) (polyMul W (selectedVariance w K p)) ≈
      quaternionHaar tail (polyMul (dropHeadPolynomial W) (heatVariance w K p)) :=
  Q'.eqv_trans _ _ _ ((selectedVariance_conditional_pin tail w K p) W)
    (independent_lift_pair tail W _ (independent_has_degree_zero hW))

/-- Exact heat/angular pairing before deleting the integrated input slot. -/
theorem selectedAngular_weighted_pin (tail : Nat) (w : Q') (K : Nat)
    (p W : RatPoly) (hW : QuaternionBlockIndependent 0 W) :
    quaternionHaar (tail+1)
      (polyMul W (polyMul (heatAt 0 1 w K) (angularSquare p))) ≈
      quaternionHaar tail (polyMul (dropHeadPolynomial W)
        (conditionalHeat w K (angularSquare p))) := by
  have hi : HeadQuaternionIndependent W := independent_has_degree_zero hW
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_headIndependent tail
        (polyMul (heatAt 0 1 w K) (angularSquare p)) W hi)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))

/-- Derived selected conditional variance bound on the SAME original
carrier. W may depend on output 1 and every spectator; only input 0 is
independent. No conditional variance/CS conclusion is a premise. -/
theorem selectedConditional_weighted_angular_variance
    (tail : Nat) (ht : 0 < tail) (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : poincareCutoff tail p ≤ K) (P : Certificate (tail+1) W)
    (hW : QuaternionBlockIndependent 0 W) :
    quaternionHaar (tail+1) (polyMul W (selectedVariance w K p)) ≤
      (1-w*w)*quaternionHaar (tail+1)
        (polyMul W (polyMul (heatAt 0 1 w K) (angularSquare p))) := by
  have hd := degree_zero_partial (independent_has_degree_zero hW)
  have PD : Certificate tail (dropHeadPolynomial W) :=
    .ofCoeff hd.symm (partialHaarHead_certificate tail P)
  have hv := selectedVariance_weighted_pin tail w K p W hW
  have he := selectedAngular_weighted_pin tail w K p W hW
  have hb := conditionalHeat_weighted_angular_variance
    tail ht w hw0 hw1 K p (dropHeadPolynomial W) hp hK PD
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hv)
    (Q'.le_trans' _ _ _ hb
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (1-w*w) _ _ (Q'.eqv_symm he))))

end YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare

#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedMean
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedVariance
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedMean_conditional_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedVariance_conditional_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedVariance_weighted_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedAngular_weighted_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare.selectedConditional_weighted_angular_variance
