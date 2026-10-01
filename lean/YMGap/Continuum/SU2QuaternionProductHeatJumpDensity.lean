/-
# The exact one-ended cost as a positive active-carrier density

The whole observable jump is squared before the lower Haar heads are removed.
In particular, mixed terms in a signed observable family are retained.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionProductHeatJumpDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- The exact heat-weighted square of the complete observable jump, after
integrating the lower heads. It is a polynomial on the original active carrier. -/
def jumpDensity (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (f : RatPoly) : RatPoly :=
  partialHaarHeads n
    (polyMul (productHeat n w K ids)
      (polyMul (jump n f) (jump n f)))

theorem jumpDensity_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (jumpDensity n w K ids f) := by
  unfold jumpDensity
  apply partialHaarHeads_supported n n
  exact supported_polyMul (productHeat_supported n w K ids hids)
    (supported_polyMul (jump_supported hf) (jump_supported hf))

/-- A Type-level positivity witness from the actual finite heat certificate. -/
def jumpDensity_certificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    Certificate n (jumpDensity n w K ids f) := by
  unfold jumpDensity
  exact partialHaarHeads_certificate n n
    ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
      (Certificate.square (jump n f) (jump_supported hf)))

private theorem head_degree {i d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree (i+1) d p) :
    HasQuaternionBlockDegree i d (partialHaarHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change quaternionBlockDegree (s.1.drop 4) i = d
  simpa only [quaternionBlockDegree, exponentAt_drop,
    show 4+4*i = 4*(i+1) by omega,
    show 4+(4*i+1) = 4*(i+1)+1 by omega,
    show 4+(4*i+2) = 4*(i+1)+2 by omega,
    show 4+(4*i+3) = 4*(i+1)+3 by omega] using hp s hs

private theorem heads_degree (n i d : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree (n+i) d p) :
    HasQuaternionBlockDegree i d (partialHaarHeads n p) := by
  induction n generalizing p with
  | zero => simpa only [Nat.zero_add] using hp
  | succ n ih =>
      apply ih
      apply head_degree (i := n+i)
      simpa only [Nat.succ_add, Nat.add_succ] using hp

/-- If the entire observable is independent of an unselected block, the
cost density is independent of that block too. -/
theorem jumpDensity_independent (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n)
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f)
    (i : Nat) (hi : i < n) (hnot : i ∉ ids)
    (hind : QuaternionBlockIndependent i f) :
    QuaternionBlockIndependent i (jumpDensity n w K ids f) := by
  have hW : HasQuaternionBlockDegree (n+i) 0 (productHeat n w K ids) :=
    independent_has_degree_zero
      (productHeat_independent_upper n w K ids hids i hi hnot)
  have hJ : HasQuaternionBlockDegree (n+i) 0 (jump n f) := by
    unfold jump
    exact (independent_has_degree_zero (supported_upper_independent hf i)).add
      ((independent_has_degree_zero (lift_upper_independent n hind)).neg)
  apply degree_zero_independent
  unfold jumpDensity
  exact heads_degree n i 0 (by simpa only [Nat.zero_add] using hW.mul (hJ.mul hJ))

/-- The original single-ended Young cost is exactly the Haar integral of the
source square against the density. No cross term of `f` is dropped. -/
theorem singleEndedCost_eq_jumpDensity (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    {b f : RatPoly} (hb : SupportedQuaternionBlocks n b)
    (hf : SupportedQuaternionBlocks n f) :
    singleEndedCost n w K ids b f ≈
      quaternionHaar n (polyMul (polyMul b b) (jumpDensity n w K ids f)) := by
  let J := jump n f
  let W := productHeat n w K ids
  let B := liftBoundary n b
  have hpoly : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul B J) (polyMul B J)) W)
      (polyMul (polyMul W (polyMul J J)) (polyMul B B)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.var 2) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => B | 1 => J | _ => W)
  have hhead := head_pairing n n (polyMul W (polyMul J J)) (polyMul b b)
  have hfirst :
      weightedPair (n+n) W (polyMul B J) (polyMul B J) ≈
        quaternionHaar (n+n)
          (polyMul (polyMul W (polyMul J J)) (liftBoundary n (polyMul b b))) := by
    unfold weightedPair
    rw [lift_product]
    exact haar_of_coeff hpoly
  have hlast :
      quaternionHaar n
        (polyMul (partialHaarHeads n (polyMul W (polyMul J J))) (polyMul b b)) ≈
      quaternionHaar n
        (polyMul (polyMul b b) (jumpDensity n w K ids f)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.eqv_trans _ _ _ (singleEnded_swap n w K ids hids hb hf)
    (Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _ hhead hlast))

#print axioms jumpDensity_supported
#print axioms jumpDensity_certificate
#print axioms jumpDensity_independent
#print axioms singleEndedCost_eq_jumpDensity

end YMGap.Continuum.SU2QuaternionProductHeatJumpDensity
