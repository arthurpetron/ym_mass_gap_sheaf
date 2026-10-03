/-
# Integrate the ORIGINAL lower fringe before the source derivative square

The absent lower kinetic coordinates are averaged in the complete signed
source derivative, before conditional Jensen. The original score is unchanged
under every surviving insertion. Its projected budget is no larger than the
previous unsplit budget under every certified output weight. No action factor,
upper spectator, source derivative or kinetic mass is removed. These finite
comparisons do not pay the remaining active conditional Jensen debt relative
to the surviving norm, or supply a changing-family survival estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
import YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
  (partialHaarHeads partialHaarHeads_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productHeat_independent_lower lift_lower_independent)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
  (partialHaarHeads_certificate)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
  (quaternionHaar_polyMul_eq_after_integratingBlocks)
open YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras
  (familyProject_weighted_square_le family_weighted_square_decomposition)
open YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras (familyResidual)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Only absent LOWER kinetic coordinates are averaged; all upper variables
and the full signed action/source derivative remain in the same polynomial. -/
def lastStepProjectedDerivative (w : Q') (K width s i j : Nat) (a c : RatPoly) : RatPoly :=
  familyProject (fringeBlocks width) (lastStepSourceDerivative w K width s i j a c)

/-- The original conditional kinetic mass is retained without cancellation. -/
def lastStepProjectedDerivativeBudget (w : Q') (K width s i j : Nat)
    (a c : RatPoly) : RatPoly :=
  let Q := lastStepProjectedDerivative w K width s i j a c
  polyMul (partialHaarHeads (N width) (kineticWeight w K width))
    (partialHaarHeads (N width) (polyMul (kineticWeight w K width) (polyMul Q Q)))

/-- The removed lower-fringe square, not the remaining active Jensen debt. -/
def lastStepProjectedDerivativeFringeDebt (w : Q') (K width s i j : Nat)
    (a c : RatPoly) : RatPoly :=
  let R := familyResidual (fringeBlocks width) (lastStepSourceDerivative w K width s i j a c)
  polyMul (partialHaarHeads (N width) (kineticWeight w K width))
    (partialHaarHeads (N width) (polyMul (kineticWeight w K width) (polyMul R R)))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

private theorem sourceDerivative_supported (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    SupportedQuaternionBlocks (N width+N width)
      (lastStepSourceDerivative w K width s i j a c) := by
  have hD {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
      SupportedQuaternionBlocks (N width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) p)) :=
    angularDerivative_supported_at (by omega) (by omega)
      (supported_polyMul (spatialWeight_supported w K width) hp)
  exact supported_add
    (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
      (support_mono (hD hc) (by omega)))
    (support_neg (supported_polyMul
      (lift_supported (transferStep_supported w K width hc) (N width))
      (support_mono (hD ha) (by omega))))

theorem lastStepProjectedDerivative_supported (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    SupportedQuaternionBlocks (N width+N width)
      (lastStepProjectedDerivative w K width s i j a c) :=
  familyProject_supported _ (sourceDerivative_supported w K width s i j hs hi hj ha hc)

private theorem kinetic_fringe_independent (w : Q') (K width i : Nat)
    (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (kineticWeight w K width) := by
  rw [kineticWeight_eq_indexedProduct]
  exact productHeat_independent_lower (N width) w K (activeBlocks width)
    (activeBlocks_lt width) i (fringeBlocks_lt width i hi)
    ((fringeBlocks_mem_iff width i).mp hi).2

/-- Conditional integration against the original kernel is unchanged by
averaging its absent lower coordinates. The upper insertion is arbitrary. -/
private theorem fringe_head_carrier (w : Q') (K width : Nat) (Y : RatPoly) :
    HaarCarrierEqv (N width)
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width) Y))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (familyProject (fringeBlocks width) Y))) := by
  intro z
  let P := kineticWeight w K width
  let r := polyMul P (liftBoundary (N width) z)
  have hr : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i r :=
    fun i hi => quaternionBlockIndependent_polyMul
      (kinetic_fringe_independent w K width i hi)
      (lift_lower_independent (N width) z i (fringeBlocks_lt width i hi))
  have he := quaternionHaar_polyMul_eq_after_integratingBlocks
    (N width+N width) (fringeBlocks width) r Y
    (fun i hi => by have := fringeBlocks_lt width i hi; omega) hr
  have reorder (p : RatPoly) : RatPolyCoeffEqv
      (polyMul (polyMul P p) (liftBoundary (N width) z)) (polyMul r p) :=
    (RatPolyCoeffEqv.mul_assoc P p (liftBoundary (N width) z)).trans
      (((RatPolyCoeffEqv.mul_comm p (liftBoundary (N width) z)).mul_left P).trans
        (RatPolyCoeffEqv.mul_assoc P (liftBoundary (N width) z) p).symm)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing (N width) (N width) (polyMul P Y) z))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (reorder Y))
        (Q'.eqv_trans _ _ _ he
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (reorder _)))
            (Q'.eqv_trans _ _ _ (head_pairing (N width) (N width)
              (polyMul P (familyProject (fringeBlocks width) Y)) z)
              (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))))))

/-- The ORIGINAL output score is recovered under every surviving insertion,
not just by a scalar total-Haar equality. No fringe locality of a,c is assumed. -/
theorem lastStep_projectedDerivative_carrier (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    HaarCarrierEqv (N width)
      (conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (lastStepProjectedDerivative w K width s i j a c))) :=
  HaarCarrierEqv.trans (lastStep_sourceDerivative_carrier w K width s i j hs hi hj ha hc)
    (fringe_head_carrier w K width _)

private def kinetic_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width) (kineticWeight w K width) := by
  rw [kineticWeight_eq_indexedProduct]
  exact productHeatCertificate (N width) hw0 hw1 K hK
    (activeBlocks width) (activeBlocks_lt width)

/-- Conditional Jensen is applied AFTER the genuine lower-fringe integration. -/
def lastStep_projectedDerivative_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    Certificate (N width) (polyAdd (lastStepProjectedDerivativeBudget w K width s i j a c)
      (polyNeg (polyMul S S))) := by
  dsimp only
  let Q := lastStepProjectedDerivative w K width s i j a c
  have P := determinant_certificate (N width) (N width) (kineticWeight w K width) Q
    (kineticWeight_supported w K width)
    (lastStepProjectedDerivative_supported w K width s i j hs hi hj ha hc)
    (kinetic_certificate hw0 hw1 K width hK)
  have hS := lastStep_projectedDerivative_carrier w K width s i j hs hi hj ha hc
  exact .transport
    (HaarCarrierEqv.add
      (HaarCarrierEqv.refl (N width) (lastStepProjectedDerivativeBudget w K width s i j a c))
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hS hS))) P

/-- Arbitrary certified surviving weight and multiplier, with the original
score and the smaller literal projected source budget. -/
theorem lastStep_projectedDerivative_weighted_multiplier_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W m : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (hm : SupportedQuaternionBlocks (N width) m) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    quaternionHaar (N width) (polyMul W (polyMul (polyMul m S) (polyMul m S))) ≤
      quaternionHaar (N width) (polyMul (polyMul W (polyMul m m))
        (lastStepProjectedDerivativeBudget w K width s i j a c)) := by
  dsimp only
  let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
  let B := lastStepProjectedDerivativeBudget w K width s i j a c
  let E := polyMul (polyMul W (polyMul m m)) (polyAdd B (polyNeg (polyMul S S)))
  have hn := ((MW.mul (Certificate.square m hm)).mul
    (lastStep_projectedDerivative_certificate hw0 hw1 K width hK s i j hs hi hj ha hc)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul m S) (polyMul m S))) E)
      (polyMul (polyMul W (polyMul m m)) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add (.var 3) (.neg (.mul (.var 2) (.var 2))))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 3))
      (by decide) (fun
        | 0 => W
        | 1 => m
        | 2 => S
        | _ => B)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (N width) _ _))
    (haar_of_coeff hid)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

private theorem budget_pairing (w : Q') (K width : Nat) (W Y : RatPoly) :
    quaternionHaar (N width)
      (polyMul W (polyMul (partialHaarHeads (N width) (kineticWeight w K width))
        (partialHaarHeads (N width) (polyMul (kineticWeight w K width) (polyMul Y Y))))) ≈
      quaternionHaar (N width+N width)
        (polyMul (polyMul (kineticWeight w K width)
          (liftBoundary (N width)
            (polyMul W (partialHaarHeads (N width) (kineticWeight w K width)))))
          (polyMul Y Y)) := by
  let P := kineticWeight w K width
  let M := partialHaarHeads (N width) P
  let I := partialHaarHeads (N width) (polyMul P (polyMul Y Y))
  have hrow : RatPolyCoeffEqv (polyMul W (polyMul M I)) (polyMul I (polyMul W M)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun
        | 0 => W
        | 1 => M
        | _ => I)
  have hcol : RatPolyCoeffEqv
      (polyMul (polyMul P (polyMul Y Y)) (liftBoundary (N width) (polyMul W M)))
      (polyMul (polyMul P (liftBoundary (N width) (polyMul W M))) (polyMul Y Y)) :=
    (RatPolyCoeffEqv.mul_assoc P (polyMul Y Y) _).trans
      (((RatPolyCoeffEqv.mul_comm (polyMul Y Y) _).mul_left P).trans
        (RatPolyCoeffEqv.mul_assoc P _ _).symm)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hrow)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm
      (head_pairing (N width) (N width) (polyMul P (polyMul Y Y)) (polyMul W M)))
      (haar_of_coeff hcol))

/-- Exact weighted decomposition: only the lower-fringe residual square
has been removed. All surviving multipliers can be included in W. -/
theorem lastStep_projectedDerivative_weighted_budget_decomposition
    (w : Q') (K width s i j : Nat) (a c W : RatPoly) :
    quaternionHaar (N width) (polyMul W (lastStepSourceDerivativeBudget w K width s i j a c)) ≈
      quaternionHaar (N width) (polyMul W (lastStepProjectedDerivativeBudget w K width s i j a c)) +
        quaternionHaar (N width) (polyMul W
          (lastStepProjectedDerivativeFringeDebt w K width s i j a c)) := by
  let P := kineticWeight w K width
  let M := partialHaarHeads (N width) P
  let Y := lastStepSourceDerivative w K width s i j a c
  let E := polyMul P (liftBoundary (N width) (polyMul W M))
  have hE : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i E :=
    fun i hi => quaternionBlockIndependent_polyMul
      (kinetic_fringe_independent w K width i hi)
      (lift_lower_independent (N width) (polyMul W M) i (fringeBlocks_lt width i hi))
  have hd := family_weighted_square_decomposition (N width+N width) (fringeBlocks width)
    (fun i hi => by have := fringeBlocks_lt width i hi; omega) E Y hE
  exact Q'.eqv_trans _ _ _ (budget_pairing w K width W Y)
    (Q'.eqv_trans _ _ _ hd (Q'.add_eqv_congr'
      (Q'.eqv_symm (budget_pairing w K width W
        (lastStepProjectedDerivative w K width s i j a c)))
      (Q'.eqv_symm (budget_pairing w K width W (familyResidual (fringeBlocks width) Y)))))

/-- The projected budget is no larger under EVERY certified surviving
weight. A reciprocal square can be included in W without losing its variables. -/
theorem lastStep_projectedDerivative_weighted_budget_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) :
    quaternionHaar (N width) (polyMul W (lastStepProjectedDerivativeBudget w K width s i j a c)) ≤
      quaternionHaar (N width) (polyMul W (lastStepSourceDerivativeBudget w K width s i j a c)) := by
  let P := kineticWeight w K width
  let M := partialHaarHeads (N width) P
  let Y := lastStepSourceDerivative w K width s i j a c
  let E := polyMul P (liftBoundary (N width) (polyMul W M))
  have PK : Certificate (N width+N width) P := kinetic_certificate hw0 hw1 K width hK
  have PM : Certificate (N width) M := partialHaarHeads_certificate (N width) (N width) PK
  have PE : Certificate (N width+N width) E := PK.mul (lift_certificate (N width) (MW.mul PM))
  have hE : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i E :=
    fun i hi => quaternionBlockIndependent_polyMul
      (kinetic_fringe_independent w K width i hi)
      (lift_lower_independent (N width) (polyMul W M) i (fringeBlocks_lt width i hi))
  have h := familyProject_weighted_square_le (N width+N width) (fringeBlocks width)
    (fun i hi => by have := fringeBlocks_lt width i hi; omega) PE
    (sourceDerivative_supported w K width s i j hs hi hj ha hc) hE
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (budget_pairing w K width W
      (lastStepProjectedDerivative w K width s i j a c)))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (budget_pairing w K width W Y)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStepProjectedDerivative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStepProjectedDerivativeBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStepProjectedDerivativeFringeDebt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStepProjectedDerivative_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStep_projectedDerivative_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStep_projectedDerivative_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStep_projectedDerivative_weighted_multiplier_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStep_projectedDerivative_weighted_budget_decomposition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lastStep_projectedDerivative_weighted_budget_le
