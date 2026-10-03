/-
# The last ORIGINAL step score without a kernel derivative cap

Angular commutation moves the kernel derivative onto the COMPLETE signed
sources V*c and V*a. Their derivatives remain in ONE paired square. The
constructed determinant certificate retains the kinetic mass I(K), both
outgoing messages, and every shared coordinate. No source inverse, relative
derivative cap, positive incoming message or canceled action factor occurs.

The weighted and reciprocal consumers retain this actual source-derivative
budget. Its useful relative size on a changing family is still unproved.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation
import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat productMap)
open YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity (reciprocalSlope_supported)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance (lastStepPairedResidual)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- The two COMPLETE source derivatives are retained in a single square. -/
def lastStepSourceDerivative (w : Q') (K width s i j : Nat) (a c : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (liftBoundary (N width) (transferStep w K width a))
      (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) c)))
    (polyNeg (polyMul (liftBoundary (N width) (transferStep w K width c))
      (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) a))))

/-- Kinetic mass times the actual conditional square; no mass is canceled. -/
def lastStepSourceDerivativeBudget (w : Q') (K width s i j : Nat) (a c : RatPoly) : RatPoly :=
  let Y := lastStepSourceDerivative w K width s i j a c
  polyMul (partialHaarHeads (N width) (kineticWeight w K width))
    (partialHaarHeads (N width) (polyMul (kineticWeight w K width) (polyMul Y Y)))

/-- Exact source/action expansion for inspection only. The budget continues
to square Y as a whole; no separate bound on these summands is taken. -/
theorem lastStepSourceDerivative_expansion (w : Q') (K width s i j : Nat) (a c : RatPoly) :
    RatPolyCoeffEqv (lastStepSourceDerivative w K width s i j a c)
      (polyAdd
        (polyMul (spatialWeight w K width)
          (polyAdd
            (polyMul (liftBoundary (N width) (transferStep w K width a))
              (angularDerivative (4*s+i) (4*s+j) c))
            (polyNeg (polyMul (liftBoundary (N width) (transferStep w K width c))
              (angularDerivative (4*s+i) (4*s+j) a)))))
        (polyMul (angularDerivative (4*s+i) (4*s+j) (spatialWeight w K width))
          (lastStepPairedResidual w K width a c))) := by
  exact (((angularDerivative_mul (4*s+i) (4*s+j) (spatialWeight w K width) c).mul_left _).add
    (RatPolyCoeffEqv.neg
      ((angularDerivative_mul (4*s+i) (4*s+j) (spatialWeight w K width) a).mul_left _))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.mul (.var 5) (.var 3)) (.mul (.var 2) (.var 6))))
        (.neg (.mul (.var 1) (.add (.mul (.var 5) (.var 4)) (.mul (.var 2) (.var 7))))))
      (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 6)) (.neg (.mul (.var 1) (.var 7)))))
        (.mul (.var 5) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 4))))))
      (by decide) (fun
        | 0 => liftBoundary (N width) (transferStep w K width a)
        | 1 => liftBoundary (N width) (transferStep w K width c)
        | 2 => spatialWeight w K width | 3 => c | 4 => a
        | 5 => angularDerivative (4*s+i) (4*s+j) (spatialWeight w K width)
        | 6 => angularDerivative (4*s+i) (4*s+j) c
        | _ => angularDerivative (4*s+i) (4*s+j) a))

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

private theorem paired_integral (heads : Nat) (P A b dc da : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul P
        (polyAdd (polyMul (liftBoundary heads A) dc)
          (polyNeg (polyMul (liftBoundary heads b) da)))))
      (polyAdd (polyMul A (partialHaarHeads heads (polyMul P dc)))
        (polyNeg (polyMul b (partialHaarHeads heads (polyMul P da))))) := by
  have hsplit := partialHaarHeads_congr heads
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4)))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.mul (.var 0) (.var 4)) (.var 3))))
      (by decide) (fun
        | 0 => P | 1 => liftBoundary heads A | 2 => dc
        | 3 => liftBoundary heads b | _ => da))
  change RatPolyCoeffEqv _
    (partialHaarHeads heads (polyAdd (polyMul (polyMul P dc) (liftBoundary heads A))
      (polyNeg (polyMul (polyMul P da) (liftBoundary heads b))))) at hsplit
  rw [partialHaarHeads_add] at hsplit
  exact hsplit.trans
    (((partialHaarHeads_mul_lift heads (polyMul P dc) A).trans
      (RatPolyCoeffEqv.mul_comm _ A)).add
      ((partialHaarHeads_neg heads _).trans
        (RatPolyCoeffEqv.neg ((partialHaarHeads_mul_lift heads (polyMul P da) b).trans
          (RatPolyCoeffEqv.mul_comm _ b)))))

private theorem derivative_transfer (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (N width)
      (angularDerivative (4*s+i) (4*s+j) (transferStep w K width p))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) p)))) := by
  rw [transferStep_eq_productMap, kineticWeight_eq_indexedProduct]
  exact productMap_angular_carrier (N width) s i j hs hi hj w K
    (activeBlocks width) (activeBlocks_lt width) _
    (supported_polyMul (spatialWeight_supported w K width) hp)

/-- This is an arbitrary-insertion ORIGINAL carrier equality, not a free
coefficient equality or a scalar-only integration by parts assertion. -/
theorem lastStep_sourceDerivative_carrier (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    HaarCarrierEqv (N width)
      (conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (lastStepSourceDerivative w K width s i j a c))) := by
  have h := HaarCarrierEqv.add
    (HaarCarrierEqv.mul_left (transferStep w K width a)
      (derivative_transfer w K width s i j hs hi hj hc))
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul_left (transferStep w K width c)
      (derivative_transfer w K width s i j hs hi hj ha)))
  exact HaarCarrierEqv.trans h (RatPolyCoeffEqv.haarCarrier
    (paired_integral (N width) (kineticWeight w K width) _ _ _ _).symm)

/-- An actual conditional determinant certificate. Only the original
kinetic density is required positive; a,c and their derivatives stay signed. -/
def lastStep_sourceDerivative_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    Certificate (N width) (polyAdd (lastStepSourceDerivativeBudget w K width s i j a c)
      (polyNeg (polyMul S S))) := by
  dsimp only
  let Y := lastStepSourceDerivative w K width s i j a c
  have hD {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
      SupportedQuaternionBlocks (N width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) p)) :=
    angularDerivative_supported_at (by omega) (by omega)
      (supported_polyMul (spatialWeight_supported w K width) hp)
  have hY : SupportedQuaternionBlocks (N width+N width) Y :=
    supported_add
      (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
        (support_mono (hD hc) (by omega)))
      (support_neg (supported_polyMul (lift_supported (transferStep_supported w K width hc) (N width))
        (support_mono (hD ha) (by omega))))
  have PK : Certificate (N width+N width) (kineticWeight w K width) := by
    rw [kineticWeight_eq_indexedProduct]
    exact productHeatCertificate (N width) hw0 hw1 K hK (activeBlocks width) (activeBlocks_lt width)
  have P := determinant_certificate (N width) (N width) (kineticWeight w K width) Y
    (kineticWeight_supported w K width) hY PK
  have hS := lastStep_sourceDerivative_carrier w K width s i j hs hi hj ha hc
  exact .transport
    (HaarCarrierEqv.add
      (HaarCarrierEqv.refl (N width) (lastStepSourceDerivativeBudget w K width s i j a c))
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hS hS))) P

/-- Every output weight and multiplier retains the complete unsplit budget. -/
theorem lastStep_sourceDerivative_weighted_multiplier_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W J : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (hJ : SupportedQuaternionBlocks (N width) J) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    quaternionHaar (N width) (polyMul W (polyMul (polyMul J S) (polyMul J S))) ≤
      quaternionHaar (N width) (polyMul (polyMul W (polyMul J J))
        (lastStepSourceDerivativeBudget w K width s i j a c)) := by
  dsimp only
  let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
  let B := lastStepSourceDerivativeBudget w K width s i j a c
  let E := polyMul (polyMul W (polyMul J J)) (polyAdd B (polyNeg (polyMul S S)))
  have hn := ((MW.mul (Certificate.square J hJ)).mul
    (lastStep_sourceDerivative_certificate hw0 hw1 K width hK s i j hs hi hj ha hc)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul J S) (polyMul J S))) E)
      (polyMul (polyMul W (polyMul J J)) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add (.var 3) (.neg (.mul (.var 2) (.var 2))))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 3))
      (by decide) (fun | 0 => W | 1 => J | 2 => S | _ => B)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (N width) _ _)) (haar_of_coeff hid)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Finite same-weight reciprocal consumer; no lower window, inverse
source, or omitted reciprocal correction is used in this square bound. -/
theorem lastStep_sourceDerivative_reciprocal_gradient_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let G := reciprocal A u hu k
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu k
    quaternionHaar (N width) (polyMul W (polyMul d d)) ≤
      sumBound
        (quaternionHaar (N width) (polyMul (polyMul W (polyMul G G))
          (lastStepSourceDerivativeBudget w K width s i j a c)))
        (quaternionHaar (N width) (polyMul W (polyMul e e))) := by
  dsimp only
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width hc
  have hdA := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hA
  have hdb := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hb
  have hG := reciprocal_supported hA u hu k
  have hS := supported_add (supported_polyMul hA hdb) (support_neg (supported_polyMul hb hdA))
  have he := supported_polyMul hb (supported_polyMul
    (supported_add hG (support_neg (supported_polyMul hA (reciprocalSlope_supported hA u hu k)))) hdA)
  have hlead := lastStep_sourceDerivative_weighted_multiplier_square_le
    hw0 hw1 K width hK s i j hs hi hj ha hc MW hG
  have hid := reciprocal_score_cleared_derivative (4*s+i) (4*s+j)
    (transferStep w K width a) (transferStep w K width c) u hu k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hid.mul hid).mul_left W)))
    (weighted_square_add_bound MW (supported_polyMul hG hS) he hlead (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms lastStepSourceDerivative
#print axioms lastStepSourceDerivativeBudget
#print axioms lastStepSourceDerivative_expansion
#print axioms lastStep_sourceDerivative_carrier
#print axioms lastStep_sourceDerivative_certificate
#print axioms lastStep_sourceDerivative_weighted_multiplier_square_le
#print axioms lastStep_sourceDerivative_reciprocal_gradient_square_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
