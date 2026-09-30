/-
# Full-action gauge pairing on the augmented original Haar carrier

The common auxiliary-vertex gauge ledger acts on both polynomial tests,
while the original full physical heat product remains the weight.  The
identity is an exact finite Haar pairing, with no claim that the gauge
ledger acts on the unaugmented completion or commutes with projections.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaugeAction
import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.BF4ExactSlabGaugeWeightedPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private abbrev Lift (p : RatPoly) := liftBoundary 3 p
private abbrev G (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) :=
  slabGaugePolynomial extent tags

private theorem gauge_mul (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (p q : RatPoly) :
    RatPolyCoeffEqv (G extent tags (polyMul p q))
      (polyMul (G extent tags p) (G extent tags q)) := by
  exact applySelectedTranslationSteps_mul
    (by omega : 0 < linkCount extent + 2)
    (gaugeLedger (startTag extent tags) (finishTag extent tags)) p q

/-- The original, untransformed full heat product is the weight on the
augmented carrier. Both supported tests are transformed by the same actual
vertex gauge ledger. All physical face factors are retained. -/
theorem fullWeight_gauge_pairing (extent : Nat)
    (tags : Z4Vertex → Option (Fin 3)) (w : Q') (K : Nat)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (linkCount extent) p)
    (hq : SupportedQuaternionBlocks (linkCount extent) q) :
    quaternionHaar (linkCount extent + 3)
      (polyMul
        (polyMul (G extent tags (Lift p)) (G extent tags (Lift q)))
        (Lift (fullWeight w K extent))) ≈
      quaternionHaar (linkCount extent)
        (polyMul (polyMul p q) (fullWeight w K extent)) := by
  let W := fullWeight w K extent
  have hW : Invariant extent tags W :=
    heatProduct_invariant tags w K (slabPhysicalFaceEdges extent) (fun _ h => h)
  have hGp : SupportedQuaternionBlocks (linkCount extent + 3)
      (G extent tags (Lift p)) :=
    gaugePolynomial_supported _ _ _ (lift_supported hp 3)
  have hGq : SupportedQuaternionBlocks (linkCount extent + 3)
      (G extent tags (Lift q)) :=
    gaugePolynomial_supported _ _ _ (lift_supported hq 3)
  have hinsert : SupportedQuaternionBlocks (linkCount extent + 3)
      (polyMul (G extent tags (Lift p)) (G extent tags (Lift q))) :=
    supported_polyMul hGp hGq
  have hcoefficient : RatPolyCoeffEqv
      (G extent tags (Lift (polyMul (polyMul p q) W)))
      (polyMul
        (polyMul (G extent tags (Lift p)) (G extent tags (Lift q)))
        (G extent tags (Lift W))) := by
    unfold Lift
    rw [lift_product 3 (polyMul p q) W, lift_product 3 p q]
    exact (gauge_mul extent tags _ _).trans
      ((gauge_mul extent tags _ _).mul_right _)
  have hsource : SupportedQuaternionBlocks (linkCount extent)
      (polyMul (polyMul p q) W) :=
    supported_polyMul (supported_polyMul hp hq) hW.support
  exact Q'.eqv_trans _ _ _
    (hW.image.symm _ hinsert)
    (Q'.eqv_trans _ _ _
      (haar_of_coeff hcoefficient.symm)
      (Q'.eqv_trans _ _ _
        (slabGauge_haar extent tags _ (lift_supported hsource 3))
        (haar_liftBoundary 3 (linkCount extent) _)))

#print axioms fullWeight_gauge_pairing

end YMGap.Continuum.BF4ExactSlabGaugeWeightedPairing
