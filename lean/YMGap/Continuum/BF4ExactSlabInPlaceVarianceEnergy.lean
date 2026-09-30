/-
# Original-coordinate covariance equals the actual finite variance energy

The singleton polynomial covariance is computed at the original physical
link index. Its finite reciprocal pairing, with every complementary action
factor retained, is exactly the already constructed head-coordinate
variance energy. No limiting or coercive estimate is used.
-/

import YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
import YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica

namespace YMGap.Continuum.BF4ExactSlabInPlaceVarianceEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional
open YMGap.Continuum.BF4ExactSlabStarReciprocalTransport
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarInsertedNumerator
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "s" => linkHeadSwap extent link hl
local notation "A" => incidentHeat w K extent link
local notation "B" => complementHeat w K extent link
local notation "D" => normalizer w K extent link hl
local notation "G" k => headReciprocal hw0 hw1 K extent link hl k

private theorem probe_add {n : Nat} (t : QuaternionBlockInvolution n) (p q : RatPoly) :
    headProbe t (polyAdd p q) = polyAdd (headProbe t p) (headProbe t q) := by
  change reindexQuaternionPolynomial t (liftBoundary 1 (polyAdd p q)) =
    polyAdd (reindexQuaternionPolynomial t (liftBoundary 1 p))
      (reindexQuaternionPolynomial t (liftBoundary 1 q))
  rw [lift_add, reindexQuaternionPolynomial_add]

private theorem probe_neg {n : Nat} (t : QuaternionBlockInvolution n) (p : RatPoly) :
    headProbe t (polyNeg p) = polyNeg (headProbe t p) := by
  change reindexQuaternionPolynomial t (liftBoundary 1 (polyNeg p)) =
    polyNeg (reindexQuaternionPolynomial t (liftBoundary 1 p))
  rw [lift_neg, reindexQuaternionPolynomial_neg]

def inPlaceCovariance (p : (F).V) : RatPoly :=
  covarianceNumerator [slot extent link] A p.val p.val

/-- No replacement of the conditional moments: every projected factor is
identified with its previously pinned head-coordinate numerator. -/
theorem covariance_head_pin (p : (F).V) :
    HaarCarrierEqv (blocks extent)
      (inPlaceCovariance hw0 hw1 K extent hK link p)
      (headProbe s (varianceNumerator w K extent link hl p.val)) := by
  let sq : (F).V := ⟨polyMul p.val p.val, supported_polyMul p.property p.property⟩
  have hD : HaarCarrierEqv (blocks extent)
      (project (slot extent link) A) (headProbe s D) :=
    inPlaceNormalizer_head_pin w K extent hl
  have hNp : HaarCarrierEqv (blocks extent)
      (project (slot extent link) (polyMul A p.val))
      (headProbe s (insertedNormalizer w K extent link hl p.val)) :=
    (RatPolyCoeffEqv.haarCarrier
      (project_congr _ (RatPolyCoeffEqv.mul_comm A p.val))).trans
      (numerator_head_pin hw0 hw1 K extent hK link hl p)
  have hNpp : HaarCarrierEqv (blocks extent)
      (project (slot extent link) (polyMul A (polyMul p.val p.val)))
      (headProbe s (insertedNormalizer w K extent link hl (polyMul p.val p.val))) :=
    (RatPolyCoeffEqv.haarCarrier
      (project_congr _ (RatPolyCoeffEqv.mul_comm A (polyMul p.val p.val)))).trans
      (numerator_head_pin hw0 hw1 K extent hK link hl sq)
  have hpoly : headProbe s (varianceNumerator w K extent link hl p.val) =
      polyAdd
        (polyMul (headProbe s D)
          (headProbe s (insertedNormalizer w K extent link hl (polyMul p.val p.val))))
        (polyNeg (polyMul
          (headProbe s (insertedNormalizer w K extent link hl p.val))
          (headProbe s (insertedNormalizer w K extent link hl p.val)))) := by
    simp only [varianceNumerator, probe_add, probe_neg, headProbe_mul]
  change HaarCarrierEqv (blocks extent)
    (polyAdd
      (polyMul (project (slot extent link) A)
        (project (slot extent link) (polyMul A (polyMul p.val p.val))))
      (polyNeg (polyMul
        (project (slot extent link) (polyMul A p.val))
        (project (slot extent link) (polyMul A p.val)))))
    (headProbe s (varianceNumerator w K extent link hl p.val))
  rw [hpoly]
  exact HaarCarrierEqv.add (HaarCarrierEqv.mul hD hNpp)
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul hNp hNp))

private theorem neg_supported {n : Nat} {q : RatPoly}
    (hq : SupportedQuaternionBlocks n q) : SupportedQuaternionBlocks n (polyNeg q) := by
  intro term hterm
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hterm
  exact hq u hu

private theorem variance_supported (p : (F).V) :
    SupportedQuaternionBlocks (blocks extent-1)
      (varianceNumerator w K extent link hl p.val) := by
  have hp : SupportedQuaternionBlocks (blocks extent-1)
      (insertedNormalizer w K extent link hl p.val) :=
    insertedNormalizer_supported w K extent link hl p.val p.property
  have hpp : SupportedQuaternionBlocks (blocks extent-1)
      (insertedNormalizer w K extent link hl (polyMul p.val p.val)) :=
    insertedNormalizer_supported w K extent link hl _
      (supported_polyMul p.property p.property)
  exact supported_add
    (supported_polyMul (normalizer_supported w K extent link hl) hpp)
    (neg_supported (supported_polyMul hp hp))

/-- The original-coordinate singleton covariance with the literal finite
inverse and complementary action is exactly the prior finite energy. -/
theorem inPlaceCovariance_energy_pin (p : (F).V) (k : Nat) :
    quaternionHaar (blocks extent)
      (polyMul
        (polyMul B
          (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
            (starUpper_positive hw0 hw1 extent link) k))
        (inPlaceCovariance hw0 hw1 K extent hK link p)) ≈
      varianceEnergy hw0 hw1 K extent hK link hl p k := by
  let R := reciprocal (inPlaceNormalizer w K extent link)
    (starUpper w extent link) (starUpper_positive hw0 hw1 extent link) k
  let V := varianceNumerator w K extent link hl p.val
  let tail := polyMul V (G k)
  have htail : SupportedQuaternionBlocks (blocks extent-1) tail :=
    supported_polyMul (variance_supported hw0 hw1 K extent hK link hl p)
      (headReciprocal_supported hw0 hw1 K extent link hl k)
  have hrec : HaarCarrierEqv (blocks extent)
      (polyMul (inPlaceCovariance hw0 hw1 K extent hK link p) R)
      (headProbe s tail) := by
    change HaarCarrierEqv (blocks extent) _
      (headProbe s (polyMul V (G k)))
    rw [headProbe_mul]
    exact HaarCarrierEqv.mul
      (covariance_head_pin hw0 hw1 K extent hK link hl p)
      (inPlace_headReciprocal_carrier hw0 hw1 K extent link hl k)
  have horder : RatPolyCoeffEqv
      (polyMul (polyMul B R) (inPlaceCovariance hw0 hw1 K extent hK link p))
      (polyMul (polyMul (inPlaceCovariance hw0 hw1 K extent hK link p) R) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 2) (.var 1)) (.var 0))
      (by decide)
      (fun | 0 => B | 1 => R | _ => inPlaceCovariance hw0 hw1 K extent hK link p)
  have hpair := headProbe_independent_pair
    (show 0 < blocks extent from Nat.lt_of_le_of_lt (Nat.zero_le _)
      (List.idxOf_lt_length_of_mem hl))
    s tail B htail (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff horder)
    (Q'.eqv_trans _ _ _
      (haar_of_carrier (HaarCarrierEqv.mul hrec (HaarCarrierEqv.refl _ _)))
      hpair)

#print axioms inPlaceCovariance
#print axioms covariance_head_pin
#print axioms inPlaceCovariance_energy_pin

end YMGap.Continuum.BF4ExactSlabInPlaceVarianceEnergy
