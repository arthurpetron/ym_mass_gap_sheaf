/-
# Source bridge from the fixed-width vector jet to the full slab

The width-only plaquette vector jet used by the selected fixed-width ORIGINAL
window is embedded at an admissible time into the full corrected-slab carrier.
The embedded weighted source is exactly the physical full-slab vector-jet
source modulo harmless zero padding.  After multiplying by the common
`2^66` scale, it is the identity-scaled pure source used by the all-chart
reassembly.

This identifies the observable and its normalization only.  It does not
identify the selected-chain action with the full-slab action or compare their
normalized expectations.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
import YMGap.Continuum.QuaternionHaarGammaFiniteSum

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_coeff_congr finitePolySum_smul)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The literal unscaled physical full-slab vector-jet source at one
chronological placement. -/
def globalCayleyVectorJetBulkPhysicalSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalPlaquetteVectorJet extent (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

private theorem vectorSquares_padded
    {blocks : Nat} {left right : PolyQuaternion}
    (hquaternion : QuaternionPrefixPolyQuaternionEqv blocks left right) :
    PaddedPolynomialCoeffEqv blocks
      (polyAdd (polyMul left.iPart left.iPart)
        (polyAdd (polyMul left.jPart left.jPart)
          (polyMul left.kPart left.kPart)))
      (polyAdd (polyMul right.iPart right.iPart)
        (polyAdd (polyMul right.jPart right.jPart)
          (polyMul right.kPart right.kPart))) := by
  have hiPart := PaddedPolynomialCoeffEqv.of_prefix hquaternion.iPart
  have hjPart := PaddedPolynomialCoeffEqv.of_prefix hquaternion.jPart
  have hkPart := PaddedPolynomialCoeffEqv.of_prefix hquaternion.kPart
  exact (hiPart.mul hiPart).add
    ((hjPart.mul hjPart).add (hkPart.mul hkPart))

private theorem polynomial_vectorSquares_padded
    {source target : Nat} (E : BlockEmbedding source target)
    {left right : PolyQuaternion}
    (hquaternion : QuaternionPrefixPolyQuaternionEqv target
      (E.quaternion left) right) :
    PaddedPolynomialCoeffEqv target
      (E.polynomial
        (polyAdd (polyMul left.iPart left.iPart)
          (polyAdd (polyMul left.jPart left.jPart)
            (polyMul left.kPart left.kPart))))
      (polyAdd (polyMul right.iPart right.iPart)
        (polyAdd (polyMul right.jPart right.jPart)
          (polyMul right.kPart right.kPart))) := by
  rw [E.polynomial_add, E.polynomial_mul,
    E.polynomial_add, E.polynomial_mul, E.polynomial_mul]
  exact vectorSquares_padded hquaternion

/-- Embedding one width-only plaquette vector norm gives the corresponding
time-shifted corrected-slab vector norm, modulo harmless zero padding. -/
theorem plaquetteVectorQuadraticJet_embedding_padded
    {width time extent : Nat} (hwidth : width ≤ extent)
    (htime : time ≤ extent) {face : Z4Plaq}
    (hface : face ∈ spatialFaces width) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding hwidth htime).polynomial
        (plaquetteVectorQuadraticJet width face))
      (globalPlaquetteVectorJet extent
        (timeShiftPlaquette time face)) := by
  simpa only [plaquetteVectorQuadraticJet, globalPlaquetteVectorJet] using
    (polynomial_vectorSquares_padded (embedding hwidth htime)
      (plaquette_pin hwidth htime hface))

private theorem imageSum
    {Index : Type} {source target : Nat}
    (E : BlockEmbedding source target) (left right : Index → RatPoly) :
    ∀ items : List Index,
      (∀ index, index ∈ items → PaddedPolynomialCoeffEqv target
        (E.polynomial (left index)) (right index)) →
      PaddedPolynomialCoeffEqv target
        (E.polynomial (finitePolySum left items))
        (finitePolySum right items)
  | [], _ => .refl _ _
  | index :: items, h => by
      change PaddedPolynomialCoeffEqv target
        (E.polynomial (polyAdd _ _)) (polyAdd _ _)
      rw [E.polynomial_add]
      exact (h index List.mem_cons_self).add
        (imageSum E left right items
          (fun next hnext => h next (List.mem_cons_of_mem index hnext)))

/-- The embedded width-only weighted vector jet is the literal unscaled
time-shifted full-slab physical vector-jet source. -/
theorem originalBulkVectorQuadraticJet_embedding
    {s : Nat} (hs : 0 < s) {extent time : Nat}
    (hwidth : s * s ≤ extent) (htime : time ≤ extent) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding hwidth htime).polynomial
        (originalBulkVectorQuadraticJet s hs))
      (globalCayleyVectorJetBulkPhysicalSource s hs extent time) := by
  let E := embedding hwidth htime
  let source := fun face => polySmul (bulkSourceCoefficient s hs face)
    (plaquetteVectorQuadraticJet (s * s) face)
  let target := fun face => polySmul (bulkSourceCoefficient s hs face)
    (globalPlaquetteVectorJet extent (timeShiftPlaquette time face))
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      PaddedPolynomialCoeffEqv (B extent)
        (E.polynomial (source face)) (target face) := by
    intro face hface
    change PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial
        (polySmul (bulkSourceCoefficient s hs face)
          (plaquetteVectorQuadraticJet (s * s) face)))
      (polySmul (bulkSourceCoefficient s hs face)
        (globalPlaquetteVectorJet extent (timeShiftPlaquette time face)))
    rw [E.polynomial_smul]
    exact (plaquetteVectorQuadraticJet_embedding_padded hwidth htime
      (bulkSourceFace_mem_spatialFaces_square hface)).smul
        (bulkSourceCoefficient s hs face)
  change PaddedPolynomialCoeffEqv (B extent)
    (E.polynomial (finitePolySum source (bulkSourceFaces s)))
    (finitePolySum target (bulkSourceFaces s))
  exact imageSum E source target (bulkSourceFaces s) hpoint

private theorem one_mul_coeff (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyOne polynomial) polynomial := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.const 1) (.var 0)) (.var 0) (by decide)
    (fun _ => polynomial)

private theorem identityScaledPhysicalSource_coeff
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    RatPolyCoeffEqv
      (polySmul globalCayleyVectorJetNorthWeightScale
        (globalCayleyVectorJetBulkPhysicalSource s hs extent time))
      (globalCayleyVectorJetBulkIdentityScaledPureSource
        s hs extent time) := by
  let physical := fun face => polySmul (bulkSourceCoefficient s hs face)
    (globalPlaquetteVectorJet extent (timeShiftPlaquette time face))
  let pure := fun face => polySmul (bulkSourceCoefficient s hs face)
    (globalCayleyVectorJetIdentityScaledPurePolynomial extent
      (timeShiftPlaquette time face))
  have hpoint : ∀ face, RatPolyCoeffEqv
      (polySmul globalCayleyVectorJetNorthWeightScale (physical face))
      (pure face) := by
    intro face
    let coefficient := bulkSourceCoefficient s hs face
    let vectorJet := globalPlaquetteVectorJet extent
      (timeShiftPlaquette time face)
    let scale := globalCayleyVectorJetNorthWeightScale
    have hpure : RatPolyCoeffEqv
        (globalCayleyVectorJetIdentityScaledPurePolynomial extent
          (timeShiftPlaquette time face))
        (polySmul scale vectorJet) := by
      exact (RatPolyCoeffEqv.polyMul_smul_left scale polyOne vectorJet).trans
        ((one_mul_coeff vectorJet).smul scale)
    have hleft : RatPolyCoeffEqv
        (polySmul scale (polySmul coefficient vectorJet))
        (polySmul (scale * coefficient) vectorJet) :=
      RatPolyCoeffEqv.smul_assoc scale coefficient vectorJet
    have hright : RatPolyCoeffEqv
        (polySmul coefficient (polySmul scale vectorJet))
        (polySmul (coefficient * scale) vectorJet) :=
      RatPolyCoeffEqv.smul_assoc coefficient scale vectorJet
    change RatPolyCoeffEqv
      (polySmul scale (polySmul coefficient vectorJet))
      (polySmul coefficient
        (globalCayleyVectorJetIdentityScaledPurePolynomial extent
          (timeShiftPlaquette time face)))
    exact hleft.trans
      ((RatPolyCoeffEqv.smul_coefficient
        (Q'.mul_comm_eqv scale coefficient) vectorJet).trans
        (hright.symm.trans (hpure.symm.smul coefficient)))
  have hsum := finitePolySum_coeff_congr
    (fun face => polySmul globalCayleyVectorJetNorthWeightScale
      (physical face)) pure hpoint (bulkSourceFaces s)
  have hdistribute := finitePolySum_smul
    globalCayleyVectorJetNorthWeightScale physical (bulkSourceFaces s)
  change RatPolyCoeffEqv
    (polySmul globalCayleyVectorJetNorthWeightScale
      (finitePolySum physical (bulkSourceFaces s)))
    (finitePolySum pure (bulkSourceFaces s))
  exact hdistribute.symm.trans hsum

/-- At the exact common `2^66` scale, the embedded width-only vector-jet
source is the full-slab identity-scaled pure source used by the all-chart
reassembly.  This remains a source identity, not an equality of actions. -/
theorem originalBulkVectorQuadraticJet_identityScaled_embedding
    {s : Nat} (hs : 0 < s) {extent time : Nat}
    (hwidth : s * s ≤ extent) (htime : time ≤ extent) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding hwidth htime).polynomial
        (polySmul globalCayleyVectorJetNorthWeightScale
          (originalBulkVectorQuadraticJet s hs)))
      (globalCayleyVectorJetBulkIdentityScaledPureSource
        s hs extent time) := by
  have hsource := originalBulkVectorQuadraticJet_embedding
    hs hwidth htime
  have hscaled := hsource.smul globalCayleyVectorJetNorthWeightScale
  rw [← (embedding hwidth htime).polynomial_smul] at hscaled
  exact hscaled.trans (PaddedPolynomialCoeffEqv.of_coeff
    (identityScaledPhysicalSource_coeff s hs extent time))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge.plaquetteVectorQuadraticJet_embedding_padded
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge.originalBulkVectorQuadraticJet_embedding
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSourceBridge.originalBulkVectorQuadraticJet_identityScaled_embedding
