/-
# Corrected-slab partition as an exact ambient conditional ensemble

The corrected reflection slab embeds into the ambient corner box by spin-zero
extension.  The preceding image theorem identifies the image with the bounded
ambient labellings whose excited plaquettes all lie in the slab.  Here we sum
the complete arbitrary-cutoff physical weight over that literal image.

This is an exact finite identity.  It does not say that the omitted ambient
configurations have zero weight; bounding their normalized contribution is the
remaining boundary estimate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two finite ambient conditional sums -/

/-- Ambient-box partition restricted to configurations whose excited support
is contained in the corrected slab. -/
def ambientSlabSupportedPhysicalPartition
    (w : Q') (K extent : Nat) : Q' :=
  listQSum
    (parametricKPhysicalTerm w K (extent + 1))
    (ambientSlabSupportedLabellings K extent)

/-- The same conditional ensemble with an arbitrary observable read back on
the corrected slab. -/
def ambientSlabSupportedWeightedSum
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun target =>
      observable (ambientToSlabPhysical extent target) *
        parametricKPhysicalTerm w K (extent + 1) target)
    (ambientSlabSupportedLabellings K extent)

/-- Corrected-slab weighted sum before zero extension. -/
def slabWeightedPhysicalSum
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun source =>
      observable source *
        slabParametricKPhysicalTerm w K extent source)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))

/-! ## 2. Restriction is a left inverse on bounded slab configurations -/

theorem ambientToSlabPhysical_slabToAmbientPhysical
    {K extent : Nat} {source : EdgeLabelling}
    (hsource : source ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    ambientToSlabPhysical extent
        (slabToAmbientPhysical extent source) = source := by
  apply slabToAmbientPhysical_injective_on
    (ambientToSlabPhysical_mem_bounded
      (slabToAmbientPhysical_mem_bounded hsource)) hsource
  exact slabToAmbientPhysical_ambientToSlab
    (slabToAmbientPhysical_mem_bounded hsource)
    (slabToAmbientPhysical_supported extent source)

/-! ## 3. Exact partition and observable identities -/

/-- The full corrected-slab physical partition is exactly the supported
ambient conditional partition. -/
theorem slabParametricKPhysicalPartition_eq_ambientSupported
    (w : Q') (K extent : Nat) :
    slabParametricKPhysicalPartition w K extent ≈
      ambientSlabSupportedPhysicalPartition w K extent := by
  unfold slabParametricKPhysicalPartition
    ambientSlabSupportedPhysicalPartition
  refine Q'.eqv_trans _
    (listQSum (parametricKPhysicalTerm w K (extent + 1))
      ((boundedEdgeLabellings K (slabPhysicalFaceEdges extent)).map
        (slabToAmbientPhysical extent))) _ ?_ ?_
  · exact YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights.listQSum_map_eqv
      (slabParametricKPhysicalTerm w K extent)
      (parametricKPhysicalTerm w K (extent + 1))
      (slabToAmbientPhysical extent)
      (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))
      (fun source hsource =>
        slabParametricKPhysicalTerm_ambient w hsource)
  · exact listQSum_perm _
      (embeddedSlabLabellings_perm_supported K extent)

/-- Every corrected-slab weighted sum is exactly the supported ambient sum
with the observable pulled back by explicit restriction. -/
theorem slabWeightedPhysicalSum_eq_ambientSupported
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') :
    slabWeightedPhysicalSum w K extent observable ≈
      ambientSlabSupportedWeightedSum w K extent observable := by
  unfold slabWeightedPhysicalSum ambientSlabSupportedWeightedSum
  let sourceWeight : EdgeLabelling -> Q' := fun source =>
    observable source * slabParametricKPhysicalTerm w K extent source
  let targetWeight : EdgeLabelling -> Q' := fun target =>
    observable (ambientToSlabPhysical extent target) *
      parametricKPhysicalTerm w K (extent + 1) target
  refine Q'.eqv_trans _
    (listQSum targetWeight
      ((boundedEdgeLabellings K (slabPhysicalFaceEdges extent)).map
        (slabToAmbientPhysical extent))) _ ?_ ?_
  · apply YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights.listQSum_map_eqv
      sourceWeight targetWeight (slabToAmbientPhysical extent)
    intro source hsource
    unfold sourceWeight targetWeight
    rw [ambientToSlabPhysical_slabToAmbientPhysical hsource]
    exact Q'.mul_eqv_congr_left _ _ _
      (slabParametricKPhysicalTerm_ambient w hsource)
  · exact listQSum_perm targetWeight
      (embeddedSlabLabellings_perm_supported K extent)

/-! ## 4. The finite OS numerator in the ambient conditional ensemble -/

def centralAmbientSlabSupportedReflectionQuadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  ambientSlabSupportedWeightedSum w K (centralExtent half)
    (fun physical =>
      coefficient (centralLowerRestriction half physical) *
        coefficient (centralReflectedUpperRestriction half physical))

theorem centralFullPhysicalReflectionQuadratic_eq_ambientSupported
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    centralFullPhysicalReflectionQuadratic w K half coefficient ≈
      centralAmbientSlabSupportedReflectionQuadratic
        w K half coefficient := by
  unfold centralFullPhysicalReflectionQuadratic
    centralAmbientSlabSupportedReflectionQuadratic
  exact slabWeightedPhysicalSum_eq_ambientSupported
    w K (centralExtent half)
      (fun physical =>
        coefficient (centralLowerRestriction half physical) *
          coefficient
            (centralReflectedUpperRestriction half physical))

#print axioms ambientToSlabPhysical_slabToAmbientPhysical
#print axioms slabParametricKPhysicalPartition_eq_ambientSupported
#print axioms slabWeightedPhysicalSum_eq_ambientSupported
#print axioms centralFullPhysicalReflectionQuadratic_eq_ambientSupported

end YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
