/-
# Literal physical-link angular differentiation in the original Haar carrier

The head-swap definition of the link derivative is compared with angular
differentiation at the literal physical block index. The comparison is under
every Haar insertion; padded polynomial representatives need not coincide
coefficientwise.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation
import YMGap.Continuum.QuaternionHaarBlockAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarBlockAngularCarrier
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation

/-- The pulled-back derivative remains supported in the unchanged slab
polynomial carrier. -/
theorem linkDerivative_supported (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {i j : Nat} (_hi : i < 4) (_hj : j < 4) {p : RatPoly}
    (_hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (linkDerivative extent link hl i j p) := by
  dsimp only [linkDerivative]
  exact reindex_supported (linkHeadSwap extent link hl) _

/-- A physical-link derivative is the raw angular derivative at the
physical link's block, after passing to the padded-safe Haar carrier. -/
theorem linkDerivative_carrier (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (linkDerivative extent link hl i j p)
      (blockAngularDerivative ((boundaryCompleteSlabLinks extent).idxOf link) i j p) := by
  let n := (boundaryCompleteSlabLinks extent).length
  let slot := (boundaryCompleteSlabLinks extent).idxOf link
  let s := linkHeadSwap extent link hl
  have hslot : slot < n := List.idxOf_lt_length_of_mem hl
  have hzero : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hslot
  have hmap : s.map 0 = slot := by
    exact headSwapBlockInvolution_map_zero n slot hslot
  have hraw : SupportedQuaternionBlocks n (blockAngularDerivative slot i j p) :=
    blockAngularDerivative_supported hslot hi hj hp
  have hhead : SupportedQuaternionBlocks n
      (blockAngularDerivative 0 i j (reindexQuaternionPolynomial s p)) :=
    blockAngularDerivative_supported hzero hi hj (reindex_supported s p)
  have hfirst : HaarCarrierEqv n
      (reindexQuaternionPolynomial s (blockAngularDerivative slot i j p))
      (blockAngularDerivative 0 i j (reindexQuaternionPolynomial s p)) := by
    simpa only [hmap] using
      (reindex_blockAngularDerivative_carrier s hzero hi hj p hp)
  have hsecond := reindex_carrier s (reindex_supported s _ ) hhead hfirst
  have htwice : HaarCarrierEqv n
      (reindexQuaternionPolynomial s
        (reindexQuaternionPolynomial s (blockAngularDerivative slot i j p)))
      (blockAngularDerivative slot i j p) :=
    carrierOfPrefix (reindex_supported s (reindexQuaternionPolynomial s _))
      hraw (reindex_twice_prefix s _)
  have hresult := (htwice.symm.trans hsecond).symm
  simpa only [linkDerivative, blockAngularDerivative, Nat.mul_zero, Nat.zero_add,
    n, slot, s] using hresult

/-- The two successive pulled-back derivatives remain supported. -/
theorem mixedDerivative_supported (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    {i j k l : Nat} (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    {p : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (mixedDerivative extent first second hfirst hsecond i j k l p) := by
  exact linkDerivative_supported extent second hsecond hk hl
    (linkDerivative_supported extent first hfirst hi hj hp)

/-- Two literal physical-link derivatives agree, under arbitrary original
Haar insertions, with the corresponding raw two-block derivative. -/
theorem mixedDerivative_carrier (extent : Nat) (first second : Z4Link)
    (hfirst : first ∈ boundaryCompleteSlabLinks extent)
    (hsecond : second ∈ boundaryCompleteSlabLinks extent)
    {i j k l : Nat} (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    {p : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (mixedDerivative extent first second hfirst hsecond i j k l p)
      (blockAngularDerivative ((boundaryCompleteSlabLinks extent).idxOf second) k l
        (blockAngularDerivative ((boundaryCompleteSlabLinks extent).idxOf first) i j p)) := by
  have hfirstSupported := linkDerivative_supported extent first hfirst hi hj hp
  have hfirstRaw := blockAngularDerivative_supported
    (List.idxOf_lt_length_of_mem hfirst) hi hj hp
  have hsecondCarrier := linkDerivative_carrier extent second hsecond hk hl hfirstSupported
  have hcongr := blockAngularDerivative_carrier
    (List.idxOf_lt_length_of_mem hsecond) hk hl
    hfirstSupported hfirstRaw (linkDerivative_carrier extent first hfirst hi hj hp)
  exact hsecondCarrier.trans hcongr

end YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier

#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier.linkDerivative_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier.linkDerivative_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier.mixedDerivative_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier.mixedDerivative_carrier
