/-
# The original head-coordinate star normalizer has the exact incident band

The selected physical link is moved to the head quaternion block and then
integrated. Reindexing and partial Haar integration preserve the constructed
incident-star certificates. The constants are the actual incident-count
`starLower` and `starUpper`; no volume-wide coarse factor is substituted.
The finite geometric reciprocal retains its supported polynomial and explicit
multiplier-error interval. No limiting inverse or path estimate is claimed.
-/

import YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
import YMGap.Continuum.BF4ExactSlabStarNormalizer
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.SU2QuaternionReplicaPairBounds

namespace YMGap.Continuum.BF4ExactSlabHeadNormalizerBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (reindex_cap_carrier)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem cap_supported (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one n s hs

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem head_cap (c : Q') :
    RatPolyCoeffEqv (partialHaarHead (cap c)) (cap c) := by
  have hone : RatPolyCoeffEqv (partialHaarHead polyOne) polyOne := by
    apply RatPolyCoeffEqv.of_canon_termwise
    decide +kernel
  exact (partialHaarHead_smul c polyOne).trans (hone.smul c)

private theorem head_neg (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyNeg p))
      (polyNeg (partialHaarHead p)) := by
  simpa only [partialHaarHeads] using partialHaarHeads_neg 1 p

private theorem lower_carrier {n tail : Nat} (hdim : n = tail + 1)
    (s : QuaternionBlockInvolution n) (p : RatPoly) (c : Q') :
    HaarCarrierEqv tail
      (partialHaarHead (reindexQuaternionPolynomial s
        (polyAdd p (polyNeg (cap c)))))
      (polyAdd (partialHaarHead (reindexQuaternionPolynomial s p))
        (polyNeg (cap c))) := by
  have hr : HaarCarrierEqv n
      (reindexQuaternionPolynomial s (polyAdd p (polyNeg (cap c))))
      (polyAdd (reindexQuaternionPolynomial s p) (polyNeg (cap c))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg (reindex_cap_carrier s c))
  have hh : HaarCarrierEqv tail
      (partialHaarHead (reindexQuaternionPolynomial s (polyAdd p (polyNeg (cap c)))))
      (partialHaarHead (polyAdd (reindexQuaternionPolynomial s p) (polyNeg (cap c)))) :=
    partialHaarHead_carrier (by simpa only [hdim] using hr)
  have hc : RatPolyCoeffEqv
      (partialHaarHead (polyAdd (reindexQuaternionPolynomial s p) (polyNeg (cap c))))
      (polyAdd (partialHaarHead (reindexQuaternionPolynomial s p))
        (polyNeg (cap c))) := by
    rw [partialHaarHead_add]
    exact (RatPolyCoeffEqv.refl _).add ((head_neg (cap c)).trans (RatPolyCoeffEqv.neg (head_cap c)))
  exact hh.trans (RatPolyCoeffEqv.haarCarrier hc)

private theorem upper_carrier {n tail : Nat} (hdim : n = tail + 1)
    (s : QuaternionBlockInvolution n) (p : RatPoly) (c : Q') :
    HaarCarrierEqv tail
      (partialHaarHead (reindexQuaternionPolynomial s
        (polyAdd (cap c) (polyNeg p))))
      (polyAdd (cap c)
        (polyNeg (partialHaarHead (reindexQuaternionPolynomial s p)))) := by
  have hr : HaarCarrierEqv n
      (reindexQuaternionPolynomial s (polyAdd (cap c) (polyNeg p)))
      (polyAdd (cap c) (polyNeg (reindexQuaternionPolynomial s p))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact HaarCarrierEqv.add (reindex_cap_carrier s c) (HaarCarrierEqv.neg (.refl _ _))
  have hh : HaarCarrierEqv tail
      (partialHaarHead (reindexQuaternionPolynomial s (polyAdd (cap c) (polyNeg p))))
      (partialHaarHead (polyAdd (cap c) (polyNeg (reindexQuaternionPolynomial s p)))) :=
    partialHaarHead_carrier (by simpa only [hdim] using hr)
  have hc : RatPolyCoeffEqv
      (partialHaarHead (polyAdd (cap c) (polyNeg (reindexQuaternionPolynomial s p))))
      (polyAdd (cap c)
        (polyNeg (partialHaarHead (reindexQuaternionPolynomial s p)))) := by
    rw [partialHaarHead_add]
    exact (head_cap c).add (head_neg (reindexQuaternionPolynomial s p))
  exact hh.trans (RatPolyCoeffEqv.haarCarrier hc)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

include hw0 hw1 in
/-- Exact incident-count lower certificate for the original head normalizer. -/
def headLowerCertificate (hK : headCutoff w ≤ K) :
    Certificate (blocks extent-1)
      (polyAdd (normalizer w K extent link hl)
        (polyNeg (cap (starLower w extent link)))) := by
  let s := linkHeadSwap extent link hl
  let p := incidentHeat w K extent link
  let c := starLower w extent link
  have hn : blocks extent = (blocks extent-1)+1 := by
    have hlt := List.idxOf_lt_length_of_mem hl
    omega
  have hp : SupportedQuaternionBlocks (blocks extent) (polyAdd p (polyNeg (cap c))) :=
    supported_add (incidentHeat_supported w K extent link)
      (neg_supported (cap_supported _ c))
  have P := reindex_certificate s hp
    (incidentHeatLowerCertificate hw0 hw1 K extent hK link)
  have Phead : Certificate (blocks extent-1)
      (partialHaarHead (reindexQuaternionPolynomial s
        (polyAdd p (polyNeg (cap c))))) :=
    partialHaarHead_certificate (blocks extent-1) (by rw [← hn]; exact P)
  exact .transport (lower_carrier hn s p c).symm Phead

include hw0 hw1 in
/-- Exact incident-count upper certificate for the same head normalizer. -/
def headUpperCertificate :
    Certificate (blocks extent-1)
      (polyAdd (cap (starUpper w extent link))
        (polyNeg (normalizer w K extent link hl))) := by
  let s := linkHeadSwap extent link hl
  let p := incidentHeat w K extent link
  let c := starUpper w extent link
  have hn : blocks extent = (blocks extent-1)+1 := by
    have hlt := List.idxOf_lt_length_of_mem hl
    omega
  have hp : SupportedQuaternionBlocks (blocks extent) (polyAdd (cap c) (polyNeg p)) :=
    supported_add (cap_supported _ c) (neg_supported (incidentHeat_supported w K extent link))
  have P := reindex_certificate s hp
    (incidentHeatUpperCertificate hw0 hw1 K extent link)
  have Phead : Certificate (blocks extent-1)
      (partialHaarHead (reindexQuaternionPolynomial s
        (polyAdd (cap c) (polyNeg p)))) :=
    partialHaarHead_certificate (blocks extent-1) (by rw [← hn]; exact P)
  exact .transport (upper_carrier hn s p c).symm Phead

/-- Finite reciprocal of the exact head-coordinate normalizer. -/
def headReciprocal (k : Nat) : RatPoly :=
  reciprocal (normalizer w K extent link hl) (starUpper w extent link)
    (starUpper_positive hw0 hw1 extent link) k

theorem headReciprocal_supported (k : Nat) :
    SupportedQuaternionBlocks (blocks extent-1)
      (headReciprocal hw0 hw1 K extent link hl k) :=
  reciprocal_supported (normalizer_supported w K extent link hl)
    (starUpper w extent link) (starUpper_positive hw0 hw1 extent link) k

/-- Exact finite reciprocal error, with the same incident-count radius used
for the two-exterior comparison. -/
def headErrorInterval (hK : headCutoff w ≤ K) (k : Nat) :
    Interval (blocks extent-1)
      (polyAdd (polyMul (normalizer w K extent link hl)
        (headReciprocal hw0 hw1 K extent link hl k)) (polyNeg polyOne))
      ((starRadius hw0 hw1 extent link)^k) :=
  multiplierErrorInterval (normalizer_supported w K extent link hl)
    (starUpper_positive hw0 hw1 extent link)
    (starLower_le_starUpper hw0 hw1 extent link)
    (headLowerCertificate hw0 hw1 K extent link hl hK)
    (headUpperCertificate hw0 hw1 K extent link hl) k

#print axioms headLowerCertificate
#print axioms headUpperCertificate
#print axioms headReciprocal
#print axioms headReciprocal_supported
#print axioms headErrorInterval

end YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
