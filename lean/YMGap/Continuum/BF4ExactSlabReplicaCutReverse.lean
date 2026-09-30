/-
# Reverse orientation of the original two-copy cut comparison

The partial replica exchange is an involution. Reindexing a supported
nonnegative insertion therefore turns the checked forward cut comparison
into the reverse orientation with the same crossing-face count. No
time-layer order, area estimate, or coercivity follows here.
-/

import YMGap.Continuum.BF4ExactSlabReplicaCutComparison

namespace YMGap.Continuum.BF4ExactSlabReplicaCutReverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

include hw0 hw1 hK

/-- The reverse inequality is the original one after the same supported
insertion and both action factors are carried through the literal involution. -/
theorem weighted_cut_comparison_reverse (selected : List Z4Link) {r : RatPoly}
    (hr : SupportedQuaternionBlocks (blocks extent + blocks extent) r)
    (R : Certificate (blocks extent + blocks extent) r) :
    (headFloor w * headFloor w)^crossingCount extent selected *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (swappedPair w K extent selected) r) ≤
      (prefixCap w * prefixCap w)^crossingCount extent selected *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (originalPair w K extent) r) := by
  let n := blocks extent + blocks extent
  let s := cutSwap extent selected
  let O := originalPair w K extent
  let S := swappedPair w K extent selected
  have hO : SupportedQuaternionBlocks n O :=
    pair_supported _ (heatProduct_supported w K extent _)
  have hS : SupportedQuaternionBlocks n S := reindex_supported s O
  have hA : Q'.eqv (quaternionHaar n (polyMul O (reindexQuaternionPolynomial s r)))
      (quaternionHaar n (polyMul S r)) :=
    reindex_pair s O r hO hr
  have hB : Q'.eqv (quaternionHaar n (polyMul S (reindexQuaternionPolynomial s r)))
      (quaternionHaar n (polyMul O r)) := by
    apply Q'.eqv_trans _ _ _ (reindex_pair s S r hS hr)
    exact quaternionHaar_prefixPolynomialEqv n
      ((reindex_twice_prefix s O).mul (QuaternionPrefixPolynomialEqv.refl n r))
      (supported_polyMul (reindex_supported s S) hr) (supported_polyMul hO hr)
  have hforward := weighted_cut_comparison hw0 hw1 K extent hK selected
    (reindex_certificate s hr R)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hA)))
    (Q'.le_trans' _ _ _ hforward
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hB)))

#print axioms weighted_cut_comparison_reverse

end YMGap.Continuum.BF4ExactSlabReplicaCutReverse
