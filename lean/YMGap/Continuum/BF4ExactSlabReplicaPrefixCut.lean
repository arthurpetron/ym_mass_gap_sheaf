/-
# Original physical prefix cuts pay the actual crossing-face count

The coordinate-prefix path is recoded to a literal list of original
physical links. Its partial replica exchange is exactly the existing cut
swap. The reverse cut comparison then bounds each path-increment square
by a one-link replacement square under the ORIGINAL full pair action.
This is not a time-ordered area estimate or a conditional-energy bound.
-/

import YMGap.Continuum.BF4ExactSlabReplicaCutReverse
import YMGap.Continuum.SU2QuaternionReplicaPathIncrement

namespace YMGap.Continuum.BF4ExactSlabReplicaPrefixCut

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReplicaCutLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaCutReverse
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The original physical links represented by the first j block indices. -/
def prefixLinks (extent j : Nat) : List Z4Link :=
  (List.range j).map (correctedSlabLinkAt extent)

theorem mem_selectedBlocks_prefix (extent j : Nat) (hj : j ≤ blocks extent) (k : Nat) :
    k ∈ selectedBlocks extent (prefixLinks extent j) ↔ k < j := by
  rw [mem_selectedBlocks]
  constructor
  · intro hk
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hk.2
    have hi' := List.mem_range.mp hi
    have hieq : i = k := correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr (Nat.lt_of_lt_of_le hi' hj))
      (List.mem_range.mpr hk.1) he
    exact hieq ▸ hi'
  · intro hk
    exact ⟨Nat.lt_of_lt_of_le hk hj,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩

private theorem involution_ext {n : Nat} {s t : QuaternionBlockInvolution n}
    (h : ∀ k, s.map k = t.map k) : s = t := by
  have hm := funext h
  cases s
  cases t
  cases hm
  rfl

/-- No surrogate physical ordering: the two actual swaps have the same map. -/
theorem cutSwap_prefix (extent j : Nat) (hj : j ≤ blocks extent) :
    cutSwap extent (prefixLinks extent j) = swap (blocks extent) (List.range j) := by
  apply involution_ext
  intro k
  simp only [cutSwap, swap, mem_selectedBlocks_prefix extent j hj, List.mem_range]

private theorem single_supported (n j : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) (singleBlockDifference n j f) :=
  difference_supported (reindex_supported _ _)
    (fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega)))

/-- Each path term pays only its actual crossing faces, in the upper-bound
direction needed by the variance telescope. The replacement still uses
the other FULL replica's coordinate, not a conditional refresh law. -/
theorem original_prefix_increment_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (j : Nat) (hj : j < blocks extent)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    (headFloor w * headFloor w)^crossingCount extent (prefixLinks extent j) *
      quaternionHaar (blocks extent + blocks extent)
        (polyMul (originalPair w K extent)
          (polyMul (prefixIncrement (blocks extent) j f)
            (prefixIncrement (blocks extent) j f))) ≤
    (prefixCap w * prefixCap w)^crossingCount extent (prefixLinks extent j) *
      quaternionHaar (blocks extent + blocks extent)
        (polyMul (originalPair w K extent)
          (polyMul (singleBlockDifference (blocks extent) j f)
            (singleBlockDifference (blocks extent) j f))) := by
  have hp := weighted_prefix_increment_change (blocks extent) j f
    (originalPair w K extent) hj hf
    (pair_supported _ (heatProduct_supported w K extent _))
  rw [← cutSwap_prefix extent j (Nat.le_of_lt hj)] at hp
  have hs := single_supported (blocks extent) j f hf
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hp))
    (weighted_cut_comparison_reverse hw0 hw1 K extent hK (prefixLinks extent j)
      (supported_polyMul hs hs) (.square _ hs))

#print axioms prefixLinks
#print axioms mem_selectedBlocks_prefix
#print axioms cutSwap_prefix
#print axioms original_prefix_increment_bound

end YMGap.Continuum.BF4ExactSlabReplicaPrefixCut
