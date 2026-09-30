/-
# Arbitrary physical block selections retain the original replica cut

An in-range list of original block indices is recoded to its actual physical
links. The resulting cut involution equals the literal block swap, without
requiring the raw coordinate order or the eight-color schedule.
The reverse cut comparison then bounds each next-coordinate path square
by its original full-replica replacement square, charging actual crossing faces.
-/

import YMGap.Continuum.BF4ExactSlabReplicaPrefixCut
import YMGap.Continuum.SU2QuaternionOrderedReplicaPath

namespace YMGap.Continuum.BF4ExactSlabOrderedPathCut

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReplicaCutLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaCutReverse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.SU2QuaternionOrderedReplicaPath
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- An actual physical link for each selected original coordinate. -/
def selectedLinks (extent : Nat) (A : List Nat) : List Z4Link :=
  A.map (correctedSlabLinkAt extent)

theorem mem_selectedBlocks_selectedLinks (extent : Nat) (A : List Nat)
    (hA : ∀ i, i ∈ A → i < blocks extent) (k : Nat) :
    k ∈ selectedBlocks extent (selectedLinks extent A) ↔ k ∈ A := by
  rw [mem_selectedBlocks]
  constructor
  · intro hk
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hk.2
    have hieq : i = k := correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr (hA i hi)) (List.mem_range.mpr hk.1) he
    exact hieq ▸ hi
  · intro hk
    exact ⟨hA k hk, List.mem_map.mpr ⟨k, hk, rfl⟩⟩

private theorem involution_ext {n : Nat} {s t : QuaternionBlockInvolution n}
    (h : ∀ k, s.map k = t.map k) : s = t := by
  have hm := funext h
  cases s
  cases t
  cases hm
  rfl

/-- Selection order does not change the physical meaning of a replica cut. -/
theorem cutSwap_selectedLinks (extent : Nat) (A : List Nat)
    (hA : ∀ i, i ∈ A → i < blocks extent) :
    cutSwap extent (selectedLinks extent A) = swap (blocks extent) A := by
  apply involution_ext
  intro k
  simp only [cutSwap, swap, mem_selectedBlocks_selectedLinks extent A hA]

/-- The actual original-pair cost of the next replacement after selection A. -/
def incrementIntegral (w : Q') (K extent : Nat) (A : List Nat) (j : Nat)
    (f : RatPoly) : Q' :=
  quaternionHaar (blocks extent + blocks extent)
    (polyMul (originalPair w K extent)
      (polyMul (increment (blocks extent) A j f) (increment (blocks extent) A j f)))

/-- The reverse original-action comparison applies to any in-range selection,
not just a coordinate prefix. Only actual crossing faces are charged. -/
theorem original_selected_increment_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (A : List Nat)
    (hA : ∀ i, i ∈ A → i < blocks extent) (j : Nat) (hnot : j ∉ A)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    (headFloor w * headFloor w)^crossingCount extent (selectedLinks extent A) *
      incrementIntegral w K extent A j f ≤
    (prefixCap w * prefixCap w)^crossingCount extent (selectedLinks extent A) *
      quaternionHaar (blocks extent + blocks extent)
        (polyMul (originalPair w K extent)
          (polyMul (singleBlockDifference (blocks extent) j f)
            (singleBlockDifference (blocks extent) j f))) := by
  have hp := weighted_increment_transport (blocks extent) A j hnot f
    (originalPair w K extent) hf
    (pair_supported _ (heatProduct_supported w K extent _))
  rw [← cutSwap_selectedLinks extent A hA] at hp
  have hs := singletonDifference_supported (blocks extent) j f hf
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hp))
    (weighted_cut_comparison_reverse hw0 hw1 K extent hK (selectedLinks extent A)
      (supported_polyMul hs hs) (.square _ hs))

#print axioms selectedLinks
#print axioms mem_selectedBlocks_selectedLinks
#print axioms cutSwap_selectedLinks
#print axioms original_selected_increment_bound

end YMGap.Continuum.BF4ExactSlabOrderedPathCut
