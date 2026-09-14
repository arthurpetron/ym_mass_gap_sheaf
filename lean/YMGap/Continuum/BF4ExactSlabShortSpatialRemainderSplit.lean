/-
# Split the ORIGINAL short-core remainder by spatial odd-face defects

This is an exact finite identity for every rational nome, cutoff, margin
and cut time. The zero-spatial branch uses the previously counted original
nonzero pairs. The other branch has an actual spatial odd-face defect.
Each selected support retains its own original detached partition square.
Only zero original signed pair terms are discarded. No branch bound is
assumed, and no positivity of the complete response is asserted.
-/

import YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount

namespace YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortSupportCancellation
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion (selected_nodup)
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4CanonicalPolymerRange

local infix:50 " ≈ " => Q'.eqv

def noSpatialKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = [])

def spatialDefectKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  !(noSpatialKeep margin pair)

def corePairs (K margin time : Nat) (ids : List Nat) : List (EdgeLabelling × EdgeLabelling) :=
  ((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)

def detachedSquare (w : Q') (K margin : Nat) (ids : List Nat) : Q' :=
  partitionSquare w K (responseExtent margin) (detachedIds (responseExtent margin)
    (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) ids
    (slabPhysicalFaceEdges (responseExtent margin)))

def branchRemainder (w : Q') (K margin time : Nat) (keep : (EdgeLabelling × EdgeLabelling) → Bool) : Q' :=
  listQSum (fun ids =>
    listQSum (weightedPairTerm w K margin) ((corePairs K margin time ids).filter keep) *
      detachedSquare w K margin ids) (shortOtherCores 33 margin)

def zeroSpatialRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (zeroSpatialKeep margin)

def spatialDefectRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (spatialDefectKeep margin)

theorem zeroSpatialKeep_eq (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    zeroSpatialKeep margin pair =
      (noSpatialKeep margin pair && decide (¬pairTerm margin pair.1 pair.2 ≈ 0)) := by
  simp only [zeroSpatialKeep, noSpatialKeep, Bool.decide_and, Bool.and_assoc]

theorem spatialDefectKeep_nonempty {margin : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (h : spatialDefectKeep margin pair = true) :
    ¬(spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = []) := by
  have hf : noSpatialKeep margin pair = false := by simpa only [spatialDefectKeep, Bool.not_eq_true'] using h
  exact of_decide_eq_false hf

theorem weightedPairTerm_zero (w : Q') (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (h : pairTerm margin pair.1 pair.2 ≈ 0) : weightedPairTerm w K margin pair ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.mul_zero_eqv _)

private theorem nonzero_filter_eq (margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    (xs.filter (noSpatialKeep margin)).filter (fun pair => decide (¬pairTerm margin pair.1 pair.2 ≈ 0)) =
      xs.filter (zeroSpatialKeep margin) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro pair _
  rw [zeroSpatialKeep_eq]
  exact Bool.and_comm _ _

theorem noSpatial_sum_eq (w : Q') (K margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) (xs.filter (noSpatialKeep margin)) ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (zeroSpatialKeep margin)) := by
  have h := sum_filter_zero (weightedPairTerm w K margin)
    (fun pair => decide (¬pairTerm margin pair.1 pair.2 ≈ 0)) (xs.filter (noSpatialKeep margin)) (by
      intro pair _ hf
      by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
      · exact weightedPairTerm_zero w K margin pair hz
      · exact False.elim ((of_decide_eq_false hf) hz))
  rw [nonzero_filter_eq] at h
  exact h

theorem original_pair_sum_split (w : Q') (K margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) xs ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (zeroSpatialKeep margin)) +
      listQSum (weightedPairTerm w K margin) (xs.filter (spatialDefectKeep margin)) :=
  Q'.eqv_trans _ _ _ (listQSum_perm _ (List.filter_append_perm (noSpatialKeep margin) xs).symm)
    (Q'.eqv_trans _ _ _ (sum_append _ _ _)
      (Q'.add_eqv_congr_right _ _ _ (noSpatial_sum_eq w K margin xs)))

/-- Exact split of the actual short remainder, with no change of action or weights. -/
theorem original_short_remainder_split (w : Q') (K margin time : Nat) :
    shortOtherRemainder w K 33 margin ≈
      zeroSpatialRemainder w K margin time + spatialDefectRemainder w K margin time := by
  apply Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ (shortOtherCores 33 margin) (by
    intro ids hs
    have hsel := connecting_selected (shortOtherCores_connecting hs)
    have hc := coefficient_leaf_filtered w K margin time ids
      (selected_nodup (CayleyParentInj.range_nodup _) hsel) (fun id hi => selected_mem hsel id hi)
    have hp := Q'.eqv_trans _ _ _ hc (original_pair_sum_split w K margin (corePairs K margin time ids))
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids) hp)
      (poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) (by decide)
        (fun i => if i=0 then listQSum (weightedPairTerm w K margin)
            ((corePairs K margin time ids).filter (zeroSpatialKeep margin))
          else if i=1 then listQSum (weightedPairTerm w K margin)
            ((corePairs K margin time ids).filter (spatialDefectKeep margin))
          else detachedSquare w K margin ids))))
  exact listQSum_add _ _ _

end YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit

#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.noSpatialKeep
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.spatialDefectKeep
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.corePairs
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.detachedSquare
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.branchRemainder
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.zeroSpatialRemainder
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.spatialDefectRemainder
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.zeroSpatialKeep_eq
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.spatialDefectKeep_nonempty
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.weightedPairTerm_zero
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.noSpatial_sum_eq
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.original_pair_sum_split
#print axioms YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit.original_short_remainder_split
