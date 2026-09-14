/-
# Extract the exact full-heat tube core from the original resummed numerator

All proper tube subselections have fewer than twelve faces, so their
original coefficients vanish. The full tube coefficient is therefore
exactly w^36, including every cutoff spin. Nonzero coefficient and the
existing rooted factorization force the computed tube core to be fixed.
It is an actual member of the resummed list, not an added summand.

The full original numerator splits as w^36 times the detached original
partition square plus the signed sum of all OTHER original cores. The
remaining sum is explicit and unbounded here; no response floor follows.
-/

import YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue
import YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget
import YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected

namespace YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue
open YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep
open YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected
open YMGap.Continuum.BF4ExactSlabShortSupportCancellation
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabCancellationTailBudget
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem filter_absent {A : Type} [DecidableEq A] (a : A) : ∀ xs : List A,
    a ∉ xs → xs.filter (fun x => decide (x=a)) = []
  | [], _ => rfl
  | x::xs, ha => by
    have hx : x ≠ a := fun h => ha (List.mem_cons.mpr (Or.inl h.symm))
    simpa only [List.filter_cons,decide_eq_false hx,Bool.false_eq_true,↓reduceIte] using
      filter_absent a xs (fun h => ha (List.mem_cons_of_mem x h))

private theorem filter_target {A : Type} [DecidableEq A] (a : A) : ∀ xs : List A,
    xs.Nodup → a ∈ xs → xs.filter (fun x => decide (x=a)) = [a]
  | [], _, hm => False.elim (List.not_mem_nil hm)
  | x::xs, hn, hm => by
    by_cases he : x = a
    · subst x
      have ht := filter_absent a xs (List.nodup_cons.mp hn).1
      simp only [List.filter_cons,decide_true,↓reduceIte,ht]
    · have ha : a ∈ xs := (List.mem_cons.mp hm).resolve_left (fun h => he h.symm)
      simpa only [List.filter_cons,decide_eq_false he,Bool.false_eq_true,↓reduceIte] using
        filter_target a xs (List.nodup_cons.mp hn).2 ha

private theorem sum_only_target {A : Type} [DecidableEq A] (f : A → Q') (a : A) (xs : List A)
    (hn : xs.Nodup) (ha : a ∈ xs) (hz : ∀ x, x ∈ xs → x ≠ a → f x ≈ 0) :
    listQSum f xs ≈ f a := by
  have h := sum_filter_zero f (fun x => decide (x=a)) xs
    (fun x hx he => hz x hx (of_decide_eq_false he))
  rw [filter_target a xs hn ha] at h
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem sum_extract_target {A : Type} [DecidableEq A] (f : A → Q') (a : A) (xs : List A)
    (hn : xs.Nodup) (ha : a ∈ xs) :
    listQSum f xs ≈ f a + listQSum f (xs.filter (fun x => !(decide (x=a)))) := by
  have h := listQSum_perm f (List.filter_append_perm (fun x => decide (x=a)) xs).symm
  refine Q'.eqv_trans _ _ _ h ?_
  rw [filter_target a xs hn ha]
  exact Q'.eqv_trans _ _ _ (sum_append f [a] _)
    (Q'.add_eqv_congr' (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.eqv_refl _))

theorem proper_tube_selection_short {margin : Nat} {ids : List Nat}
    (hi : ids ∈ selections (tubeIds margin)) (hne : ids ≠ tubeIds margin) : ids.length < 12 := by
  have hs := selected_sublist hi
  have hl := tubeIds_length margin
  by_cases hb : 12 ≤ ids.length
  · exact False.elim (hne (hs.eq_of_length_le (by omega)))
  · omega

theorem tube_coefficient_is_numerator (w : Q') (K margin : Nat) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) (tubeIds margin) ≈
    connectedNumerator w K (responseExtent margin) (tubeIds margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) := by
  have hsum := sum_only_target (connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)))
    (tubeIds margin) (selections (tubeIds margin)) (selections_nodup _ (tubeIds_nodup margin))
    (sublist_selected (List.Sublist.refl _)) (fun ids hi hne =>
      original_short_coefficient_zero w K margin ids
        (sublist_selected ((selected_sublist hi).trans (selected_sublist (tubeIds_selected margin))))
        (proper_tube_selection_short hi hne))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsum)
    (Q'.eqv_symm (connectedNumerator_expansion w K (responseExtent margin) _ _ (tubeIds margin)))

theorem original_tube_coefficient (w : Q') (K margin : Nat) (hK : 1 ≤ K) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) (tubeIds margin) ≈
      RingNormaliser.qpow w 36 :=
  Q'.eqv_trans _ _ _ (tube_coefficient_is_numerator w K margin) (original_tube_numerator w K margin hK)

/-- Nonzero exact coefficient forces the EXISTING computed rooted core to be the whole tube. -/
theorem tube_core_fixed (margin : Nat) : core (responseExtent margin)
    (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) (tubeIds margin) = tubeIds margin := by
  let links := edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)
  let ids := core (responseExtent margin) links (tubeIds margin)
  by_cases he : ids = tubeIds margin
  · exact he
  · have hi := core_selected (responseExtent margin) links (tubeIds margin)
    have hz := original_short_coefficient_zero 1 1 margin ids
      (sublist_selected ((selected_sublist hi).trans (selected_sublist (tubeIds_selected margin))))
      (proper_tube_selection_short hi he)
    have hp := coefficient_rooted_pin 1 1 (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) links
      (lower_supported _) (upper_supported _)
      ((lower_link_local margin).mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      ((upper_link_local margin).mono (fun _ h => List.mem_append.mpr (Or.inr h))) (tubeIds margin)
    have hzero := Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _))
    have hone := Q'.eqv_trans _ _ _ (original_tube_coefficient 1 1 margin (by decide))
      (by decide : RingNormaliser.qpow (1 : Q') 36 ≈ 1)
    exact False.elim ((by decide : ¬ Q'.eqv 1 0) (Q'.eqv_trans _ _ _ (Q'.eqv_symm hone) hzero))

theorem tube_large_anchor (margin : Nat) : tubeIds margin ∈
    largeConnectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) 12 :=
  List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨tubeIds_selected margin,decide_eq_true (tube_core_fixed margin)⟩,tube_connected_keep margin⟩,
    decide_eq_true (by rw [tubeIds_length]; exact Nat.le_refl _)⟩

def otherCoreRemainder (w : Q') (K margin : Nat) : Q' :=
  listQSum (fun ids => connectedCoefficient w K (responseExtent margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids *
    partitionSquare w K (responseExtent margin) (detachedIds (responseExtent margin)
      (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) ids
      (slabPhysicalFaceEdges (responseExtent margin))))
    ((largeConnectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) 12).filter
      (fun ids => !(decide (ids = tubeIds margin))))

/-- Exact original numerator: the full tube core is evaluated, all other signed cores remain. -/
theorem original_dressed_tube_split (w : Q') (K margin : Nat) (hK : 1 ≤ K) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
      RingNormaliser.qpow w 36 * partitionSquare w K (responseExtent margin)
        (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
          (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))) + otherCoreRemainder w K margin := by
  refine Q'.eqv_trans _ _ _ (original_large_expansion w K margin) ?_
  refine Q'.eqv_trans _ _ _ (sum_extract_target _ (tubeIds margin) _
    ((connecting_nodup _ _ _ _ (CayleyParentInj.range_nodup _)).filter _) (tube_large_anchor margin)) ?_
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (original_tube_coefficient w K margin hK)) (Q'.eqv_refl _)

end YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit

#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.proper_tube_selection_short
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.tube_coefficient_is_numerator
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.original_tube_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.tube_core_fixed
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.tube_large_anchor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.otherCoreRemainder
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit.original_dressed_tube_split
