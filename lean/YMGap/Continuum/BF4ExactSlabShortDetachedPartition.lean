/-
# Restore each ORIGINAL short-core detached partition square

The literal collar has at most 816 faces for an eight-link probe and a
core of at most 32 faces. Its two-copy removal cost is bounded by 2 at
the explicit SU(2) nome 1/1024, independently of cutoff and volume.
Every original detached partition square is therefore at most twice the
SAME full partition square. No coefficient or spatial-defect estimate
is assumed or concluded here.
-/

import YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate

namespace YMGap.Continuum.BF4ExactSlabShortDetachedPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "hd₀" => (And.right existingNome_guards)
local notation "r₀" => inverseFaceFloor nome hd₀

theorem inverse_ninetysix_le : r₀^96 ≤ Q'.mkPos 65 64 (by decide) := by
  have h := TotalMajorantClose.pow_le_pow_base
    (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos nome hd₀)) 8) inverse_eighth_le_block 12
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r₀ 8 12))
    (Q'.le_trans' _ _ _ h (by decide : blockCeiling^12 ≤ Q'.mkPos 65 64 (by decide)))

theorem short_inverse_cost_le_two : r₀^1632 ≤ 2 := by
  have h := TotalMajorantClose.pow_le_pow_base
    (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos nome hd₀)) 96) inverse_ninetysix_le 17
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r₀ 96 17))
    (Q'.le_trans' _ _ _ h (by decide : (Q'.mkPos 65 64 (by decide))^17 ≤ (2 : Q')))

private theorem inside_all (ids : List Nat) : inside (fun _ => true) ids = ids :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

private theorem mixedPartition_all (w : Q') (K extent : Nat) (ids : List Nat) :
    mixedPartition w K extent (fun _ => true) ids = partitionSquare w K extent ids := by
  unfold mixedPartition partitionSquare
  rw [inside_all]

theorem short_collar_reciprocal_le_two (extent : Nat) (links : List Z4Link) (ambient ids : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hl : links.length ≤ 8) (hi : ids.length ≤ 32) :
    Q'.recipPos (mixedRemovalFloor nome (fun _ => true) (collarIds extent links ids ambient))
      (mixedRemovalFloor_pos hd₀ _ _) ≤ 2 := by
  have hsize : 12*links.length+48*ids.length ≤ 1632 := by omega
  exact Q'.le_trans' _ _ _
    (collarReciprocal_bound (Q'.le_of_lt nome_pos) hd₀ extent links (fun _ => true) ambient ids hn hphys)
    (Q'.le_trans' _ _ _ (TotalMajorantClose.q_pow_mono
      (one_le_inverseFaceFloor (Q'.le_of_lt nome_pos) hd₀) hsize) short_inverse_cost_le_two)

private theorem remove_floor {F z Z : Q'} (hF : (0 : Q') < F) (h : F*z ≤ Z) :
    z ≤ Q'.recipPos F hF * Z := by
  let r := Q'.recipPos F hF
  have hr : r*F ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  have he : r*(F*z) ≈ z := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z hr) (Q'.one_mul_eqv z))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ r h (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- Each core retains its own original detached face list. -/
theorem short_detached_square_le_two (K extent : Nat) (links : List Z4Link) (ambient ids : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hl : links.length ≤ 8) (hi : ids.length ≤ 32) :
    partitionSquare nome K extent (detachedIds extent links ids ambient) ≤
      2*partitionSquare nome K extent ambient := by
  have hf := detached_mixed_floor (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one)
    existingNome_guards.1 (Q'.le_of_lt hd₀) K extent (fun _ => true) links ids ambient hphys
  rw [mixedPartition_all, mixedPartition_all] at hf
  exact Q'.le_trans' _ _ _ (remove_floor (mixedRemovalFloor_pos hd₀ _ _) hf)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (short_collar_reciprocal_le_two extent links ambient ids hn hphys hl hi)
      (SumOfSquares.q_mul_self_nonneg _))

theorem original_short_detached_square_le_two (K margin : Nat) {ids : List Nat}
    (hs : ids ∈ shortOtherCores 33 margin) :
    partitionSquare nome K (responseExtent margin) (detachedIds (responseExtent margin)
      (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) ids
      (slabPhysicalFaceEdges (responseExtent margin))) ≤
    2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hsize := (shortOtherCores_window hs).2.1
  exact short_detached_square_le_two K (responseExtent margin) _ _ ids
    (CayleyParentInj.range_nodup _) (fun _ h => h) (by change 8 ≤ 8; exact Nat.le_refl _) (by omega)

end YMGap.Continuum.BF4ExactSlabShortDetachedPartition

#print axioms YMGap.Continuum.BF4ExactSlabShortDetachedPartition.inverse_ninetysix_le
#print axioms YMGap.Continuum.BF4ExactSlabShortDetachedPartition.short_inverse_cost_le_two
#print axioms YMGap.Continuum.BF4ExactSlabShortDetachedPartition.short_collar_reciprocal_le_two
#print axioms YMGap.Continuum.BF4ExactSlabShortDetachedPartition.short_detached_square_le_two
#print axioms YMGap.Continuum.BF4ExactSlabShortDetachedPartition.original_short_detached_square_le_two
