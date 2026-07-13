/-
# Symmetric original-left residual block

This is the left-side counterpart of the original right residual allocator.
It enumerates every submask of the path-cleared original left side, emits an
ordinary external carrier code for each submask, and proves exact `2^k`
multiplicity.  When the original right residual is empty, the maximal left
residual code has exactly the exceptional source weight.
-/

import YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

namespace YMGap.Continuum.XiExceptionalSymmetricResidualBlock

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalParallelSubmaskBlock
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalParallelSubmaskCount
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-- Enumerate all and only external occurrence masks below the original
path-cleared left residual. -/
def leftResidualExternalMasks
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccBitVec Gamma.length) :=
  (bitVectors Gamma.length).filter
    (fun external => occurrenceSubmaskB external
      (leftPathResidual Gamma qP b1 b2 entry))

theorem leftResidualExternalMasks_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (leftResidualExternalMasks Gamma qP b1 b2 entry).Nodup := by
  unfold leftResidualExternalMasks
  exact nodup_filter_bool _ _ (bitVectors_nodup Gamma.length)

theorem mem_leftResidualExternalMasks_iff
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length) :
    external ∈ leftResidualExternalMasks Gamma qP b1 b2 entry ↔
      ∀ i, external.at i = true →
        (leftPathResidual Gamma qP b1 b2 entry).at i = true := by
  constructor
  · intro hmem
    exact occurrenceSubmaskB_sound external
      (leftPathResidual Gamma qP b1 b2 entry)
      (List.mem_filter.mp hmem).2
  · intro hsub
    apply List.mem_filter.mpr
    exact ⟨bitVectors_complete external,
      occurrenceSubmaskB_complete external
        (leftPathResidual Gamma qP b1 b2 entry) hsub⟩

theorem leftPathResidual_submask_left
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ i,
    (leftPathResidual Gamma qP b1 b2 entry).at i = true →
      entry.1.1.at i = true := by
  intro i hres
  cases hlt : decide (i < Gamma.length) with
  | true =>
      have hi := of_decide_eq_true hlt
      rw [leftPathResidual_at Gamma qP b1 b2 entry i hi] at hres
      exact ((Bool.and_eq_true _ _).mp hres).2
  | false =>
      have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
      have hout := bitVec_at_false_of_ge
        (leftPathResidual Gamma qP b1 b2 entry) i (by omega)
      rw [hres] at hout
      cases hout

theorem mem_leftResidualExternalMasks_submask_left
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ leftResidualExternalMasks Gamma qP b1 b2 entry) :
    ∀ i, external.at i = true → entry.1.1.at i = true := by
  intro i hext
  exact leftPathResidual_submask_left Gamma qP b1 b2 entry i
    ((mem_leftResidualExternalMasks_iff Gamma qP b1 b2 entry external).mp
      hmem i hext)

def leftResidualParallelCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  parallelExternalBlock Gamma qP b1 b2 (fun _ => entry) (fun x => x)
    (leftResidualExternalMasks Gamma qP b1 b2 entry)

theorem leftResidualParallelCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (leftResidualParallelCodes Gamma qP b1 b2 entry).Nodup := by
  unfold leftResidualParallelCodes
  apply parallelExternalBlock_nodup Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (leftResidualExternalMasks Gamma qP b1 b2 entry)
    (leftResidualExternalMasks_nodup Gamma qP b1 b2 entry)
  intro a _ b _ hab
  exact hab

theorem leftResidualParallelCodes_mem_target
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ code,
    code ∈ leftResidualParallelCodes Gamma qP b1 b2 entry →
      code ∈ occurrenceCarrierXiCodes Gamma := by
  unfold leftResidualParallelCodes
  exact parallelExternalBlock_mem Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (leftResidualExternalMasks Gamma qP b1 b2 entry)

theorem leftResidualParallelCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ leftResidualExternalMasks Gamma qP b1 b2 entry) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  exact parallelExternalCarrierCode_weight_eqv_of_left_submask
    w qP b1 b2 Gamma label entry external
    (mem_leftResidualExternalMasks_submask_left Gamma qP b1 b2
      entry external hmem)

theorem leftResidualExternalMasks_length
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (leftResidualExternalMasks Gamma qP b1 b2 entry).length =
      2 ^ occurrenceBitCount (leftPathResidual Gamma qP b1 b2 entry) := by
  unfold leftResidualExternalMasks
  rw [← occurrenceSubmasks_eq_filter]
  exact occurrenceSubmasks_length _

theorem leftResidualParallelCodes_length
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (leftResidualParallelCodes Gamma qP b1 b2 entry).length =
      2 ^ occurrenceBitCount (leftPathResidual Gamma qP b1 b2 entry) := by
  unfold leftResidualParallelCodes parallelExternalBlock
  rw [List.length_map]
  exact leftResidualExternalMasks_length Gamma qP b1 b2 entry

theorem leftPathResidual_mem_external_masks
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    leftPathResidual Gamma qP b1 b2 entry ∈
      leftResidualExternalMasks Gamma qP b1 b2 entry := by
  apply (mem_leftResidualExternalMasks_iff Gamma qP b1 b2 entry _).mpr
  intro _ h
  exact h

/-- If the right cleared residual is empty, the maximal left residual code
has exactly the original exceptional source weight. -/
theorem leftOnlyResidualCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightEmpty : selectByBits Gamma
      (rightPathResidual Gamma qP b1 b2 entry) = []) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry
          (leftPathResidual Gamma qP b1 b2 entry)) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  have hcode := leftResidualParallelCode_weight_eqv
    w qP b1 b2 Gamma label entry
    (leftPathResidual Gamma qP b1 b2 entry)
    (leftPathResidual_mem_external_masks Gamma qP b1 b2 entry)
  have hsource := occurrencePairWeight_eqv_original_path_residuals
    w qP b1 b2 Gamma label entry
  dsimp only at hcode hsource
  rw [hrightEmpty] at hsource
  simp only [familyActivity_nil] at hsource
  have hsourceReduced := Q'.eqv_trans _ _ _ hsource
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ hcode (Q'.eqv_symm hsourceReduced)

#print axioms leftResidualExternalMasks_nodup
#print axioms mem_leftResidualExternalMasks_iff
#print axioms leftPathResidual_submask_left
#print axioms leftResidualParallelCodes_nodup
#print axioms leftResidualParallelCodes_mem_target
#print axioms leftResidualParallelCode_weight_eqv
#print axioms leftResidualExternalMasks_length
#print axioms leftResidualParallelCodes_length
#print axioms leftPathResidual_mem_external_masks
#print axioms leftOnlyResidualCode_weight_eqv_source

end YMGap.Continuum.XiExceptionalSymmetricResidualBlock
