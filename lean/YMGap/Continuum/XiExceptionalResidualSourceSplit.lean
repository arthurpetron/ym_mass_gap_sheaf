/-
# Exact split by original cleared residual sides

The full exceptional source is partitioned constructively into:

* empty left residual (handled by the original-right carrier),
* nonempty left and empty right residual (handled by the symmetric carrier),
* both original residuals nonempty (the remaining mixed region).

The first two regions each inject into the ordinary occurrence target with
exact source weight.  No global empty-side claim is assumed.
-/

import YMGap.Continuum.XiOneEndedOriginalResidualBound
import YMGap.Continuum.XiExceptionalSymmetricResidualInjection

namespace YMGap.Continuum.XiExceptionalResidualSourceSplit

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiExceptionalSymmetricResidualBlock
open YMGap.Continuum.XiExceptionalSymmetricResidualInjection
open YMGap.Continuum.XiOneEndedOriginalResidualBound

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Boolean emptiness and the three finite source lists -/

def occurrenceEmptyB : OccBitVec n → Bool
  | .nil => true
  | .cons b tail => (!b) && occurrenceEmptyB tail

theorem occurrenceEmptyB_true_iff_select_nil :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length),
      occurrenceEmptyB bits = true ↔ selectByBits Gamma bits = []
  | [], .nil => by simp [occurrenceEmptyB, selectByBits]
  | X :: Gamma, .cons false tail => by
      simp [occurrenceEmptyB, selectByBits,
        occurrenceEmptyB_true_iff_select_nil Gamma tail]
  | X :: Gamma, .cons true tail => by
      simp [occurrenceEmptyB, selectByBits]

def emptyLeftResidualSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) :=
  (fullExceptionalSource Gamma qP b1 b2).filter (fun entry =>
    occurrenceEmptyB (leftPathResidual Gamma qP b1 b2 entry))

def nonemptyLeftResidualSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) :=
  (fullExceptionalSource Gamma qP b1 b2).filter (fun entry =>
    !(occurrenceEmptyB (leftPathResidual Gamma qP b1 b2 entry)))

def leftOnlyResidualSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) :=
  (nonemptyLeftResidualSource Gamma qP b1 b2).filter (fun entry =>
    occurrenceEmptyB (rightPathResidual Gamma qP b1 b2 entry))

def mixedResidualSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) :=
  (nonemptyLeftResidualSource Gamma qP b1 b2).filter (fun entry =>
    !(occurrenceEmptyB (rightPathResidual Gamma qP b1 b2 entry)))

theorem emptyLeftResidualSource_left_empty
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ emptyLeftResidualSource Gamma qP b1 b2) :
    selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = [] := by
  exact (occurrenceEmptyB_true_iff_select_nil Gamma _).mp
    (List.mem_filter.mp hentry).2

theorem leftOnlyResidualSource_left_nonempty_right_empty
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ leftOnlyResidualSource Gamma qP b1 b2) :
    selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) ≠ [] ∧
      selectByBits Gamma (rightPathResidual Gamma qP b1 b2 entry) = [] := by
  have hp := List.mem_filter.mp hentry
  have hnonemptyLeft := (List.mem_filter.mp hp.1).2
  have hright := hp.2
  constructor
  · intro hnil
    have hempty := (occurrenceEmptyB_true_iff_select_nil Gamma _).mpr hnil
    rw [hempty] at hnonemptyLeft
    cases hnonemptyLeft
  · exact (occurrenceEmptyB_true_iff_select_nil Gamma _).mp hright

theorem mixedResidualSource_both_nonempty
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ mixedResidualSource Gamma qP b1 b2) :
    selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) ≠ [] ∧
      selectByBits Gamma (rightPathResidual Gamma qP b1 b2 entry) ≠ [] := by
  have hp := List.mem_filter.mp hentry
  have hleft := (List.mem_filter.mp hp.1).2
  have hright := hp.2
  constructor
  · intro hnil
    have hempty := (occurrenceEmptyB_true_iff_select_nil Gamma _).mpr hnil
    rw [hempty] at hleft
    cases hleft
  · intro hnil
    have hempty := (occurrenceEmptyB_true_iff_select_nil Gamma _).mpr hnil
    rw [hempty] at hright
    cases hright

theorem exceptionalSource_residual_partition
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (emptyLeftResidualSource Gamma qP b1 b2) +
        (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
            entry.1) (leftOnlyResidualSource Gamma qP b1 b2) +
          qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
            entry.1) (mixedResidualSource Gamma qP b1 b2)) := by
  let weight := fun entry : ExceptionalSourceEntry Gamma qP b1 b2 =>
    occurrencePairWeight w qP b1 b2 Gamma label entry.1
  let leftEmpty := fun entry : ExceptionalSourceEntry Gamma qP b1 b2 =>
    occurrenceEmptyB (leftPathResidual Gamma qP b1 b2 entry)
  let rightEmpty := fun entry : ExceptionalSourceEntry Gamma qP b1 b2 =>
    occurrenceEmptyB (rightPathResidual Gamma qP b1 b2 entry)
  have hleft := qListSum_filter_partition weight leftEmpty
    (fullExceptionalSource Gamma qP b1 b2)
  have hright := qListSum_filter_partition weight rightEmpty
    (nonemptyLeftResidualSource Gamma qP b1 b2)
  change qListSum weight (fullExceptionalSource Gamma qP b1 b2) ≈
    qListSum weight (emptyLeftResidualSource Gamma qP b1 b2) +
      qListSum weight (nonemptyLeftResidualSource Gamma qP b1 b2) at hleft
  change qListSum weight (nonemptyLeftResidualSource Gamma qP b1 b2) ≈
    qListSum weight (leftOnlyResidualSource Gamma qP b1 b2) +
      qListSum weight (mixedResidualSource Gamma qP b1 b2) at hright
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.add_eqv_congr_left _ _ _ hright)

/-! ## 2. The symmetric region embeds globally -/

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem originalLeftResidual_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hrightEmpty : ∀ entry, entry ∈ source →
      selectByBits Gamma (rightPathResidual Gamma qP b1 b2 entry) = []) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun entry => [originalLeftResidualCarrierCode Gamma qP b1 b2 entry])
  · rw [flatMap_singleton_eq_map]
    apply nodup_map_of_injOn _ source hsource
    intro a ha b hb hcode
    exact originalLeftResidualCarrierCode_injective Gamma qP b1 b2 a b
      (hrightEmpty a ha) (hrightEmpty b hb) hcode
  · intro code hcode
    obtain ⟨entry, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact parallelExternalCarrierCode_mem Gamma qP b1 b2 entry
      (leftPathResidual Gamma qP b1 b2 entry)
  · intro entry hentry
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    change occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≤
      occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry
          (leftPathResidual Gamma qP b1 b2 entry))
    exact Q'.le_of_eqv (Q'.eqv_symm
      (leftOnlyResidualCode_weight_eqv_source w qP b1 b2 Gamma label
        entry (hrightEmpty entry hentry)))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

theorem emptyLeftResidualSource_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (emptyLeftResidualSource Gamma qP b1 b2) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply originalRightResidual_region_global_bound hw Gamma qP b1 b2 label
    (emptyLeftResidualSource Gamma qP b1 b2)
  · exact nodup_filter_bool _ _
      (fullExceptionalSource_nodup Gamma qP b1 b2)
  · exact emptyLeftResidualSource_left_empty Gamma qP b1 b2

theorem leftOnlyResidualSource_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (leftOnlyResidualSource Gamma qP b1 b2) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply originalLeftResidual_region_global_bound hw Gamma qP b1 b2 label
    (leftOnlyResidualSource Gamma qP b1 b2)
  · exact nodup_filter_bool _ _
      (nodup_filter_bool _ _
        (fullExceptionalSource_nodup Gamma qP b1 b2))
  · intro entry hentry
    exact (leftOnlyResidualSource_left_nonempty_right_empty
      Gamma qP b1 b2 entry hentry).2

#print axioms occurrenceEmptyB_true_iff_select_nil
#print axioms emptyLeftResidualSource_left_empty
#print axioms leftOnlyResidualSource_left_nonempty_right_empty
#print axioms mixedResidualSource_both_nonempty
#print axioms exceptionalSource_residual_partition
#print axioms originalLeftResidual_region_global_bound
#print axioms emptyLeftResidualSource_global_bound
#print axioms leftOnlyResidualSource_global_bound

end YMGap.Continuum.XiExceptionalResidualSourceSplit
