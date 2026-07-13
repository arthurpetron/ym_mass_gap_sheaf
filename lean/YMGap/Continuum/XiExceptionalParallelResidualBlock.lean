/-
# Parallel branch block with canonical-path occurrences removed

Before allocating parallel children, remove every occurrence used by the
canonical marked-to-bad path from the right admissible source side.  All
submasks of this residual side are then enumerated as external carrier
families.  Hence no allocated child occurrence can duplicate the path or its
articulation vertices, while target membership, exact weight factorization,
duplicate-freedom, and singleton fibers remain constructive.
-/

import YMGap.Continuum.XiExceptionalParallelSubmaskBlock
import YMGap.Continuum.XiExceptionalPathMaskAlgebra

namespace YMGap.Continuum.XiExceptionalParallelResidualBlock

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalParallelSubmaskBlock

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- The right source side with all canonical-path occurrences cleared. -/
def rightPathResidual
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  residualBits
    (pathOccurrenceBits Gamma.length path.indexWalk.vertices) pair.2

theorem rightPathResidual_at
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (rightPathResidual Gamma qP b1 b2 entry).at i =
      ((!decide (i ∈ path.indexWalk.vertices)) && entry.1.2.at i) := by
  dsimp only
  unfold rightPathResidual
  rw [residualBits_at _ _ i hi]
  rw [pathOccurrenceBits_at Gamma.length _ i hi]

theorem rightPathResidual_submask_right
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ i,
    (rightPathResidual Gamma qP b1 b2 entry).at i = true →
      entry.1.2.at i = true := by
  intro i hres
  cases hi : decide (i < Gamma.length) with
  | true =>
      have hiN := of_decide_eq_true hi
      rw [rightPathResidual_at Gamma qP b1 b2 entry i hiN] at hres
      exact ((Bool.and_eq_true _ _).mp hres).2
  | false =>
      have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
      have hout := bitVec_at_false_of_ge
        (rightPathResidual Gamma qP b1 b2 entry) i (by omega)
      rw [hres] at hout
      cases hout

/-- Enumerate all and only external occurrence masks below the path-cleared
right residual. -/
def rightResidualExternalMasks
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccBitVec Gamma.length) :=
  (bitVectors Gamma.length).filter
    (fun external => occurrenceSubmaskB external
      (rightPathResidual Gamma qP b1 b2 entry))

theorem rightResidualExternalMasks_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightResidualExternalMasks Gamma qP b1 b2 entry).Nodup := by
  unfold rightResidualExternalMasks
  exact nodup_filter_bool _ _ (bitVectors_nodup Gamma.length)

theorem mem_rightResidualExternalMasks_iff
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length) :
    external ∈ rightResidualExternalMasks Gamma qP b1 b2 entry ↔
      ∀ i, external.at i = true →
        (rightPathResidual Gamma qP b1 b2 entry).at i = true := by
  constructor
  · intro hmem
    exact occurrenceSubmaskB_sound external
      (rightPathResidual Gamma qP b1 b2 entry)
      (List.mem_filter.mp hmem).2
  · intro hsub
    apply List.mem_filter.mpr
    exact ⟨bitVectors_complete external,
      occurrenceSubmaskB_complete external
        (rightPathResidual Gamma qP b1 b2 entry) hsub⟩

theorem mem_rightResidualExternalMasks_submask_right
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ rightResidualExternalMasks Gamma qP b1 b2 entry) :
    ∀ i, external.at i = true → entry.1.2.at i = true := by
  intro i hext
  exact rightPathResidual_submask_right Gamma qP b1 b2 entry i
    ((mem_rightResidualExternalMasks_iff Gamma qP b1 b2 entry external).mp
      hmem i hext)

/-- No allocated external occurrence is a canonical-path occurrence. -/
theorem mem_rightResidualExternalMasks_avoids_path
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ rightResidualExternalMasks Gamma qP b1 b2 entry)
    (i : Nat) (hi : i < Gamma.length) (hext : external.at i = true) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    i ∉ path.indexWalk.vertices := by
  dsimp only
  have hres :=
    (mem_rightResidualExternalMasks_iff Gamma qP b1 b2 entry external).mp
      hmem i hext
  rw [rightPathResidual_at Gamma qP b1 b2 entry i hi] at hres
  have hnotDecide := ((Bool.and_eq_true _ _).mp hres).1
  exact of_decide_eq_false (eq_false_of_not_true hnotDecide)

def rightResidualParallelCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  parallelExternalBlock Gamma qP b1 b2 (fun _ => entry) (fun x => x)
    (rightResidualExternalMasks Gamma qP b1 b2 entry)

theorem rightResidualParallelCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightResidualParallelCodes Gamma qP b1 b2 entry).Nodup := by
  unfold rightResidualParallelCodes
  apply parallelExternalBlock_nodup Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (rightResidualExternalMasks Gamma qP b1 b2 entry)
    (rightResidualExternalMasks_nodup Gamma qP b1 b2 entry)
  intro a _ b _ hab
  exact hab

theorem rightResidualParallelCodes_mem_target
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ code,
    code ∈ rightResidualParallelCodes Gamma qP b1 b2 entry →
      code ∈ occurrenceCarrierXiCodes Gamma := by
  unfold rightResidualParallelCodes
  exact parallelExternalBlock_mem Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (rightResidualExternalMasks Gamma qP b1 b2 entry)

theorem rightResidualParallelCode_fiber_unique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external1 external2 : OccBitVec Gamma.length)
    (hcode : parallelExternalCarrierCode Gamma qP b1 b2 entry external1 =
      parallelExternalCarrierCode Gamma qP b1 b2 entry external2) :
    external1 = external2 :=
  parallelExternal_source_fiber_unique Gamma qP b1 b2
    (fun _ => entry) (fun x => x) (fun _ _ h => h)
    external1 external2 hcode

theorem rightResidualParallelCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ rightResidualExternalMasks Gamma qP b1 b2 entry) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  exact parallelExternalCarrierCode_weight_eqv_of_right_submask
    w qP b1 b2 Gamma label entry external
    (mem_rightResidualExternalMasks_submask_right Gamma qP b1 b2
      entry external hmem)

theorem rightResidualParallelCodes_global_bound
    (w : Q') (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (sourceWeight : OccBitVec Gamma.length → Q')
    (hlocal : ∀ external,
      external ∈ rightResidualExternalMasks Gamma qP b1 b2 entry →
      sourceWeight external ≤ occurrenceCarrierXiCodeWeight
        w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external)) :
    qListSum sourceWeight
        (rightResidualExternalMasks Gamma qP b1 b2 entry) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply parallelExternal_global_bound w hw qP b1 b2 Gamma label
    (fun _ => entry) (fun x => x)
    (rightResidualExternalMasks Gamma qP b1 b2 entry) sourceWeight
    (rightResidualExternalMasks_nodup Gamma qP b1 b2 entry)
  · intro a _ b _ hab
    exact hab
  · exact hlocal

#print axioms rightPathResidual_at
#print axioms rightPathResidual_submask_right
#print axioms rightResidualExternalMasks_nodup
#print axioms mem_rightResidualExternalMasks_iff
#print axioms mem_rightResidualExternalMasks_submask_right
#print axioms mem_rightResidualExternalMasks_avoids_path
#print axioms rightResidualParallelCodes_nodup
#print axioms rightResidualParallelCodes_mem_target
#print axioms rightResidualParallelCode_fiber_unique
#print axioms rightResidualParallelCode_weight_eqv
#print axioms rightResidualParallelCodes_global_bound

end YMGap.Continuum.XiExceptionalParallelResidualBlock
