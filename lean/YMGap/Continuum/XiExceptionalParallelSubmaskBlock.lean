/-
# Finite multicode block of parallel source-side submasks

For one exceptional source entry, enumerate every occurrence submask of its
right admissible side.  Each submask is allocated to the external family of
a carrier with the same canonical articulation path.  The resulting target
block is complete for these masks, duplicate-free, has singleton fibers, and
inherits the exact path-times-family rational weight identity.
-/

import YMGap.Continuum.XiExceptionalParallelSourceSide

namespace YMGap.Continuum.XiExceptionalParallelSubmaskBlock

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelSourceSide

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- Boolean recognition of occurrence-submask inclusion. -/
def occurrenceSubmaskB : {n : Nat} → OccBitVec n → OccBitVec n → Bool
  | 0, .nil, .nil => true
  | _ + 1, .cons smallHead smallTail, .cons bigHead bigTail =>
      ((!smallHead) || bigHead) && occurrenceSubmaskB smallTail bigTail

theorem occurrenceSubmaskB_sound : ∀ {n : Nat}
    (small big : OccBitVec n), occurrenceSubmaskB small big = true →
      ∀ i, small.at i = true → big.at i = true
  | 0, .nil, .nil, _, i, hsmall => by
      simp [BitVec.at] at hsmall
  | _ + 1, .cons smallHead smallTail, .cons bigHead bigTail,
      hmask, 0, hsmall => by
      have hhead := (Bool.and_eq_true _ _).mp hmask |>.1
      cases smallHead <;> cases bigHead <;>
        simp_all [occurrenceSubmaskB, BitVec.at]
  | _ + 1, .cons smallHead smallTail, .cons bigHead bigTail,
      hmask, i + 1, hsmall => by
      exact occurrenceSubmaskB_sound smallTail bigTail
        ((Bool.and_eq_true _ _).mp hmask).2 i hsmall

theorem occurrenceSubmaskB_complete : ∀ {n : Nat}
    (small big : OccBitVec n),
    (∀ i, small.at i = true → big.at i = true) →
      occurrenceSubmaskB small big = true
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons smallHead smallTail, .cons bigHead bigTail, hsub => by
      apply (Bool.and_eq_true _ _).mpr
      constructor
      · cases smallHead with
        | false => simp
        | true =>
            cases bigHead with
            | false => exact hsub 0 rfl
            | true => rfl
      · exact occurrenceSubmaskB_complete smallTail bigTail
          (fun i hsmall => hsub (i + 1) hsmall)

/-- All and only occurrence submasks of the right source side. -/
def rightExternalMasks
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccBitVec Gamma.length) :=
  (bitVectors Gamma.length).filter
    (fun external => occurrenceSubmaskB external entry.1.2)

theorem rightExternalMasks_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightExternalMasks Gamma qP b1 b2 entry).Nodup := by
  unfold rightExternalMasks
  exact nodup_filter_bool _ _ (bitVectors_nodup Gamma.length)

theorem mem_rightExternalMasks_iff
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length) :
    external ∈ rightExternalMasks Gamma qP b1 b2 entry ↔
      ∀ i, external.at i = true → entry.1.2.at i = true := by
  constructor
  · intro hmem
    exact occurrenceSubmaskB_sound external entry.1.2
      (List.mem_filter.mp hmem).2
  · intro hsub
    apply List.mem_filter.mpr
    exact ⟨bitVectors_complete external,
      occurrenceSubmaskB_complete external entry.1.2 hsub⟩

/-- The complete finite target block for all right-side parallel submasks. -/
def rightParallelCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  parallelExternalBlock Gamma qP b1 b2 (fun _ => entry) (fun x => x)
    (rightExternalMasks Gamma qP b1 b2 entry)

theorem rightParallelCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightParallelCodes Gamma qP b1 b2 entry).Nodup := by
  unfold rightParallelCodes
  apply parallelExternalBlock_nodup Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (rightExternalMasks Gamma qP b1 b2 entry)
    (rightExternalMasks_nodup Gamma qP b1 b2 entry)
  intro a _ b _ hab
  exact hab

theorem rightParallelCodes_mem_target
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ code,
    code ∈ rightParallelCodes Gamma qP b1 b2 entry →
      code ∈ occurrenceCarrierXiCodes Gamma := by
  unfold rightParallelCodes
  exact parallelExternalBlock_mem Gamma qP b1 b2
    (fun _ => entry) (fun x => x)
    (rightExternalMasks Gamma qP b1 b2 entry)

/-- Equality of allocated target codes recovers the occurrence submask, so
every source fiber has multiplicity one. -/
theorem rightParallelCode_fiber_unique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external1 external2 : OccBitVec Gamma.length)
    (hcode : parallelExternalCarrierCode Gamma qP b1 b2 entry external1 =
      parallelExternalCarrierCode Gamma qP b1 b2 entry external2) :
    external1 = external2 :=
  parallelExternal_source_fiber_unique Gamma qP b1 b2
    (fun _ => entry) (fun x => x) (fun _ _ h => h)
    external1 external2 hcode

/-- Every enumerated code has the exact articulation-once factorization. -/
theorem rightParallelCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hmem : external ∈ rightExternalMasks Gamma qP b1 b2 entry) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  exact parallelExternalCarrierCode_weight_eqv_of_right_submask
    w qP b1 b2 Gamma label entry external
    ((mem_rightExternalMasks_iff Gamma qP b1 b2 entry external).mp hmem)

/-- Finite summation closure for the entire submask block. -/
theorem rightParallelCodes_global_bound
    (w : Q') (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (sourceWeight : OccBitVec Gamma.length → Q')
    (hlocal : ∀ external,
      external ∈ rightExternalMasks Gamma qP b1 b2 entry →
      sourceWeight external ≤ occurrenceCarrierXiCodeWeight
        w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external)) :
    qListSum sourceWeight (rightExternalMasks Gamma qP b1 b2 entry) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply parallelExternal_global_bound w hw qP b1 b2 Gamma label
    (fun _ => entry) (fun x => x)
    (rightExternalMasks Gamma qP b1 b2 entry) sourceWeight
    (rightExternalMasks_nodup Gamma qP b1 b2 entry)
  · intro a _ b _ hab
    exact hab
  · exact hlocal

#print axioms occurrenceSubmaskB_sound
#print axioms occurrenceSubmaskB_complete
#print axioms rightExternalMasks_nodup
#print axioms mem_rightExternalMasks_iff
#print axioms rightParallelCodes_nodup
#print axioms rightParallelCodes_mem_target
#print axioms rightParallelCode_fiber_unique
#print axioms rightParallelCode_weight_eqv
#print axioms rightParallelCodes_global_bound

end YMGap.Continuum.XiExceptionalParallelSubmaskBlock
