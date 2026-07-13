/-
# Global summation for the residual-component carrier

On the right-safe component branch, the source-specific carrier is an
injective exact-weight map into the unchanged finite carrier enumeration.
Singleton target blocks therefore bound every duplicate-free certified
source list by the full carrier partition sum.
-/

import YMGap.Continuum.XiExceptionalComponentInjection

namespace YMGap.Continuum.XiExceptionalComponentSummation

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalComponentCarrier
open YMGap.Continuum.XiExceptionalComponentExactWeight
open YMGap.Continuum.XiExceptionalComponentInjection

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

def componentSourceWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Q' :=
  occurrencePairWeight w qP b1 b2 Gamma label entry.1

def componentBlock
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  [exceptionalComponentCarrierCode Gamma qP b1 b2 entry]

private theorem flatMap_singleton_eq_map (f : alpha → beta) :
    ∀ xs : List alpha, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem componentRightSafe_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hrightSafe : ∀ entry, entry ∈ source →
      componentRightSafe Gamma qP b1 b2 entry) :
    qListSum (componentSourceWeight w qP b1 b2 Gamma label) source ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (componentSourceWeight w qP b1 b2 Gamma label)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (componentBlock Gamma qP b1 b2)
  · rw [show source.flatMap (componentBlock Gamma qP b1 b2) =
      source.map (exceptionalComponentCarrierCode Gamma qP b1 b2) by
      simpa only [componentBlock] using
        flatMap_singleton_eq_map
          (exceptionalComponentCarrierCode Gamma qP b1 b2) source]
    apply nodup_map_of_injOn
      (exceptionalComponentCarrierCode Gamma qP b1 b2) source hsource
    intro entry1 hentry1 entry2 hentry2 hcode
    exact exceptionalComponentCarrierCode_injective_of_rightSafe
      Gamma qP b1 b2 entry1 entry2
      (hrightSafe entry1 hentry1) (hrightSafe entry2 hentry2) hcode
  · intro code hcode
    rw [show source.flatMap (componentBlock Gamma qP b1 b2) =
      source.map (exceptionalComponentCarrierCode Gamma qP b1 b2) by
      simpa only [componentBlock] using
        flatMap_singleton_eq_map
          (exceptionalComponentCarrierCode Gamma qP b1 b2) source]
      at hcode
    obtain ⟨entry, _, hcodeEq⟩ := List.mem_map.mp hcode
    rw [← hcodeEq]
    exact exceptionalComponentCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry hentry
    simp only [componentSourceWeight, componentBlock,
      qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (exceptionalComponentCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry (hrightSafe entry hentry))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms componentRightSafe_region_global_bound

end YMGap.Continuum.XiExceptionalComponentSummation
