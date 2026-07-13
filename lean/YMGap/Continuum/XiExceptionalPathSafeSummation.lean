/-
# Global exceptional summation without a right-safe restriction

The source-specific path-safe carrier is an unconditional injection on
exceptional source entries.  Its exact weight is the source weight whenever
the finite target-validity checks hold.  Singleton target blocks therefore
give the global weighted bound for every duplicate-free certified source
list, with no `rightSafe` premise and no unsafe-right remainder.
-/

import YMGap.Continuum.XiExceptionalPathSafeExactWeight

namespace YMGap.Continuum.XiExceptionalPathSafeSummation

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalPathSafeExactWeight

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

def pathSafeSourceWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Q' :=
  occurrencePairWeight w qP b1 b2 Gamma label entry.1

def pathSafeBlock
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  [exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry]

private theorem flatMap_singleton_eq_map (f : alpha → beta) :
    ∀ xs : List alpha, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem pathSafe_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hfacts : ∀ entry, entry ∈ source →
      PathSafeRoutedFacts Gamma qP b1 b2 entry) :
    qListSum (pathSafeSourceWeight w qP b1 b2 Gamma label) source ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (pathSafeSourceWeight w qP b1 b2 Gamma label)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (pathSafeBlock Gamma qP b1 b2)
  · rw [show source.flatMap (pathSafeBlock Gamma qP b1 b2) =
      source.map (exceptionalPathSafeCarrierCode Gamma qP b1 b2) by
      simpa only [pathSafeBlock] using
        flatMap_singleton_eq_map
          (exceptionalPathSafeCarrierCode Gamma qP b1 b2) source]
    apply nodup_map_of_injOn
      (exceptionalPathSafeCarrierCode Gamma qP b1 b2) source hsource
    intro entry1 _ entry2 _ hcode
    exact exceptionalPathSafeCarrierCode_injective
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro code hcode
    rw [show source.flatMap (pathSafeBlock Gamma qP b1 b2) =
      source.map (exceptionalPathSafeCarrierCode Gamma qP b1 b2) by
      simpa only [pathSafeBlock] using
        flatMap_singleton_eq_map
          (exceptionalPathSafeCarrierCode Gamma qP b1 b2) source]
      at hcode
    obtain ⟨entry, _, hcodeEq⟩ := List.mem_map.mp hcode
    rw [← hcodeEq]
    exact exceptionalPathSafeCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry hentry
    simp only [pathSafeSourceWeight, pathSafeBlock,
      qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (exceptionalPathSafeCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry (hfacts entry hentry))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms pathSafe_region_global_bound

end YMGap.Continuum.XiExceptionalPathSafeSummation
