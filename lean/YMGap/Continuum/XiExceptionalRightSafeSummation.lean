/-
# Global weighted injection on the right-safe region

The exact-weight residual router and its decoder assemble into a finite
weighted injection.  Any duplicate-free list of exceptional entries carrying
the explicit right-safe target checks maps injectively into the full
occurrence-carrier enumeration, with source weight bounded termwise by the
exact target weight.
-/

import YMGap.Continuum.XiExceptionalResidualRoutedInjection

namespace YMGap.Continuum.XiExceptionalRightSafeSummation

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalResidualRoutedInjection
open YMGap.Continuum.XiExceptionalTargetBlocks

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

structure RightSafeRoutedFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Type where
  rightSafe :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let rightResidual := residualBits pathBits switched.2
    ∀ i, i < Gamma.length → rightResidual.at i = true → safe i = true
  backgroundCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    familyCompatibleB
      (selectByBits Gamma (routedBackground safe leftResidual)) = true
  backgroundQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    (selectByBits Gamma (routedBackground safe leftResidual)).all qP = true
  backgroundPath :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    ∀ X, X ∈ path.polymerWalk.vertices →
      ∀ T, T ∈ selectByBits Gamma (routedBackground safe leftResidual) →
        compatibleB X T = true
  externalCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    familyCompatibleB (selectByBits Gamma
      (routedExternal safe leftResidual rightResidual)) = true
  externalQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    (selectByBits Gamma
      (routedExternal safe leftResidual rightResidual)).all qP = true

def rightSafeSourceWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Q' :=
  occurrencePairWeight w qP b1 b2 Gamma label entry.1

def rightSafeBlock
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  [exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe entry]

private theorem flatMap_singleton_eq_map (f : alpha → beta) :
    ∀ xs : List alpha, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem rightSafe_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hfacts : ∀ entry, entry ∈ source →
      RightSafeRoutedFacts Gamma qP b1 b2 safe entry) :
    qListSum (rightSafeSourceWeight w qP b1 b2 Gamma label) source ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (rightSafeSourceWeight w qP b1 b2 Gamma label)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (rightSafeBlock Gamma qP b1 b2 safe)
  · rw [show source.flatMap (rightSafeBlock Gamma qP b1 b2 safe) =
      source.map
        (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe) by
      simpa only [rightSafeBlock] using
        flatMap_singleton_eq_map
          (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe) source]
    apply nodup_map_of_injOn
      (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe)
      source hsource
    intro entry1 hentry1 entry2 hentry2 hcode
    exact exceptionalResidualRoutedCarrierCode_injective
      Gamma qP b1 b2 safe entry1 entry2
      (hfacts entry1 hentry1).rightSafe
      (hfacts entry2 hentry2).rightSafe hcode
  · intro code hcode
    rw [show source.flatMap (rightSafeBlock Gamma qP b1 b2 safe) =
      source.map
        (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe) by
      simpa only [rightSafeBlock] using
        flatMap_singleton_eq_map
          (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe) source]
      at hcode
    obtain ⟨entry, hentry, hcodeEq⟩ := List.mem_map.mp hcode
    rw [← hcodeEq]
    exact exceptionalResidualRoutedCarrierCode_mem Gamma qP b1 b2 safe entry
  · intro entry hentry
    have hfacts := hfacts entry hentry
    simp only [rightSafeSourceWeight, rightSafeBlock,
      qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (exceptionalResidualRoutedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label safe entry hfacts.rightSafe
        hfacts.backgroundCompatible hfacts.backgroundQ
        hfacts.backgroundPath hfacts.externalCompatible hfacts.externalQ)
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms rightSafe_region_global_bound

end YMGap.Continuum.XiExceptionalRightSafeSummation
