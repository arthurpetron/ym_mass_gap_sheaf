/-
# Global injection on the compatible merged-residual region

The path-safe router already retains the only colouring information which the
merged external mask forgets: safe left residual bits stay in the terminal
background, while unsafe left bits and all right bits enter the external
family.  Its only open target-validity field was compatibility of that
external family.

On the region where the complete merged residual union is compatible, this
field is automatic: the routed external family is a subfamily of the merged
union.  The existing source theorem excludes the sole unsafe colouring
collision, so the resulting ordinary carriers are unconditionally injective
across distinct right-residual keys and retain the exact source weight.
-/

import YMGap.Continuum.XiExceptionalMergedResidualCarrier
import YMGap.Continuum.XiExceptionalPathSafeSummation
import YMGap.Continuum.XiPathSafeFactsClosure

namespace YMGap.Continuum.XiExceptionalMergedPathSafeGlobal

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiPathSafeFactsClosure
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalParallelResidualBlock

variable {L : Lattice} [DecidableEq L.Plaquette]

private theorem switchedBranchCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switchedBranchCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem switchedResidualUnion_eq_mergedResidualBits
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    unionBits (residualBits pathBits switched.1)
        (residualBits pathBits switched.2) =
      mergedResidualBits Gamma qP b1 b2 entry := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  change unionBits (residualBits pathBits switched.1)
      (residualBits pathBits switched.2) =
    unionBits (residualBits pathBits pair.1)
      (residualBits pathBits pair.2)
  apply BitVec.ext
  intro i
  by_cases hi : i < Gamma.length
  · rw [unionBits_at, unionBits_at]
    rw [residualBits_at pathBits switched.1 i hi,
      residualBits_at pathBits switched.2 i hi,
      residualBits_at pathBits pair.1 i hi,
      residualBits_at pathBits pair.2 i hi]
    rw [switchedBranchCode_at_left Gamma b2 pair i hi,
      switchedBranchCode_at_right Gamma b2 pair i hi]
    unfold switchedLeft switchedRight swapLeftMask swapRightMask bitMask
    cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
        (fun j => pair.1.at j) (fun j => pair.2.at j)
        (predAt Gamma b2) i <;>
      cases hp : pathBits.at i <;>
      cases hl : pair.1.at i <;> cases hr : pair.2.at i <;> rfl
  · have hge : Gamma.length ≤ i := by omega
    exact (bitVec_at_false_of_ge
      (unionBits (residualBits pathBits switched.1)
        (residualBits pathBits switched.2)) i hge).trans
      (bitVec_at_false_of_ge
        (unionBits (residualBits pathBits pair.1)
          (residualBits pathBits pair.2)) i hge).symm

/-! ## The routed external mask is contained in the merged mask -/

theorem routedExternal_select_sublist_unionBits
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) :
    (selectByBits Gamma (routedExternal safe left right)).Sublist
      (selectByBits Gamma (unionBits left right)) := by
  rw [← maskFamily_toMask_eq_selectByBits]
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_sublist_of_submask
  intro i hext
  by_cases hi : i < Gamma.length
  · change (routedExternal safe left right).at i = true at hext
    change (unionBits left right).at i = true
    rw [routedExternal_at safe left right i hi] at hext
    rw [unionBits_at]
    cases hs : safe i <;> cases hl : left.at i <;>
      cases hr : right.at i <;> simp_all
  · have hge : Gamma.length ≤ i := by omega
    change (routedExternal safe left right).at i = true at hext
    rw [bitVec_at_false_of_ge (routedExternal safe left right) i hge] at hext
    cases hext

/-! ## The missing path-safe fact follows from merged compatibility -/

def pathSafe_externalCompatible_of_merged
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hmerged : familyCompatibleB
      (selectByBits Gamma (mergedResidualBits Gamma qP b1 b2 entry)) = true) :
    PathSafeExternalCompatibility Gamma qP b1 b2 entry := by
  refine ⟨?_⟩
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let left := residualBits pathBits switched.1
  let right := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  have hsub :
      (selectByBits Gamma (routedExternal safe left right)).Sublist
        (selectByBits Gamma (unionBits left right)) :=
    routedExternal_select_sublist_unionBits Gamma safe left right
  apply familyCompatibleB_of_sublist hsub
  rw [switchedResidualUnion_eq_mergedResidualBits
    Gamma qP b1 b2 entry]
  exact hmerged

def mergedCompatiblePathSafeFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hmerged : familyCompatibleB
      (selectByBits Gamma (mergedResidualBits Gamma qP b1 b2 entry)) = true) :
    PathSafeRoutedFacts Gamma qP b1 b2 entry :=
  pathSafeRoutedFactsOfExternalCompatibility Gamma qP b1 b2 entry
    (pathSafe_externalCompatible_of_merged Gamma qP b1 b2 entry hmerged)

/-! ## Cross-key global summation -/

/-- Every duplicate-free source region with compatible merged residuals is
paid by distinct ordinary occurrence carriers.  No right-residual fibre key
or disjointness premise is needed. -/
theorem mergedCompatible_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hmerged : ∀ entry, entry ∈ source → familyCompatibleB
      (selectByBits Gamma
        (mergedResidualBits Gamma qP b1 b2 entry)) = true) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply pathSafe_region_global_bound hw Gamma qP b1 b2 label source hsource
  intro entry hentry
  exact mergedCompatiblePathSafeFacts Gamma qP b1 b2 entry
    (hmerged entry hentry)

#print axioms routedExternal_select_sublist_unionBits
#print axioms switchedResidualUnion_eq_mergedResidualBits
#print axioms pathSafe_externalCompatible_of_merged
#print axioms mergedCompatiblePathSafeFacts
#print axioms mergedCompatible_region_global_bound

end YMGap.Continuum.XiExceptionalMergedPathSafeGlobal
