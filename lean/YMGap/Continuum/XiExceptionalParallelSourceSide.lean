/-
# Parallel external families inherited from one source side

The external-family allocator asks only for compatibility and q-admissibility
of the chosen parallel children.  For an actual exceptional source these are
not new assumptions: any occurrence submask of either admissible source side
inherits both properties.  Thus a parallel branch family can be moved to the
external carrier while the canonical articulation path remains counted once.
-/

import YMGap.Continuum.XiExceptionalParallelExternalFamily

namespace YMGap.Continuum.XiExceptionalParallelSourceSide

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalParallelExternalFamily

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- Occurrence submasks select a genuine list subfamily, even when `Gamma`
contains repeated polymer values. -/
theorem selectByBits_sublist_of_submask
    (Gamma : List (Polymer L))
    (small big : OccBitVec Gamma.length)
    (hsub : ∀ i, small.at i = true → big.at i = true) :
    (selectByBits Gamma small).Sublist (selectByBits Gamma big) := by
  rw [← maskFamily_toMask_eq_selectByBits]
  rw [← maskFamily_toMask_eq_selectByBits]
  exact maskFamily_sublist_of_submask Gamma (bitMask small) (bitMask big)
    (fun i hi => hsub i hi)

/-- Compatibility is inherited by every occurrence submask. -/
theorem selectByBits_compatible_of_submask
    (Gamma : List (Polymer L))
    (small big : OccBitVec Gamma.length)
    (hsub : ∀ i, small.at i = true → big.at i = true)
    (hbig : familyCompatibleB (selectByBits Gamma big) = true) :
    familyCompatibleB (selectByBits Gamma small) = true :=
  familyCompatibleB_of_sublist
    (selectByBits_sublist_of_submask Gamma small big hsub) hbig

/-- Pointwise q-admissibility is inherited by every occurrence submask. -/
theorem selectByBits_all_of_submask
    (Gamma : List (Polymer L)) (qP : Polymer L → Bool)
    (small big : OccBitVec Gamma.length)
    (hsub : ∀ i, small.at i = true → big.at i = true)
    (hbigQ : ∀ i, i < Gamma.length → big.at i = true →
      qP (polyAt Gamma i) = true) :
    (selectByBits Gamma small).all qP = true := by
  rw [← maskFamily_toMask_eq_selectByBits]
  exact maskFamily_all_of_pointwise Gamma (bitMask small) qP
    (fun i hi hsmall => hbigQ i hi (hsub i hsmall))

theorem exceptional_left_submask_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.1.at i = true) :
    familyCompatibleB (selectByBits Gamma external) = true := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  exact selectByBits_compatible_of_submask Gamma external entry.1.1 hsub
    facts.left_family_compatible

theorem exceptional_right_submask_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.2.at i = true) :
    familyCompatibleB (selectByBits Gamma external) = true := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  exact selectByBits_compatible_of_submask Gamma external entry.1.2 hsub
    facts.right_family_compatible

theorem exceptional_left_submask_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.1.at i = true) :
    (selectByBits Gamma external).all qP = true := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  exact selectByBits_all_of_submask Gamma qP external entry.1.1 hsub facts.left_q

theorem exceptional_right_submask_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.2.at i = true) :
    (selectByBits Gamma external).all qP = true := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  exact selectByBits_all_of_submask Gamma qP external entry.1.2 hsub facts.right_q

/-- An external submask of the left source side has the exact carrier
factorization without any added compatibility or q premise. -/
theorem parallelExternalCarrierCode_weight_eqv_of_left_submask
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.1.at i = true) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  exact parallelExternalCarrierCode_weight_eqv w qP b1 b2 Gamma label
    entry external
    (exceptional_left_submask_compatible Gamma qP b1 b2 entry external hsub)
    (exceptional_left_submask_q Gamma qP b1 b2 entry external hsub)

/-- An external submask of the right source side has the exact carrier
factorization without any added compatibility or q premise. -/
theorem parallelExternalCarrierCode_weight_eqv_of_right_submask
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (hsub : ∀ i, external.at i = true → entry.1.2.at i = true) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry external) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma external) label := by
  exact parallelExternalCarrierCode_weight_eqv w qP b1 b2 Gamma label
    entry external
    (exceptional_right_submask_compatible Gamma qP b1 b2 entry external hsub)
    (exceptional_right_submask_q Gamma qP b1 b2 entry external hsub)

/-- The allocation is an actual target occurrence code, independently of
which admissible side supplies the external submask. -/
theorem parallelExternalCarrierCode_mem_of_right_submask
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (external : OccBitVec Gamma.length)
    (_hsub : ∀ i, external.at i = true → entry.1.2.at i = true) :
    parallelExternalCarrierCode Gamma qP b1 b2 entry external ∈
      occurrenceCarrierXiCodes Gamma :=
  parallelExternalCarrierCode_mem Gamma qP b1 b2 entry external

#print axioms selectByBits_sublist_of_submask
#print axioms selectByBits_compatible_of_submask
#print axioms selectByBits_all_of_submask
#print axioms exceptional_left_submask_compatible
#print axioms exceptional_right_submask_compatible
#print axioms exceptional_left_submask_q
#print axioms exceptional_right_submask_q
#print axioms parallelExternalCarrierCode_weight_eqv_of_left_submask
#print axioms parallelExternalCarrierCode_weight_eqv_of_right_submask
#print axioms parallelExternalCarrierCode_mem_of_right_submask

end YMGap.Continuum.XiExceptionalParallelSourceSide
