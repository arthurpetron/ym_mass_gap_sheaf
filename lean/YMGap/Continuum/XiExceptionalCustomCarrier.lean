/-
# Branch-sensitive custom exceptional carriers

This file exposes the two finite mask slots of an exceptional path carrier as
inputs.  A chosen terminal background must be admissible and compatible with
every path vertex; a chosen external family only needs its own admissibility.
Under exactly those checkable conditions the target weight factors exactly as
path activity times the two family activities.  Target-block constructions can
therefore move path-incompatible branches from the terminal mask to a suitable
external mask while retaining a positive, derived weight.
-/

import YMGap.Continuum.XiExceptionalTargetBlocks

namespace YMGap.Continuum.XiExceptionalCustomCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalSafeCarrierWeight

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def exceptionalCustomCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background external : OccBitVec Gamma.length) :
    OccCarrierXiCodeAt Gamma :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  { carrier :=
      { start := exceptionalMarkedIndex Gamma b1 b2 pair
        chain := occurrenceChainCodeOfWalk path.indexWalk background }
    external := external }

theorem exceptionalCustomCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background external : OccBitVec Gamma.length) :
    exceptionalCustomCarrierCode Gamma qP b1 b2 entry background external ∈
      occurrenceCarrierXiCodes Gamma := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨external, bitVectors_complete external, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    background external).carrier, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨exceptionalMarkedIndex Gamma b1 b2 pair,
    occurrenceIndices_complete facts.marked_lt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk path.indexWalk background, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background path.indexWalk
    Gamma.length
  · have hlen := path.length_le
    rw [path.polymer_vertices, List.length_map] at hlen
    exact hlen
  · intro k hk
    have hseedN := (forwardSeed_parts Gamma.length
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
      path.seed_true).1
    exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) path.indexWalk hseedN k hk

theorem exceptionalCustomCarrierCode_weight_eqv
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background external : OccBitVec Gamma.length)
    (hbackgroundCompatible :
      familyCompatibleB (selectByBits Gamma background) = true)
    (hbackgroundQ : (selectByBits Gamma background).all qP = true)
    (hbackgroundPath :
      let pair := entry.1
      let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
      let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
      ∀ X, X ∈ path.polymerWalk.vertices →
        ∀ T, T ∈ selectByBits Gamma background →
          compatibleB X T = true)
    (hexternalCompatible :
      familyCompatibleB (selectByBits Gamma external) = true)
    (hexternalQ : (selectByBits Gamma external).all qP = true) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalCustomCarrierCode Gamma qP b1 b2 entry
          background external) ≈
      (path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma background) label) *
        familyActivity w (selectByBits Gamma external) label := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hb2seed : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hmap := sourceExceptionalPath_polymerWalk_eq_map
    Gamma qP b1 b2 pair facts
  have herase := erase_occurrenceChainCodeOfWalk_map Gamma
    (fun _ _ h => disagreementEdge_incAtDistinct Gamma
      (bitMask pair.1) (bitMask pair.2) h)
    path.indexWalk background
  rw [← hmap] at herase
  have hchain : chainCodeWeight w qP b2 Gamma label
      (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair))
      (fun _ => true)
      (eraseOccChainCode Gamma
        (occurrenceChainCodeOfWalk path.indexWalk background)) ≈
      path.polymerWalk.activityWeight w label *
        familyActivity w (selectByBits Gamma background) label := by
    rw [herase]
    apply chainCodeOfWalk_weight_eqv w qP b2 Gamma
      (selectByBits Gamma background) label path.polymerWalk
      (fun _ => true) path.q_true hb2seed hbackgroundCompatible
      hbackgroundQ
    · apply List.all_eq_true.mpr
      intro _ _
      rfl
    · exact hbackgroundPath
  have hexternal : admissibleFamilyWeight w qP label
      (selectByBits Gamma external) =
        familyActivity w (selectByBits Gamma external) label := by
    unfold admissibleFamilyWeight
    rw [hexternalQ, hexternalCompatible]
    rfl
  have hqMarked : qP
      (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair)) = true :=
    facts.right_q _ facts.marked_lt facts.marked_right_true
  change
    carrierCodeWeight w qP b1 b2 Gamma label
        (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair),
          eraseOccChainCode Gamma
            (occurrenceChainCodeOfWalk path.indexWalk background)) *
      admissibleFamilyWeight w qP label (selectByBits Gamma external) ≈
    (path.polymerWalk.activityWeight w label *
      familyActivity w (selectByBits Gamma background) label) *
      familyActivity w (selectByBits Gamma external) label
  unfold carrierCodeWeight
  simp only [hqMarked, facts.marked_b1, Bool.true_and, if_true]
  rw [hexternal]
  exact Q'.mul_eqv_congr_right _ _ _ hchain

#print axioms exceptionalCustomCarrierCode_mem
#print axioms exceptionalCustomCarrierCode_weight_eqv

end YMGap.Continuum.XiExceptionalCustomCarrier
