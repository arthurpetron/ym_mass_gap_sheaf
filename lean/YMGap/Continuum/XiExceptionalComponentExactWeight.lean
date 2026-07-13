/-
# Exact weight of the residual-component carrier

On the right-safe component branch, the source pair factors into the decoded
path activity and the two residual family activities.  Residual-component
switching is an exact occurrence swap, so the corrected compatible target
has exactly the source weight.
-/

import YMGap.Continuum.XiExceptionalComponentCarrier

namespace YMGap.Continuum.XiExceptionalComponentExactWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathBitWeight
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalComponentRouter
open YMGap.Continuum.XiExceptionalComponentCarrier

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

private theorem residual_maskWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path bits : OccBitVec Gamma.length) :
    maskWeight w Gamma label (bitMask (residualBits path bits)) =
      maskWeight w Gamma label
        (residualMask (bitMask path) (bitMask bits)) := by
  apply maskWeight_congr_on
  intro i hi
  change (residualBits path bits).at i =
    residualMask (bitMask path) (bitMask bits) i
  rw [residualBits_at path bits i hi]
  rfl

private theorem switchedCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switchedCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem exceptionalComponentCarrierCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightSafe : componentRightSafe Gamma qP b1 b2 entry) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalComponentCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  let background := componentBackground Gamma safe leftResidual rightResidual
  let external := componentExternal Gamma safe leftResidual rightResidual
  let targetFacts := componentCarrierFacts_of_rightSafe Gamma qP b1 b2 entry
    hrightSafe
  have hcustom := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry background external
    targetFacts.backgroundCompatible targetFacts.backgroundQ
    targetFacts.backgroundPath targetFacts.externalCompatible
    targetFacts.externalQ
  dsimp only at hcustom
  have hsourceEq := occurrencePairWeight_eq_source_activity_of_mem
    w qP b1 b2 Gamma label pair entry.2
  have hleftOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.1)
  have hrightOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.2)
  rw [maskFamily_toMask_eq_selectByBits] at hleftOriginal hrightOriginal
  have hsourceToOriginal :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hsourceEq)
      (mul_eqv_congr_both (Q'.eqv_symm hleftOriginal)
        (Q'.eqv_symm hrightOriginal))
  have hswitchedLeft :
      maskWeight w Gamma label (bitMask switched.1) =
        maskWeight w Gamma label
          (switchedLeft Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_left Gamma b2 pair i hi
  have hswitchedRight :
      maskWeight w Gamma label (bitMask switched.2) =
        maskWeight w Gamma label
          (switchedRight Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_right Gamma b2 pair i hi
  have hswitch :
      maskWeight w Gamma label (bitMask switched.1) *
          maskWeight w Gamma label (bitMask switched.2) ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) := by
    rw [hswitchedLeft, hswitchedRight]
    exact maskWeight_swap_preserved w Gamma label
      (forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      (bitMask pair.1) (bitMask pair.2)
  have hpartition := maskWeight_path_partition w Gamma label
    (bitMask pathBits) (bitMask switched.1) (bitMask switched.2)
    (exceptional_pathBits_switched_exclusive Gamma qP b1 b2 entry)
  have hleftResidualEq := residual_maskWeight_eq w Gamma label
    pathBits switched.1
  have hrightResidualEq := residual_maskWeight_eq w Gamma label
    pathBits switched.2
  rw [← hleftResidualEq, ← hrightResidualEq] at hpartition
  have hpath := pathOccurrenceMaskWeight_eqv_walk w Gamma label path
  have hleftResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask leftResidual)
  have hrightResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask rightResidual)
  rw [maskFamily_toMask_eq_selectByBits] at hleftResidual hrightResidual
  have hcomponent := component_familyActivity_preserved w Gamma label safe
    leftResidual rightResidual
  have hsourceToFactor :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        (path.polymerWalk.activityWeight w label *
          familyActivity w (selectByBits Gamma background) label) *
          familyActivity w (selectByBits Gamma external) label := by
    refine Q'.eqv_trans _ _ _ hsourceToOriginal ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hswitch) ?_
    refine Q'.eqv_trans _ _ _ hpartition ?_
    refine Q'.eqv_trans _ _ _
      (mul_eqv_congr_both hpath
        (mul_eqv_congr_both hleftResidual hrightResidual)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcomponent)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  change occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
    (exceptionalCustomCarrierCode Gamma qP b1 b2 entry background external) ≈
      occurrencePairWeight w qP b1 b2 Gamma label pair
  exact Q'.eqv_trans _ _ _ hcustom (Q'.eqv_symm hsourceToFactor)

#print axioms exceptionalComponentCarrierCode_weight_eqv_source

end YMGap.Continuum.XiExceptionalComponentExactWeight
