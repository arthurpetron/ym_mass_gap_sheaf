/-
# The cut-as-start normalization is false

The first parametric occurrence realization stored the cut index as the
carrier start.  This is injective, but it violates the carrier weight: the
start must satisfy the marked predicate `b1`, while a genuine first gap lies
on the long arm.  Hence the carrier weight is identically zero whenever the
cut occurrence is unmarked.

The closed C12 witness below has a nonzero source weight at the vacuum label,
so no `CutOccurrenceWeightNormalization` can inhabit the proposed field.
This is a kernel-checked fence around the incorrect normalization.  The
corrected carrier must keep the marked-to-bad short chain and encode the cut
only in its terminal/external masks.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage
import YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier
open YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

theorem cutOccurrenceCode_weight_zero_of_unmarked
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L))
    (p : CutPattern) (hlen : p.pathLength = Gamma.length)
    (w : Q') (label : L.Plaquette → Rep)
    (hunmarked : b1 (polyAt Gamma p.cut) = false) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
      (cutOccurrenceCode Gamma p hlen) ≈ 0 := by
  unfold occurrenceCarrierXiCodeWeight eraseOccCarrierXiCode
  unfold cutOccurrenceCode eraseOccCarrierCode
  unfold carrierXiCodeWeight carrierCodeWeight
  simp only [hunmarked, Bool.and_false]
  exact Q'.zero_mul_eqv _

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def gapAtFour : CutPattern :=
  ⟨4, List.replicate 7 false⟩

theorem gapAtFour_length : gapAtFour.pathLength = G.length := by rfl

def gapAtFourEntry : ExceptionalSourceEntry G qAll markV0 badV3 :=
  adaptiveEntry false false false false false false false false

def vacuumLabel : TL.Plaquette → Rep := fun _ => 0

theorem gapAtFour_unmarked : markV0 (polyAt G gapAtFour.cut) = false := by
  rfl

theorem gapAtFour_target_weight_zero (w : Q') :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G vacuumLabel
      (cutOccurrenceCode G gapAtFour gapAtFour_length) ≈ 0 :=
  cutOccurrenceCode_weight_zero_of_unmarked qAll markV0 badV3 G
    gapAtFour gapAtFour_length w vacuumLabel gapAtFour_unmarked

theorem gapAtFour_source_weight_one (w : Q') :
    occurrencePairWeight w qAll markV0 badV3 G vacuumLabel
      gapAtFourEntry.1 = 1 := by
  rfl

theorem gapAtFour_target_not_eqv_source (w : Q') :
    ¬ occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G vacuumLabel
        (cutOccurrenceCode G gapAtFour gapAtFour_length) ≈
      occurrencePairWeight w qAll markV0 badV3 G vacuumLabel
        gapAtFourEntry.1 := by
  intro h
  rw [gapAtFour_source_weight_one] at h
  have hzero := gapAtFour_target_weight_zero w
  have hfalse : (0 : Q') ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hzero) h
  exact (by decide : ¬ ((0 : Q') ≈ 1)) hfalse

/-- The geometry-dependent normalization requested by the first occurrence
realization is formally uninhabited, already on the first missing C12 arm
vertex. -/
theorem no_gapAtFour_weight_normalization :
    CutOccurrenceWeightNormalization qAll markV0 badV3 G gapAtFourEntry
      gapAtFour gapAtFour_length → False := by
  intro norm
  exact gapAtFour_target_not_eqv_source 0
    (cutOccurrenceCode_weight_eqv_source norm 0 vacuumLabel)

end YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence.cutOccurrenceCode_weight_zero_of_unmarked
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence.gapAtFour_target_weight_zero
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence.gapAtFour_source_weight_one
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence.gapAtFour_target_not_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence.no_gapAtFour_weight_normalization
