/-
# Positive half-amplitude certificate for the translated cutoff-two cell

The positive transported physical term and its exact Gram factorization force
the concrete lower half-amplitude to be strictly positive.  This file isolates
that large concrete proposition behind an opaque compiled theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakageRowCertificate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem q_right_pos_of_mul_pos_local
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

theorem translatedSingleFaceLowerAmplitude_pos :
    (0 : Q') <
      centralHalfAmplitude cutoffTwoHalfCoupling 2 1
        translatedSingleFaceLower translatedSingleFaceBoundary := by
  have hgram := centralPhysicalTerm_eq_gram_integrand
    cutoffTwoHalfCoupling translatedSingleFaceLower_mem
    translatedSingleFaceBoundary_mem translatedSingleFaceUpper_mem
  rw [translatedSingleFace_assemble] at hgram
  have hproduct :
      (0 : Q') <
        centralBoundaryWeight cutoffTwoHalfCoupling 2 1
            translatedSingleFaceBoundary *
          (centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceLower translatedSingleFaceBoundary *
            centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceUpper translatedSingleFaceBoundary) :=
    Q'.pos_of_lt_of_le translatedSingleFaceTerm_pos
      (Q'.le_of_eqv hgram)
  have hampProduct :
      (0 : Q') <
        centralHalfAmplitude cutoffTwoHalfCoupling 2 1
            translatedSingleFaceLower translatedSingleFaceBoundary *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 1
            translatedSingleFaceUpper translatedSingleFaceBoundary :=
    q_right_pos_of_mul_pos_local
      (centralBoundaryWeight_nonnegative_on
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        translatedSingleFaceBoundary translatedSingleFaceBoundary_mem)
      hproduct
  exact q_left_pos_of_mul_pos_local
    (centralHalfAmplitude_nonnegative
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 1 translatedSingleFaceUpper translatedSingleFaceBoundary)
    hampProduct

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceLowerAmplitude_pos
