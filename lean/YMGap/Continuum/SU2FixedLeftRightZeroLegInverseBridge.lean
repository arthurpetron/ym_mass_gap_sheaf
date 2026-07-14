/-
# Inverse ordered-associator normalization on the zero-first-leg family

The forward zero-first-leg ordered F entry is exactly one.  This companion
module closes the inverse Schur row on the same infinite family directly from
the equality of the left and right coordinate functionals and exact recovery
of a fixed-right section.
-/

import YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
import YMGap.Continuum.SU2OrderedRacahZeroLegRawF

namespace YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2OrderedRacahZeroLegFamily
open YMGap.Continuum.SU2OrderedRacahZeroLegKernel
open YMGap.Continuum.SU2OrderedRacahZeroLegRawF
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-- The inverse ordered-associator coefficient is exactly one on every
physical zero-first-leg channel. -/
theorem zero_family_fixedLeftRightDiagonalCoeff_eq_one (b c p : Nat)
    (hp : p ≤ min b c) :
    fixedLeftRightDiagonalCoeff (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) 0 ≈ 1 := by
  let qL := zeroLeftFamily b c p hp
  let qR := zeroRightFamily b c p hp
  let x := fixedRightSection qR (mono 0)
  have hfun := zero_family_coordinate_functionals b c p hp x
  have hright := directRightNestedCoordinates_reconstruct 0 b c
    (fixedRightSectionData qR (mono 0))
    (fixedRightNestedChannel qR 0 (by omega))
  have hone : fixedRightSectionData qR (mono 0)
      (fixedRightNestedChannel qR 0 (by omega)) ≈ 1 := by
    unfold fixedRightSectionData fixedRightNestedChannel qR
    rw [dif_pos]
    · unfold mono
      rw [if_pos rfl]
      exact Q'.eqv_refl 1
    · exact ⟨rfl, rfl⟩
  unfold fixedLeftRightDiagonalCoeff fixedLeftAnalysis
  rw [dif_pos (by omega : 0 ≤ b + c - 2 * p)]
  refine Q'.eqv_trans _ _ _ hfun ?_
  refine Q'.eqv_trans _ _ _ (by
    simpa only [x, fixedRightSection] using hright) hone

/-- The inverse raw square is one on the full zero-first-leg family. -/
theorem zero_family_fixedLeftRightRawKernel_eq_one (b c p : Nat)
    (hp : p ≤ min b c) :
    fixedLeftRightRawKernel (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp) ≈ 1 := by
  have h := zero_family_fixedLeftRightDiagonalCoeff_eq_one b c p hp
  unfold fixedLeftRightRawKernel
  refine Q'.eqv_trans _
    (1 * fixedLeftRightDiagonalCoeff (zeroLeftFamily b c p hp)
      (zeroRightFamily b c p hp) 0) _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  exact Q'.eqv_trans _ (1 * 1) _
    (Q'.mul_eqv_congr_left 1 _ _ h) (Q'.one_mul_eqv 1)

/-- The corrected inverse-row Gram/Racah normalization holds throughout the
zero-first-leg family, not only at the fundamental block. -/
theorem zero_family_inverseSchurGramRacahBridge (b c p : Nat)
    (hp : p ≤ min b c) :
    InverseSchurGramRacahBridgeAt (zeroLeftFamily b c p hp)
      (zeroRightFamily b c p hp) := by
  unfold InverseSchurGramRacahBridgeAt
  have he := (zero_family_intermediates b c p hp).1
  have hf := (zero_family_intermediates b c p hp).2
  rw [he, hf]
  let W := Q'.ofNat (b + c - 2 * p + 1) *
    YMGap.Continuum.SU2TransvectantClosedBinaryGram.binaryRowFactorialProduct b c p
  have hL := (zero_family_closed_factorial_normalization b c p hp).2.1
  have hR := (zero_family_closed_factorial_normalization b c p hp).2.2
  have hP := zero_leg_racahKernel_eq_one b c p hp
  have hK := zero_family_fixedLeftRightRawKernel_eq_one b c p hp
  have hleft :
      triLeftChannelWeight 0 b c (b + c - 2 * p) b *
          racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p) ≈ W := by
    refine Q'.eqv_trans _
      (W * racahKernel6 0 b c (zeroLegD b c p) b (zeroLegD b c p)) _
      (Q'.mul_eqv_congr_right _ _ _ hL) ?_
    exact Q'.eqv_trans _ (W * 1) _
      (Q'.mul_eqv_congr_left W _ _ hP) (Q'.mul_one_eqv W)
  have hright :
      triRightChannelWeight 0 b c (b + c - 2 * p) (b + c - 2 * p) *
          fixedLeftRightRawKernel (zeroLeftFamily b c p hp)
            (zeroRightFamily b c p hp) ≈ W := by
    refine Q'.eqv_trans _
      (W * fixedLeftRightRawKernel (zeroLeftFamily b c p hp)
        (zeroRightFamily b c p hp)) _
      (Q'.mul_eqv_congr_right _ _ _ hR) ?_
    exact Q'.eqv_trans _ (W * 1) _
      (Q'.mul_eqv_congr_left W _ _ hK) (Q'.mul_one_eqv W)
  exact Q'.eqv_trans _ W _ hleft (Q'.eqv_symm hright)

end YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge

#print axioms YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge.zero_family_fixedLeftRightDiagonalCoeff_eq_one
#print axioms YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge.zero_family_fixedLeftRightRawKernel_eq_one
#print axioms YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge.zero_family_inverseSchurGramRacahBridge
