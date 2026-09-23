/-
# A relative SU(2) heat-coefficient tail at every subunit nome

Hankel log-concavity factors a shifted heat coefficient through its first
coefficient.  The existing explicit degree-thirteen face envelope then sums
the remaining factor, uniformly in the finite truncation.  Thus every
positive subunit nome has an explicit rational relative-tail constant.

This is a one-dimensional coefficient estimate.  It does not assert a BF4
operator gap, a coupling-uniform constant as `w -> 1`, or a continuum claim.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.FusionCoreStep
import YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope

namespace YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope

local infix:50 " ≈ " => Q'.eqv

/-- An explicit cutoff-independent relative-tail constant at fixed nome. -/
def relativeHeatTailCeiling (w : Q') : Q' :=
  1 + explicitFixedNomeDecoratedFaceCeiling w

theorem relativeHeatTailCeiling_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < relativeHeatTailCeiling w := by
  unfold relativeHeatTailCeiling
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 _
      (explicitFixedNomeDecoratedFaceCeiling_nonnegative hw0))

private theorem coeffW_zero_eqv_one (w : Q') : coeffW w 0 ≈ 1 := by
  exact Q'.eqv_of_eq (coeffW_zero w)

private theorem coeffW_le_decorated
    {w : Q'} (hw0 : (0 : Q') ≤ w) (spin : Nat) :
    coeffW w spin ≤ fixedNomeDecoratedFaceActivity w spin := by
  rw [coeffW_eq_tailTerm]
  unfold tailTerm fixedNomeDecoratedFaceActivity
  apply Q'.mul_le_mul_of_nonneg_right
  · exact CReal.ofNat_le_ofNat
      (Nat.pow_le_pow_right (by omega : 1 ≤ spin + 1) (by omega : 1 ≤ 13))
  · exact qpow_nonneg w hw0 (c4 spin)

private theorem fsum_coeffW_eqv_one_add_plaqActivity
    (w : Q') : ∀ count : Nat,
    fsum (coeffW w) (count + 1) ≈
      1 + finSum (fun offset => coeffW w (1 + offset)) count
  | 0 => by
      simp only [fsum_succ, fsum_zero, Q'.zero_add', finSum_zero,
        Q'.add_zero']
      exact coeffW_zero_eqv_one w
  | count + 1 => by
      rw [fsum_succ, finSum_succ]
      refine Q'.eqv_trans _
        ((1 + finSum (fun offset => coeffW w (1 + offset)) count) +
          coeffW w (count + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (fsum_coeffW_eqv_one_add_plaqActivity w count)
      · simpa only [Nat.one_add] using
          Q'.add_assoc_eqv 1
            (finSum (fun offset => coeffW w (1 + offset)) count)
            (coeffW w (count + 1))

private theorem plaqActivity_le_explicitDecoratedCeiling
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (count : Nat) :
    plaqActivity w count ≤ explicitFixedNomeDecoratedFaceCeiling w := by
  have hterms : ∀ offset,
      coeffW w (1 + offset) ≤ fixedNomeDecoratedFaceActivity w (1 + offset) :=
    fun offset => coeffW_le_decorated (Q'.le_of_lt hw0) (1 + offset)
  have hsum : plaqActivity w count ≤ fixedNomeDecoratedPlaqActivity w count := by
    unfold plaqActivity fixedNomeDecoratedPlaqActivity
    induction count with
    | zero => exact Q'.le_refl' 0
    | succ count ih =>
        rw [finSum_succ, finSum_succ]
        exact Q'.add_le_add ih (hterms count)
  exact Q'.le_trans' _ _ _ hsum
    (fixedNomeDecoratedPlaqActivity_le_explicitCeiling hw0 hw1 count)

private theorem fsum_coeffW_le_relativeConstant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ count : Nat,
      fsum (coeffW w) count ≤ relativeHeatTailCeiling w
  | 0 => by
      exact Q'.le_of_lt (relativeHeatTailCeiling_pos hw0)
  | count + 1 => by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (fsum_coeffW_eqv_one_add_plaqActivity w count))
        (Q'.add_le_add_left 1 _ _
          (by simpa only [plaqActivity] using
            plaqActivity_le_explicitDecoratedCeiling hw0 hw1 count))

private theorem fsum_eqv_zero_of_terms_zero
    (value : Nat → Q') : ∀ count : Nat,
    (∀ index, index < count → value index = 0) → fsum value count ≈ 0
  | 0, _ => Q'.eqv_refl 0
  | count + 1, hzero => by
      rw [fsum_succ, hzero count (by omega)]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ 0
          (fsum_eqv_zero_of_terms_zero value count
            (fun index hindex => hzero index (by omega))))
        (Q'.eqv_of_eq (Q'.add_zero' 0))

private theorem maskedTail_eqv_shifted
    (value : Nat → Q') (base : Nat) : ∀ extra : Nat,
    fsum (fun spin => if base ≤ spin then value spin else 0) (base + extra) ≈
      fsum (fun offset => value (base + offset)) extra
  | 0 => by
      exact fsum_eqv_zero_of_terms_zero _ base (fun index hindex => by
        rw [if_neg (by omega : ¬ base ≤ index)])
  | extra + 1 => by
      rw [Nat.add_succ, fsum_succ, if_pos (by omega : base ≤ base + extra),
        fsum_succ]
      exact Q'.add_eqv_congr_right _ _ _ (maskedTail_eqv_shifted value base extra)

private theorem shifted_coeffW_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base offset : Nat) :
    coeffW w (base + offset) ≤ coeffW w base * coeffW w offset := by
  have h := coeffW_rect (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hw0 offset base 0
  have hz := coeffW_zero_eqv_one w
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right 1 (coeffW w 0)
        (coeffW w (base + offset)) (Q'.eqv_symm hz)))
      (by simpa only [Nat.zero_add, Nat.add_zero] using h))

private theorem shiftedTail_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base : Nat) : ∀ count : Nat,
    fsum (fun offset => coeffW w (base + offset)) count ≤
      coeffW w base * fsum (coeffW w) count
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | count + 1 => by
      rw [fsum_succ, fsum_succ]
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add (shiftedTail_le hw0 hw1 base count)
          (shifted_coeffW_le hw0 hw1 base count))
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.mul_add_eqv (coeffW w base) _ _)))

/-- Every finite coefficient tail above `base` is bounded by one explicit
nome-dependent multiple of its first coefficient. -/
theorem coeffW_tail_le_relativeCeiling
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base count : Nat) :
    fsum (fun spin => if base ≤ spin then coeffW w spin else 0) count ≤
      relativeHeatTailCeiling w * coeffW w base := by
  by_cases hcount : count ≤ base
  · have hzero : ∀ spin, spin < count →
        (if base ≤ spin then coeffW w spin else 0) = 0 := by
      intro spin hspin
      rw [if_neg (by omega)]
    have hs : fsum (fun spin => if base ≤ spin then coeffW w spin else 0) count ≈ 0 :=
      fsum_eqv_zero_of_terms_zero _ count hzero
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hs)
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt (relativeHeatTailCeiling_pos hw0))
        (coeffW_nonneg (Q'.le_of_lt hw0) base))
  · let extra := count - base
    have hsum : base + extra = count := by
      unfold extra
      omega
    have hreindex := maskedTail_eqv_shifted (coeffW w) base extra
    rw [hsum] at hreindex
    have hshift := shiftedTail_le hw0 hw1 base extra
    have htotal := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w base)
      (fsum_coeffW_le_relativeConstant hw0 hw1 extra)
      (coeffW_nonneg (Q'.le_of_lt hw0) base)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreindex)
      (Q'.le_trans' _ _ _ hshift
        (Q'.le_trans' _ _ _ htotal
          (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

end YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail

#print axioms YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail.relativeHeatTailCeiling
#print axioms YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail.relativeHeatTailCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail.coeffW_tail_le_relativeCeiling
