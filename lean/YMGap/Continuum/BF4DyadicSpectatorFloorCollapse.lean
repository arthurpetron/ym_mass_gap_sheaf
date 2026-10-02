/-
# Collapse of the existing certified dyadic spectator floor

The ACTUAL explicit squareResponseFraction is at most 1/1024, uniformly
over every strict nome. Its side-length power is at most the assigned
dyadic spacing, with the existing computable epsilon.den modulus, even
along an arbitrary strict nome schedule.

This bounds ONLY the certified lower-bound coefficient. It does not upper
bound the actual Wilson response, prove that response vanishes, or refute
physical survival. It rules out THIS coefficient as a standalone positive
scale-uniform survival floor; better same-state estimates remain open.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse

namespace YMGap.Continuum.BF4DyadicSpectatorFloorCollapse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
  (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
  (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse

private theorem qpow_rg (w : Q') : ∀ n, qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun x : Q' => x*w) (qpow_rg w n)

private theorem one_le_pow (r : Q') (hr : (1 : Q') ≤ r) :
    ∀ n : Nat, (1 : Q') ≤ r^n
  | 0 => Q'.le_refl' _
  | n+1 => by
      have hr0 := Q'.le_trans' _ _ _ Q'.zero_le_one hr
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hr
        (Q'.pow_nonneg r hr0 n)
      exact Q'.le_trans' _ _ _ (one_le_pow r hr n)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hm)

private theorem succ_le_two_pow : ∀ n : Nat, n+1 ≤ 2^n
  | 0 => by decide
  | n+1 => by
      have h := Nat.mul_le_mul_left 2 (succ_le_two_pow n)
      have hs : n+2 ≤ 2*(n+1) := by omega
      simpa only [Nat.pow_succ, Nat.mul_comm] using Nat.le_trans hs h

/-- Uniform ceiling on the existing coefficient, NOT on actual response. -/
theorem squareResponseFraction_le_one1024 {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    squareResponseFraction hw0 hw1 scale ≤ Q'.mkPos 1 1024 (by decide) := by
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  let c := Q'.mkPos 1 32 (by decide)
  let d := Q'.mkPos 1 1024 (by decide)
  have hl0 : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hhead := headFloor_le_oneThirtySecond hw0 hw1
  have hl : l ≤ c := by
    have hp := HKConvGen.pow_base_antitone
      (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (Q'.le_trans' _ _ _ hhead (by decide : c ≤ (1 : Q')))
      (m := 1) (n := 7*(4*side scale))
      (by have hs := side_positive scale; omega)
    exact Q'.le_trans' _ _ _ hp
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv (headFloor w))) hhead)
  have hll : l*l ≤ d := Q'.le_trans' _ _ _
    (HKConv.mul_le_mul' hl0 (by decide : (0 : Q') ≤ c) hl hl) (by decide)
  have hu : (1 : Q') ≤ u := one_le_pow (prefixCap w) (prefixCap_ge_one hw0 hw1) _
  have hU : (1 : Q') ≤ u*u := Q'.le_trans' _ _ _
    (by decide : (1 : Q') ≤ (1 : Q')*1)
    (HKConv.mul_le_mul' Q'.zero_le_one
      (Q'.le_of_lt (localUpper_positive hw0 hw1 _)) hu hu)
  have ha : qpow w (12*side scale) ≤ (1 : Q') := by
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  have hnum : qpow w (12*side scale)*(l*l) ≤ d := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.mul_nonneg l l hl0 hl0))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hll)
  let hUp := Q'.mul_pos (localUpper_positive hw0 hw1 (4*side scale))
    (localUpper_positive hw0 hw1 (4*side scale))
  let r := Q'.recipPos (u*u) hUp
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hr1 : r ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv r))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ r hU hr0)
      (Q'.le_of_eqv (Q'.mul_recipPos_eqv (u*u) hUp)))
  change (qpow w (12*side scale)*(l*l))*r ≤ d
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ r hnum hr0)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ d hr1 (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv d)))

theorem squareResponseFraction_le_half {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    squareResponseFraction hw0 hw1 scale ≤ half :=
  Q'.le_trans' _ _ _ (squareResponseFraction_le_one1024 hw0 hw1 scale) (by decide)

/-- The certified side-lag coefficient is bounded by the actual assigned
spacing. This is not a response upper bound. -/
theorem squareResponseFraction_side_le_spacing {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    (squareResponseFraction hw0 hw1 scale)^(side scale) ≤ spacing scale := by
  have hs : scale ≤ side scale :=
    Nat.le_trans (Nat.le_succ scale) (succ_le_two_pow scale)
  exact Q'.le_trans' _ _ _
    (HKConv.pow_le_pow_base (Q'.le_of_lt (squareResponseFraction_positive hw0 hw1 scale))
      (squareResponseFraction_le_half hw0 hw1 scale) (side scale))
    (HKConvGen.pow_base_antitone half_nonneg (by decide) hs)

/-- Explicit coupling-uniform modulus epsilon.den, with no assumption on
how the nome changes with scale. -/
theorem squareResponseFraction_side_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (scale : Nat)
    (hscale : epsilon.den ≤ scale) :
    (squareResponseFraction hw0 hw1 scale)^(side scale) ≤ epsilon :=
  Q'.le_trans' _ _ _ (squareResponseFraction_side_le_spacing hw0 hw1 scale)
    (spacing_small epsilon he scale hscale)

theorem scheduled_squareResponseFraction_side_small (w : Nat → Q')
    (hw0 : ∀ scale, (0 : Q') < w scale) (hw1 : ∀ scale, w scale < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (scale : Nat)
    (hscale : epsilon.den ≤ scale) :
    (squareResponseFraction (hw0 scale) (hw1 scale) scale)^(side scale) ≤ epsilon :=
  squareResponseFraction_side_small (hw0 scale) (hw1 scale) epsilon he scale hscale

/-- No positive fixed rational can be below all THESE certified coefficients
along any strict nome schedule. No statement about actual response follows. -/
theorem not_uniform_certified_floor (w : Nat → Q')
    (hw0 : ∀ scale, (0 : Q') < w scale) (hw1 : ∀ scale, w scale < (1 : Q'))
    (delta : Q') (hd : (0 : Q') < delta) :
    ¬ (∀ scale, delta ≤
      (squareResponseFraction (hw0 scale) (hw1 scale) scale)^(side scale)) := by
  intro hfloor
  let epsilon := half*delta
  have he : (0 : Q') < epsilon := ExpNeg.half_mul_pos delta hd
  have hsmall := scheduled_squareResponseFraction_side_small w hw0 hw1
    epsilon he epsilon.den (Nat.le_refl _)
  have h : delta ≤ half*delta := Q'.le_trans' _ _ _ (hfloor epsilon.den) hsmall
  have hnum : (0 : Int) < delta.num := CReal.num_pos_of_pos hd
  have hden : (0 : Int) < (delta.den : Int) := by exact_mod_cast delta.den_pos
  have hprod := Int.mul_pos hnum hden
  have hh : delta.num*((half*delta).den : Int) ≤
      (half*delta).num*(delta.den : Int) := h
  rw [Q'.mul_den_cast] at hh
  change delta.num*((2 : Int)*(delta.den : Int)) ≤
    ((1 : Int)*delta.num)*(delta.den : Int) at hh
  simp only [Int.one_mul] at hh
  rw [← Int.mul_assoc, Int.mul_comm delta.num (2 : Int), Int.mul_assoc] at hh
  omega

private theorem certified_responseFloor_le_fraction {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    (squareResponseFraction hw0 hw1 scale)^(side scale)*starRatio w ≤
      (squareResponseFraction hw0 hw1 scale)^(side scale) := by
  have hstar : starRatio w ≤ (1 : Q') := Q'.le_trans' _ _ _
    (BF4ExactSlabStarRateObstruction.starRatio_le_oneSixtyFourth hw0 hw1) (by decide)
  have hp := Q'.pow_nonneg _
    (Q'.le_of_lt (squareResponseFraction_positive hw0 hw1 scale)) (side scale)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hstar hp)
    (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- The FULL rational floor printed by the original completed response
theorem has the same explicit uniform modulus. Still no response upper bound. -/
theorem scheduled_responseFloor_side_small (w : Nat → Q')
    (hw0 : ∀ scale, (0 : Q') < w scale) (hw1 : ∀ scale, w scale < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (scale : Nat)
    (hscale : epsilon.den ≤ scale) :
    (squareResponseFraction (hw0 scale) (hw1 scale) scale)^(side scale)*
      starRatio (w scale) ≤ epsilon :=
  Q'.le_trans' _ _ _
    (certified_responseFloor_le_fraction (hw0 scale) (hw1 scale) scale)
    (scheduled_squareResponseFraction_side_small w hw0 hw1 epsilon he scale hscale)

/-- A positive all-scale lower floor cannot be obtained from the FULL
existing rational certificate. This does not refute actual continuum survival. -/
theorem not_uniform_response_floor (w : Nat → Q')
    (hw0 : ∀ scale, (0 : Q') < w scale) (hw1 : ∀ scale, w scale < (1 : Q'))
    (delta : Q') (hd : (0 : Q') < delta) :
    ¬ (∀ scale, delta ≤
      (squareResponseFraction (hw0 scale) (hw1 scale) scale)^(side scale)*
        starRatio (w scale)) := by
  intro hfloor
  apply not_uniform_certified_floor w hw0 hw1 delta hd
  intro scale
  exact Q'.le_trans' _ _ _ (hfloor scale)
    (certified_responseFloor_le_fraction (hw0 scale) (hw1 scale) scale)

#print axioms squareResponseFraction_le_one1024
#print axioms squareResponseFraction_le_half
#print axioms squareResponseFraction_side_le_spacing
#print axioms squareResponseFraction_side_small
#print axioms scheduled_squareResponseFraction_side_small
#print axioms not_uniform_certified_floor
#print axioms scheduled_responseFloor_side_small
#print axioms not_uniform_response_floor

end YMGap.Continuum.BF4DyadicSpectatorFloorCollapse
