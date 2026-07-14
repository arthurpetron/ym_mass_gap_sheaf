/-
# Closed binary-Gram ratio at the ordered Racah endpoint

The two binary Gram factors of a right-associated channel already contain
the complete endpoint detailed-balance ratio.  This file proves the exact
factorial identity before identifying that closed product with the concrete
three-factor `triRightChannelWeight`.

For the endpoint intermediate labels `f=b+c` and `f-2`, the identity is

`(f-1) G_0 J_+ = (f+1) G_1 R_+`,

where `G_p` is the product of the inner and outer closed binary Grams,
`J_+` is the section-side Jacobi coefficient, and `R_+` is the already
derived raw endpoint coefficient.  The two dimension factors are exactly
those needed when the nested channel weight is `G_p/(rightLabel+1)`.
-/

import YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose

namespace YMGap.Continuum.SU2OrderedRacahEndpointClosedGramRatio

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder
open YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose
open YMGap.Continuum.SU2SignedRacahSquareNormalization
open YMGap.Continuum.TreeGraphBoundProgress

local infix:50 " ≈ " => Q'.eqv

private theorem fact_eq_mul_pred (n : Nat) (hn : 0 < n) :
    fact n = n * fact (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rfl

/-- **All-label closed endpoint detailed balance.**  This is a derived
factorial identity, not an assumed normalization or a finite-label audit. -/
theorem endpoint_closed_binary_gram_ratio
    (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    Q'.ofNat (b + c - 1) *
        ((closedBinaryGram b c (b + c) *
            closedBinaryGram a (b + c) (endpointFinalLabel a b c q)) *
          jacobiForward a b c (endpointFinalLabel a b c q) 0) ≈
      Q'.ofNat (b + c + 1) *
        ((closedBinaryGram b c (b + c - 2) *
            closedBinaryGram a (b + c - 2)
              (endpointFinalLabel a b c q)) *
          rawEndpointForward a b c q) := by
  let f := b + c
  let d := endpointFinalLabel a b c q
  have hf2 : 2 ≤ f := by dsimp only [f]; omega
  have hforward : rightOrderOK a b c d 1 = true := by
    apply (rightOrderOK_spec a b c d 1).2
    constructor
    · dsimp only [f] at hf2
      omega
    · have hlabel : rightLabel b c 1 = f - 2 := by
        unfold rightLabel f
        omega
      rw [hlabel]
      apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
        a (f - 2) d).mpr
      refine ⟨q - 1, by omega, by omega, ?_⟩
      dsimp only [d, endpointFinalLabel, f]
      omega
  have hkbc0 : couplingOrder b c f = 0 := by
    unfold couplingOrder f
    omega
  have hkaf0 : couplingOrder a f d = q := by
    unfold couplingOrder d endpointFinalLabel f
    omega
  have hkbc1 : couplingOrder b c (f - 2) = 1 := by
    unfold couplingOrder f
    omega
  have hkaf1 : couplingOrder a (f - 2) d = q - 1 := by
    unfold couplingOrder d endpointFinalLabel f
    omega
  have houter0 : outerOrder a b c d 0 = q := by
    dsimp only [d]
    unfold outerOrder rightLabel endpointFinalLabel
    omega
  have hforwardNum : forwardNum a b c d 0 = b * c * (f - q) := by
    unfold forwardNum
    dsimp only
    rw [houter0]
    have hlabel : rightLabel b c 0 = f := by
      unfold rightLabel f
      omega
    rw [hlabel]
    simp only [Nat.zero_add, Nat.sub_zero, Nat.one_mul]
  have hforwardDen : forwardDen b c 0 = f * (f - 1) := by
    unfold forwardDen
    dsimp only
    have hlabel : rightLabel b c 0 = f := by
      unfold rightLabel f
      omega
    rw [hlabel]
  have hfa : fact (a + f - q + 1) =
      (a + f - q + 1) * fact (a + f - q) := by
    rw [show a + f - q + 1 = (a + f - q) + 1 by omega]
    rfl
  have hfaq : fact (a - q + 1) = (a - q + 1) * fact (a - q) := by
    rw [show a - q + 1 = (a - q) + 1 by omega]
    rfl
  have hff : fact f = f * (f - 1) * fact (f - 2) := by
    rw [fact_eq_mul_pred f (by omega),
      fact_eq_mul_pred (f - 1) (by omega)]
    ac_rfl
  have hfq : fact (f - q) = (f - q) * fact (f - q - 1) := by
    rw [show f - q = (f - q - 1) + 1 by omega]
    rfl
  have hqf : fact q = q * fact (q - 1) := by
    rw [show q = (q - 1) + 1 by omega]
    rfl
  have hfp1 : fact (f + 1) = (f + 1) * fact f := by
    rfl
  change Q'.ofNat (f - 1) *
        ((closedBinaryGram b c f * closedBinaryGram a f d) *
          jacobiForward a b c d 0) ≈
      Q'.ofNat (f + 1) *
        ((closedBinaryGram b c (f - 2) * closedBinaryGram a (f - 2) d) *
          rawEndpointForward a b c q)
  unfold closedBinaryGram closedBinaryGramNum closedBinaryGramDen
  simp only [hkbc0, hkaf0, hkbc1, hkaf1]
  unfold jacobiForward
  rw [dif_pos hforward]
  unfold rawEndpointForward
  rw [dif_pos (by dsimp only [f] at hf2 ⊢; omega)]
  simp only [hforwardNum, hforwardDen]
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  rw [show fact 0 = 1 by rfl, show fact 1 = 1 by rfl]
  simp only [Nat.mul_one, Nat.sub_zero]
  rw [show b + c + 1 = f + 1 by rfl,
    show b + c - 1 + 1 = f by dsimp only [f]; omega,
    show b + c = f by rfl,
    show a + (f - 2) - (q - 1) + 1 = a + f - q by omega,
    show a - (q - 1) = a - q + 1 by omega,
    show f - 2 - (q - 1) = f - q - 1 by omega]
  rw [fact_eq_mul_pred b hb, fact_eq_mul_pred c hc,
    hfp1, hff, hfa, hfaq, hfq, hqf]
  push_cast
  rw [Int.ofNat_sub hqa,
    Int.ofNat_sub (by omega : q ≤ a + f),
    Int.ofNat_sub (by omega : q ≤ f)]
  have hfcast : (f : Int) = (b : Int) + (c : Int) := by
    dsimp only [f]
    push_cast
    rfl
  rw [← hfcast]
  ac_rfl

end YMGap.Continuum.SU2OrderedRacahEndpointClosedGramRatio

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointClosedGramRatio.endpoint_closed_binary_gram_ratio
