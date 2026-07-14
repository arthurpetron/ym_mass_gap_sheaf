/-
# Gram transpose from raw endpoint action to reconstructed sections

The endpoint coefficient computed on the raw right carrier is the backward
Jacobi coefficient in the neighboring row.  A reconstructed right section is
the Gram-dual basis element, so its forward coefficient is characterized by
the denominator-free transpose equation

`W_p * sectionForward = W_(p+1) * rawForward`.

Strict positivity of `W_p` makes that coefficient unique.  The fundamental
and asymmetric mixed blocks instantiate the equation with the actual
`triRightChannelWeight`s and connect the extracted coefficient to the pinned
`CandidateJacobiAt` endpoint equation.
-/

import YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder

namespace YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose

open YMGap.Constructive
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder

local infix:50 " ≈ " => Q'.eqv

/-- Final label forced by outer contraction order `q` at the raw endpoint. -/
def endpointFinalLabel (a b c q : Nat) : Nat :=
  a + (b + c) - 2 * q

private theorem endpoint_fusionOK (a b c q : Nat)
    (hqa : q ≤ a) (hqf : q ≤ b + c) :
    fusionOK a (b + c) (endpointFinalLabel a b c q) = true := by
  apply (fusionOK_iff_ladder a (b + c) (endpointFinalLabel a b c q)).mpr
  refine ⟨q, hqa, hqf, ?_⟩
  unfold endpointFinalLabel
  omega

/-- **Raw/transpose coefficient identification.**  At every physical
endpoint with a neighboring order-one channel, the raw forward coefficient
is exactly `jacobiBackward` in that neighboring row. -/
theorem rawEndpointForward_eq_jacobiBackward_one
    (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    rawEndpointForward a b c q ≈
      jacobiBackward a b c (endpointFinalLabel a b c q) 1 := by
  let f := b + c
  let d := endpointFinalLabel a b c q
  have hf2 : 2 ≤ f := by dsimp only [f]; omega
  have hfusion : fusionOK a f d = true := by
    simpa only [f, d] using endpoint_fusionOK a b c q hqa (by omega)
  have hright0 : rightOrderOK a b c d 0 = true := by
    apply (rightOrderOK_spec a b c d 0).2
    exact ⟨by omega, hfusion⟩
  have hguard : 0 < (1 : Nat) ∧ rightOrderOK a b c d (1 - 1) = true := by
    simpa only [Nat.one_sub] using And.intro (by omega : 0 < (1 : Nat)) hright0
  have hlabel : rightLabel b c 1 = f - 2 := by
    unfold rightLabel
    omega
  have houter : outerOrder a b c d 1 = q - 1 := by
    dsimp only [outerOrder, rightLabel, d, endpointFinalLabel, f]
    omega
  have hnum : backwardNum a b c d 1 =
      q * (a - q + 1) * (a + f - q + 1) * (f + 1) := by
    unfold backwardNum
    dsimp only
    rw [hlabel, houter]
    rw [show q - 1 + 1 = q by omega,
      show a - (q - 1) = a - q + 1 by omega,
      show a + (f - 2) - (q - 1) + 2 = a + f - q + 1 by omega,
      show b + c - 1 + 2 = f + 1 by dsimp only [f]; omega]
  have hden : backwardDen b c 1 = f * (f + 1) := by
    unfold backwardDen
    dsimp only
    rw [hlabel]
    rw [show f - 2 + 2 = f by omega,
      show f - 2 + 3 = f + 1 by omega]
  unfold rawEndpointForward
  rw [dif_pos (show 0 < b + c by omega)]
  unfold jacobiBackward
  rw [dif_pos (by simpa only [d] using hguard)]
  unfold Q'.eqv
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  rw [hnum, hden]
  dsimp only [f]
  push_cast
  rw [Int.ofNat_sub hqa,
    Int.ofNat_sub (by omega : q ≤ a + (b + c))]
  ac_rfl

/-- Division-free definition of a section-side Gram transpose coefficient. -/
def SectionForwardGramTranspose
    (Wcur Wnext raw sectionForward : Q') : Prop :=
  Wcur * sectionForward ≈ Wnext * raw

/-- Positivity of the current diagonal Gram weight makes the reconstructed
section coefficient unique. -/
theorem sectionForward_unique_of_gram_transpose
    (Wcur Wnext raw x y : Q') (hW : (0 : Q') < Wcur)
    (hx : SectionForwardGramTranspose Wcur Wnext raw x)
    (hy : SectionForwardGramTranspose Wcur Wnext raw y) : x ≈ y := by
  unfold SectionForwardGramTranspose at hx hy
  exact Q'.mul_left_cancel_of_pos hW (Q'.eqv_trans _ _ _ hx (Q'.eqv_symm hy))

/-- If the exact Gram ratio is known for the proposed Jacobi coefficient,
every reconstructed section coefficient satisfying duality equals it. -/
theorem sectionForward_eq_jacobi_of_gram_ratio
    (Wcur Wnext raw jacobi sectionForward : Q')
    (hW : (0 : Q') < Wcur)
    (hsection : SectionForwardGramTranspose Wcur Wnext raw sectionForward)
    (hjacobi : Wcur * jacobi ≈ Wnext * raw) :
    sectionForward ≈ jacobi :=
  sectionForward_unique_of_gram_transpose Wcur Wnext raw sectionForward jacobi
    hW hsection hjacobi

/-- Actual fundamental right-channel Gram weights transpose raw `3/2` to
section-side `1/2`. -/
theorem fundamental_endpoint_gram_ratio :
    triRightChannelWeight 1 1 1 1 2 * jacobiForward 1 1 1 1 0 ≈
      triRightChannelWeight 1 1 1 1 0 * rawEndpointForward 1 1 1 1 := by
  decide

/-- Actual mixed `(2,2,1,1)` right-channel Gram weights transpose raw `8/3`
to section-side `1/3`. -/
theorem mixed221_endpoint_gram_ratio :
    triRightChannelWeight 2 2 1 1 3 * jacobiForward 2 2 1 1 0 ≈
      triRightChannelWeight 2 2 1 1 1 * rawEndpointForward 2 2 1 2 := by
  decide

/-- Any fundamental reconstructed-section coefficient satisfying the actual
Gram-dual equation is forced to be the pinned Jacobi forward coefficient. -/
theorem fundamental_sectionForward_eq_jacobi (sectionForward : Q')
    (hsection : SectionForwardGramTranspose
      (triRightChannelWeight 1 1 1 1 2)
      (triRightChannelWeight 1 1 1 1 0)
      (rawEndpointForward 1 1 1 1) sectionForward) :
    sectionForward ≈ jacobiForward 1 1 1 1 0 := by
  exact sectionForward_eq_jacobi_of_gram_ratio _ _ _ _ _
    (by decide) hsection fundamental_endpoint_gram_ratio

/-- The same dual extraction on the asymmetric mixed block. -/
theorem mixed221_sectionForward_eq_jacobi (sectionForward : Q')
    (hsection : SectionForwardGramTranspose
      (triRightChannelWeight 2 2 1 1 3)
      (triRightChannelWeight 2 2 1 1 1)
      (rawEndpointForward 2 2 1 2) sectionForward) :
    sectionForward ≈ jacobiForward 2 2 1 1 0 := by
  exact sectionForward_eq_jacobi_of_gram_ratio _ _ _ _ _
    (by decide) hsection mixed221_endpoint_gram_ratio

/-- Fundamental endpoint package: raw/backward orientation, exact Gram
transpose, and both signed-candidate endpoint Jacobi equations. -/
theorem fundamental_endpoint_candidate_package :
    rawEndpointForward 1 1 1 1 ≈ jacobiBackward 1 1 1 1 1 ∧
    triRightChannelWeight 1 1 1 1 2 * jacobiForward 1 1 1 1 0 ≈
      triRightChannelWeight 1 1 1 1 0 * rawEndpointForward 1 1 1 1 ∧
    CandidateJacobiAt 1 1 1 1 0 0 ∧
    CandidateJacobiAt 1 1 1 1 2 0 := by
  exact ⟨rawEndpointForward_eq_jacobiBackward_one 1 1 1 1
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fundamental_endpoint_gram_ratio,
    fundamental_candidate_jacobi_audit.1,
    fundamental_candidate_jacobi_audit.2.2.1⟩

/-- Mixed endpoint package with both signed candidate rows. -/
theorem mixed221_endpoint_candidate_package :
    rawEndpointForward 2 2 1 2 ≈ jacobiBackward 2 2 1 1 1 ∧
    triRightChannelWeight 2 2 1 1 3 * jacobiForward 2 2 1 1 0 ≈
      triRightChannelWeight 2 2 1 1 1 * rawEndpointForward 2 2 1 2 ∧
    CandidateJacobiAt 2 2 1 1 0 0 ∧
    CandidateJacobiAt 2 2 1 1 2 0 := by
  exact ⟨rawEndpointForward_eq_jacobiBackward_one 2 2 1 2
      (by omega) (by omega) (by omega) (by omega) (by omega),
    mixed221_endpoint_gram_ratio,
    mixed221_candidate_jacobi_audit.1,
    mixed221_candidate_jacobi_audit.2.2.1⟩

end YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.rawEndpointForward_eq_jacobiBackward_one
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.sectionForward_unique_of_gram_transpose
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.fundamental_endpoint_gram_ratio
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.mixed221_endpoint_gram_ratio
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.fundamental_endpoint_candidate_package
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose.mixed221_endpoint_candidate_package
