/-
# Generic finite-row normalization certificate for ordered SU(2) recoupling

A denominator-free polynomial identity becomes physical normalization data
once it is lifted to a finite row of proof-carrying right channels.  This file
packages exactly that interface.  The all-label Casimir Gram law collapses the
row at a selected channel, and positivity of the selected Gram weight then
extracts the corresponding inverse Schur coefficient.

No Racah square or factorial/Racah compatibility statement is assumed.  A
future arbitrary-label instance supplies only its finite physical row, its
duplicate-free selected index, and elementary exact-rational factorisations.
-/

import YMGap.Continuum.SU2OrderedRacahCasimirCapstone

namespace YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRacahCasimirCapstone
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem mul_swap_nested (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  exact Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ ((b * a) * c) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- A finite denominator-free recoupling row with one selected physical right
channel.  The only substantive field is `row`; `target_onehot` is finite
duplicate-free bookkeeping on contraction orders. -/
structure FiniteRightRowCertificate {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) where
  N : Nat
  target : Nat
  channel : Nat → FixedRightCGChannel a b c d
  coeff : Nat → Q'
  scale : Q'
  target_lt : target < N
  target_onehot : ∀ q, q < N → ((channel q).p = qR.p ↔ q = target)
  row : TriMapEqv a b c d
    (fun x y z => scaleForm scale
      (triLeft a b c d qL.intermediate x y z))
    (rightChannelPrefix a b c d N (fun q => (channel q).p) coeff)

/-- The selected proof-carrying row channel is exactly the requested target.
This is derived from the one-hot contraction-order field and channel
uniqueness, rather than stored as a second normalization assumption. -/
theorem selected_channel_eq {a b c d : Nat}
    {qL : FixedLeftCGChannel a b c d}
    {qR : FixedRightCGChannel a b c d}
    (C : FiniteRightRowCertificate qL qR) :
    C.channel C.target = qR := by
  apply fixedRightChannel_eq_of_p_eq
  exact (C.target_onehot (q := C.target) C.target_lt).2 rfl

/-- Pairing any certified finite row against its selected right channel
automatically kills every other summand by the unconditional all-label
Casimir Gram law. -/
theorem scaled_cross_eq_selected_gram {a b c d : Nat}
    {qL : FixedLeftCGChannel a b c d}
    {qR : FixedRightCGChannel a b c d}
    (C : FiniteRightRowCertificate qL qR) :
    C.scale * triCrossChannelWeight qL qR ≈
      C.coeff C.target *
        triRightChannelWeight a b c d qR.intermediate := by
  let L := triLeft a b c d qL.intermediate
  let R := triRight a b c d qR.intermediate
  have horth : ∀ q, q < C.N →
      triMapInner a b c d
          (triRight a b c d
            (rightChannelLabel b c (C.channel q).p)) R ≈
        if q = C.target then
          triRightChannelWeight a b c d qR.intermediate else 0 := by
    intro q hq
    have hgram := rightChannel_gram_all (C.channel q) qR
    have hone := C.target_onehot (q := q) hq
    by_cases hqt : q = C.target
    · have hp : (C.channel q).p = qR.p := hone.2 hqt
      rw [if_pos hqt]
      simpa only [R, rightChannelLabel,
        FixedRightCGChannel.intermediate, hp, if_pos rfl] using hgram
    · have hp : (C.channel q).p ≠ qR.p := by
        intro hp
        exact hqt (hone.1 hp)
      rw [if_neg hqt]
      simpa only [R, rightChannelLabel,
        FixedRightCGChannel.intermediate, hp, if_false] using hgram
  have hpair := schur_pairing_of_right_orthogonality
    (a := a) (b := b) (c := c) (d := d)
    (N := C.N) (target := C.target)
    (fun q => (C.channel q).p) C.coeff
    (fun x y z => scaleForm C.scale (L x y z)) qR
    C.target_lt C.row horth
  have hscale := triMapInner_scale_left a b c d C.scale L R
  exact Q'.eqv_trans _ (triMapInner a b c d
      (fun x y z => scaleForm C.scale (L x y z)) R) _
    (Q'.eqv_symm (by
      simpa only [L, R, triCrossChannelWeight] using hscale))
    (by simpa only [R] using hpair)

/-- A certified finite row determines the selected inverse Schur coefficient
without division:

`rowScale * inverseSchur = selectedRowCoefficient`.

The proof compares the selected Gram collapse with the independently proved
arbitrary-channel Schur cross normalization and cancels the strictly positive
right Gram weight. -/
theorem inverseSchur_scale_eq_selected_coeff {a b c d : Nat}
    {qL : FixedLeftCGChannel a b c d}
    {qR : FixedRightCGChannel a b c d}
    (C : FiniteRightRowCertificate qL qR) :
    C.scale * fixedLeftRightDiagonalCoeff qL qR 0 ≈
      C.coeff C.target := by
  let X := triCrossChannelWeight qL qR
  let W := triRightChannelWeight a b c d qR.intermediate
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  have hrow : C.scale * X ≈ C.coeff C.target * W := by
    simpa only [X, W] using scaled_cross_eq_selected_gram C
  have hcarrier := triCrossChannelWeight_eq_collapsedFactorialCrossSum qL qR
  have hschur := collapsed_cross_inverse_normalization_arbitrary qL qR
  have hX : X ≈ W * K := by
    exact Q'.eqv_trans _ _ _
      (by simpa only [X] using hcarrier)
      (by simpa only [W, K] using hschur)
  have hscaled : W * (C.scale * K) ≈ W * C.coeff C.target := by
    refine Q'.eqv_trans _ (C.scale * (W * K)) _
      (mul_swap_nested W C.scale K) ?_
    refine Q'.eqv_trans _ (C.scale * X) _
      (Q'.mul_eqv_congr_left C.scale _ _ (Q'.eqv_symm hX)) ?_
    exact Q'.eqv_trans _ (C.coeff C.target * W) _ hrow
      (Q'.mul_comm_eqv _ _)
  have hW : (0 : Q') < W := by
    simpa only [W] using right_channel_weight_pos_all qR
  simpa only [K] using Q'.mul_left_cancel_of_pos hW hscaled

/-- Exact common-factor cancellation for a finite row.  If its scale and
selected coefficient share a positive factor, that factor can be removed
constructively from the inverse Schur normalization. -/
theorem inverseSchur_reduced_scale {a b c d : Nat}
    {qL : FixedLeftCGChannel a b c d}
    {qR : FixedRightCGChannel a b c d}
    (C : FiniteRightRowCertificate qL qR)
    (common den num : Q')
    (hcommon : (0 : Q') < common)
    (hscale : C.scale ≈ common * den)
    (hcoeff : C.coeff C.target ≈ common * num) :
    den * fixedLeftRightDiagonalCoeff qL qR 0 ≈ num := by
  let K := fixedLeftRightDiagonalCoeff qL qR 0
  have hrow : C.scale * K ≈ C.coeff C.target := by
    simpa only [K] using inverseSchur_scale_eq_selected_coeff C
  have hscaled : common * (den * K) ≈ common * num := by
    refine Q'.eqv_trans _ ((common * den) * K) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv common den K)) ?_
    refine Q'.eqv_trans _ (C.scale * K) _
      (Q'.mul_eqv_congr_right _ _ K (Q'.eqv_symm hscale)) ?_
    exact Q'.eqv_trans _ (C.coeff C.target) _ hrow hcoeff
  simpa only [K] using Q'.mul_left_cancel_of_pos hcommon hscaled

/-- If a proposed exact rational coefficient obeys the same positive reduced
scale equation, the finite row identifies it with the physical inverse Schur
coefficient. -/
theorem inverseSchur_eq_candidate {a b c d : Nat}
    {qL : FixedLeftCGChannel a b c d}
    {qR : FixedRightCGChannel a b c d}
    (C : FiniteRightRowCertificate qL qR)
    (common den num candidate : Q')
    (hcommon : (0 : Q') < common)
    (hden : (0 : Q') < den)
    (hscale : C.scale ≈ common * den)
    (hcoeff : C.coeff C.target ≈ common * num)
    (hcandidate : den * candidate ≈ num) :
    fixedLeftRightDiagonalCoeff qL qR 0 ≈ candidate := by
  have hphysical := inverseSchur_reduced_scale C common den num
    hcommon hscale hcoeff
  exact Q'.mul_left_cancel_of_pos hden
    (Q'.eqv_trans _ num _ hphysical (Q'.eqv_symm hcandidate))

end YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate

#print axioms YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate.selected_channel_eq
#print axioms YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate.scaled_cross_eq_selected_gram
#print axioms YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate.inverseSchur_scale_eq_selected_coeff
#print axioms YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate.inverseSchur_reduced_scale
#print axioms YMGap.Continuum.SU2FiniteRightRowNormalizationCertificate.inverseSchur_eq_candidate
