/-
# Located spectrum of the four-valent SU(2) intertwiner transfer

The four-fundamental intertwiner space is genuinely two-dimensional.  Its
weighted GNS form is `diag(3,1)`, its physical four-link transfer is scalar
multiplication by `(1/8)^4 = 1/4096`, and the rational F-move is an isometry of
that weighted form.

This file keeps both multiplicity channels in a concrete diagonal spectral
model.  For a state `x`, its two spectral weights are the exact contributions
of the two orthogonal intertwiner coordinates to

    B(Tx,x),

and both squared-transfer eigenvalues are `(1/4096)^2`.  Consequently `corr 0`
and `corr 1` are exactly the same-state GNS pairings before and after applying
the physical transfer to both arguments.  The resulting located gap has exact
margin `1 - 1/16777216`, and the F-move preserves both correlators and the
entire two-entry eigenvalue list.

Honest scope: this is a local four-valent spectral cell.  It does not construct
the global overlapping-plaquette transfer operator, nor a spacing-uniform
continuum gap.
-/

import YMGap.Continuum.SU2FourValentRecouplingCompleted
import YMGap.Continuum.CompactTransferGNS

namespace YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted
open YMGap.Continuum.SU2FourValentRecouplingCompleted

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Two-channel spectral realization -/

/-- Both multiplicity channels have the squared same-state transfer
eigenvalue `(1/4096)^2`. -/
def fourValentSquaredEigen (_i : Nat) : Q' :=
  fourLegEigen * fourLegEigen

theorem fourValentSquaredEigen_nonneg (i : Nat) :
    (0 : Q') ≤ fourValentSquaredEigen i :=
  q_mul_self_nonneg fourLegEigen

/-- The exact contribution of each orthogonal multiplicity coordinate to
`B(Tx,x)`.  The two weights retain the `diag(3,1)` GNS multiplicities. -/
def fourValentSpectralWeight (x : Q' × Q') : Nat → Q'
  | 0 => fourLegEigen * (3 * (x.1 * x.1))
  | _ => fourLegEigen * (x.2 * x.2)

theorem fourValentSpectralWeight_nonneg (x : Q' × Q') (i : Nat) :
    (0 : Q') ≤ fourValentSpectralWeight x i := by
  cases i with
  | zero =>
      exact Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg x.1))
  | succ i =>
      exact Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg x.2)

/-- The concrete two-channel squared-transfer spectral model of a
four-valent intertwiner state. -/
def fourValentSquaredSpectralModel (x : Q' × Q') : SpectralModel :=
  diagOp.toSpectralModel fourValentSquaredEigen
    (fourValentSpectralWeight x) 2
    (fourValentSpectralWeight_nonneg x) fourValentSquaredEigen_nonneg

/-- The finite two-dimensional diagonal operator underlying the model. -/
def fourValentSquaredOp : FiniteOp :=
  diagOp fourValentSquaredEigen 2

theorem fourValentSquaredModel_lam_is_eigen (x : Q' × Q')
    (i : Nat) (hi : i < 2) :
    (fourValentSquaredSpectralModel x).lam i ≈
      fourValentSquaredOp.apply (basis i) i :=
  toSpectralModel_lam_is_eigen fourValentSquaredEigen
    (fourValentSpectralWeight x) 2
    (fourValentSpectralWeight_nonneg x) fourValentSquaredEigen_nonneg i hi

/-! ## Exact identification of the first two correlators -/

/-- `corr 0` is exactly the physical four-valent GNS form with one positive
four-link transfer inserted. -/
theorem fourValentGNS_eq_squaredCorr_zero (x : Q' × Q') :
    intertwinerGNS.B (intertwinerTransfer x) x ≈
      corr (fourValentSquaredSpectralModel x) 0 := by
  change
    3 * ((fourLegEigen * x.1) * x.1) +
        1 * ((fourLegEigen * x.2) * x.2) ≈
      (0 + (fourLegEigen * (3 * (x.1 * x.1))) * 1) +
        (fourLegEigen * (x.2 * x.2)) * 1
  ring_qeqv

/-- `corr 1` is exactly the same GNS form after applying the physical
four-link transfer to both state arguments. -/
theorem fourValentTransferredGNS_eq_squaredCorr_one (x : Q' × Q') :
    intertwinerGNS.B
        (intertwinerTransfer (intertwinerTransfer x))
        (intertwinerTransfer x) ≈
      corr (fourValentSquaredSpectralModel x) 1 := by
  change
    3 * ((fourLegEigen * (fourLegEigen * x.1)) *
        (fourLegEigen * x.1)) +
      1 * ((fourLegEigen * (fourLegEigen * x.2)) *
        (fourLegEigen * x.2)) ≈
    (0 + (fourLegEigen * (3 * (x.1 * x.1))) *
        ((fourLegEigen * fourLegEigen) * 1)) +
      (fourLegEigen * (x.2 * x.2)) *
        ((fourLegEigen * fourLegEigen) * 1)
  ring_qeqv

/-! ## Located edge and exact margin -/

def fourValentSquaredSep : Q' := fourLegEigen * fourLegEigen

theorem fourValentSquaredSep_exact :
    fourValentSquaredSep ≈ Q'.mkPos 1 16777216 (by decide) := by
  decide

theorem fourValentSquaredSep_lt_one :
    fourValentSquaredSep < (1 : Q') := by decide

theorem fourValentSquaredEigen_le_sep (i : Nat) :
    fourValentSquaredEigen i ≤ fourValentSquaredSep :=
  Q'.le_refl' _

/-- A located gap for the actual two-channel squared transfer.  It is uniform
in the state because the spectrum, unlike the spectral weights, is fixed. -/
def fourValentSquaredLocatedGap (x : Q' × Q') :
    LocatedSpectralGap (fourValentSquaredSpectralModel x) :=
  diagLocatedGap fourValentSquaredEigen (fourValentSpectralWeight x) 2
    (fourValentSpectralWeight_nonneg x) fourValentSquaredEigen_nonneg
    fourValentSquaredSep fourValentSquaredSep_lt_one
    fourValentSquaredEigen_le_sep

theorem fourValentSquared_gapMargin_exact (x : Q' × Q') :
    (fourValentSquaredLocatedGap x).gapMargin ≈
      Q'.mkPos 16777215 16777216 (by decide) := by
  change ((1 : Q') - fourValentSquaredSep) ≈
    Q'.mkPos 16777215 16777216 (by decide)
  decide

theorem fourValentSquared_gapMargin_pos (x : Q' × Q') :
    (0 : Q') < (fourValentSquaredLocatedGap x).gapMargin :=
  (fourValentSquaredLocatedGap x).gapMargin_pos

/-- Both retained multiplicity modes attain the displayed separator, so the
computed top of the spectrum is exactly the edge, not merely bounded by it. -/
theorem fourValentSquared_specMax_eq_edge (x : Q' × Q') :
    specMax (fourValentSquaredSpectralModel x) ≈
      fourValentSquaredSep := by
  change Q'.max'
      (Q'.max' 0 (fourLegEigen * fourLegEigen))
      (fourLegEigen * fourLegEigen) ≈
    fourLegEigen * fourLegEigen
  unfold Q'.max'
  rw [if_pos (by decide : (0 : Q') ≤ fourLegEigen * fourLegEigen)]
  rw [if_pos (Q'.le_refl' (fourLegEigen * fourLegEigen))]
  exact Q'.eqv_refl _

/-- Spectral decay reproduces the exact squared-transfer contraction on the
same physical four-valent GNS pairing. -/
theorem sameGNS_contraction_from_locatedSpectrum (x : Q' × Q') :
    intertwinerGNS.B
        (intertwinerTransfer (intertwinerTransfer x))
        (intertwinerTransfer x) ≤
      fourValentSquaredSep *
        intertwinerGNS.B (intertwinerTransfer x) x := by
  have hdec := (fourValentSquaredLocatedGap x).decay 1
  rw [Q'.pow_succ, Q'.pow_zero] at hdec
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fourValentTransferredGNS_eq_squaredCorr_one x)) ?_
  refine Q'.le_trans' _ _ _ hdec ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (corr (fourValentSquaredSpectralModel x) 0) _ _
      (Q'.mul_one_eqv fourValentSquaredSep)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ fourValentSquaredSep) ?_
  exact Q'.mul_eqv_congr_left fourValentSquaredSep _ _
    (Q'.eqv_symm (fourValentGNS_eq_squaredCorr_zero x))

/-! ## F-move covariance of the localized spectrum -/

/-- The scalar physical transfer commutes with the rational four-valent
recoupling map. -/
theorem intertwinerTransfer_recoupling_commutes (x : Q' × Q') :
    intertwinerGNS.veq
      (intertwinerTransfer (intertwinerRecoupling x))
      (intertwinerRecoupling (intertwinerTransfer x)) := by
  change
    fourLegEigen *
        (SU2FourValentRecouplingCompleted.half * (x.1 + (-x.2))) ≈
      SU2FourValentRecouplingCompleted.half *
        (fourLegEigen * x.1 + (-(fourLegEigen * x.2))) ∧
    fourLegEigen *
        (SU2FourValentRecouplingCompleted.half * (3 * x.1 + x.2)) ≈
      SU2FourValentRecouplingCompleted.half *
        (3 * (fourLegEigen * x.1) + fourLegEigen * x.2)
  exact ⟨by ring_qeqv, by ring_qeqv⟩

/-- Recoupling changes spectral weights but not either entry of the exact
two-channel eigenvalue list. -/
theorem fourValentSquared_lam_recoupling_invariant
    (x : Q' × Q') (i : Nat) :
    (fourValentSquaredSpectralModel (intertwinerRecoupling x)).lam i =
      (fourValentSquaredSpectralModel x).lam i := rfl

/-- The time-zero spectral correlator is invariant under the physical
four-valent F-move. -/
theorem fourValentSquared_corr_zero_recoupling_invariant (x : Q' × Q') :
    corr (fourValentSquaredSpectralModel (intertwinerRecoupling x)) 0 ≈
      corr (fourValentSquaredSpectralModel x) 0 := by
  refine Q'.eqv_trans _
    (intertwinerGNS.B
      (intertwinerTransfer (intertwinerRecoupling x))
      (intertwinerRecoupling x)) _
    (Q'.eqv_symm (fourValentGNS_eq_squaredCorr_zero _)) ?_
  refine Q'.eqv_trans _
    (fourLegEigen *
      intertwinerGNS.B (intertwinerRecoupling x) (intertwinerRecoupling x)) _ ?_ ?_
  · change
      3 * ((fourLegEigen * (intertwinerRecoupling x).1) *
          (intertwinerRecoupling x).1) +
        1 * ((fourLegEigen * (intertwinerRecoupling x).2) *
          (intertwinerRecoupling x).2) ≈
      fourLegEigen *
        (3 * ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1) +
          1 * ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2))
    ring_qeqv
  · refine Q'.eqv_trans _
      (fourLegEigen * intertwinerGNS.B x x) _
      (Q'.mul_eqv_congr_left fourLegEigen _ _
        (intertwinerRecoupling_norm x)) ?_
    refine Q'.eqv_trans _
      (intertwinerGNS.B (intertwinerTransfer x) x) _ ?_
      (fourValentGNS_eq_squaredCorr_zero x)
    change
      fourLegEigen * (3 * (x.1 * x.1) + 1 * (x.2 * x.2)) ≈
        3 * ((fourLegEigen * x.1) * x.1) +
          1 * ((fourLegEigen * x.2) * x.2)
    ring_qeqv

/-- The time-one spectral correlator is also F-move invariant; this uses both
commutation with transfer and preservation of the weighted GNS norm. -/
theorem fourValentSquared_corr_one_recoupling_invariant (x : Q' × Q') :
    corr (fourValentSquaredSpectralModel (intertwinerRecoupling x)) 1 ≈
      corr (fourValentSquaredSpectralModel x) 1 := by
  have hnorm := intertwinerRecoupling_norm x
  change
    (0 + (fourLegEigen * (3 *
        ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1))) *
          ((fourLegEigen * fourLegEigen) * 1)) +
      (fourLegEigen *
        ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2)) *
          ((fourLegEigen * fourLegEigen) * 1) ≈
    (0 + (fourLegEigen * (3 * (x.1 * x.1))) *
          ((fourLegEigen * fourLegEigen) * 1)) +
      (fourLegEigen * (x.2 * x.2)) *
          ((fourLegEigen * fourLegEigen) * 1)
  change
    3 * ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1) +
        1 * ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2) ≈
      3 * (x.1 * x.1) + 1 * (x.2 * x.2) at hnorm
  refine Q'.eqv_trans _
    ((fourLegEigen * (fourLegEigen * fourLegEigen)) *
      (3 * ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1) +
        1 * ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    ((fourLegEigen * (fourLegEigen * fourLegEigen)) *
      (3 * (x.1 * x.1) + 1 * (x.2 * x.2))) _
    (Q'.mul_eqv_congr_left _ _ _ hnorm) ?_
  ring_qeqv

/-- In fact the entire two-channel Källén--Lehmann correlator is invariant
under recoupling at every integer time.  The proof uses the common exact
eigenvalue and the weighted-isometry theorem; no spectral weight is assumed. -/
theorem fourValentSquared_corr_recoupling_invariant
    (x : Q' × Q') (n : Nat) :
    corr (fourValentSquaredSpectralModel (intertwinerRecoupling x)) n ≈
      corr (fourValentSquaredSpectralModel x) n := by
  have hnorm := intertwinerRecoupling_norm x
  change
    (0 + (fourLegEigen * (3 *
        ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1))) *
          ((fourLegEigen * fourLegEigen) ^ n)) +
      (fourLegEigen *
        ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2)) *
          ((fourLegEigen * fourLegEigen) ^ n) ≈
    (0 + (fourLegEigen * (3 * (x.1 * x.1))) *
          ((fourLegEigen * fourLegEigen) ^ n)) +
      (fourLegEigen * (x.2 * x.2)) *
          ((fourLegEigen * fourLegEigen) ^ n)
  change
    3 * ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1) +
        1 * ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2) ≈
      3 * (x.1 * x.1) + 1 * (x.2 * x.2) at hnorm
  refine Q'.eqv_trans _
    ((fourLegEigen * ((fourLegEigen * fourLegEigen) ^ n)) *
      (3 * ((intertwinerRecoupling x).1 * (intertwinerRecoupling x).1) +
        1 * ((intertwinerRecoupling x).2 * (intertwinerRecoupling x).2))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    ((fourLegEigen * ((fourLegEigen * fourLegEigen) ^ n)) *
      (3 * (x.1 * x.1) + 1 * (x.2 * x.2))) _
    (Q'.mul_eqv_congr_left _ _ _ hnorm) ?_
  ring_qeqv

end YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization

#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquaredModel_lam_is_eigen
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentGNS_eq_squaredCorr_zero
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentTransferredGNS_eq_squaredCorr_one
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquaredLocatedGap
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_gapMargin_exact
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_specMax_eq_edge
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.sameGNS_contraction_from_locatedSpectrum
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.intertwinerTransfer_recoupling_commutes
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_lam_recoupling_invariant
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_corr_zero_recoupling_invariant
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_corr_one_recoupling_invariant
#print axioms YMGap.Continuum.SU2FourValentIntertwinerSpectralLocalization.fourValentSquared_corr_recoupling_invariant
