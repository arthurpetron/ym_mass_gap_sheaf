/-
# Relative-dissipation scale chain: Schur decomposition, scale-chain contraction, AF prefix budget

**Label: conditional reduction. NOT gap evidence and NOT a proof of the Yang–Mills mass gap.**

This file consumes the existing relative-dissipation machinery
(`relative_comparison_iff_dissipation`, `contraction_of_relative_comparison`, `relativeRate`,
`relativeRate_margin_lower`) and chains it across the dyadic scales `j0, j0+1, …` of a
`NomeSchedule`. Every analytic input is an explicit hypothesis whose name ends in `_OPEN`:

* `hupper_OPEN` : per-scale upper norm comparison `‖Φ_n y‖_c ≤ ‖y‖_f` (fine `j0+n+1` → coarse `j0+n`).
* `hschur_OPEN` : per-scale exact Schur decomposition `A - F = (1-δ_n)(A - C) + D`, `D ≥ 0`.
  This is equivalent to the relative comparison itself (take `D := (A-F) - (1-δ)(A-C)`), so it is
  a reformulation in the r46 defect shape, not new information.
* `hafδ_OPEN` : AF-quadratic dissipation `δ_k ≤ C · afGap(j0+k)²`.
* `hbudget` : the numerical budget `C·afA²/(j0+3) < seed` (decidable for concrete data).

The seed contraction at the trajectory's own nome `w_{j0}` is either a hypothesis or the
PROVED `wilsonVacuumSqContraction_mixRate` (`scaleChain_contraction_mixRate`).
No hypothesis bounds `1 - r_j` by `2^{-j}` or by anything else. The rates `r_n = relativeRate seed δ n`
are constructed. The dyadic floor `2^n (1 - r_n) ≥ (1-seed)(seed-D)` is a CONCLUSION.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
import YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction

namespace YMGap.RG.RelativeDissipationScaleChain

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction
  (WilsonVacuumSqContraction wilsonVacuumSqContraction_mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.RGExplicitRationalRate (explicitRate)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
  (relativeFactor relativeFactor_error relative_comparison_iff_dissipation
   contraction_of_relative_comparison)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget
  (relativeRate relativeRate_bounds relativeRate_margin_lower)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf ofNat_two_pow_mul_half_pow)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afGap_pos afGap_den afA afE)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)

local infix:50 " ≈ " => Q'.eqv

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_le_add_nonneg (a b : RC) (hb : RCnonneg b) : RCle a (RCadd a b) := by
  have h := RCadd_le_add (RCle_refl a) hb
  rwa [rc_add_zero] at h

/-! ## 1. Schur decomposition ⇒ relative comparison -/

/-- **Exact Schur decomposition gives the relative comparison (PROVED).** -/
theorem hrelative_of_schurDecomposition (delta : Q') (A F C D : RC) (hD : RCnonneg D)
    (hdec : RCsub A F = RCadd (RCscale ((1 : Q') - delta) (RCsub A C)) D) :
    RCle F (RCadd (RCscale delta A) (RCscale ((1 : Q') - delta) C)) :=
  (relative_comparison_iff_dissipation delta A F C).mpr
    (by rw [hdec]; exact rc_le_add_nonneg _ _ hD)

section Carrier
variable {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
  (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))

/-- Per-scale exact Schur decomposition on the completed carriers (r46 defect shape). -/
def SchurDecomposition (widthF widthC : Nat) (delta : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) → VacuumComplement hwC0 hwC1 (width := widthC))
    (D : VacuumComplement hwF0 hwF1 (width := widthF) → RC) : Prop :=
  ∀ y, RCnonneg (D y) ∧
    RCsub (completedInner hwF0 hwF1 y.val y.val)
        (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 2 y.val) (completedTime hwF0 hwF1 2 y.val)) =
      RCadd (RCscale ((1 : Q') - delta) (RCsub (completedInner hwF0 hwF1 y.val y.val)
        (completedInner hwC0 hwC1 (completedTime hwC0 hwC1 1 (Phi y).val)
          (completedTime hwC0 hwC1 1 (Phi y).val)))) (D y)

/-- Carrier form: exactly the `hrelative` input of `contraction_of_relative_comparison`. -/
theorem hrelative_of_schurDecomposition_carrier (widthF widthC : Nat) (delta : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) → VacuumComplement hwC0 hwC1 (width := widthC))
    (D : VacuumComplement hwF0 hwF1 (width := widthF) → RC)
    (h : SchurDecomposition hwF0 hwF1 hwC0 hwC1 widthF widthC delta Phi D) :
    ∀ y, RCle
      (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 2 y.val) (completedTime hwF0 hwF1 2 y.val))
      (RCadd (RCscale delta (completedInner hwF0 hwF1 y.val y.val))
        (RCscale ((1 : Q') - delta) (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (Phi y).val) (completedTime hwC0 hwC1 1 (Phi y).val)))) :=
  fun y => hrelative_of_schurDecomposition delta _ _ _ (D y) (h y).1 (h y).2

end Carrier

/-! ## 2. Scale-chain contraction from the IR seed `j0` -/

theorem explicitRate_congr {a b : Q'} (h : a ≈ b) : explicitRate a ≈ explicitRate b :=
  Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ h)

theorem contraction_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)
    {r r' : Q'} (h : r ≈ r') (hc : WilsonVacuumSqContraction hw0 hw1 width r) :
    WilsonVacuumSqContraction hw0 hw1 width r' := by
  intro y
  have hsq : r*r ≈ r'*r' :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right r r' r h) (Q'.mul_eqv_congr_left r' r r' h)
  rw [← scale_congr hsq]; exact hc y

/-- **Scale-chain contraction (PROVED from explicit OPEN inputs).** -/
theorem scaleChain_contraction (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (seed : Q') (delta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed ≤ (1 : Q'))
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n)) (delta n) (Phi n) (D n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed) :
    ∀ n, WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
      (relativeRate seed delta n) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have hr := relativeRate_bounds seed delta hs0 hs1 hd0 hd1 n
    have hc := contraction_of_relative_comparison (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n)) (delta n)
      (relativeRate seed delta n) (Phi n) (hd0 n) (hd1 n) hr.1 hr.2 (hupper_OPEN n)
      (hrelative_of_schurDecomposition_carrier _ _ _ _ _ _ _ _ _ (hschur_OPEN n)) ih
    exact contraction_congr _ _ _ (explicitRate_congr (relativeFactor_error _ _)) hc

/-- Seed at the trajectory's own nome `w_{j0}` supplied by the PROVED mixing-rate contraction. -/
theorem scaleChain_contraction_mixRate (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (delta : Nat → Q') (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n)) (delta n) (Phi n) (D n)) :
    ∀ n, WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
      (relativeRate (mixRate (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0)) delta n) :=
  scaleChain_contraction ns width j0 _ delta (mixRate_nonnegative _ _ _)
    (Q'.le_of_lt (mixRate_lt_one _ _ _)) hd0 hd1 Phi D hupper_OPEN hschur_OPEN
    (wilsonVacuumSqContraction_mixRate _ _ _)

/-- `0 ≤ ofNat n` (local copy; avoids importing `SU3CharFactor`). -/
private theorem ofNat_nonneg'' (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- **Operator-level relative-side floor `2^n (1 - r_n) ≥ (1-seed)(seed-D)` (PROVED).** -/
theorem relativeRate_side_floor (seed Dq : Q') (delta : Nat → Q')
    (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q')) (hD0 : (0 : Q') ≤ Dq) (hD : Dq < seed)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hprefix : ∀ n, finSum delta n ≤ Dq) (n : Nat) :
    ((1 : Q') - seed)*(seed-Dq) ≤ Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (2 ^ n))
    (relativeRate_margin_lower seed Dq delta hs0 hs1 hD0 hD hd0 hd1 hprefix n)
    (ofNat_nonneg'' (2 ^ n))
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_mul_half_pow n)) (Q'.one_mul_eqv _))

/-! ## 3. AF-quadratic prefix budget (telescoping `1/(m+1) - 1/(m+2)`) -/

/-- `inv m = 1/(m+1)`. -/
def inv (m : Nat) : Q' := ⟨1, m⟩

theorem inv_nonneg (m : Nat) : (0 : Q') ≤ inv m := by
  show (0 : Int) * _ ≤ 1 * _; rw [Int.zero_mul, Int.one_mul]; exact Int.natCast_nonneg _

/-- `1/(m+2)² ≤ 1/(m+1) - 1/(m+2)` (PROVED). -/
theorem inv_sq_le_tele (m : Nat) : inv (m+1) * inv (m+1) ≤ inv m + -inv (m+1) := by
  show (1 * 1) * ((inv m + -inv (m+1)).den : Int) ≤
    (1 * ((m+1+1 : Nat) : Int) + -1 * ((m+1 : Nat) : Int)) * ((inv (m+1) * inv (m+1)).den : Int)
  rw [Q'.add_den_cast, Q'.mul_den_cast]
  show (1 * 1) * (((m+1 : Nat) : Int) * ((m+1+1 : Nat) : Int)) ≤
    (1 * ((m+1+1 : Nat) : Int) + -1 * ((m+1 : Nat) : Int)) *
      (((m+1+1 : Nat) : Int) * ((m+1+1 : Nat) : Int))
  have h1 : 1 * ((m+1+1 : Nat) : Int) + -1 * ((m+1 : Nat) : Int) = 1 := by
    rw [Int.one_mul, Int.neg_one_mul, Int.natCast_add ((m+1)) 1, Int.add_comm, Int.neg_add_cancel_left]; rfl
  rw [h1, Int.one_mul, Int.one_mul, Int.one_mul]
  exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr (Nat.le_succ _)) (Int.natCast_nonneg _)

private theorem afE_ge (j : Nat) : 121 * (j + 4) ≤ afE j := by
  show 121 * (j + 4) ≤ 121 * j + 51 * Nat.log2 (j+1) + 484
  rw [Nat.mul_add, Nat.add_right_comm]; exact Nat.le_add_right _ _

/-- `afGap j ≤ afA / (j+4)` (PROVED). -/
theorem afGap_le (j : Nat) : afGap j ≤ afA * inv (j+3) := by
  show (234982 : Int) * ((afA * inv (j+3)).den : Int) ≤ (1942 * 1) * ((afGap j).den : Int)
  rw [Q'.mul_den_cast, afGap_den]
  have hN : 1942 * 121 * (1000 * (j+3+1)) ≤ 1942 * 1 * (1000 * afE j) := by
    rw [Nat.mul_assoc 1942 121, Nat.mul_left_comm 121 1000, Nat.mul_one]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (afE_ge j))
  have := Int.ofNat_le.mpr hN
  exact this

/-- Generic telescoping prefix bound (PROVED). -/
theorem finSum_le_tele (delta t : Nat → Q') (c : Q')
    (h : ∀ k, delta k ≤ c * (t k + -t (k+1))) : ∀ n, finSum delta n ≤ c * (t 0 + -t n) := by
  intro n
  induction n with
  | zero => exact Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 1)))) (.const 0) (by decide)
      (fun | 0 => c | _ => t 0))
  | succ n ih =>
    exact Q'.le_trans' _ _ _ (Q'.add_le_add ih (h n)) (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.mul (.var 0) (.add (.var 2) (.neg (.var 3)))))
      (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))) (by decide)
      (fun | 0 => c | 1 => t 0 | 2 => t n | _ => t (n+1))))

/-- **AF-quadratic prefix budget: `finSum δ n ≤ C·afA²/(j0+3)` (PROVED from `hafδ_OPEN`).** -/
theorem afQuadratic_prefix_budget (C : Q') (hC : (0 : Q') ≤ C) (j0 : Nat) (delta : Nat → Q')
    (hafδ_OPEN : ∀ k, delta k ≤ C * (afGap (j0+k) * afGap (j0+k))) :
    ∀ n, finSum delta n ≤ C * (afA * afA) * inv (j0+2) := by
  have hA : (0 : Q') ≤ afA := by decide
  have hc : (0 : Q') ≤ C * (afA * afA) := Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ hA hA)
  have hstep : ∀ k, delta k ≤ C * (afA * afA) * (inv (j0+k+2) + -inv (j0+(k+1)+2)) := by
    intro k
    have hg := afGap_le (j0+k)
    have hsq := Q'.mul_le_mul_of_nonneg hg hg (Q'.mul_nonneg _ _ hA (inv_nonneg _))
      (Q'.le_of_lt (afGap_pos _))
    have ht : (afA * inv (j0+k+3)) * (afA * inv (j0+k+3)) ≤
        (afA * afA) * (inv (j0+k+2) + -inv (j0+k+3)) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
        (fun | 0 => afA | _ => inv (j0+k+3))))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (inv_sq_le_tele (j0+k+2)) (Q'.mul_nonneg _ _ hA hA))
    refine Q'.le_trans' _ _ _ (hafδ_OPEN k) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ C (Q'.le_trans' _ _ _ hsq ht) hC) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  intro n
  have h := finSum_le_tele delta (fun k => inv (j0+k+2)) _ hstep n
  refine Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hc)
  have hn := Q'.add_le_add_left (inv (j0+0+2) + -inv (j0+n+2)) 0 _ (inv_nonneg (j0+n+2))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _))
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => inv (j0+0+2) | _ => inv (j0+n+2)))))

/-- **Capstone: AF-budgeted scale chain ⇒ contraction at every scale and floor (conditional).** -/
theorem scaleChain_afBudget_floor (ns : NomeSchedule) (width : Nat → Nat) (j0 : Nat)
    (seed C : Q') (delta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hafδ_OPEN : ∀ k, delta k ≤ C * (afGap (j0+k) * afGap (j0+k)))
    (hbudget : C * (afA * afA) * inv (j0+2) < seed)
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n)) (delta n) (Phi n) (D n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed) (n : Nat) :
    WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
        (relativeRate seed delta n) ∧
      ((1 : Q') - seed)*(seed - C * (afA * afA) * inv (j0+2)) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n :=
  ⟨scaleChain_contraction ns width j0 seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1 Phi D
      hupper_OPEN hschur_OPEN hseed n,
   relativeRate_side_floor seed _ delta hs0 hs1
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide))) (inv_nonneg _))
      hbudget hd0 hd1 (afQuadratic_prefix_budget C hC j0 delta hafδ_OPEN) n⟩

/-- Decidable budget instance: `C = 1/10`, `j0 = 8`, `seed = 1/2` (`0.1·3.77/11 ≈ 0.034 < 1/2`). -/
theorem afBudget_example : Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2) < Q'.mkPos 1 2 (by decide) := by
  decide

end YMGap.RG.RelativeDissipationScaleChain
