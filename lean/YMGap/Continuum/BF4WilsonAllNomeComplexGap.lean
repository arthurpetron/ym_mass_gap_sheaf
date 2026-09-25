/-
# Fixed-parameter complex gap on the SAME all-nome Wilson completion

The complex carrier is the two-component realification from
`BF4WilsonAllNomeComplexification`.  Its unit is the existing Wilson unit,
and its strict form estimate is obtained by adding the two actual real
component estimates.  Nome and width remain parameters; this is not a
continuum or physical-Hamiltonian gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexification
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.BF4WilsonAllNomeComplexGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4WilsonAllNomeComplexification
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative twoStepRate_lt_one)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "I" => inner hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv (A.approx n))))

/-! The complex unit is the actual completed Wilson unit, embedded as a real
component. -/
def complexUnit : VC := embedReal hw0 hw1 width U

local notation "CU" => complexUnit hw0 hw1 width

theorem complexUnit_fixed (n : Nat) : CT n CU = CU := by
  unfold complexUnit
  rw [complexTime_embedReal, completedUnit_fixed]

theorem inner_unit_left (x : VC) :
    I CU x = (B x.1 U, B x.2 U) := by
  simp only [inner, complexUnit, embedReal, completedInner_zero_left,
    rc_add_zero, rc_sub_zero]
  rw [completedInner_symm hw0 hw1 U x.1,
    completedInner_symm hw0 hw1 U x.2]

theorem complex_orthogonal_iff (x : VC) :
    I CU x = (RCzero, RCzero) ↔
      B x.1 U = RCzero ∧ B x.2 U = RCzero := by
  rw [inner_unit_left]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

theorem complexTime_preserves_orthogonal (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    I CU (CT n x) = (RCzero, RCzero) := by
  obtain ⟨h1, h2⟩ := (complex_orthogonal_iff hw0 hw1 width x).mp hx
  apply (complex_orthogonal_iff hw0 hw1 width (CT n x)).mpr
  have ht1 : B (completedTime hw0 hw1 n x.1) U = RCzero := by
    rw [completedInner_time_balance, completedUnit_fixed]
    exact h1
  have ht2 : B (completedTime hw0 hw1 n x.2) U = RCzero := by
    rw [completedInner_time_balance, completedUnit_fixed]
    exact h2
  change B (completedTime hw0 hw1 n x.1) U = RCzero ∧
    B (completedTime hw0 hw1 n x.2) U = RCzero
  exact ⟨ht1, ht2⟩

theorem inner_time_sum (m n : Nat) (x y : VC) :
    I (CT m x) (CT n y) = I x (CT (m+n) y) := by
  simp only [inner, complexTime, completedInner_time_sum]

theorem inner_even_diagonal (n : Nat) (x : VC) :
    I x (CT (2*n) x) = I (CT n x) (CT n x) := by
  simpa only [Nat.two_mul] using (inner_time_sum hw0 hw1 width n n x x).symm

theorem complex_twoStep_form_gap (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    RCle (I x (CT 2 x)).1
      (RCscale (twoStepRate hw0 hw1 width) (I x x).1) := by
  obtain ⟨h1, h2⟩ := (complex_orthogonal_iff hw0 hw1 width x).mp hx
  have h1' := completed_twoStep_form_gap hw0 hw1 width x.1 h1
  have h2' := completed_twoStep_form_gap hw0 hw1 width x.2 h2
  change RCle (B x.1 (completedTime hw0 hw1 2 x.1))
    (RCscale (twoStepRate hw0 hw1 width) (B x.1 x.1)) at h1'
  change RCle (B x.2 (completedTime hw0 hw1 2 x.2))
    (RCscale (twoStepRate hw0 hw1 width) (B x.2 x.2)) at h2'
  change RCle
    (RCadd (B x.1 (completedTime hw0 hw1 2 x.1))
      (B x.2 (completedTime hw0 hw1 2 x.2)))
    (RCscale (twoStepRate hw0 hw1 width)
      (RCadd (B x.1 x.1) (B x.2 x.2)))
  have h := RCadd_le_add h1' h2'
  rw [← RCscale_RCadd] at h
  exact h

theorem complexTime_zero (x : VC) : CT 0 x = x := by
  simp only [complexTime, completedTime_zero]

theorem complexTime_add (m n : Nat) (x : VC) :
    CT (m+n) x = CT m (CT n x) := by
  simp only [complexTime, completedTime_add]

theorem complexTime_preserves_gap_sector (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    I CU (CT n x) = (RCzero, RCzero) :=
  complexTime_preserves_orthogonal hw0 hw1 width n x hx

/-! The fixed-parameter gap is a same-object discrete correlator estimate at
every translated time slice.  The exact `n+2` indexing is exposed rather than
hidden behind a new transfer or a continuum-time notation. -/
theorem complex_twoStep_translated (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    RCle (I (CT n x) (CT (n+2) x)).1
      (RCscale (twoStepRate hw0 hw1 width) (I (CT n x) (CT n x)).1) := by
  have horth := complexTime_preserves_orthogonal hw0 hw1 width n x hx
  have h := complex_twoStep_form_gap hw0 hw1 width (CT n x) horth
  rw [show n+2 = 2+n by omega,
    complexTime_add hw0 hw1 width 2 n x]
  exact h

/-! The translated two-step estimate is also a same-carrier norm contraction at
the intervening time slice.  This is an exact discrete identity, not a claim
about a continuum generator or a physical mass normalization. -/
theorem complex_oneStep_norm_gap (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    RCle (I (CT (n+1) x) (CT (n+1) x)).1
      (RCscale (twoStepRate hw0 hw1 width)
        (I (CT n x) (CT n x)).1) := by
  have h := complex_twoStep_translated hw0 hw1 width n x hx
  rw [inner_time_sum hw0 hw1 width n (n+2) x x,
    show n + (n+2) = 2*(n+1) by omega,
    inner_even_diagonal hw0 hw1 width (n+1) x] at h
  exact h

/-! Iteration of the same completed-carrier contraction.  The power is the
fixed nome/width rate; this remains a discrete finite-parameter statement. -/
theorem complex_iterated_norm_gap (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    RCle (I (CT n x) (CT n x)).1
      (RCscale ((twoStepRate hw0 hw1 width)^n) (I x x).1) := by
  induction n with
  | zero =>
      rw [complexTime_zero, Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | succ k ih =>
      have hstep := complex_oneStep_norm_gap hw0 hw1 width k x hx
      refine RCle_trans hstep ?_
      have hrateNonnegative : (0 : Q') ≤ twoStepRate hw0 hw1 width :=
        twoStepRate_nonnegative hw0 hw1 width
      have hscaled := RCscale_mono hrateNonnegative ih
      refine RCle_trans hscaled ?_
      rw [RCscale_RCscale, Q'.pow_succ]
      exact RCle_refl _

/-! The norm iteration is the same-object even-lag correlator through the
completed-time pairing identity.  No separate observable or representative is
introduced. -/
theorem complex_even_lag_corr_decay (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) :
    RCle (I x (CT (2*n) x)).1
      (RCscale ((twoStepRate hw0 hw1 width)^n) (I x x).1) := by
  rw [inner_even_diagonal hw0 hw1 width n x]
  exact complex_iterated_norm_gap hw0 hw1 width n x hx

theorem complex_even_lag_corr_nonnegative (n : Nat) (x : VC) :
    RCnonneg (I x (CT (2*n) x)).1 := by
  rw [inner_even_diagonal hw0 hw1 width n x]
  exact inner_nonnegative hw0 hw1 width (CT n x)

/-! The scalar rate has an explicit constructive cutoff when its strict
positivity is supplied.  This is only a coefficient modulus: an absolute
observable modulus additionally needs a norm cap for the chosen state. -/
def complexRateCutoff (epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff (twoStepRate hw0 hw1 width) epsilon

theorem complexRateCutoff_bound (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hrate : (0 : Q') < twoStepRate hw0 hw1 width) :
    (twoStepRate hw0 hw1 width) ^ (complexRateCutoff hw0 hw1 width epsilon)
      ≤ epsilon := by
  exact HKConvGen.pow_base_le_cutoff hrate
    (twoStepRate_lt_one hw0 hw1 width) hepsilon

/-! A response-floor consumer for the same completed complex carrier.  The
norm cap and response floor are explicit hypotheses; no absolute observable
bound or scaling-uniform survival is inferred from the fixed-parameter gap. -/
theorem complex_even_lag_response_power_floor (x : VC)
    (hx : I CU x = (RCzero, RCzero))
    (C floor : Q')
    (hcap : RCle (I x x).1
      (Quotient.mk crealSetoid (ofQ' C)))
    (n : Nat)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (I x (CT (2*n) x)).1) :
    floor ≤ (twoStepRate hw0 hw1 width)^n * C := by
  have hdecay := complex_even_lag_corr_decay hw0 hw1 width n x hx
  have hcap' := RCscale_mono
    (Q'.pow_nonneg (twoStepRate hw0 hw1 width)
      (twoStepRate_nonnegative hw0 hw1 width) n) hcap
  have h := RCle_trans hdecay hcap'
  exact GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hresponse h)

#print axioms complexUnit
#print axioms complexUnit_fixed
#print axioms inner_unit_left
#print axioms complex_orthogonal_iff
#print axioms complexTime_preserves_orthogonal
#print axioms inner_time_sum
#print axioms inner_even_diagonal
#print axioms complex_twoStep_form_gap
#print axioms complexTime_zero
#print axioms complexTime_add
#print axioms complexTime_preserves_gap_sector
#print axioms complex_twoStep_translated
#print axioms complex_oneStep_norm_gap
#print axioms complex_iterated_norm_gap
#print axioms complex_even_lag_corr_decay
#print axioms complex_even_lag_corr_nonnegative
#print axioms complexRateCutoff
#print axioms complexRateCutoff_bound
#print axioms complex_even_lag_response_power_floor

end YMGap.Continuum.BF4WilsonAllNomeComplexGap
