/-
# Automatic global-vacuum projection for finite SU(2) spin networks

`SU2FiniteSpinNetworkSpectralEnvelope` assumes that every retained global
labeling contains an excited edge.  This file performs that projection
internally.  A labeling is retained exactly when some edge in the actual
finite elimination list has positive irrep label.  The all-zero global vacuum
labeling receives both zero weight and zero excited eigenvalue.

Every retained mode then has the exact product transfer eigenvalue and hence
the same squared separator `1/64`.  The result is a concrete located diagonal
operator with no excited-support premise, exact correlators, and permutation
independence.  When the input family was already excited-supported, the new
model agrees with the earlier envelope on every physical mode.

Honest scope: this projects the global *label* vacuum once a finite spin-network
family has been constructed.  Constructing that family from the complete
overlapping four-dimensional plaquette algebra remains open.
-/

import YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

namespace YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope

set_option maxHeartbeats 1000000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem q_pow_eqv_congr {a b : Q'} (h : a ≈ b) :
    ∀ n : Nat, a ^ n ≈ b ^ n
  | 0 => by
      rw [Q'.pow_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | n + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      exact q_mul_congr h (q_pow_eqv_congr h n)

/-! ## Project the unique all-zero global labeling -/

def ModeExcited (order : List Nat) (label : Nat → Nat) : Prop :=
  ∃ edge, edge ∈ order ∧ 1 ≤ label edge

instance modeExcitedDecidable (order : List Nat) (label : Nat → Nat) :
    Decidable (ModeExcited order label) := by
  unfold ModeExcited
  exact List.decidableBEx (fun edge => 1 ≤ label edge) order

/-- Exact global-vacuum projection on the state weight. -/
def globalVacuumFamilyWeight (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (i : Nat) : Q' :=
  if ModeExcited order (labels i) then weight i else 0

/-- Squared exact transfer eigenvalue on retained modes; the removed global
vacuum coordinate is represented by zero in the excited operator. -/
def globalVacuumFamilySquaredEigen (order : List Nat)
    (labels : Nat → Nat → Nat) (i : Nat) : Q' :=
  if ModeExcited order (labels i) then
    networkEigen order (labels i) * networkEigen order (labels i)
  else 0

theorem globalVacuumFamilyWeight_nonneg (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q')
    (hweight : ∀ i, (0 : Q') ≤ weight i) (i : Nat) :
    (0 : Q') ≤ globalVacuumFamilyWeight order labels weight i := by
  by_cases h : ModeExcited order (labels i)
  · rw [globalVacuumFamilyWeight, if_pos h]
    exact hweight i
  · rw [globalVacuumFamilyWeight, if_neg h]
    exact Q'.le_refl' 0

theorem globalVacuumFamilySquaredEigen_nonneg (order : List Nat)
    (labels : Nat → Nat → Nat) (i : Nat) :
    (0 : Q') ≤ globalVacuumFamilySquaredEigen order labels i := by
  by_cases h : ModeExcited order (labels i)
  · rw [globalVacuumFamilySquaredEigen, if_pos h]
    exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (networkEigen order (labels i))
  · rw [globalVacuumFamilySquaredEigen, if_neg h]
    exact Q'.le_refl' 0

/-- The automatic projection makes the `1/64` bound unconditional: a mode is
either removed, or its witness excited edge supplies the `1/8` factor. -/
theorem globalVacuumFamilySquaredEigen_le_sep (order : List Nat)
    (labels : Nat → Nat → Nat) (i : Nat) :
    globalVacuumFamilySquaredEigen order labels i ≤
      finiteNetworkSquaredSep := by
  by_cases h : ModeExcited order (labels i)
  · rw [globalVacuumFamilySquaredEigen, if_pos h]
    let a := networkEigen order (labels i)
    have ha : (0 : Q') ≤ a := networkEigen_nonneg (labels i) order
    have hae : a ≤ eighth :=
      networkEigen_excited_le_eighth (labels i) order h
    have h1 : a * a ≤ eighth * a :=
      Q'.mul_le_mul_of_nonneg_right a eighth a hae ha
    have h2 : eighth * a ≤ eighth * eighth :=
      Q'.mul_le_mul_of_nonneg_left a eighth eighth hae (by decide)
    exact Q'.le_trans' _ _ _ h1 h2
  · rw [globalVacuumFamilySquaredEigen, if_neg h]
    unfold finiteNetworkSquaredSep
    exact Q'.mul_nonneg eighth eighth (by decide) (by decide)

/-! ## Located operator and exact correlators -/

def globalVacuumFamilyModel (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) : SpectralModel :=
  diagOp.toSpectralModel (globalVacuumFamilySquaredEigen order labels)
    (globalVacuumFamilyWeight order labels weight) N
    (globalVacuumFamilyWeight_nonneg order labels weight hweight)
    (globalVacuumFamilySquaredEigen_nonneg order labels)

def globalVacuumFamilyOp (order : List Nat)
    (labels : Nat → Nat → Nat) (N : Nat) : FiniteOp :=
  diagOp (globalVacuumFamilySquaredEigen order labels) N

theorem globalVacuumFamily_lam_is_operator_eigen (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) (i : Nat) (hi : i < N) :
    (globalVacuumFamilyModel order labels weight N hweight).lam i ≈
      (globalVacuumFamilyOp order labels N).apply (basis i) i :=
  toSpectralModel_lam_is_eigen
    (globalVacuumFamilySquaredEigen order labels)
    (globalVacuumFamilyWeight order labels weight) N
    (globalVacuumFamilyWeight_nonneg order labels weight hweight)
    (globalVacuumFamilySquaredEigen_nonneg order labels) i hi

def globalVacuumFamilyLocatedGap (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    LocatedSpectralGap
      (globalVacuumFamilyModel order labels weight N hweight) :=
  diagLocatedGap (globalVacuumFamilySquaredEigen order labels)
    (globalVacuumFamilyWeight order labels weight) N
    (globalVacuumFamilyWeight_nonneg order labels weight hweight)
    (globalVacuumFamilySquaredEigen_nonneg order labels)
    finiteNetworkSquaredSep finiteNetworkSquaredSep_lt_one
    (globalVacuumFamilySquaredEigen_le_sep order labels)

theorem globalVacuumFamily_gapMargin_exact (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    (globalVacuumFamilyLocatedGap order labels weight N hweight).gapMargin
      ≈ Q'.mkPos 63 64 (by decide) := by
  change (1 - finiteNetworkSquaredSep) ≈ Q'.mkPos 63 64 (by decide)
  decide

def globalVacuumFamilyNorm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat) : Q' :=
  fsum (globalVacuumFamilyWeight order labels weight) N

def globalVacuumFamilyTransferredNorm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat) : Q' :=
  fsum (fun i =>
    globalVacuumFamilyWeight order labels weight i *
      globalVacuumFamilySquaredEigen order labels i) N

theorem globalVacuumFamily_corr_zero_eq_norm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (globalVacuumFamilyModel order labels weight N hweight) 0 ≈
      globalVacuumFamilyNorm order labels weight N := by
  refine Q'.eqv_trans _ _ _
    (corr_zero (globalVacuumFamilyModel order labels weight N hweight)) ?_
  unfold globalVacuumFamilyNorm globalVacuumFamilyModel
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact Q'.eqv_refl _

theorem globalVacuumFamily_corr_one_eq_transferred_norm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (globalVacuumFamilyModel order labels weight N hweight) 1 ≈
      globalVacuumFamilyTransferredNorm order labels weight N := by
  unfold corr globalVacuumFamilyModel globalVacuumFamilyTransferredNorm
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact finSum_eqv_of_termwise _ _ (fun i => by
    change globalVacuumFamilyWeight order labels weight i *
        (globalVacuumFamilySquaredEigen order labels i) ^ 1 ≈
      globalVacuumFamilyWeight order labels weight i *
        globalVacuumFamilySquaredEigen order labels i
    rw [Q'.pow_succ, Q'.pow_zero]
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_one_eqv (globalVacuumFamilySquaredEigen order labels i))) N

/-! ## Compatibility with already supported families -/

theorem globalVacuumWeight_eq_of_excited {order : List Nat}
    {labels : Nat → Nat → Nat} {weight : Nat → Q'} {i : Nat}
    (h : ModeExcited order (labels i)) :
    globalVacuumFamilyWeight order labels weight i = weight i := by
  unfold globalVacuumFamilyWeight
  rw [if_pos h]

theorem globalVacuumSquaredEigen_eq_of_excited {order : List Nat}
    {labels : Nat → Nat → Nat} {i : Nat}
    (h : ModeExcited order (labels i)) :
    globalVacuumFamilySquaredEigen order labels i =
      networkEigen order (labels i) * networkEigen order (labels i) := by
  unfold globalVacuumFamilySquaredEigen
  rw [if_pos h]

/-- On an already excited-supported finite family, automatic vacuum projection
does not change any finite-time correlator. -/
theorem globalVacuum_corr_eq_supported_corr (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N n : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i)
    (hsupport : ExcitedSupport order labels N) :
    corr (globalVacuumFamilyModel order labels weight N hweight) n ≈
      corr (finiteNetworkFamilyModel order labels weight N hweight) n := by
  unfold corr globalVacuumFamilyModel finiteNetworkFamilyModel
  exact finSum_eqv_congr_lt _ _ N (fun i hi => by
    have hexc : ModeExcited order (labels i) := hsupport i hi
    change globalVacuumFamilyWeight order labels weight i *
        (globalVacuumFamilySquaredEigen order labels i) ^ n ≈
      weight i * (familySquaredEigen order labels N i) ^ n
    rw [globalVacuumWeight_eq_of_excited hexc,
      globalVacuumSquaredEigen_eq_of_excited hexc]
    unfold familySquaredEigen
    rw [if_pos hi]
    exact Q'.eqv_refl _)

/-! ## Elimination-order independence -/

theorem modeExcited_iff_of_perm {order order' : List Nat}
    (h : order.Perm order') (label : Nat → Nat) :
    ModeExcited order label ↔ ModeExcited order' label := by
  constructor
  · rintro ⟨edge, hmem, hexc⟩
    exact ⟨edge, (List.Perm.mem_iff h).mp hmem, hexc⟩
  · rintro ⟨edge, hmem, hexc⟩
    exact ⟨edge, (List.Perm.mem_iff h).mpr hmem, hexc⟩

theorem globalVacuumFamilyWeight_order_independent
    {order order' : List Nat} (h : order.Perm order')
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (i : Nat) :
    globalVacuumFamilyWeight order labels weight i =
      globalVacuumFamilyWeight order' labels weight i := by
  by_cases hexc : ModeExcited order (labels i)
  · have hexc' := (modeExcited_iff_of_perm h (labels i)).mp hexc
    rw [globalVacuumWeight_eq_of_excited hexc,
      globalVacuumWeight_eq_of_excited hexc']
  · have hexc' : ¬ ModeExcited order' (labels i) := fun hh =>
      hexc ((modeExcited_iff_of_perm h (labels i)).mpr hh)
    unfold globalVacuumFamilyWeight
    rw [if_neg hexc, if_neg hexc']

theorem globalVacuumFamilySquaredEigen_order_independent
    {order order' : List Nat} (h : order.Perm order')
    (labels : Nat → Nat → Nat) (i : Nat) :
    globalVacuumFamilySquaredEigen order labels i ≈
      globalVacuumFamilySquaredEigen order' labels i := by
  by_cases hexc : ModeExcited order (labels i)
  · have hexc' := (modeExcited_iff_of_perm h (labels i)).mp hexc
    rw [globalVacuumSquaredEigen_eq_of_excited hexc,
      globalVacuumSquaredEigen_eq_of_excited hexc']
    exact q_mul_congr
      (networkEigen_order_independent (labels i) h)
      (networkEigen_order_independent (labels i) h)
  · have hexc' : ¬ ModeExcited order' (labels i) := fun hh =>
      hexc ((modeExcited_iff_of_perm h (labels i)).mpr hh)
    unfold globalVacuumFamilySquaredEigen
    rw [if_neg hexc, if_neg hexc']
    exact Q'.eqv_refl 0

theorem globalVacuumFamily_corr_order_independent
    {order order' : List Nat} (h : order.Perm order')
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N n : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (globalVacuumFamilyModel order labels weight N hweight) n ≈
      corr (globalVacuumFamilyModel order' labels weight N hweight) n := by
  unfold corr globalVacuumFamilyModel
  exact finSum_eqv_of_termwise _ _ (fun i =>
    q_mul_congr
      (Q'.eqv_of_eq
        (globalVacuumFamilyWeight_order_independent h labels weight i))
      (q_pow_eqv_congr
        (globalVacuumFamilySquaredEigen_order_independent h labels i) n)) N

end YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope

#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamilySquaredEigen_le_sep
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamily_lam_is_operator_eigen
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamilyLocatedGap
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamily_gapMargin_exact
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamily_corr_zero_eq_norm
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamily_corr_one_eq_transferred_norm
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuum_corr_eq_supported_corr
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope.globalVacuumFamily_corr_order_independent
