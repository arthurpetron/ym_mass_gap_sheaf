/-
# Exact pruning of zero-weight spectral modes

A finite spectral presentation may attach arbitrary diagonal eigenvalues to
modes whose spectral weight is exactly zero.  Such modes do not contribute
to any correlator, but they can obstruct a literal all-mode gap bound.  This
module constructively sets their eigenvalues to zero, proves every
integer-time correlator unchanged, and identifies an ordinary spectral gap
of the pruned model with a weighted gap on the original presentation.

Semantic rational zero is decidable in the existing `Q'` substrate, so no
choice, excluded middle beyond a decidable proposition, or numerical input
is used.
-/

import YMGap.Continuum.SpectralGap
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SpectralSupportPruning

set_option maxHeartbeats 600000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_eqv_zero_of_left {a b : Q'} (ha : a ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.zero_mul_eqv _)

/-- Replace the eigenvalue of every semantically zero-weight mode by exact
zero. -/
def weightPrunedEigen (S : SpectralModel) (i : Nat) : Q' :=
  if S.w i ≈ 0 then 0 else S.lam i

theorem weightPrunedEigen_nonneg (S : SpectralModel) (i : Nat) :
    (0 : Q') ≤ weightPrunedEigen S i := by
  unfold weightPrunedEigen
  by_cases h : S.w i ≈ 0
  · rw [if_pos h]
    exact Q'.le_refl' 0
  · rw [if_neg h]
    exact S.lam_nonneg i

/-- The support-pruned positive spectral model.  Its mode count and weights
are definitionally the same as the original model. -/
def weightPrunedModel (S : SpectralModel) : SpectralModel where
  k := S.k
  w := S.w
  lam := weightPrunedEigen S
  w_nonneg := S.w_nonneg
  lam_nonneg := weightPrunedEigen_nonneg S

/-- Pruning zero-weight modes leaves every integer-time correlator exactly
unchanged, including time zero. -/
theorem weightPrunedModel_corr (S : SpectralModel) (n : Nat) :
    corr (weightPrunedModel S) n ≈ corr S n := by
  unfold corr
  change finSum (fun i => S.w i * (weightPrunedEigen S i) ^ n) S.k ≈
    finSum (fun i => S.w i * (S.lam i) ^ n) S.k
  apply finSum_eqv_of_termwise
  intro i
  unfold weightPrunedEigen
  by_cases h : S.w i ≈ 0
  · rw [if_pos h]
    exact Q'.eqv_trans _ 0 _
      (mul_eqv_zero_of_left h)
      (Q'.eqv_symm (mul_eqv_zero_of_left h))
  · rw [if_neg h]
    exact Q'.eqv_refl _

/-- A gap bound only on modes that occur with nonzero spectral weight. -/
def WeightedSpectralGapBound (S : SpectralModel) (mu : Q') : Prop :=
  ∀ i, ¬ (S.w i ≈ 0) → S.lam i ≤ mu

/-- A weighted gap becomes an ordinary all-mode gap after exact support
pruning. -/
theorem weightPrunedModel_gap (S : SpectralModel) (mu : Q')
    (hmu : (0 : Q') ≤ mu)
    (hgap : WeightedSpectralGapBound S mu) :
    SpectralGapBound (weightPrunedModel S) mu := by
  intro i
  change weightPrunedEigen S i ≤ mu
  unfold weightPrunedEigen
  by_cases h : S.w i ≈ 0
  · rw [if_pos h]
    exact hmu
  · rw [if_neg h]
    exact hgap i h

/-- Conversely, an ordinary gap on the pruned model controls every nonzero
weight mode of the original presentation. -/
theorem weightedGap_of_weightPrunedModel_gap (S : SpectralModel) (mu : Q')
    (hgap : SpectralGapBound (weightPrunedModel S) mu) :
    WeightedSpectralGapBound S mu := by
  intro i hi
  have h := hgap i
  change weightPrunedEigen S i ≤ mu at h
  unfold weightPrunedEigen at h
  rw [if_neg hi] at h
  exact h

/-- Weighted spectral control already implies the usual constructive
geometric correlator decay, because pruning changes no correlator. -/
theorem decay_of_weightedSpectralGap (S : SpectralModel) (mu : Q')
    (hmu : (0 : Q') ≤ mu)
    (hgap : WeightedSpectralGapBound S mu) (n : Nat) :
    corr S n ≤ (finSum S.w S.k) * mu ^ n := by
  have hcorr := weightPrunedModel_corr S n
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcorr)
    (decay_of_spectralGap (weightPrunedModel S) mu hmu
      (weightPrunedModel_gap S mu hmu hgap) n)

end YMGap.Continuum.SpectralSupportPruning

#print axioms YMGap.Continuum.SpectralSupportPruning.weightPrunedEigen_nonneg
#print axioms YMGap.Continuum.SpectralSupportPruning.weightPrunedModel_corr
#print axioms YMGap.Continuum.SpectralSupportPruning.weightPrunedModel_gap
#print axioms YMGap.Continuum.SpectralSupportPruning.weightedGap_of_weightPrunedModel_gap
#print axioms YMGap.Continuum.SpectralSupportPruning.decay_of_weightedSpectralGap
