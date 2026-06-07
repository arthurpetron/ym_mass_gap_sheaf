/-
Finite-volume spectral gap ⇒ correlator clustering (cluster→gap, folded).

# Why this module exists

`Continuum/OSReconstruction.lean` carries the cluster↔gap relationship as
a `True`-valued interface Prop (`HasSpectralGap`, `ClusterImpliesGap`):
the substantive content lived only in the paper, because the *continuum*
statement needs the spectral theorem for unbounded self-adjoint operators
(Källén–Lehmann), a major constructive-analysis build-out the Q′/CReal
stack does not yet have.

But at **finite lattice volume** the transfer matrix is a genuine finite
positive matrix, so its spectral decomposition is a *finite* positive
sum and the Källén–Lehmann representation is elementary:

    G(n) = Σ_i w_i · λ_i^n,   w_i ≥ 0,  λ_i ≥ 0,

the connected two-point function at integer time separation `n`, with
`λ_i = e^{-E_i}` the transfer-matrix eigenvalues and `w_i` the (positive)
spectral weights `|⟨Ω, A i⟩|²`. This is exactly the object the lattice
glueball analysis measures (the GEVP effective mass is `−log λ_0`).

This module folds the **gap ⇒ clustering** direction into a *proved,
constructive, axiom-clean* Lean theorem over that finite spectral model:
a spectral gap (`λ_i ≤ μ` for all modes) forces the correlator to be
bounded by the geometric envelope `(Σ_i w_i)·μ^n` — exponential decay at
rate `−log μ`. The converse (clustering ⇒ gap), the physically
load-bearing direction, is scoped in
`docs/uniform-parametric-bound-plan.md` (folding plan) with its
division-free pair-Bernoulli proof; it is not yet discharged here.

This gives the redundancy the program targets: the cluster→gap link now
exists as **paper** (continuum proof), **code** (the measured GEVP decay
rate), and **Lean** (this finite-volume theorem), rather than paper-only.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` only (via the reused Q′ order lemmas).
No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.Geometric
import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.SpectralGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## `Q'` power is monotone in the base

`0 ≤ a ≤ b ⇒ a^n ≤ b^n`. The missing pow-monotonicity lemma (only the
half-base case existed, in `ExpNeg`); proved here by induction on `n`
from `mul_le_mul_of_nonneg_{left,right}`. Reusable across the program. -/
theorem pow_le_pow_left {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero =>
      show (1 : Q') ≤ 1
      exact Q'.le_refl' 1
  | succ n ih =>
      have hb : (0 : Q') ≤ b := Q'.le_trans' 0 a b ha hab
      show a * a ^ n ≤ b * b ^ n
      have h1 : a * a ^ n ≤ b * a ^ n :=
        Q'.mul_le_mul_of_nonneg_right a b (a ^ n) hab (Q'.pow_nonneg a ha n)
      have h2 : b * a ^ n ≤ b * b ^ n :=
        Q'.mul_le_mul_of_nonneg_left (a ^ n) (b ^ n) b ih hb
      exact Q'.le_trans' _ _ _ h1 h2

/-! ## Termwise `finSum` lemmas (self-contained) -/

/-- Termwise `≤` lifts to `finSum`. -/
theorem finSum_le_of_termwise (f g : QSeq) (h : ∀ i, f i ≤ g i) :
    ∀ n, finSum f n ≤ finSum g n
  | 0 => by
      show (0 : Q') ≤ 0
      exact Q'.le_refl' 0
  | n + 1 => by
      show finSum f n + f n ≤ finSum g n + g n
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_left (finSum f n) (f n) (g n) (h n))
        (Q'.add_le_add_right (finSum f n) (finSum g n) (g n)
          (finSum_le_of_termwise f g h n))

/-- Termwise `eqv` lifts to `finSum`. -/
theorem finSum_eqv_of_termwise (f g : QSeq) (h : ∀ i, (f i).eqv (g i)) :
    ∀ n, (finSum f n).eqv (finSum g n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (finSum f n + f n).eqv (finSum g n + g n)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (finSum f n) (finSum g n) (f n)
          (finSum_eqv_of_termwise f g h n))
        (Q'.add_eqv_congr_left (finSum g n) (f n) (g n) (h n))

/-! ## The finite positive spectral model

A finite Källén–Lehmann decomposition: `k` modes, nonnegative weights
`w` and nonnegative transfer-matrix eigenvalues `lam`. Only the first
`k` entries of the `QSeq`s are read. -/
structure SpectralModel where
  /-- Number of spectral modes (finite at fixed lattice volume). -/
  k : Nat
  /-- Spectral weights `w_i = |⟨Ω, A i⟩|² ≥ 0`. -/
  w : QSeq
  /-- Transfer-matrix eigenvalues `λ_i = e^{-E_i} ≥ 0`. -/
  lam : QSeq
  /-- Weights are nonnegative (reflection positivity). -/
  w_nonneg : ∀ i, (0 : Q') ≤ w i
  /-- Eigenvalues are nonnegative (positive transfer matrix). -/
  lam_nonneg : ∀ i, (0 : Q') ≤ lam i

/-- The connected two-point function at integer time separation `n`:
`G(n) = Σ_{i<k} w_i · λ_i^n`. -/
def corr (S : SpectralModel) (n : Nat) : Q' :=
  finSum (fun i => S.w i * (S.lam i) ^ n) S.k

/-- A spectral gap at `μ`: every excited eigenvalue is `≤ μ`
(every energy is `≥ −log μ`). -/
def SpectralGapBound (S : SpectralModel) (μ : Q') : Prop :=
  ∀ i, S.lam i ≤ μ

/-- `corr(0) = Σ_i w_i` — the total spectral weight `⟨AΩ, AΩ⟩`. -/
theorem corr_zero (S : SpectralModel) : (corr S 0).eqv (finSum S.w S.k) := by
  show (finSum (fun i => S.w i * (S.lam i) ^ 0) S.k).eqv (finSum S.w S.k)
  apply finSum_eqv_of_termwise
  intro i
  show (S.w i * (S.lam i) ^ 0).eqv (S.w i)
  have h0 : (S.lam i) ^ 0 = (1 : Q') := Q'.pow_zero (S.lam i)
  rw [h0]
  exact Q'.mul_one_eqv (S.w i)

/-! ## Pulling the common factor out of the envelope sum

`Σ_i (f i · c) ≤ (Σ_i f i) · c` for nonnegative data. The `≤` direction
suffices and its base case avoids `zero_mul`. -/
theorem finSum_mul_const_le (f : QSeq) (c : Q') (hc : (0 : Q') ≤ c) :
    ∀ m, finSum (fun i => f i * c) m ≤ (finSum f m) * c
  | 0 => by
      show (0 : Q') ≤ (0 : Q') * c
      exact Q'.mul_nonneg 0 c (Q'.le_refl' 0) hc
  | m + 1 => by
      show finSum (fun i => f i * c) m + f m * c ≤ (finSum f m + f m) * c
      have hdist :
          ((finSum f m + f m) * c).eqv ((finSum f m) * c + f m * c) :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (finSum f m + f m) c)
          (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (finSum f m) (f m))
            (Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right (c * finSum f m) ((finSum f m) * c) (c * f m)
                (Q'.mul_comm_eqv c (finSum f m)))
              (Q'.add_eqv_congr_left ((finSum f m) * c) (c * f m) (f m * c)
                (Q'.mul_comm_eqv c (f m)))))
      have ih := finSum_mul_const_le f c hc m
      have step : finSum (fun i => f i * c) m + f m * c
          ≤ (finSum f m) * c + f m * c :=
        Q'.add_le_add_right (finSum (fun i => f i * c) m) ((finSum f m) * c) (f m * c) ih
      exact Q'.le_trans' _ _ _ step (Q'.ge_of_eqv hdist)

/-! ## Gap ⇒ exponential clustering (the folded theorem) -/

/-- Spectral gap ⇒ correlator bounded termwise by the `μ`-envelope. -/
theorem corr_le_envelope (S : SpectralModel) (μ : Q')
    (hgap : SpectralGapBound S μ) (n : Nat) :
    corr S n ≤ finSum (fun i => S.w i * μ ^ n) S.k := by
  show finSum (fun i => S.w i * (S.lam i) ^ n) S.k
      ≤ finSum (fun i => S.w i * μ ^ n) S.k
  apply finSum_le_of_termwise
  intro i
  have hlam : (S.lam i) ^ n ≤ μ ^ n :=
    pow_le_pow_left (S.lam_nonneg i) (hgap i) n
  exact Q'.mul_le_mul_of_nonneg_left ((S.lam i) ^ n) (μ ^ n) (S.w i) hlam (S.w_nonneg i)

/-- **Gap ⇒ geometric decay (Källén–Lehmann, finite volume).**

A spectral gap at `μ ≥ 0` forces exponential clustering: the connected
two-point function decays at least as fast as `(Σ_i w_i)·μ^n`. By
`corr_zero`, `Σ_i w_i = corr(0)`, so this is `G(n) ≤ G(0)·μ^n` — the
finite-volume, constructive, axiom-clean form of the gap ⇒ clustering
content abstracted in `OSReconstruction.ClusterImpliesGap`. -/
theorem decay_of_spectralGap (S : SpectralModel) (μ : Q') (hμ : (0 : Q') ≤ μ)
    (hgap : SpectralGapBound S μ) (n : Nat) :
    corr S n ≤ (finSum S.w S.k) * μ ^ n :=
  Q'.le_trans' _ _ _ (corr_le_envelope S μ hgap n)
    (finSum_mul_const_le S.w (μ ^ n) (Q'.pow_nonneg μ hμ n) S.k)

/-- The same bound phrased with `corr(0)` in place of `Σ_i w_i`. -/
theorem decay_of_spectralGap_corr0 (S : SpectralModel) (μ : Q') (hμ : (0 : Q') ≤ μ)
    (hgap : SpectralGapBound S μ) (n : Nat) :
    corr S n ≤ (corr S 0) * μ ^ n :=
  Q'.le_trans' _ _ _ (decay_of_spectralGap S μ hμ hgap n)
    (Q'.mul_le_mul_of_nonneg_right (finSum S.w S.k) (corr S 0) (μ ^ n)
      (Q'.ge_of_eqv (corr_zero S)) (Q'.pow_nonneg μ hμ n))

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms pow_le_pow_left
#print axioms finSum_le_of_termwise
#print axioms finSum_eqv_of_termwise
#print axioms corr_zero
#print axioms finSum_mul_const_le
#print axioms corr_le_envelope
#print axioms decay_of_spectralGap
#print axioms decay_of_spectralGap_corr0

end YMGap.Continuum.SpectralGap
