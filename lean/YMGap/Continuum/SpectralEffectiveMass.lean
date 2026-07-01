/-
The SPECTRAL / EFFECTIVE-MASS layer: the gap as the long-time SURVIVAL RATE of the
Euclidean two-point function, and the effective-mass PLATEAU as its operational
witness.

# The physics — "the system has evolved" is a FEATURE, not a bug

The connected Euclidean two-point function of a local observable `O` is a
positive spectral sum over the energy eigenstates of the transfer operator:

    C_O(t) = ⟨Ω| O e^{−Ht} O |Ω⟩_c
           = Σ_{k≥1} |⟨k|O|Ω⟩|² e^{−E_k t}
           = Σ_{k≥1} |c_k|² λ_k^{t},     λ_k = e^{−E_k a}.

`O` creates a disturbance at `t = 0`; Euclidean time EVOLVES it; `O` measures the
survival at time `t`.  Higher states die faster (`e^{−E₂ t} ≪ e^{−E₁ t}`), so the
LOWEST non-vacuum energy dominates the long-time behaviour:

    C_O(t) ~ A₀ · e^{−m t},   m = E₁ = −log sep,   sep = λ₁ = second-largest
                                                          transfer eigenvalue.

The OPERATIONAL diagnostic is the effective mass

    m_eff(t) = (1/a)·log[ C(t) / C(t+a) ]  →  m_phys   as t → ∞,

whose PLATEAU is exactly the witness of a clean, isolated lowest state — a
spectral gap.  This module builds that structure OVER the repo's already-proved
character transfer spectrum: excited eigenvalues `λ_s = qpow w (c4 (s+1)) =
w^{C₄(s+1)}`, largest excited `sep = w³` (`= heatKernelSep w`), and the SECOND
gap `λ₂/λ₁ = w^{C₄(2)−C₄(1)} = w^{8−3} = w⁵ < 1`, which controls the plateau
rate.

# What this module delivers

  * `spectralTwoPoint` — the spectral-sum two-point function
    `C(t) = Σ_{s<N} coeffSq_s · (λ_s)^t` over the excited transfer eigenvalues
    `λ_s = qpow w (c4 (s+1))`, realized as `SpectralGap.corr` of a genuine
    `SpectralModel` (`specTwoPointModel`) whose eigenvalues coincide with
    `WilsonSpectralBridge.excitedCharModel` (`specTwoPointModel_lam`) and whose
    weights are the overlaps `coeffSq_s = |c_s|² ≥ 0`.

  * `spectralTwoPoint_upper` (PROVED) — the clean "higher states die faster"
    bound `C(t) ≤ C(0)·sep^t` (`sep = heatKernelSep w = w³`): every excited
    `λ_s ≤ sep` (`WilsonSpectralBridge.casimir_qpow_le`), so the whole sum is
    dominated by the `sep`-envelope.  This IS `C(t) ≤ A₀·e^{−m t}`,
    `m = −log sep`.

  * `spectralTwoPoint_dominance` (PROVED) — the lowest-state dominance
    sandwich, `coeffSq₀·sep^t ≤ C(t) ≤ coeffSq₀·sep^t + K_tail·λ₂^t`, with the
    subleading remainder controlled by the second eigenvalue `λ₂ = qpow w 8`.
    The EXPLICIT geometric modulus from the second gap is
    `λ₂ = sep · w⁵` (`lam2_eq`) with `w⁵ < 1` (`secondGapRatio_lt_one`): the
    subleading terms decay at RELATIVE rate `w⁵` per step, so `C(t)/sep^t →
    coeffSq₀` (a genuine positive number when the leading overlap
    `coeffSq₀ > 0`).

  * `effectiveMass` (PROVED — a definition) — the operational diagnostic
    `m_eff(t) = (1/a)·(log C(t) − log C(t+1))` built from the constructive
    `CReal` logarithm (`CRealLog.CReal.log`, the artanh series), taking the
    range-reduction data for `C(t)` as input.

  * `spectralTwoPoint_plateau` (PROVED) — the ratio-free correlator plateau
    `sep·C(t) ≤ C(t+1) + K_tail·λ₂^t` AND `C(t+1) ≤ sep·C(t) + K_tail·λ₂^t`:
    the successor ratio `C(t+1)/C(t) → sep` with geometric error `λ₂^t`, so the
    effective mass plateaus at `m_phys = −log sep`.  This is the substantive,
    log-free heart of the plateau; the single remaining step — `CReal`-log
    continuity turning this ratio plateau into an `m_eff(t) → m_phys`
    convergence — is carried as the NAMED, uninhabited residual
    `EffMassLogContinuity` (not faked).

  * `spectralGap_imp_correlationDecay` (PROVED) — the connection: the located
    spectral gap (`specTwoPointLocatedGap`) forces the per-spacing geometric
    correlation decay `C(t) ≤ C(0)·sep^t`, which is exactly the fixed-spacing
    content that `UniformCorrelationDecay.UniformPhysicalCorrelationDecay` must
    supply UNIFORMLY in the spacing `a`.  The gap also yields a genuine
    `UniformCorrelationDecay.MassGap` (`spectralMassGap`, `Δ = 1 − sep > 0`).
    The `a → 0` uniformity of the rate stays the honest OPEN input.

# Honest verdict

This layer GROUNDS the mass-gap input in the transfer-operator spectrum: it makes
`C(t) ~ A₀·e^{−m t}` and the effective-mass plateau precise, PROVED, and
axiom-clean over the real character spectrum, with the plateau modulus `w⁵` read
off the second Casimir gap.  It does NOT close 4D Yang–Mills: the coefficients
`coeffSq_s` (Peter–Weyl overlaps) and the spacing-UNIFORMITY of `sep` (the
continuum limit) remain the open inputs, and the `CReal`-log continuity that
upgrades the proved correlator plateau to a full `m_eff` convergence is the one
named residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat` arithmetic over the proved finite-sum, `qpow`, and `corr`
machinery, plus composition over the constructive `CReal` log; witnesses are
`Type`-level data, the open items are NAMED structures with NO inhabitant.  Every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `by_contra`, no `native_decide`, no `sorry`,
no custom axiom.
-/

import YMGap.Continuum.WilsonSpectralBridge
import YMGap.Continuum.UniformCorrelationDecay
import YMGap.Constructive.CRealLog
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SpectralEffectiveMass

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.WilsonSpectralBridge

/-! ## 0. Small `Q'` helpers reused throughout -/

/-- `finSum` of a nonnegative sequence is nonnegative. -/
theorem finSum_nonneg (f : QSeq) (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (finSum_nonneg f hf n) (hf n)

/-- `a·(b·c) ≃ b·(a·c)` — swap the outer factor inward (used for the leading
term recurrence `sep·(coeffSq₀·sep^t) ≃ coeffSq₀·(sep·sep^t)`). -/
theorem mul_swap_outer (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (a * b) (b * a) c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-- **`qpow` is additive in the exponent** (for the `RGTransport` right-fold
`qpow`): `qpow w (m+n) ≃ qpow w m · qpow w n`.  By induction on `n`. -/
theorem qpow_add_eqv (w : Q') (m : Nat) :
    ∀ n, (qpow w (m + n)).eqv (qpow w m * qpow w n)
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (qpow w m))
  | n + 1 => by
      -- qpow w (m+(n+1)) = qpow w ((m+n)+1) = qpow w (m+n) · w
      show (qpow w (m + n) * w).eqv (qpow w m * (qpow w n * w))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (qpow w (m + n)) (qpow w m * qpow w n) w
          (qpow_add_eqv w m n)) ?_
      exact Q'.mul_assoc_eqv (qpow w m) (qpow w n) w

/-! ## 1. The spectral two-point function `C(t) = Σ_s coeffSq_s · (λ_s)^t`

`specTwoPointModel` is a genuine `SpectralGap.SpectralModel`: `N` excited modes,
mode `s` (spin `s+1`) with WEIGHT the overlap `coeffSq_s = |⟨s|O|Ω⟩|² ≥ 0` and
EIGENVALUE the heat-kernel transfer value `λ_s = qpow w (c4 (s+1))` — exactly the
eigenvalues of `WilsonSpectralBridge.excitedCharModel`.  The two-point function
is its `SpectralGap.corr`. -/

/-- **The excited spectral model with overlap weights.**  Mode `s` carries the
overlap `coeffSq s` and the heat-kernel eigenvalue `qpow w (c4 (s+1))`. -/
def specTwoPointModel (w : Q') (hw0 : (0 : Q') ≤ w) (N : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) : SpectralModel where
  k := N
  w := coeffSq
  lam := fun i => qpow w (c4 (i + 1))
  w_nonneg := hc
  lam_nonneg := fun i => qpow_nonneg w hw0 (c4 (i + 1))

/-- The model's eigenvalues coincide with the `excitedCharModel` eigenvalues
`λ_s = qpow w (c4 (s+1))` (same transfer spectrum; only the weights differ). -/
@[simp] theorem specTwoPointModel_lam (w : Q') (hw0 : (0 : Q') ≤ w) (N : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (i : Nat) :
    (specTwoPointModel w hw0 N coeffSq hc).lam i = (excitedCharModel w hw0 N).lam i :=
  rfl

/-- **The spectral-sum two-point function** `C(t) = Σ_{s<N} coeffSq_s·(λ_s)^t`,
the connected Euclidean correlator as a positive spectral sum over the excited
transfer eigenvalues. -/
def spectralTwoPoint (w : Q') (hw0 : (0 : Q') ≤ w) (N : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) : Q' :=
  corr (specTwoPointModel w hw0 N coeffSq hc) t

/-- `C(0) = Σ_s coeffSq_s` — the total spectral weight `⟨OΩ, OΩ⟩`. -/
theorem spectralTwoPoint_zero (w : Q') (hw0 : (0 : Q') ≤ w) (N : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) :
    (spectralTwoPoint w hw0 N coeffSq hc 0).eqv (finSum coeffSq N) :=
  corr_zero (specTwoPointModel w hw0 N coeffSq hc)

/-! ## 2. The long-time upper bound — "higher states die faster"

Every excited eigenvalue clears the separator `sep = heatKernelSep w = w³`
(`casimir_qpow_le`), so the whole spectral sum is dominated by the `sep`-envelope:
`C(t) ≤ C(0)·sep^t`.  This is the clean `C(t) ≤ A₀·e^{−m t}`, `m = −log sep`. -/

/-- The excited spectrum clears the separator `sep = heatKernelSep w`: this is the
`SpectralGapBound` for the model. -/
theorem specTwoPoint_gapBound (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) :
    SpectralGapBound (specTwoPointModel w hw0 N coeffSq hc) (heatKernelSep w) :=
  fun i => casimir_qpow_le hw0 (Q'.le_of_lt hw1) i

/-- **`spectralTwoPoint_upper` (PROVED).**  The long-time survival bound
`C(t) ≤ C(0)·sep^t`, `sep = heatKernelSep w = w³`.  Because every excited
eigenvalue `λ_s ≤ sep` (`casimir_qpow_le`), each term `coeffSq_s·λ_s^t ≤
coeffSq_s·sep^t`, and the sum is `≤ (Σ_s coeffSq_s)·sep^t = C(0)·sep^t`.  The
"higher states die faster" bound: `C(t) ≤ A₀·e^{−m t}` with `m = −log sep`. -/
theorem spectralTwoPoint_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    spectralTwoPoint w hw0 N coeffSq hc t
      ≤ (spectralTwoPoint w hw0 N coeffSq hc 0) * (heatKernelSep w) ^ t :=
  decay_of_spectralGap_corr0 (specTwoPointModel w hw0 N coeffSq hc)
    (heatKernelSep w) (heatKernelSep_nonneg hw0)
    (specTwoPoint_gapBound w hw0 hw1 N coeffSq hc) t

/-! ## 3. Lowest-state dominance and the second-gap modulus `w⁵`

Peel the leading (spin-1, `s = 0`) term `coeffSq₀·sep^t` off the spectral sum.
The remainder runs over `s ≥ 1`, each with `λ_s ≤ λ₂ = qpow w 8`, so it is
bounded by `K_tail·λ₂^t`.  Since `λ₂ = sep·w⁵` (`lam2_eq`) with `w⁵ < 1`
(`secondGapRatio_lt_one`), the remainder decays at RELATIVE rate `w⁵` — the
second-gap modulus — and `C(t)/sep^t → coeffSq₀`. -/

/-- The leading (spin-1, `s = 0`) term `coeffSq₀·sep^t`, `sep = heatKernelSep w`. -/
def leadTerm (w : Q') (coeffSq : Nat → Q') (t : Nat) : Q' :=
  coeffSq 0 * (heatKernelSep w) ^ t

/-- The subleading remainder `Σ_{s=1}^{M} coeffSq_s·(λ_s)^t` (modes `s ≥ 1`). -/
def tailSum (w : Q') (coeffSq : Nat → Q') (M t : Nat) : Q' :=
  finSum (fun i => coeffSq (i + 1) * (qpow w (c4 (i + 1 + 1))) ^ t) M

/-- The total tail overlap `K_tail = Σ_{s=1}^{M} coeffSq_s`. -/
def tailWeight (coeffSq : Nat → Q') (M : Nat) : Q' :=
  finSum (fun i => coeffSq (i + 1)) M

/-- The second transfer eigenvalue `λ₂ = qpow w (c4 2) = qpow w 8 = w⁸`. -/
def lam2 (w : Q') : Q' := qpow w 8

/-- **The second-gap ratio** `w⁵ = λ₂ / λ₁ = qpow w 5`: the RELATIVE decay rate of
the subleading tower against the leading (spin-1) state. -/
def secondGapRatio (w : Q') : Q' := qpow w 5

/-- **`lam2_eq` — the explicit second-gap modulus.**  `λ₂ = sep · w⁵`, i.e.
`qpow w 8 ≃ heatKernelSep w · qpow w 5` (since `8 = 3 + 5 = C₄(2)`).  Exposes the
relative decay rate `λ₂/sep = w⁵`. -/
theorem lam2_eq (w : Q') : (lam2 w).eqv (heatKernelSep w * secondGapRatio w) :=
  qpow_add_eqv w 3 5

/-- **`secondGapRatio_lt_one` (PROVED).**  The relative modulus `w⁵ < 1` for
`0 ≤ w < 1` (`qpow w (4+1) < 1`): the subleading tower is strictly suppressed
against the leading state each step. -/
theorem secondGapRatio_lt_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    secondGapRatio w < (1 : Q') :=
  qpow_succ_lt_one hw0 hw1 4

/-- `λ₂ = qpow w 8 ≥ 0`. -/
theorem lam2_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) : (0 : Q') ≤ lam2 w :=
  qpow_nonneg w hw0 8

/-- `λ₂ = qpow w 8 ≤ 1` for `0 ≤ w ≤ 1`. -/
theorem lam2_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    lam2 w ≤ (1 : Q') :=
  qpow_le_one hw0 hw1 8

/-- `sep = heatKernelSep w ≤ 1` for `0 ≤ w ≤ 1`. -/
theorem sep_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    heatKernelSep w ≤ (1 : Q') :=
  qpow_le_one hw0 hw1 3

/-- **The spectral-sum split** `C(t) ≃ coeffSq₀·sep^t + tailSum`: peel the leading
(spin-1) term off the finite spectral sum (`finSum_peel_left`).  `sep = qpow w
(c4 1)` definitionally, so the peeled head IS `leadTerm`. -/
theorem spectralTwoPoint_split (w : Q') (hw0 : (0 : Q') ≤ w) (M : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    (spectralTwoPoint w hw0 (M + 1) coeffSq hc t).eqv
      (leadTerm w coeffSq t + tailSum w coeffSq M t) :=
  finSum_peel_left (fun i => coeffSq i * (qpow w (c4 (i + 1))) ^ t) M

/-- `tailSum ≥ 0` (a sum of nonnegative terms). -/
theorem tailSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (coeffSq : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ coeffSq i) (M t : Nat) :
    (0 : Q') ≤ tailSum w coeffSq M t :=
  finSum_nonneg _ (fun i => Q'.mul_nonneg _ _ (hc (i + 1))
    (Q'.pow_nonneg _ (qpow_nonneg w hw0 (c4 (i + 1 + 1))) t)) M

/-- Each tail eigenvalue clears the second separator: `qpow w (c4 (i+2)) ≤ λ₂`
(since `c4 (i+2) = (i+2)(i+4) ≥ 8 = c4 2`). -/
theorem tail_lam_le_lam2 {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (i : Nat) : qpow w (c4 (i + 1 + 1)) ≤ lam2 w := by
  have h8 : 8 ≤ c4 (i + 1 + 1) := by
    show 8 ≤ (i + 1 + 1) * ((i + 1 + 1) + 2)
    calc 8 = 2 * 4 := by decide
      _ ≤ (i + 1 + 1) * ((i + 1 + 1) + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨d, hd⟩ := Nat.le.dest h8
  show qpow w (c4 (i + 1 + 1)) ≤ qpow w 8
  rw [← hd]
  exact qpow_ge_shift hw0 hw1 8 d

/-- **`tailSum_le` (PROVED).**  The subleading remainder is bounded by the
second-eigenvalue envelope: `tailSum ≤ K_tail·λ₂^t`.  Each excited base
`λ_s ≤ λ₂` (`tail_lam_le_lam2`), so each term `≤ coeffSq_s·λ₂^t`, and the sum is
`≤ (Σ coeffSq_s)·λ₂^t`. -/
theorem tailSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (M t : Nat) :
    tailSum w coeffSq M t ≤ (tailWeight coeffSq M) * (lam2 w) ^ t := by
  have htw : tailSum w coeffSq M t
      ≤ finSum (fun i => coeffSq (i + 1) * (lam2 w) ^ t) M := by
    apply finSum_le_of_termwise
    intro i
    have hbase : (qpow w (c4 (i + 1 + 1))) ^ t ≤ (lam2 w) ^ t :=
      pow_le_pow_left (qpow_nonneg w hw0 (c4 (i + 1 + 1)))
        (tail_lam_le_lam2 hw0 hw1 i) t
    exact Q'.mul_le_mul_of_nonneg_left _ _ (coeffSq (i + 1)) hbase (hc (i + 1))
  refine Q'.le_trans' _ _ _ htw ?_
  exact finSum_mul_const_le (fun i => coeffSq (i + 1)) ((lam2 w) ^ t)
    (Q'.pow_nonneg _ (lam2_nonneg hw0) t) M

/-- **`spectralTwoPoint_dominance` (PROVED) — lowest-state dominance sandwich.**

    coeffSq₀·sep^t  ≤  C(t)  ≤  coeffSq₀·sep^t + K_tail·λ₂^t.

The lower bound drops the nonnegative remainder; the upper bound bounds it by the
second-eigenvalue envelope.  With `λ₂ = sep·w⁵` (`lam2_eq`) and `w⁵ < 1`
(`secondGapRatio_lt_one`), the normalized remainder `(C(t) − coeffSq₀·sep^t)/sep^t
≤ K_tail·(w⁵)^t → 0`, i.e. `C(t)/sep^t → coeffSq₀` — the lowest-state dominance,
a genuine positive number when the leading overlap `coeffSq₀ > 0`. -/
theorem spectralTwoPoint_dominance (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (M : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    leadTerm w coeffSq t ≤ spectralTwoPoint w hw0 (M + 1) coeffSq hc t
    ∧ spectralTwoPoint w hw0 (M + 1) coeffSq hc t
        ≤ leadTerm w coeffSq t + (tailWeight coeffSq M) * (lam2 w) ^ t := by
  have hsplit := spectralTwoPoint_split w hw0 M coeffSq hc t
  refine ⟨?_, ?_⟩
  · -- leadTerm ≤ leadTerm + tailSum ≃ C(t)
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (leadTerm w coeffSq t) (tailSum w coeffSq M t)
        (tailSum_nonneg hw0 coeffSq hc M t)) ?_
    exact Q'.ge_of_eqv hsplit
  · -- C(t) ≃ leadTerm + tailSum ≤ leadTerm + K_tail·λ₂^t
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    exact Q'.add_le_add_left (leadTerm w coeffSq t) (tailSum w coeffSq M t)
      ((tailWeight coeffSq M) * (lam2 w) ^ t) (tailSum_le hw0 hw1 coeffSq hc M t)

/-! ## 4. The effective mass `m_eff(t) = (1/a)·(log C(t) − log C(t+1))`

The operational diagnostic, built from the constructive `CReal` logarithm
(`CRealLog.CReal.log`, the genuine artanh series).  The physical `1/a` is a
positive-rational rescale `ainv`; the difference of logs is the constructive
`CReal.sub`.  Taking the range-reduction data as input keeps the definition
honest (the general `CReal` log rests on `CRealLog.CRealLogRangeReduction`). -/

/-- **`effectiveMass` (a definition).**  `m_eff(t) = (1/a)·(log C(t) − log C(t+1))`
as a constructive real.  `Ct`, `Ct1` are the correlator values `C(t)`, `C(t+1)`
lifted to `CReal`; `redT`, `redT1` are their `CReal`-log range-reduction data. -/
def effectiveMass (ainv : Q') (Ct Ct1 : CReal)
    (redT : CRealLog.CRealLogRangeReduction Ct)
    (redT1 : CRealLog.CRealLogRangeReduction Ct1) : CReal :=
  CReal.mul (CReal.ofQ' ainv)
    (CReal.sub (CRealLog.CReal.log Ct redT) (CRealLog.CReal.log Ct1 redT1))

/-- The step-unit effective mass (`a = 1`): `m_eff(t) = log C(t) − log C(t+1)`. -/
def effectiveMassStep (Ct Ct1 : CReal)
    (redT : CRealLog.CRealLogRangeReduction Ct)
    (redT1 : CRealLog.CRealLogRangeReduction Ct1) : CReal :=
  CReal.sub (CRealLog.CReal.log Ct redT) (CRealLog.CReal.log Ct1 redT1)

/-! ## 5. The plateau — the operational mass-gap witness

The effective-mass plateau `m_eff(t) → m_phys = −log sep` is, at the correlator
level, the statement that the successor ratio `C(t+1)/C(t) → sep`.  We PROVE the
ratio-free form: `C(t+1)` and `sep·C(t)` differ by at most `K_tail·λ₂^t → 0`
(both directions).  This is the substantive, log-free heart of the plateau; the
`CReal`-log continuity that turns it into an `m_eff(t) → m_phys` statement is the
one NAMED residual. -/

/-- `sep · leadTerm(t) ≃ leadTerm(t+1)` (the leading term is a pure geometric
`coeffSq₀·sep^t`, whose ratio is exactly `sep`). -/
theorem sep_mul_leadTerm (w : Q') (coeffSq : Nat → Q') (t : Nat) :
    (heatKernelSep w * leadTerm w coeffSq t).eqv (leadTerm w coeffSq (t + 1)) := by
  -- sep·(coeffSq₀·sep^t) ≃ coeffSq₀·(sep·sep^t) = coeffSq₀·sep^(t+1)
  unfold leadTerm
  refine Q'.eqv_trans _ _ _
    (mul_swap_outer (heatKernelSep w) (coeffSq 0) ((heatKernelSep w) ^ t)) ?_
  -- coeffSq₀·(sep·sep^t) = coeffSq₀·sep^(t+1)
  show (coeffSq 0 * (heatKernelSep w * (heatKernelSep w) ^ t)).eqv
        (coeffSq 0 * (heatKernelSep w) ^ (t + 1))
  exact Q'.eqv_refl _

/-- `sep·C(t) ≃ leadTerm(t+1) + sep·tailSum`. -/
theorem sep_mul_corr (w : Q') (hw0 : (0 : Q') ≤ w) (M : Nat)
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    (heatKernelSep w * spectralTwoPoint w hw0 (M + 1) coeffSq hc t).eqv
      (leadTerm w coeffSq (t + 1) + heatKernelSep w * tailSum w coeffSq M t) := by
  have hsplit := spectralTwoPoint_split w hw0 M coeffSq hc t
  -- sep·C(t) ≃ sep·(leadTerm + tailSum) ≃ sep·leadTerm + sep·tailSum
  --         ≃ leadTerm(t+1) + sep·tailSum
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (heatKernelSep w) _ _ hsplit) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (heatKernelSep w) (leadTerm w coeffSq t) (tailSum w coeffSq M t)) ?_
  exact Q'.add_eqv_congr_right _ _ (heatKernelSep w * tailSum w coeffSq M t)
    (sep_mul_leadTerm w coeffSq t)

/-- `tailSum(t+1) ≤ K_tail·λ₂^t` (the tail at `t+1` is `≤ K_tail·λ₂^{t+1} ≤
K_tail·λ₂^t` since `λ₂ ≤ 1`). -/
theorem tailSum_succ_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (M t : Nat) :
    tailSum w coeffSq M (t + 1) ≤ (tailWeight coeffSq M) * (lam2 w) ^ t := by
  refine Q'.le_trans' _ _ _ (tailSum_le hw0 hw1 coeffSq hc M (t + 1)) ?_
  -- K_tail·λ₂^{t+1} = K_tail·(λ₂·λ₂^t) ≤ K_tail·(1·λ₂^t) ≃ K_tail·λ₂^t
  have hKtail : (0 : Q') ≤ tailWeight coeffSq M :=
    finSum_nonneg _ (fun i => hc (i + 1)) M
  have hpow : (0 : Q') ≤ (lam2 w) ^ t := Q'.pow_nonneg _ (lam2_nonneg hw0) t
  have hstep : (lam2 w) ^ (t + 1) ≤ (lam2 w) ^ t := by
    show lam2 w * (lam2 w) ^ t ≤ (lam2 w) ^ t
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (lam2 w) 1 ((lam2 w) ^ t) (lam2_le_one hw0 hw1) hpow) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv ((lam2 w) ^ t))
  exact Q'.mul_le_mul_of_nonneg_left _ _ (tailWeight coeffSq M) hstep hKtail

/-- `sep·tailSum(t) ≤ K_tail·λ₂^t` (`sep ≤ 1` and `tailSum ≤ K_tail·λ₂^t`). -/
theorem sep_mul_tailSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (M t : Nat) :
    heatKernelSep w * tailSum w coeffSq M t ≤ (tailWeight coeffSq M) * (lam2 w) ^ t := by
  have hbound : (0 : Q') ≤ (tailWeight coeffSq M) * (lam2 w) ^ t :=
    Q'.mul_nonneg _ _ (finSum_nonneg _ (fun i => hc (i + 1)) M)
      (Q'.pow_nonneg _ (lam2_nonneg hw0) t)
  -- sep·tail ≤ sep·(K_tail·λ₂^t) ≤ 1·(K_tail·λ₂^t) ≃ K_tail·λ₂^t
  have h1 : heatKernelSep w * tailSum w coeffSq M t
      ≤ heatKernelSep w * ((tailWeight coeffSq M) * (lam2 w) ^ t) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (heatKernelSep w)
      (tailSum_le hw0 hw1 coeffSq hc M t) (heatKernelSep_nonneg hw0)
  have h2 : heatKernelSep w * ((tailWeight coeffSq M) * (lam2 w) ^ t)
      ≤ (1 : Q') * ((tailWeight coeffSq M) * (lam2 w) ^ t) :=
    Q'.mul_le_mul_of_nonneg_right (heatKernelSep w) 1 _ (sep_le_one hw0 hw1) hbound
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
    (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-- **`spectralTwoPoint_plateau` (PROVED) — the ratio-free correlator plateau.**

    sep·C(t)  ≤  C(t+1) + K_tail·λ₂^t     (lower)
    C(t+1)    ≤  sep·C(t) + K_tail·λ₂^t     (upper)

`C(t+1)` and `sep·C(t)` differ by at most `K_tail·λ₂^t → 0` (`λ₂ = qpow w 8 < 1`),
so the successor ratio `C(t+1)/C(t) → sep`, i.e. the effective mass PLATEAUS at
`m_phys = −log sep`.  Both sides use `C(t) ≃ leadTerm + tailSum`, the exact
leading recurrence `sep·leadTerm(t) ≃ leadTerm(t+1)`, and the tail bounds. -/
theorem spectralTwoPoint_plateau (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (M : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    heatKernelSep w * spectralTwoPoint w hw0 (M + 1) coeffSq hc t
        ≤ spectralTwoPoint w hw0 (M + 1) coeffSq hc (t + 1)
          + (tailWeight coeffSq M) * (lam2 w) ^ t
    ∧ spectralTwoPoint w hw0 (M + 1) coeffSq hc (t + 1)
        ≤ heatKernelSep w * spectralTwoPoint w hw0 (M + 1) coeffSq hc t
          + (tailWeight coeffSq M) * (lam2 w) ^ t := by
  have hsepC := sep_mul_corr w hw0 M coeffSq hc t
  have hCsucc := spectralTwoPoint_split w hw0 M coeffSq hc (t + 1)
  refine ⟨?_, ?_⟩
  · -- sep·C(t) ≃ L(t+1) + sep·tail(t) ≤ L(t+1) + (tail(t+1) + Ktail)
    --          ≃ (L(t+1) + tail(t+1)) + Ktail ≃ C(t+1) + Ktail
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsepC) ?_
    -- sep·tail(t) ≤ Ktail ≤ Ktail + tail(t+1) ≃ tail(t+1) + Ktail
    have hstep : heatKernelSep w * tailSum w coeffSq M t
        ≤ tailSum w coeffSq M (t + 1) + (tailWeight coeffSq M) * (lam2 w) ^ t := by
      refine Q'.le_trans' _ _ _ (sep_mul_tailSum_le hw0 hw1 coeffSq hc M t) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg ((tailWeight coeffSq M) * (lam2 w) ^ t)
          (tailSum w coeffSq M (t + 1))
          (tailSum_nonneg hw0 coeffSq hc M (t + 1))) ?_
      exact Q'.le_of_eqv (Q'.add_comm_eqv ((tailWeight coeffSq M) * (lam2 w) ^ t)
        (tailSum w coeffSq M (t + 1)))
    -- L(t+1) + sep·tail(t) ≤ L(t+1) + (tail(t+1) + Ktail) ≃ (C(t+1)) + Ktail
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (leadTerm w coeffSq (t + 1)) _ _ hstep) ?_
    -- L(t+1) + (tail(t+1) + Ktail) ≃ (L(t+1) + tail(t+1)) + Ktail ≃ C(t+1) + Ktail
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (leadTerm w coeffSq (t + 1))
        (tailSum w coeffSq M (t + 1)) ((tailWeight coeffSq M) * (lam2 w) ^ t))) ?_
    exact Q'.add_eqv_congr_right _ _ ((tailWeight coeffSq M) * (lam2 w) ^ t)
      (Q'.eqv_symm hCsucc)
  · -- C(t+1) ≃ L(t+1) + tail(t+1) ≤ (L(t+1) + sep·tail(t)) + Ktail ≃ sep·C(t) + Ktail
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hCsucc) ?_
    -- tail(t+1) ≤ Ktail ≤ Ktail + sep·tail(t) ≃ sep·tail(t) + Ktail
    have hstep : tailSum w coeffSq M (t + 1)
        ≤ heatKernelSep w * tailSum w coeffSq M t + (tailWeight coeffSq M) * (lam2 w) ^ t := by
      refine Q'.le_trans' _ _ _ (tailSum_succ_le hw0 hw1 coeffSq hc M t) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg ((tailWeight coeffSq M) * (lam2 w) ^ t)
          (heatKernelSep w * tailSum w coeffSq M t)
          (Q'.mul_nonneg _ _ (heatKernelSep_nonneg hw0)
            (tailSum_nonneg hw0 coeffSq hc M t))) ?_
      exact Q'.le_of_eqv (Q'.add_comm_eqv ((tailWeight coeffSq M) * (lam2 w) ^ t)
        (heatKernelSep w * tailSum w coeffSq M t))
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (leadTerm w coeffSq (t + 1)) _ _ hstep) ?_
    -- L(t+1) + (sep·tail(t) + Ktail) ≃ (L(t+1) + sep·tail(t)) + Ktail ≃ sep·C(t) + Ktail
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (leadTerm w coeffSq (t + 1))
        (heatKernelSep w * tailSum w coeffSq M t) ((tailWeight coeffSq M) * (lam2 w) ^ t))) ?_
    exact Q'.add_eqv_congr_right _ _ ((tailWeight coeffSq M) * (lam2 w) ^ t)
      (Q'.eqv_symm hsepC)

/-- **NAMED residual: `CReal`-log continuity at the plateau (uninhabited).**

The single remaining step of the effective-mass plateau: upgrade the PROVED
ratio-free correlator plateau (`spectralTwoPoint_plateau`, `C(t+1)/C(t) → sep`
with geometric error) to a convergence of the `CReal` effective mass,
`m_eff(t) → m_phys`.  This requires the (standard) continuity of the constructive
`CReal` logarithm at the plateau ratio — carried here as `Type`-level data (the
target `m_phys` and the modulus turning the correlator error into an `m_eff`
error), with NO inhabitant.  It is NOT faked. -/
structure EffMassLogContinuity (ainv w : Q') (C : Nat → Q') : Type where
  /-- The physical mass `m_phys = ainv·(−log sep)` as a `CReal`. -/
  mPhys : CReal
  /-- The `CReal`-log range-reduction data for each correlator value `C(t)`. -/
  red : (t : Nat) → CRealLog.CRealLogRangeReduction (CReal.ofQ' (C t))
  /-- The plateau modulus: for every tolerance `η > 0` a time `T` past which the
  effective mass is within `η` of `m_phys` (as a two-sided `CReal` order bound). -/
  modulus : (η : Q') → (0 : Q') < η →
    { T : Nat // ∀ t, T ≤ t →
        CReal.leEv
          (effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1))) (red t) (red (t + 1)))
          (CReal.add mPhys (CReal.ofQ' η))
        ∧ CReal.leEv
          (mPhys)
          (CReal.add
            (effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1))) (red t) (red (t + 1)))
            (CReal.ofQ' η)) }

/-! ## 6. Connection: the located spectral gap grounds the correlation decay

The excited spectral model carries a genuine `LocatedSpectralGap` (`sep =
heatKernelSep w < 1`, every excited eigenvalue below it).  That gap FORCES the
per-spacing geometric correlation decay `C(t) ≤ C(0)·sep^t` — exactly the
fixed-spacing content of `UniformCorrelationDecay.UniformPhysicalCorrelationDecay`
— and yields a genuine `UniformCorrelationDecay.MassGap` `Δ = 1 − sep > 0`.  The
`a → 0` uniformity of `sep` stays the honest open input. -/

/-- **The located spectral gap of the excited two-point model.** -/
def specTwoPointLocatedGap (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) :
    LocatedSpectralGap (specTwoPointModel w hw0 N coeffSq hc) where
  sep := heatKernelSep w
  sep_lt_one := heatKernelSep_lt_one hw0 hw1
  bound := fun i => casimir_qpow_le hw0 (Q'.le_of_lt hw1) i

/-- **`spectralGap_imp_correlationDecay` (PROVED).**  The located spectral gap
forces the per-spacing geometric correlation decay `C(t) ≤ C(0)·sep^t`,
`sep = heatKernelSep w < 1`.  This is precisely the fixed-spacing content that
`UniformCorrelationDecay.UniformPhysicalCorrelationDecay` must supply UNIFORMLY in
the lattice spacing `a`; the spectral picture GROUNDS the correlation-decay
statement (the `a → 0` uniformity of `sep` stays the open input). -/
theorem spectralGap_imp_correlationDecay (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (N : Nat) (coeffSq : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ coeffSq i) (t : Nat) :
    spectralTwoPoint w hw0 N coeffSq hc t
      ≤ (spectralTwoPoint w hw0 N coeffSq hc 0) * (heatKernelSep w) ^ t :=
  (specTwoPointLocatedGap w hw0 hw1 N coeffSq hc).decay t

/-- **`spectralMassGap` (PROVED).**  The located gap yields a genuine
`UniformCorrelationDecay.MassGap`: the reconstructed margin `Δ = 1 − sep > 0`
(`LocatedSpectralGap.gapMargin_pos`) lifted to a positive `CReal`.  This is the
SAME constructive mass gap the physical correlation-decay input carries. -/
def spectralMassGap (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (coeffSq : Nat → Q') (hc : ∀ i, (0 : Q') ≤ coeffSq i) :
    UniformCorrelationDecay.MassGap where
  m := CReal.ofQ' (specTwoPointLocatedGap w hw0 hw1 N coeffSq hc).gapMargin
  pos :=
    { floor := (specTwoPointLocatedGap w hw0 hw1 N coeffSq hc).gapMargin
      floor_pos := (specTwoPointLocatedGap w hw0 hw1 N coeffSq hc).gapMargin_pos
      floor_le := CReal.le_refl _ }

end YMGap.Continuum.SpectralEffectiveMass

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpectralEffectiveMass.qpow_add_eqv
#print axioms YMGap.Continuum.SpectralEffectiveMass.specTwoPointModel_lam
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralTwoPoint_zero
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralTwoPoint_upper
#print axioms YMGap.Continuum.SpectralEffectiveMass.lam2_eq
#print axioms YMGap.Continuum.SpectralEffectiveMass.secondGapRatio_lt_one
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralTwoPoint_split
#print axioms YMGap.Continuum.SpectralEffectiveMass.tailSum_le
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralTwoPoint_dominance
#print axioms YMGap.Continuum.SpectralEffectiveMass.effectiveMass
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralTwoPoint_plateau
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralGap_imp_correlationDecay
#print axioms YMGap.Continuum.SpectralEffectiveMass.spectralMassGap
