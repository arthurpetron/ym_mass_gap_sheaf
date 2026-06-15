/-
Track B / R2 — the LOCATED spectral gap of the finite (compact) transfer operator.

# Why this module (the constructive-spectral-theory verdict)

Deep research into the continuum frontier (OS reconstruction + the mass gap)
established a decisive constructive fact:

  * For a GENERAL bounded self-adjoint / normal operator the spectrum is only
    *lower-semicomputable* (Brattka–Dillhage, J.UCS 11(12), 2005): a fully
    LOCATED spectrum is constructively IMPOSSIBLE, and the unbounded
    self-adjoint spectral theorem + Stone's theorem are therefore to be
    AVOIDED in a choice-free / `CReal` setting.
  * BUT for a COMPACT self-adjoint operator the spectrum IS fully located
    (positive AND negative information; `σ(T)` is a recursive compact set).

The finite-volume Yang–Mills transfer operator is finite-dimensional, hence
compact, hence its spectrum is constructively located.  This module makes that
precise for the repo's `SpectralModel` (the finite Källén–Lehmann transfer
data): it upgrades the bare `SpectralGapBound` predicate (`∀ i, λᵢ ≤ μ`) to a
genuinely LOCATED gap — a COMPUTABLE top-of-(excited)-spectrum `specMax`, the
DECIDABLE separation `specMax ≤ μ`, and a Type-level `LocatedSpectralGap`
witness carrying `sep < 1` (the located second eigenvalue strictly below the
vacuum eigenvalue `1`).  This is the constructive content the mass gap should
rest on — at the bounded transfer-operator level, with the continuum
self-adjoint Hamiltonian only an interpretation layer.

Everything is axiom-clean (`propext` / `Quot.sound` only), pure `Q'`/`Nat`,
and reuses the proven finite-volume decay (`decay_of_spectralGap_corr0`).
-/

import YMGap.Continuum.SpectralGap
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SpectralGap

/-! ## The computable top-of-spectrum `specMax`

`specMaxAux lam n = max{ lam 0, …, lam (n−1) }` (with a `0` floor at `n = 0`),
built from the decidable `Q'.max'`.  This is the COMPUTABLE largest eigenvalue
of the finite spectrum — the located datum that exists for a compact operator
but not for a general bounded one. -/

/-- Running maximum of `lam 0, …, lam (n−1)` (`0` for the empty prefix). -/
def specMaxAux (lam : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => Q'.max' (specMaxAux lam n) (lam n)

/-- `max' a b ≤ c ↔ a ≤ c ∧ b ≤ c` (the located join). -/
theorem max'_le_iff (a b c : Q') : Q'.max' a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  unfold Q'.max'
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact ⟨fun hbc => ⟨Q'.le_trans' a b c h hbc, hbc⟩, fun hp => hp.2⟩
  · rw [if_neg h]
    have hba : b ≤ a := by
      show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
      have h' : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := h
      exact Int.le_of_lt (Int.not_le.mp h')
    exact ⟨fun hac => ⟨hac, Q'.le_trans' b a c hba hac⟩, fun hp => hp.1⟩

/-- **The located bridge.**  `specMaxAux lam n ≤ μ` iff `0 ≤ μ` and every entry
`lam i` (`i < n`) is `≤ μ`.  The single comparison `specMaxAux ≤ μ` packages the
whole finite gap predicate — this is the located-spectrum content (the gap is one
decidable test against a computed real). -/
theorem specMaxAux_le_iff (lam : Nat → Q') (μ : Q') :
    ∀ n, specMaxAux lam n ≤ μ ↔ ((0 : Q') ≤ μ ∧ ∀ i, i < n → lam i ≤ μ)
  | 0 => by
      constructor
      · intro h; exact ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · intro h; exact h.1
  | n + 1 => by
      show Q'.max' (specMaxAux lam n) (lam n) ≤ μ ↔ _
      rw [max'_le_iff, specMaxAux_le_iff lam μ n]
      constructor
      · rintro ⟨⟨hμ, hlt⟩, hn⟩
        refine ⟨hμ, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i n with hin | hin
        · exact hlt i hin
        · have : i = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hin
          subst this; exact hn
      · rintro ⟨hμ, h⟩
        exact ⟨⟨hμ, fun i hi => h i (Nat.lt_succ_of_lt hi)⟩, h n (Nat.lt_succ_self n)⟩

/-- The located top-of-spectrum of a finite spectral model: the computable
maximum eigenvalue over its `k` modes. -/
def specMax (S : SpectralModel) : Q' := specMaxAux S.lam S.k

/-- **`specMax` is constructively located.**  Given `0 ≤ μ`, the gap predicate
`∀ i < k, λᵢ ≤ μ` is EQUIVALENT to the single decidable comparison
`specMax S ≤ μ`. -/
theorem specMax_le_iff (S : SpectralModel) (μ : Q') (hμ : (0 : Q') ≤ μ) :
    specMax S ≤ μ ↔ ∀ i, i < S.k → S.lam i ≤ μ := by
  rw [specMax, specMaxAux_le_iff S.lam μ S.k]
  exact ⟨fun h => h.2, fun h => ⟨hμ, h⟩⟩

/-- `specMaxAux lam n ≥ 0` (a max fold of nonneg entries from a `0` base). -/
theorem specMaxAux_nonneg (lam : Nat → Q') (hlam : ∀ i, (0 : Q') ≤ lam i) :
    ∀ n, (0 : Q') ≤ specMaxAux lam n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ Q'.max' (specMaxAux lam n) (lam n)
      unfold Q'.max'
      by_cases h : specMaxAux lam n ≤ lam n
      · rw [if_pos h]; exact hlam n
      · rw [if_neg h]; exact specMaxAux_nonneg lam hlam n

/-- The located top-of-spectrum is itself nonnegative. -/
theorem specMax_nonneg (S : SpectralModel) : (0 : Q') ≤ specMax S :=
  specMaxAux_nonneg S.lam S.lam_nonneg S.k

/-! ## The located spectral gap (Type-level witness)

`LocatedSpectralGap S` is the constructive mass-gap datum at the bounded
transfer-operator level: a separator `sep` (the located bound on the excited
spectrum) STRICTLY below the vacuum eigenvalue `1`, with `∀ i, λᵢ ≤ sep`.  The
located content (`specMax S ≤ sep`, decidable) is DERIVED.  No Stone / unbounded
spectral theorem: the gap is the located second eigenvalue of the compact
(finite) transfer operator. -/

/-- A located spectral gap for the finite transfer model: a computable
separator `sep < 1` bounding every eigenvalue.  Carried as `Type`-level data
(Rule 8). -/
structure LocatedSpectralGap (S : SpectralModel) : Type where
  /-- The located separator (an upper bound on the excited spectrum). -/
  sep : Q'
  /-- The separator is strictly below the vacuum eigenvalue `1` — THE gap. -/
  sep_lt_one : sep < (1 : Q')
  /-- Every transfer eigenvalue lies at or below the separator. -/
  bound : SpectralGapBound S sep

/-- The separator is nonnegative (`0 ≤ λ₀ ≤ sep`). -/
theorem LocatedSpectralGap.sep_nonneg {S : SpectralModel} (g : LocatedSpectralGap S) :
    (0 : Q') ≤ g.sep :=
  Q'.le_trans' 0 (S.lam 0) g.sep (S.lam_nonneg 0) (g.bound 0)

/-- **The located content.**  The computable top-of-spectrum is at or below the
separator: `specMax S ≤ sep`.  Equivalent (given `0 ≤ sep`) to the whole finite
gap predicate by `specMax_le_iff` — the gap is one decidable comparison. -/
theorem LocatedSpectralGap.located {S : SpectralModel} (g : LocatedSpectralGap S) :
    specMax S ≤ g.sep :=
  (specMax_le_iff S g.sep g.sep_nonneg).mpr (fun i _ => g.bound i)

/-- **Located ⇒ geometric clustering.**  The located gap forces the connected
two-point function to decay geometrically, `G(n) ≤ G(0)·sep ^ n`, with `sep < 1`
— the finite-volume, constructive mass-gap consequence at the transfer-operator
level (reuses the proven `decay_of_spectralGap_corr0`). -/
theorem LocatedSpectralGap.decay {S : SpectralModel} (g : LocatedSpectralGap S)
    (n : Nat) : corr S n ≤ (corr S 0) * g.sep ^ n :=
  decay_of_spectralGap_corr0 S g.sep g.sep_nonneg g.bound n

/-- The finite spectral gap is constructively DECIDABLE — the hallmark of a
located spectrum for the compact (finite) transfer operator (`specMax S ≤ μ` is
a single decidable `Q'` comparison; contrast a general bounded operator, whose
spectrum is only lower-semicomputable). -/
instance locatedGap_decidable (S : SpectralModel) (μ : Q') :
    Decidable (specMax S ≤ μ) := inferInstance

/-! ## The positive eigenvalue-gap margin

`sep < 1 ⟹ 0 < 1 − sep`: the located gap below the vacuum eigenvalue `1` is a
STRICTLY POSITIVE `Q'` quantity — the mass gap in transfer-eigenvalue space, with
no `log` needed (the physical mass is `m = −log sep`; here `1 − sep > 0` is the
constructive positive-gap witness). -/

/-- `sep < 1 ⟹ 0 < 1 − sep` (positivity of the eigenvalue-gap margin). -/
theorem one_sub_pos_of_lt_one {sep : Q'} (h : sep < (1 : Q')) : (0 : Q') < 1 - sep := by
  apply CReal.pos_of_num_pos
  have h' : sep.num * ((1 : Q').den : Int) < (1 : Q').num * (sep.den : Int) := h
  have hone_num : (1 : Q').num = 1 := rfl
  have hone_den : ((1 : Q').den : Int) = 1 := rfl
  change (0 : Int) < (1 : Q').num * (sep.den : Int) + (-sep.num) * (((1 : Q').den : Int))
  rw [hone_num, hone_den]
  rw [hone_num, hone_den] at h'
  omega

/-- The positive eigenvalue-gap margin `1 − sep > 0` of a located gap — the
located mass gap as a strictly positive `Q'` quantity (the spectral gap in
transfer-eigenvalue space, no `log` required). -/
def LocatedSpectralGap.gapMargin {S : SpectralModel} (g : LocatedSpectralGap S) : Q' :=
  1 - g.sep

/-- The eigenvalue-gap margin is strictly positive — THE constructive
"there is a mass gap" witness at the bounded transfer-operator level. -/
theorem LocatedSpectralGap.gapMargin_pos {S : SpectralModel} (g : LocatedSpectralGap S) :
    (0 : Q') < g.gapMargin :=
  one_sub_pos_of_lt_one g.sep_lt_one

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.specMaxAux_le_iff
#print axioms YMGap.Continuum.specMax_le_iff
#print axioms YMGap.Continuum.specMax_nonneg
#print axioms YMGap.Continuum.LocatedSpectralGap.located
#print axioms YMGap.Continuum.LocatedSpectralGap.decay
#print axioms YMGap.Continuum.one_sub_pos_of_lt_one
#print axioms YMGap.Continuum.LocatedSpectralGap.gapMargin_pos
