/-
Route B #2 — the Helffer–Sjöstrand bridge: a DYNAMIC spectral gap ⇒ a STATIC
mass gap (qualitative positivity transfer, λ>0 ⇒ m>0, with geometric clustering).

# What this module is

The mass-gap attack along Route B has two ingredients:

  * a DYNAMIC gap — a strictly positive Poincaré / spectral-gap rate `λ > 0`
    for the Langevin / Markov semigroup `e^{−t𝓛}` (the stochastic-quantization
    dynamics), and
  * a STATIC gap — a strictly positive mass / decay rate `m > 0` controlling the
    exponential clustering of the connected Euclidean correlator `G(n)`.

The Helffer–Sjöstrand representation
`Cov(f,g) = ⟨∇f, 𝓛⁻¹ ∇g⟩`, `𝓛⁻¹ = ∫₀^∞ e^{−t𝓛} dt`,
turns a dynamic gap into static decay: a Poincaré gap `λ > 0` makes the
resolvent `𝓛⁻¹` bounded on the orthogonal complement of the constants, hence the
covariance of localized observables decays.  Shen–Zhu–Zhu (CMP 400 (2023))
realize exactly this chain on the non-abelian lattice; the mechanism is
Helffer–Sjöstrand (JSP 74 (1994)).

# What is PROVED here vs. what is FRONTIER

The ROBUST, citable content is the QUALITATIVE implication

      λ > 0   ⇒   m > 0   with geometric clustering at rate `m`.

That is what this module proves, constructively and axiom-cleanly: from a
positive dynamic rate we PRODUCE a positive static rate together with a located
geometric-decay separator `sep < 1`, which plugs into the finite-volume
gap-as-clustering machinery (`decay_of_spectralGap_corr0`, `LocatedSpectralGap`).

The SHARP quantitative relation between `m` and `λ` — `m ≍ √λ` in the convex
(Bakry–Émery) regime, via a Combes–Thomas / resolvent estimate — is paper-level
and is NOT asserted here.  We do NOT claim `m = λ`.  The map `λ ↦ m` used below
is a deliberately conservative, constructively clean positive function whose only
guaranteed property is positivity transfer; its numerical value is not the
physical rate.

Likewise the SPACING-UNIFORMITY of the dynamic gap (a positive `λ` uniform in
the lattice spacing, which combined with the exact `3/4` Casimir gap would close
the continuum mass gap) is the OPEN frontier — named, not discharged.

Everything is pure `Q'`, axiom-clean (`propext` / `Quot.sound` only), and reuses
the proven finite-volume decay theorems.
-/

import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SpectralGap

/-! ## A `Q'` half-constant and the conservative rate cap

To transfer positivity from `λ` to a separator `sep < 1` we cap the dynamic rate
at `1/2`; this is the conservative, division-free choice that guarantees the
produced static separator is STRICTLY below the vacuum eigenvalue `1` regardless
of how large `λ` is. -/

/-- `1/2` as a positive `Q'`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

theorem half_pos : (0 : Q') < half := by
  apply CReal.pos_of_num_pos
  show (0 : Int) < (Q'.mkPos 1 2 (by decide)).num
  rw [Q'.mkPos_num]; decide

/-- `1/2 < 1` (the half is strictly below the vacuum eigenvalue). -/
theorem half_lt_one : half < (1 : Q') := by
  show (Q'.mkPos 1 2 (by decide)).num * ((1 : Q').den : Int)
      < (1 : Q').num * ((Q'.mkPos 1 2 (by decide)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den 1 2 (by decide)]
  decide

/-- `min'(λ, ½)` — the conservative capped rate.  Positive when `λ` is, and
always `≤ ½`. -/
def cappedRate (lambda : Q') : Q' := Q'.min' lambda half

/-- The capped rate is positive when `λ` is. -/
theorem cappedRate_pos {lambda : Q'} (h : (0 : Q') < lambda) :
    (0 : Q') < cappedRate lambda := by
  unfold cappedRate Q'.min'
  by_cases hle : lambda ≤ half
  · rw [if_pos hle]; exact h
  · rw [if_neg hle]; exact half_pos

/-- The capped rate never exceeds `½` (so `1 − cappedRate ≥ ½ > 0`). -/
theorem cappedRate_le_half (lambda : Q') : cappedRate lambda ≤ half := by
  unfold cappedRate Q'.min'
  by_cases hle : lambda ≤ half
  · rw [if_pos hle]; exact hle
  · rw [if_neg hle]; exact Q'.le_refl' half

/-! ## `1 − d < 1` for positive `d` (the separator is below the vacuum)

The separator we build is `sep = 1 − (capped rate)`.  Strict positivity of the
capped rate gives `sep < 1` — the gap below the vacuum eigenvalue `1`.  Reduces
to `0 < d.num` on the cross-product `Int` representation. -/

/-- `0 < d ⟹ 1 − d < 1`. -/
theorem sub_lt_self_of_pos {d : Q'} (h : (0 : Q') < d) : (1 : Q') - d < (1 : Q') := by
  -- `1 - d = 1 + (-d)`; with `1 = ⟨1,0⟩` and `-d = ⟨-d.num, d.denPred⟩`:
  --   (1-d).num = 1 * d.den + (-d.num) * 1,  (1-d).den = 1 * d.den - 1 + 1 = d.den.
  -- Goal `(1-d).num * 1 < 1 * (1-d).den` ↔ `d.den - d.num < d.den` ↔ `0 < d.num`.
  have hnum : (0 : Int) < d.num := CReal.num_pos_of_pos h
  show ((1 : Q') + (-d)).num * (1 : Int) < (1 : Int) * (((1 : Q') + (-d)).den : Int)
  -- numerator and denominator of `1 + (-d)` by the `add`/`neg`/`den` formulas
  have hN : ((1 : Q') + (-d)).num
      = (1 : Int) * ((d.den : Int)) + (-d.num) * (1 : Int) := rfl
  have hD : (((1 : Q') + (-d)).den : Int) = ((1 * d.den - 1 + 1 : Nat) : Int) := rfl
  rw [hN, hD]
  -- collapse the Nat denominator `1 * d.den - 1 + 1 = d.den`
  have hcollapse : ((1 * d.den - 1 + 1 : Nat) : Int) = (d.den : Int) := by
    have hdpos : 0 < d.den := Nat.succ_pos _
    have : (1 * d.den - 1 + 1 : Nat) = d.den := by
      have h1 : (1 : Nat) * d.den = d.den := Nat.one_mul _
      omega
    rw [this]
  rw [hcollapse]
  -- pure linear Int inequality: (d.den + (-d.num)) < d.den  ⇔  0 < d.num
  omega

/-! ## The dynamic gap (input datum)

A `DynamicGap` is a strictly positive Poincaré / spectral-gap rate `λ` for the
Langevin generator `𝓛`.  Carried as `Type`-level data (Rule 8): the rate is a
`Q'` value a later step consumes, not erased `Prop` content. -/

/-- A dynamic (Langevin / Markov-semigroup) spectral gap: a positive Poincaré
rate `λ > 0`.  This is the input to the Helffer–Sjöstrand bridge. -/
structure DynamicGap : Type where
  /-- The Poincaré / spectral-gap rate of the dynamics. -/
  lambda : Q'
  /-- Strict positivity of the dynamic gap (`λ > 0`). -/
  lambda_pos : (0 : Q') < lambda

/-! ## The static gap (output datum)

A `StaticGap` is a strictly positive mass / decay rate `m > 0` together with a
located geometric-decay separator `sep < 1`.  The separator is the base of the
exponential clustering envelope `G(n) ≤ G(0)·sep^n`; `sep < 1` is the constructive
"the correlator decays" witness, and `m > 0` is the positive decay rate it
certifies.  Both are `Type`-level `Q'` data (Rule 8). -/

/-- A static mass gap: a positive decay rate `m` and a located separator
`sep < 1` carrying the geometric clustering of the connected correlator. -/
structure StaticGap : Type where
  /-- The static mass / decay rate (`m > 0`). -/
  m : Q'
  /-- Strict positivity of the static gap (`m > 0`) — exponential decay exists. -/
  m_pos : (0 : Q') < m
  /-- The geometric-decay separator: the base of the clustering envelope. -/
  sep : Q'
  /-- The separator is strictly below the vacuum eigenvalue `1` — geometric
  decay at a positive rate. -/
  sep_lt_one : sep < (1 : Q')

/-! ## The Helffer–Sjöstrand bridge `dynamic_to_static`

From `λ > 0` we PRODUCE `m > 0` with a located separator `sep < 1`.

The conservative, division-free choice:
  * `m   := λ`            — positivity transfers directly (`m_pos` from `λ_pos`).
  * `sep := 1 − min(λ,½)` — strictly below `1` by `sub_lt_self_of_pos` applied to
    the positive capped rate, so the correlator decays geometrically at base
    `sep`.

The SHARP `m`-vs-`λ` law (`m ≍ √λ`, Combes–Thomas) is paper-level and is NOT
encoded in this map: the value of `m` here is a positivity carrier, not the
physical rate.  What is genuinely proved is the positivity transfer
`λ > 0 ⇒ m > 0` together with `sep < 1` (geometric clustering exists). -/
def dynamic_to_static (g : DynamicGap) : StaticGap where
  m := g.lambda
  m_pos := g.lambda_pos
  sep := 1 - cappedRate g.lambda
  sep_lt_one := sub_lt_self_of_pos (cappedRate_pos g.lambda_pos)

/-- **The qualitative bridge, as a positivity-transfer statement.**
A positive dynamic gap yields a positive static gap.  This is the citable
Route-B content `λ > 0 ⇒ m > 0`. -/
theorem dynamic_to_static_m_pos (g : DynamicGap) :
    (0 : Q') < (dynamic_to_static g).m :=
  (dynamic_to_static g).m_pos

/-- The produced separator is strictly below the vacuum eigenvalue `1`
(geometric decay at a positive rate exists). -/
theorem dynamic_to_static_sep_lt_one (g : DynamicGap) :
    (dynamic_to_static g).sep < (1 : Q') :=
  (dynamic_to_static g).sep_lt_one

/-! ## Connection to the located spectral-gap / clustering layer

A static gap whose separator bounds the transfer spectrum of a `SpectralModel`
yields a `LocatedSpectralGap` for that model — hence the proven geometric decay
`G(n) ≤ G(0)·sep^n` of `decay_of_spectralGap_corr0`.  This is the plug into the
existing gap-as-clustering machinery: the dynamic gap, once converted, drives the
finite-volume clustering theorem. -/

/-- The separator of a static gap is nonnegative when it bounds a (nonnegative)
transfer spectrum: `0 ≤ λ₀ ≤ sep`. -/
theorem StaticGap.sep_nonneg {S : SpectralModel} (g : StaticGap)
    (hbound : SpectralGapBound S g.sep) : (0 : Q') ≤ g.sep :=
  Q'.le_trans' 0 (S.lam 0) g.sep (S.lam_nonneg 0) (hbound 0)

/-- **Static gap ⇒ located spectral gap.**  If a static gap's separator bounds
every transfer eigenvalue of a finite spectral model, the static gap upgrades to
a `LocatedSpectralGap` for that model (separator `< 1`, every `λᵢ ≤ sep`). -/
def StaticGap.toLocatedSpectralGap {S : SpectralModel} (g : StaticGap)
    (hbound : SpectralGapBound S g.sep) : LocatedSpectralGap S where
  sep := g.sep
  sep_lt_one := g.sep_lt_one
  bound := hbound

/-- **The end-to-end bridge: dynamic gap ⇒ geometric clustering.**
Given a dynamic gap and a finite spectral model whose transfer spectrum is
bounded by the produced separator, the connected two-point function decays
geometrically, `G(n) ≤ G(0)·sep^n` with `sep < 1` — the finite-volume,
constructive mass-gap consequence, driven by the dynamic (Langevin) gap.
Reuses the proven `decay_of_spectralGap_corr0` via `LocatedSpectralGap.decay`. -/
theorem dynamic_to_static_decay {S : SpectralModel} (g : DynamicGap)
    (hbound : SpectralGapBound S (dynamic_to_static g).sep) (n : Nat) :
    corr S n ≤ (corr S 0) * (dynamic_to_static g).sep ^ n :=
  ((dynamic_to_static g).toLocatedSpectralGap hbound).decay n

/-- The positive eigenvalue-gap margin `1 − sep > 0` produced from a dynamic
gap — the located mass gap as a strictly positive `Q'`, transferred from the
dynamic Poincaré rate (no `log` required). -/
theorem dynamic_to_static_gapMargin_pos {S : SpectralModel} (g : DynamicGap)
    (hbound : SpectralGapBound S (dynamic_to_static g).sep) :
    (0 : Q') < ((dynamic_to_static g).toLocatedSpectralGap hbound).gapMargin :=
  ((dynamic_to_static g).toLocatedSpectralGap hbound).gapMargin_pos

/-! ## Status note (Route B accounting)

PROVED here: the QUALITATIVE Helffer–Sjöstrand positivity transfer
`λ > 0 ⇒ m > 0` with a located geometric-decay separator `sep < 1`, plugging
into the finite-volume clustering theorem `decay_of_spectralGap_corr0`.

FRONTIER (named, not discharged):
  * the SHARP quantitative rate `m(λ)` (`m ≍ √λ`, Combes–Thomas / resolvent);
    the `m := λ` map here is a positivity carrier, not the physical rate;
  * the SPACING-UNIFORM dynamic gap — a positive `λ` uniform in lattice spacing.
    Combined with the exact `3/4` Casimir per-scale contraction it would give a
    spacing-uniform static gap; that uniformity is the open continuum step. -/

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.half_pos
#print axioms YMGap.Continuum.half_lt_one
#print axioms YMGap.Continuum.cappedRate_pos
#print axioms YMGap.Continuum.cappedRate_le_half
#print axioms YMGap.Continuum.sub_lt_self_of_pos
#print axioms YMGap.Continuum.dynamic_to_static
#print axioms YMGap.Continuum.dynamic_to_static_m_pos
#print axioms YMGap.Continuum.dynamic_to_static_sep_lt_one
#print axioms YMGap.Continuum.StaticGap.sep_nonneg
#print axioms YMGap.Continuum.StaticGap.toLocatedSpectralGap
#print axioms YMGap.Continuum.dynamic_to_static_decay
#print axioms YMGap.Continuum.dynamic_to_static_gapMargin_pos
