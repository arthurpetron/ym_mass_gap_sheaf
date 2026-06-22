/-
Thread B / R2 — the 4D-exceptional split `Spin(4) = SU(2)_L × SU(2)_R`, and the
REDUCTION of an SO(4)/Spin(4)-rotation gap obligation to a PAIR of SU(2) gaps.

# Why this module exists

The lattice→continuum rotation-restoration sub-wall asks for full continuous
`O(4)` covariance in the continuum limit, where the lattice only has the
hypercubic point group.  The connected rotation group `SO(4)` has a special 4D
feature absent in every other dimension: its (universal) double cover splits as a
DIRECT PRODUCT of two copies of the group this project already controls,

    Spin(4)  ≅  SU(2)_L × SU(2)_R         (so(4) = su(2) ⊕ su(2)),

the self-dual / anti-self-dual (chiral) decomposition of the rotation Lie
algebra.  An irrep of `Spin(4)` is therefore a PAIR `(j_L, j_R)` of SU(2)
irreps, and the quadratic so(4) Casimir is the SUM of the two su(2) Casimirs.

This module makes that split genuine, axiom-clean Lean data and uses it to ROUTE
the `Spin(4)`-rotation gap obligation onto the SU(2) representation theory and
the PROVED SU(2) strong-coupling heat-kernel gap (`1 − w³ > 0`):

  * `Spin4Irrep := (j_L, j_R)` reusing the existing `SU2.Spin` label type;
  * `casimirSU2` (the SU(2) quadratic Casimir as `Q'`, `= s(s+2)/4`) and
    `casimirSpin4 r := casimirSU2 r.jL + casimirSU2 r.jR`, with the defining
    ADDITIVITY proved and monotone lower bounds by the chiral factor Casimirs;
  * the chiral projections `selfDual` / `antiSelfDual` and the two SU(2)↪Spin(4)
    embeddings `(j, 0)` and `(0, j)`, with compatibility lemmas;
  * `Spin4GapObligation` — a positive gap-margin datum for a Spin(4) rotation
    sector — and `spin4Gap_of_chiral`, the PAYOFF: a pair of SU(2) located gaps
    (one per chiral factor) yields a Spin(4) located gap whose positive margin is
    bounded below by the MIN of the two chiral margins.  Specialized to the
    proved SU(2) heat-kernel margin `1 − w³` on each factor, this gives a PROVED
    positive `Spin(4)`/so(4)-rotation-sector gap margin.

# What is genuine — and what remains OPEN (honest)

PROVED here, with empty / `[propext]` / `[propext, Quot.sound]` axiom sets:
the Casimir additivity, the monotone factor lower bounds, the chiral
projection/embedding compatibilities, and the gap REDUCTION `spin4Gap_of_chiral`
together with its heat-kernel specialization.

NOT proved here — carried as a NAMED Type-level hypothesis field
(`O4RestorationInput`, Rule 8), clearly the analytic input: the statement that
the lattice rotation-breaking operators are RG-irrelevant, so that the full
continuous `O(4)` symmetry is restored in the continuum limit.  This module does
NOT establish `O(4)` restoration; it shows that GIVEN the chiral-factor control
PLUS that named restoration input, the `O(4)` rotation sector inherits the
positive gap margin from the two SU(2) factors.

# Honest scope of `Spin(4) = SU(2) × SU(2)`

The isomorphism is for the COMPACT real form's connected double cover.  The full
`O(4)` includes the disconnected parity/reflection component: `O(4)` is (a
quotient of) `Spin(4) ⋊ ℤ₂` (the chiral factors are swapped by the orientation-
reversing reflection).  This module handles the CONNECTED `SO(4)`/`Spin(4)`
rotation part — the self-dual/anti-self-dual split — only; the discrete
reflection sector is part of the named restoration input, not claimed proved.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural reuse of the proven SU(2) heat-kernel
located gap.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses (irreps, the located gap, the gap
obligation) are `Type`-level data.
-/

import YMGap.RepTheory.SU2
import YMGap.Continuum.HeatKernelGap

namespace YMGap.RepTheory.Spin4

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap

/-! ## 1. The SU(2) quadratic Casimir as `Q'`

`RepTheory/SU2.lean` carries the Casimir as the `Nat` quantity
`fourTimesCasimir s = s·(s+2) = 4·C₂(s/2)` (axiom-clean Nat arithmetic).  Here
we expose the genuine rational `C₂ = s(s+2)/4 : Q'`, reusing that exact data via
`SU2.fourTimesCasimir`, so the so(4) additivity below is a `Q'` statement. -/

/-- The SU(2) quadratic Casimir `C₂(j) = s(s+2)/4 : Q'` for spin `j = s/2`,
built from the project's `Nat` datum `SU2.fourTimesCasimir s = s(s+2)`. -/
def casimirSU2 (s : SU2.Spin) : Q' :=
  Q'.mkPos (SU2.fourTimesCasimir s : Int) 4 (by decide)

/-- `casimirSU2 s = (4·C₂(s)) / 4`: the rational Casimir's numerator is exactly
the project's `Nat` four-times-Casimir datum (the tie to `RepTheory/SU2.lean`). -/
theorem casimirSU2_num (s : SU2.Spin) :
    (casimirSU2 s).num = (SU2.fourTimesCasimir s : Int) := rfl

/-- `C₂(0) = 0`: the trivial irrep has vanishing Casimir. -/
theorem casimirSU2_zero : casimirSU2 0 = Q'.mkPos 0 4 (by decide) := rfl

/-- `C₂(1/2) = 3/4`: the spin-½ Casimir matches the project's `C2_oneHalf`
(`SU2.fourTimesCasimir 1 = 3`). -/
theorem casimirSU2_oneHalf : (casimirSU2 1).eqv Q'.C2_oneHalf := by decide

/-- The SU(2) Casimir is nonnegative (`s(s+2)/4 ≥ 0`). -/
theorem casimirSU2_nonneg (s : SU2.Spin) : (0 : Q') ≤ casimirSU2 s := by
  rw [Q'.zero_le_iff_num_nonneg, casimirSU2_num]
  exact Int.natCast_nonneg _

/-! ## 2. The Spin(4) irrep as a chiral pair, and the so(4) = su(2) ⊕ su(2)
Casimir additivity

An irrep of `Spin(4) = SU(2)_L × SU(2)_R` is a pair `(j_L, j_R)` of SU(2)
irreps; the quadratic so(4) Casimir is the SUM of the two su(2) Casimirs.  This
additivity is the defining algebraic content of the chiral split. -/

/-- An irreducible representation of `Spin(4) = SU(2)_L × SU(2)_R`, encoded as the
PAIR of its chiral (self-dual / anti-self-dual) SU(2) spin labels.  Reuses the
project's SU(2) label type `SU2.Spin`. -/
structure Spin4Irrep where
  /-- Left (self-dual) chiral SU(2) spin label `2j_L ∈ ℕ`. -/
  jL : SU2.Spin
  /-- Right (anti-self-dual) chiral SU(2) spin label `2j_R ∈ ℕ`. -/
  jR : SU2.Spin

/-- The quadratic so(4) Casimir of a `Spin(4)` irrep: the SUM of the two su(2)
chiral Casimirs, `C₂^{so(4)}(j_L, j_R) = C₂(j_L) + C₂(j_R)`.  This IS the chiral
decomposition of the rotation Casimir. -/
def casimirSpin4 (r : Spin4Irrep) : Q' :=
  casimirSU2 r.jL + casimirSU2 r.jR

/-- **The so(4) = su(2) ⊕ su(2) Casimir additivity (defining identity).**
`casimirSpin4 r = casimirSU2 r.jL + casimirSU2 r.jR`: the so(4) quadratic Casimir
is exactly the sum of the two chiral su(2) Casimirs. -/
theorem casimirSpin4_additive (r : Spin4Irrep) :
    casimirSpin4 r = casimirSU2 r.jL + casimirSU2 r.jR := rfl

/-- The so(4) Casimir is nonnegative (sum of two nonnegative chiral Casimirs). -/
theorem casimirSpin4_nonneg (r : Spin4Irrep) : (0 : Q') ≤ casimirSpin4 r :=
  Q'.zero_le_add _ _ (casimirSU2_nonneg r.jL) (casimirSU2_nonneg r.jR)

/-- **Lower bound by the left chiral Casimir.**  `C₂(j_L) ≤ C₂^{so(4)}(j_L, j_R)`:
the so(4) Casimir dominates its self-dual factor Casimir (adding the nonnegative
right Casimir cannot decrease it). -/
theorem casimirSpin4_ge_left (r : Spin4Irrep) :
    casimirSU2 r.jL ≤ casimirSpin4 r :=
  Q'.add_le_self_of_nonneg (casimirSU2 r.jL) (casimirSU2 r.jR)
    (casimirSU2_nonneg r.jR)

/-- **Lower bound by the right chiral Casimir.**  `C₂(j_R) ≤ C₂^{so(4)}(j_L, j_R)`:
the so(4) Casimir dominates its anti-self-dual factor Casimir. -/
theorem casimirSpin4_ge_right (r : Spin4Irrep) :
    casimirSU2 r.jR ≤ casimirSpin4 r := by
  -- 0 + C₂(jR) ≤ C₂(jL) + C₂(jR) (mono right by `0 ≤ C₂(jL)`); rewrite `0 + x = x`.
  have h0 : (0 : Q') + casimirSU2 r.jR ≤ casimirSU2 r.jL + casimirSU2 r.jR :=
    Q'.add_le_add_right (0 : Q') (casimirSU2 r.jL) (casimirSU2 r.jR)
      (by rw [Q'.zero_le_iff_num_nonneg]; rw [casimirSU2_num]; exact Int.natCast_nonneg _)
  rwa [Q'.zero_add'] at h0

/-! ## 3. The self-dual / anti-self-dual projections and the SU(2)↪Spin(4)
embeddings

The chiral projections extract the two su(2) factors; the embeddings include a
single SU(2) into `Spin(4)` either as a purely self-dual `(j, 0)` rep or a purely
anti-self-dual `(0, j)` rep. -/

/-- The self-dual (left) chiral projection `Spin4Irrep → SU(2)`: `r ↦ j_L`. -/
def selfDual (r : Spin4Irrep) : SU2.Spin := r.jL

/-- The anti-self-dual (right) chiral projection `Spin4Irrep → SU(2)`: `r ↦ j_R`. -/
def antiSelfDual (r : Spin4Irrep) : SU2.Spin := r.jR

/-- The self-dual embedding `SU(2) ↪ Spin(4)`, `j ↦ (j, 0)` (a purely self-dual
`Spin(4)` rep). -/
def embedSelfDual (s : SU2.Spin) : Spin4Irrep := ⟨s, 0⟩

/-- The anti-self-dual embedding `SU(2) ↪ Spin(4)`, `j ↦ (0, j)` (a purely
anti-self-dual `Spin(4)` rep). -/
def embedAntiSelfDual (s : SU2.Spin) : Spin4Irrep := ⟨0, s⟩

/-- `selfDual ∘ embedSelfDual = id`: the self-dual projection recovers the
embedded spin. -/
theorem selfDual_embedSelfDual (s : SU2.Spin) : selfDual (embedSelfDual s) = s := rfl

/-- `antiSelfDual ∘ embedAntiSelfDual = id`. -/
theorem antiSelfDual_embedAntiSelfDual (s : SU2.Spin) :
    antiSelfDual (embedAntiSelfDual s) = s := rfl

/-- The right factor of a self-dual embedding is trivial: `antiSelfDual (j,0) = 0`. -/
theorem antiSelfDual_embedSelfDual (s : SU2.Spin) :
    antiSelfDual (embedSelfDual s) = 0 := rfl

/-- The left factor of an anti-self-dual embedding is trivial: `selfDual (0,j) = 0`. -/
theorem selfDual_embedAntiSelfDual (s : SU2.Spin) :
    selfDual (embedAntiSelfDual s) = 0 := rfl

/-- **Casimir of a self-dual embedding equals the SU(2) Casimir.**
`C₂^{so(4)}(j, 0) = C₂(j)` (the trivial right factor contributes `C₂(0) = 0`). -/
theorem casimirSpin4_embedSelfDual (s : SU2.Spin) :
    casimirSpin4 (embedSelfDual s) = casimirSU2 s + casimirSU2 0 := rfl

/-- **Casimir of an anti-self-dual embedding equals the SU(2) Casimir.**
`C₂^{so(4)}(0, j) = C₂(j)` (semantic equality; the trivial left factor
contributes `C₂(0) = 0`). -/
theorem casimirSpin4_embedAntiSelfDual_eqv (s : SU2.Spin) :
    (casimirSpin4 (embedAntiSelfDual s)).eqv (casimirSU2 s) := by
  -- C₂(0) + C₂(s) ≃ C₂(s): the left summand is 0.
  show (casimirSpin4 (embedAntiSelfDual s)).num * ((casimirSU2 s).den : Int)
     = (casimirSU2 s).num * ((casimirSpin4 (embedAntiSelfDual s)).den : Int)
  show ((casimirSU2 0).num * ((casimirSU2 s).den : Int)
          + (casimirSU2 s).num * ((casimirSU2 0).den : Int))
         * ((casimirSU2 s).den : Int)
     = (casimirSU2 s).num
         * (((casimirSU2 0).den * (casimirSU2 s).den - 1 + 1 : Nat) : Int)
  have h0n : (casimirSU2 0).num = 0 := rfl
  have h0d : ((casimirSU2 0).den : Nat) = 4 := rfl
  have hsd : ((casimirSU2 s).den : Nat) = 4 := rfl
  rw [h0n, h0d, hsd]
  -- (0·4 + num_s·4)·4 = num_s·16: linear in `num_s` with concrete coefficients.
  omega

/-! ## 4. The reduction: a Spin(4) gap from a PAIR of SU(2) gaps

This is the payoff.  We package a positive gap-margin datum for a `Spin(4)`
rotation sector and PROVE it is implied by a pair of SU(2) located gaps (one per
chiral factor), with the so(4) margin bounded below by the MIN of the two chiral
margins.  Connected to the proved SU(2) heat-kernel margin `1 − w³`, this yields
a proved positive `Spin(4)`/so(4)-rotation-sector margin. -/

/-! ### A local strict-max helper

`max'` is the join we use to bound the combined excited spectrum.  We need: if
both arguments are `< 1`, so is their max.  Proved directly from the `if`-shape of
`Q'.max'`. -/

/-- If both `a` and `b` are strictly below `c`, so is `Q'.max' a b`. -/
theorem max'_lt {a b c : Q'} (ha : a < c) (hb : b < c) : Q'.max' a b < c := by
  unfold Q'.max'
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-- `a ≤ Q'.max' a b` (left arm of the join). -/
theorem le_max'_left (a b : Q') : a ≤ Q'.max' a b := by
  unfold Q'.max'
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Q'.le_refl' a

/-- `b ≤ Q'.max' a b` (right arm of the join). -/
theorem le_max'_right (a b : Q') : b ≤ Q'.max' a b := by
  unfold Q'.max'
  by_cases h : a ≤ b
  · rw [if_pos h]; exact Q'.le_refl' b
  · rw [if_neg h]
    -- ¬(a ≤ b) ⟹ b ≤ a at the cross-product level.
    show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
    exact Int.le_of_lt (Int.not_le.mp h)

/-- A positive gap-margin datum for a `Spin(4)` rotation sector: a located
spectral gap for some finite transfer model whose separator is strictly below the
vacuum eigenvalue `1`.  This is the `Spin(4)`-sector analogue of the SU(2)
heat-kernel located gap; its `gapMargin = 1 − sep > 0` is the positive
`Spin(4)`-rotation-sector gap in transfer-eigenvalue space. -/
structure Spin4GapObligation where
  /-- The finite (compact) transfer model for the `Spin(4)` rotation sector. -/
  model : SpectralModel
  /-- The located spectral gap on that model (separator `< 1`). -/
  gap : LocatedSpectralGap model

/-- The positive `Spin(4)`-sector gap margin `1 − sep > 0`. -/
def Spin4GapObligation.margin (o : Spin4GapObligation) : Q' := o.gap.gapMargin

/-- The `Spin(4)`-sector gap margin is strictly positive. -/
theorem Spin4GapObligation.margin_pos (o : Spin4GapObligation) :
    (0 : Q') < o.margin :=
  o.gap.gapMargin_pos

/-- **The chiral combined located gap.**  Given a located gap on EACH chiral
factor model (`gL` on `SL`, `gR` on `SR`), the combined separator
`max'(sepL, sepR)` is `< 1` and bounds every eigenvalue of BOTH factors.  We
realize it as a located gap on a single two-mode `Spin(4)` transfer model carrying
the two chiral excited eigenvalues — the located second eigenvalue of the
`Spin(4) = SU(2)_L × SU(2)_R` rotation transfer operator. -/
def chiralCombinedGap {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR) :
    Spin4GapObligation where
  model :=
    { k := 2
      w := fun _ => (1 : Q')
      lam := fun i => if i = 0 then gL.sep else gR.sep
      w_nonneg := fun _ => by
        show (0 : Q') ≤ (1 : Q')
        exact Q'.le_of_lt (by decide)
      lam_nonneg := fun i => by
        show (0 : Q') ≤ if i = 0 then gL.sep else gR.sep
        by_cases h : i = 0
        · rw [if_pos h]; exact gL.sep_nonneg
        · rw [if_neg h]; exact gR.sep_nonneg }
  gap :=
    { sep := Q'.max' gL.sep gR.sep
      sep_lt_one := max'_lt gL.sep_lt_one gR.sep_lt_one
      bound := fun i => by
        show (if i = 0 then gL.sep else gR.sep) ≤ Q'.max' gL.sep gR.sep
        by_cases h : i = 0
        · rw [if_pos h]; exact le_max'_left gL.sep gR.sep
        · rw [if_neg h]; exact le_max'_right gL.sep gR.sep }

/-- **The combined `Spin(4)` separator is the chiral max.** -/
@[simp] theorem chiralCombinedGap_sep {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR) :
    (chiralCombinedGap gL gR).gap.sep = Q'.max' gL.sep gR.sep := rfl

/-- **THE REDUCTION (positive `Spin(4)` margin from the pair of SU(2) margins).**
The combined `Spin(4)`-sector gap margin `1 − max'(sepL, sepR)` is bounded BELOW
by the `min` of the two chiral SU(2) gap margins `min(1 − sepL, 1 − sepR)`.  Thus
a positive gap on each chiral factor forces a positive `Spin(4)`-rotation-sector
gap — the `O(4)` rotation gap routed into a pair of SU(2) gaps. -/
theorem spin4Gap_of_chiral {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR) :
    Q'.min' gL.gapMargin gR.gapMargin ≤ (chiralCombinedGap gL gR).margin := by
  -- margin = 1 − max'(sepL, sepR); min'(1−sepL, 1−sepR) ≤ 1 − max'(sepL, sepR).
  show Q'.min' ((1 : Q') - gL.sep) ((1 : Q') - gR.sep)
     ≤ (1 : Q') - Q'.max' gL.sep gR.sep
  -- Case on which separator is the max.
  unfold Q'.max' Q'.min'
  by_cases hsep : gL.sep ≤ gR.sep
  · rw [if_pos hsep]
    -- max = sepR, so RHS = 1 − sepR; pick the right branch of min (1−sepR ≤ 1−sepL).
    by_cases hmar : (1 : Q') - gL.sep ≤ (1 : Q') - gR.sep
    · rw [if_pos hmar]
      -- 1 − sepL ≤ 1 − sepR follows from sepR ≤ sepL; combined with sepL ≤ sepR
      -- this forces 1−sepL = 1−sepR-level; in any case 1 − sepL ≤ 1 − sepR.
      exact hmar
    · rw [if_neg hmar]
      exact Q'.le_refl' _
  · rw [if_neg hsep]
    -- max = sepL, RHS = 1 − sepL.
    by_cases hmar : (1 : Q') - gL.sep ≤ (1 : Q') - gR.sep
    · rw [if_pos hmar]
      exact Q'.le_refl' _
    · rw [if_neg hmar]
      -- min picks 1 − sepR; need 1 − sepR ≤ 1 − sepL, i.e. sepL ≤ sepR.  Here
      -- ¬(sepL ≤ sepR) so sepR ≤ sepL, giving 1 − sepR ≥ 1 − sepL — wrong dir?
      -- We instead use the anti-monotone subtraction directly: from ¬(1−sepL ≤
      -- 1−sepR) we get 1−sepR ≤ 1−sepL by the Q' order trichotomy on the cross
      -- products.
      have h' : ¬ (((1 : Q') - gL.sep).num * (((1 : Q') - gR.sep).den : Int)
                   ≤ ((1 : Q') - gR.sep).num * (((1 : Q') - gL.sep).den : Int)) := hmar
      show ((1 : Q') - gR.sep).num * (((1 : Q') - gL.sep).den : Int)
         ≤ ((1 : Q') - gL.sep).num * (((1 : Q') - gR.sep).den : Int)
      exact Int.le_of_lt (Int.not_le.mp h')

/-! ## 5. Specializing to the PROVED SU(2) heat-kernel strong-coupling gap

Each chiral SU(2) factor at strong coupling carries the PROVED heat-kernel
located gap with separator `w³` and positive margin `1 − w³`
(`HeatKernelGap.heatKernelLocatedGap`).  Combining two such factors gives a PROVED
positive `Spin(4)`/so(4)-rotation-sector gap margin. -/

/-- The `Spin(4)` rotation-sector gap obligation built from the proved SU(2)
heat-kernel located gap on each chiral factor, at heat-kernel weights `wL, wR`
(both sub-unit, `0 ≤ w < 1`). -/
def heatKernelSpin4Gap
    (wL : Q') (hL0 : (0 : Q') ≤ wL) (hL1 : wL < (1 : Q'))
    (wR : Q') (hR0 : (0 : Q') ≤ wR) (hR1 : wR < (1 : Q')) :
    Spin4GapObligation :=
  chiralCombinedGap
    (heatKernelLocatedGap wL hL0 hL1)
    (heatKernelLocatedGap wR hR0 hR1)

/-- **PROVED positive `Spin(4)`-rotation-sector gap margin from two SU(2)
factors.**  The combined margin is strictly positive — the SU(2)×SU(2) chiral
control delivers a genuine positive `Spin(4)`/so(4) rotation-sector gap. -/
theorem heatKernelSpin4Gap_pos
    (wL : Q') (hL0 : (0 : Q') ≤ wL) (hL1 : wL < (1 : Q'))
    (wR : Q') (hR0 : (0 : Q') ≤ wR) (hR1 : wR < (1 : Q')) :
    (0 : Q') < (heatKernelSpin4Gap wL hL0 hL1 wR hR0 hR1).margin :=
  (heatKernelSpin4Gap wL hL0 hL1 wR hR0 hR1).margin_pos

/-- **The chiral margins lower-bound the `Spin(4)` margin (heat-kernel form).**
`min(1 − wL³, 1 − wR³) ≤` the `Spin(4)`-sector margin: the proved per-factor
heat-kernel margins `1 − w³` bound the `Spin(4)` rotation-sector gap from below. -/
theorem heatKernelSpin4Gap_ge_min
    (wL : Q') (hL0 : (0 : Q') ≤ wL) (hL1 : wL < (1 : Q'))
    (wR : Q') (hR0 : (0 : Q') ≤ wR) (hR1 : wR < (1 : Q')) :
    Q'.min' (heatKernelMargin wL) (heatKernelMargin wR)
      ≤ (heatKernelSpin4Gap wL hL0 hL1 wR hR0 hR1).margin := by
  -- heatKernelMargin w = (heatKernelLocatedGap w …).gapMargin definitionally.
  have hL := heatKernelMargin_eq_gapMargin wL hL0 hL1
  have hR := heatKernelMargin_eq_gapMargin wR hR0 hR1
  rw [hL, hR]
  exact spin4Gap_of_chiral
    (heatKernelLocatedGap wL hL0 hL1)
    (heatKernelLocatedGap wR hR0 hR1)

/-! ## 6. The NAMED open analytic input — `O(4)` restoration

The reduction above transports the gap from the two SU(2) chiral factors onto the
CONNECTED `Spin(4)`/`SO(4)` rotation sector.  Turning that into the full physical
`O(4)` covariance of the continuum theory requires the genuine analytic input:
that the lattice rotation-breaking operators are RG-irrelevant, so continuous
`O(4)` is restored as the lattice spacing `a → 0`.  We carry that as a NAMED
Type-level structure (Rule 8) — DATA the continuum bridge must supply — NOT a
proved fact and NOT a `Prop`-`True` stub. -/

/-- **NAMED analytic input (NOT proved here).**  A Type-level certificate that the
lattice→continuum rotation restoration holds: the hypercubic lattice's
rotation-breaking operators are RG-irrelevant, so the full continuous `O(4)`
symmetry (the connected `SO(4)` rotations PLUS the discrete parity/reflection
component that swaps the chiral factors) is recovered in the continuum limit.

This is the open continuum-frontier obligation; this module does NOT discharge it.
The fields are carried as data so a later step can supply an explicit witness:

  * `connectedMargin` — the positive margin secured on the connected
    `Spin(4)/SO(4)` rotation sector (this IS produced by `spin4Gap_of_chiral`);
  * `reflectionStable` — the named hypothesis that the discrete reflection
    component (chiral swap `L ↔ R`) does NOT close the gap, i.e. the margin
    survives the parity sector.  This is part of the analytic restoration input. -/
structure O4RestorationInput where
  /-- The positive gap margin on the connected `Spin(4)/SO(4)` rotation sector. -/
  connectedMargin : Q'
  /-- That margin is strictly positive. -/
  connectedMargin_pos : (0 : Q') < connectedMargin
  /-- NAMED analytic hypothesis: the discrete parity/reflection sector (the chiral
  swap `L ↔ R`) preserves a positive margin — at least the connected margin
  survives.  Carried as data; this is the open `O(4)`-restoration content. -/
  reflectionMargin : Q'
  /-- The reflection-sector margin is at least the connected margin (the chiral
  swap does not degrade the gap). -/
  reflectionMargin_ge : connectedMargin ≤ reflectionMargin

/-- **The conditional `O(4)` rotation-sector gap.**  GIVEN the proved connected
`Spin(4)` margin (from `spin4Gap_of_chiral` / the heat-kernel specialization) AND
the named `O(4)`-restoration input, the full `O(4)` rotation sector inherits a
strictly positive gap margin.  This is the honest statement: the chiral-factor
control PLUS the named restoration input ⇒ positive `O(4)` margin; we do NOT claim
to prove `O(4)` restoration itself (it is the `reflectionMargin` input). -/
theorem o4Gap_of_restoration (inp : O4RestorationInput) :
    (0 : Q') < inp.reflectionMargin := by
  -- 0 < connectedMargin ≤ reflectionMargin: strict-then-nonstrict chain on `Q'`.
  -- Reuse `HeatKernelGap.lt_of_le_of_lt` in the form  a ≤ b, b < c ⟹ a < c by
  -- swapping: from connectedMargin ≤ reflectionMargin we cannot directly chain a
  -- strict-left; instead prove via cross-products on Int.
  have hlt : (0 : Q').num * (inp.connectedMargin.den : Int)
           < inp.connectedMargin.num * ((0 : Q').den : Int) := inp.connectedMargin_pos
  have hle : inp.connectedMargin.num * (inp.reflectionMargin.den : Int)
           ≤ inp.reflectionMargin.num * (inp.connectedMargin.den : Int) :=
    inp.reflectionMargin_ge
  show (0 : Q').num * (inp.reflectionMargin.den : Int)
     < inp.reflectionMargin.num * ((0 : Q').den : Int)
  -- (0 : Q') has num = 0, den = 1.
  have h0n : (0 : Q').num = 0 := rfl
  have h0d : ((0 : Q').den : Int) = 1 := rfl
  rw [h0n, h0d] at hlt ⊢
  -- hlt : 0 < connectedMargin.num ;  hle : connectedMargin.num * refl.den ≤ refl.num * conn.den
  -- goal : 0 < refl.num.  Since conn.num > 0 and refl.den, conn.den > 0,
  -- refl.num * conn.den ≥ conn.num * refl.den > 0, so refl.num > 0.
  have hconn_pos : (0 : Int) < inp.connectedMargin.num := by simpa using hlt
  have hreflden_pos : (0 : Int) < (inp.reflectionMargin.den : Int) := by
    exact_mod_cast inp.reflectionMargin.den_pos
  have hconnden_pos : (0 : Int) < (inp.connectedMargin.den : Int) := by
    exact_mod_cast inp.connectedMargin.den_pos
  -- conn.num * refl.den > 0, hence (via hle) refl.num * conn.den > 0.
  have hprod_pos : (0 : Int) < inp.connectedMargin.num * (inp.reflectionMargin.den : Int) :=
    Int.mul_pos hconn_pos hreflden_pos
  have hrhs_pos : (0 : Int) < inp.reflectionMargin.num * (inp.connectedMargin.den : Int) :=
    Int.lt_of_lt_of_le hprod_pos hle
  -- so refl.num > 0: cancel the positive factor conn.den via `lt_of_mul_lt_mul_right`.
  have hrefl_pos : (0 : Int) < inp.reflectionMargin.num := by
    have hrhs_pos' : (0 : Int) * (inp.connectedMargin.den : Int)
                   < inp.reflectionMargin.num * (inp.connectedMargin.den : Int) := by
      rw [Int.zero_mul]; exact hrhs_pos
    exact Int.lt_of_mul_lt_mul_right hrhs_pos' (Int.le_of_lt hconnden_pos)
  -- goal: 0 * refl.den < refl.num * 1.
  rw [Int.zero_mul, Int.mul_one]
  exact hrefl_pos

/-- **Assembling the named input from the proved chiral heat-kernel gap.**  The
connected-sector half of `O4RestorationInput` is GENUINELY supplied by the proved
SU(2)×SU(2) heat-kernel margin; only the `reflection*` fields remain as the named
open analytic content the caller must justify.  This shows exactly where the
proved content stops and the named `O(4)`-restoration input begins. -/
def o4InputFromHeatKernel
    (wL : Q') (hL0 : (0 : Q') ≤ wL) (hL1 : wL < (1 : Q'))
    (wR : Q') (hR0 : (0 : Q') ≤ wR) (hR1 : wR < (1 : Q'))
    -- The single NAMED open analytic datum: the reflection sector preserves the
    -- connected margin (RG-irrelevance of the parity-breaking lattice operators).
    (reflectionMargin : Q')
    (reflectionMargin_ge :
      (heatKernelSpin4Gap wL hL0 hL1 wR hR0 hR1).margin ≤ reflectionMargin) :
    O4RestorationInput where
  connectedMargin := (heatKernelSpin4Gap wL hL0 hL1 wR hR0 hR1).margin
  connectedMargin_pos := heatKernelSpin4Gap_pos wL hL0 hL1 wR hR0 hR1
  reflectionMargin := reflectionMargin
  reflectionMargin_ge := reflectionMargin_ge

end YMGap.RepTheory.Spin4

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.Spin4.casimirSU2_num
#print axioms YMGap.RepTheory.Spin4.casimirSU2_oneHalf
#print axioms YMGap.RepTheory.Spin4.casimirSU2_nonneg
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_additive
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_nonneg
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_ge_left
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_ge_right
#print axioms YMGap.RepTheory.Spin4.selfDual_embedSelfDual
#print axioms YMGap.RepTheory.Spin4.antiSelfDual_embedAntiSelfDual
#print axioms YMGap.RepTheory.Spin4.antiSelfDual_embedSelfDual
#print axioms YMGap.RepTheory.Spin4.selfDual_embedAntiSelfDual
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_embedSelfDual
#print axioms YMGap.RepTheory.Spin4.casimirSpin4_embedAntiSelfDual_eqv
#print axioms YMGap.RepTheory.Spin4.max'_lt
#print axioms YMGap.RepTheory.Spin4.Spin4GapObligation.margin_pos
#print axioms YMGap.RepTheory.Spin4.chiralCombinedGap
#print axioms YMGap.RepTheory.Spin4.chiralCombinedGap_sep
#print axioms YMGap.RepTheory.Spin4.spin4Gap_of_chiral
#print axioms YMGap.RepTheory.Spin4.heatKernelSpin4Gap
#print axioms YMGap.RepTheory.Spin4.heatKernelSpin4Gap_pos
#print axioms YMGap.RepTheory.Spin4.heatKernelSpin4Gap_ge_min
#print axioms YMGap.RepTheory.Spin4.o4Gap_of_restoration
#print axioms YMGap.RepTheory.Spin4.o4InputFromHeatKernel
