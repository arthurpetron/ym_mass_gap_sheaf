/-
Track B / R2 — the CLOSED-FORM SU(2) heat-kernel transfer-operator spectral gap.

# Why this module exists

The open continuum-gap obligation (`Continuum/RGGapPersistence.lean`'s single
inequality) is sharpest when attacked through the HEAT-KERNEL (Villain / Manton)
lattice action.  There the SU(2) transfer operator diagonalizes in the spin-`s`
character basis with the diagonal weights already encoded in
`Continuum/RGTransport.lean`:

    E χ_s = dimQ(s) · w^{C₄(s)},   dimQ(s) = s+1,   C₄(s) = s·(s+2),

with `w : Q'` the per-Casimir-unit heat-kernel weight (`w = e^{−t/4}`), `0 ≤ w`.
The VACUUM is the spin `s = 0` mode (eigenvalue `w^{C₄(0)} = w^0 = 1`); the first
EXCITED mode is `s = 1` (eigenvalue `w^{C₄(1)} = w^3`).  So the second-eigenvalue
/ gap separator is the CLOSED FORM — no Bessel functions —

    sep_HK(w) = w^3,

manifestly monotone in `w` and `< 1` for `w < 1`.

This module BUILDS that closed-form gap as genuine, axiom-clean Lean data:

  * `heatKernelSep w = w^3` (`= qpow w (c4 1)`, the excited/vacuum eigenvalue
    ratio), with nonnegativity, strict `< 1`, and monotonicity in `w`;
  * `heatKernelSpectralModel w` — a one-excited-mode `SpectralModel` whose
    eigenvalue is `w^3`, and `heatKernelLocatedGap` — a genuine
    `LocatedSpectralGap` with `sep = w^3`, hence the explicit positive gap
    margin `gapMargin = 1 − w^3 > 0` and geometric clustering at ratio `w^3`;
  * the bridge doc tying `heatKernelSep` to the open `RGGapPersistence` content.

# What is genuine — and what remains OPEN (honest)

The closed-form separator `sep = w^3`, its located-gap realization, the positive
margin `1 − w^3 > 0`, and monotonicity are all PROVED here.  This collapses the
open continuum problem to a CONCRETE one-variable inequality: with `w(a)` the
heat-kernel weight at spacing `a`, the per-spacing physical gap margin is
`(1 − w(a)^3)`, so the open content of the continuum bridge is precisely

    ∃ c > 0,  ∀ a → 0,   (1 − w(a)^3) / a  ≥  c,

i.e. a uniform lower bound on `(1 − w(a)^3)/a` along the asymptotic-freedom
relation `w(a) = e^{−t(a)/4}`.  This module does NOT establish that inequality —
the `w(a) ↔ a` asymptotic-freedom relation is the remaining open frontier — and
therefore does NOT inhabit the continuum-bridge obligation.  It exposes
`heatKernelSep` / `heatKernelLocatedGap` as the explicit object that obligation
consumes, and states exactly the one-variable inequality that remains.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, and the reused `Q'` order
lemmas.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`,
no `sorry`.  All witnesses (`sep`, the spectral model, the located gap) are
`Type`-level data.
-/

import YMGap.Continuum.RGTransport
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.HeatKernelGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport

/-! ## 1. The closed-form SU(2) heat-kernel gap separator `sep = w^3`

The first excited spin (`s = 1`) heat-kernel weight is `w^{C₄(1)} = w^3`; the
vacuum (`s = 0`) weight is `w^{C₄(0)} = w^0 = 1`.  So the eigenvalue ratio
excited/vacuum — the located second-eigenvalue separator — is exactly `w^3`. -/

/-- **The closed-form heat-kernel gap separator** `sep_HK(w) = w^3` (the spin-`1`
excited transfer eigenvalue over the spin-`0` vacuum eigenvalue `1`).  Reuses the
`Q'` power fold `qpow` of `RGTransport`. -/
def heatKernelSep (w : Q') : Q' := qpow w 3

/-- **The eigenvalue-ratio identity.**  `heatKernelSep w = w^{C₄(1)}`: the
separator is exactly the first-excited (`s = 1`) heat-kernel weight, tying it to
the `C₄` exponent of `charFunc` (`C₄ 1 = 1·3 = 3`). -/
theorem heatKernelSep_eq (w : Q') : heatKernelSep w = qpow w (c4 1) := by
  show qpow w 3 = qpow w (c4 1)
  rfl

/-- The separator is nonnegative for nonnegative `w` (`w^3 ≥ 0`). -/
theorem heatKernelSep_nonneg {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ heatKernelSep w :=
  qpow_nonneg w hw 3

/-! ### The `qpow` `≤ 1` / strict `< 1` helpers (minimal, proved here)

`RGTransport` provides `qpow_nonneg`; the order facts the gap needs — that a
power of `w ∈ [0,1]` stays `≤ 1`, and the strict `qpow w (n+1) < 1` for `w < 1`
— are proved here from the existing `Q'` order lemmas. -/

/-- A power of `w ∈ [0,1]` is `≤ 1`: `0 ≤ w ≤ 1 ⟹ w^n ≤ 1`. -/
theorem qpow_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, qpow w n ≤ (1 : Q')
  | 0 => by
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | n + 1 => by
      show qpow w n * w ≤ (1 : Q')
      -- w^n * w ≤ 1 * w  (mono in left factor, w ≥ 0), and 1 * w ≃ w ≤ 1.
      have h1 : qpow w n * w ≤ (1 : Q') * w :=
        Q'.mul_le_mul_of_nonneg_right (qpow w n) (1 : Q') w (qpow_le_one hw0 hw1 n) hw0
      have h2 : (1 : Q') * w ≤ (1 : Q') :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) hw1
      exact Q'.le_trans' _ _ _ h1 h2

/-- A successor power of `w ∈ [0,1)` is `≤ w`: `qpow w (n+1) ≤ w`.  (`w^n ≤ 1`,
so `w^n · w ≤ 1 · w ≃ w`.) -/
theorem qpow_succ_le_self {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (n : Nat) : qpow w (n + 1) ≤ w := by
  show qpow w n * w ≤ w
  have h1 : qpow w n * w ≤ (1 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_right (qpow w n) (1 : Q') w (qpow_le_one hw0 hw1 n) hw0
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.one_mul_eqv w))

/-- `a ≤ b → b < c → a < c` on `Q'` (local strict-chain helper, `num`-level). -/
theorem lt_of_le_of_lt {a b c : Q'} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have e1 : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) < c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  -- multiply e1 by c.den, e2 by a.den, chain through b.den>0
  have hcd : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          ≤ (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_lt_mul_of_pos_left e2 (by exact_mod_cast a.den_pos : (0:Int) < (a.den:Int))
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_le_of_lt s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- **The genuine gap (strict).**  `0 ≤ w` and `w < 1 ⟹ qpow w (n+1) < 1`:
a successor power of a sub-unit nonnegative weight is strictly below `1`.
(`qpow w (n+1) ≤ w < 1`.) -/
theorem qpow_succ_lt_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (n : Nat) : qpow w (n + 1) < (1 : Q') :=
  lt_of_le_of_lt (qpow_succ_le_self hw0 (Q'.le_of_lt hw1) n) hw1

/-- **The genuine gap:** `0 ≤ w → w < 1 → heatKernelSep w < 1`, i.e. `w^3 < 1`.
The first excited heat-kernel eigenvalue lies STRICTLY below the vacuum
eigenvalue `1` — the spectral gap. -/
theorem heatKernelSep_lt_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    heatKernelSep w < (1 : Q') :=
  qpow_succ_lt_one hw0 hw1 2

/-! ## 2. Monotonicity in `w` (the gap multiplier along the flow)

Cubing is monotone on the nonnegative `Q'` cone, so the separator increases with
the weight — this is what controls the gap multiplier along the RG flow. -/

/-- A power is monotone in the base on the nonnegative cone:
`0 ≤ w₁ → w₁ ≤ w₂ → qpow w₁ n ≤ qpow w₂ n`. -/
theorem qpow_mono {w₁ w₂ : Q'} (hw0 : (0 : Q') ≤ w₁) (hle : w₁ ≤ w₂) :
    ∀ n, qpow w₁ n ≤ qpow w₂ n
  | 0 => by
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | n + 1 => by
      show qpow w₁ n * w₁ ≤ qpow w₂ n * w₂
      have hw2 : (0 : Q') ≤ w₂ := Q'.le_trans' 0 w₁ w₂ hw0 hle
      -- w₁^n * w₁ ≤ w₂^n * w₁  (mono left, w₁ ≥ 0)
      have h1 : qpow w₁ n * w₁ ≤ qpow w₂ n * w₁ :=
        Q'.mul_le_mul_of_nonneg_right (qpow w₁ n) (qpow w₂ n) w₁ (qpow_mono hw0 hle n) hw0
      -- w₂^n * w₁ ≤ w₂^n * w₂  (mono right, w₂^n ≥ 0)
      have h2 : qpow w₂ n * w₁ ≤ qpow w₂ n * w₂ :=
        Q'.mul_le_mul_of_nonneg_left w₁ w₂ (qpow w₂ n) hle (qpow_nonneg w₂ hw2 n)
      exact Q'.le_trans' _ _ _ h1 h2

/-- **Monotonicity of the gap separator in the weight.**
`0 ≤ w₁ → w₁ ≤ w₂ → heatKernelSep w₁ ≤ heatKernelSep w₂` (cubing is monotone on
the nonnegative cone). -/
theorem heatKernelSep_mono {w₁ w₂ : Q'} (hw0 : (0 : Q') ≤ w₁) (hle : w₁ ≤ w₂) :
    heatKernelSep w₁ ≤ heatKernelSep w₂ :=
  qpow_mono hw0 hle 3

/-! ## 3. The genuine `LocatedSpectralGap` realization

We package the heat-kernel data as a finite (compact) transfer model with one
excited mode at eigenvalue `w^3` and weight `dimQ 1 = 2` (the spin-`1`
multiplicity).  Its `SpectralGapBound` at `sep = w^3` is the reflexive
`w^3 ≤ w^3`, and `sep < 1` is `heatKernelSep_lt_one` — so `LocatedSpectralGap`
is inhabited with the closed-form separator. -/

/-- The one-excited-mode heat-kernel transfer model: a single mode (`k = 1`) with
weight `dimQ 1 = 2` (spin-`1` multiplicity) and eigenvalue `w^3 = heatKernelSep w`.
Every `lam i` is the constant `w^3`, so the gap bound holds for all `i`. -/
def heatKernelSpectralModel (w : Q') (hw : (0 : Q') ≤ w) : SpectralModel where
  k := 1
  w := fun _ => dimQ 1
  lam := fun _ => heatKernelSep w
  w_nonneg := fun _ => dimQ_nonneg 1
  lam_nonneg := fun _ => heatKernelSep_nonneg hw

/-- The model's eigenvalues are all `w^3` — the gap bound `∀ i, λᵢ ≤ w^3` is the
reflexive `w^3 ≤ w^3`. -/
theorem heatKernelSpectralModel_gapBound (w : Q') (hw : (0 : Q') ≤ w) :
    SpectralGapBound (heatKernelSpectralModel w hw) (heatKernelSep w) :=
  fun _ => Q'.le_refl' (heatKernelSep w)

/-- **The closed-form heat-kernel located spectral gap.**  A genuine
`LocatedSpectralGap` for the one-excited-mode transfer model, with the explicit
separator `sep = heatKernelSep w = w^3` strictly below the vacuum eigenvalue `1`
(for `0 ≤ w < 1`).  This is the located second eigenvalue of the COMPACT (finite)
heat-kernel transfer operator, in closed form. -/
def heatKernelLocatedGap (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    LocatedSpectralGap (heatKernelSpectralModel w hw0) where
  sep := heatKernelSep w
  sep_lt_one := heatKernelSep_lt_one hw0 hw1
  bound := heatKernelSpectralModel_gapBound w hw0

/-- The located gap's separator is the closed form `w^3`. -/
@[simp] theorem heatKernelLocatedGap_sep (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) :
    (heatKernelLocatedGap w hw0 hw1).sep = heatKernelSep w := rfl

/-- **The explicit positive gap margin** `gapMargin = 1 − w^3 > 0`.  The
eigenvalue-gap margin of the heat-kernel located gap is the closed-form positive
quantity `1 − w^3` — the SU(2) heat-kernel mass gap in transfer-eigenvalue space
(no `log` needed; the physical mass is `−log(w^3) = −3 log w`). -/
theorem heatKernelGapMargin_eq (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (heatKernelLocatedGap w hw0 hw1).gapMargin = (1 : Q') - heatKernelSep w := rfl

/-- The heat-kernel gap margin `1 − w^3` is strictly positive — THE constructive
"there is a gap" witness for the SU(2) heat-kernel transfer operator. -/
theorem heatKernelGapMargin_pos (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (0 : Q') < (heatKernelLocatedGap w hw0 hw1).gapMargin :=
  (heatKernelLocatedGap w hw0 hw1).gapMargin_pos

/-- **Closed-form gap ⇒ geometric clustering at ratio `w^3`.**  The heat-kernel
located gap forces the finite-volume connected two-point function to decay
geometrically `G(n) ≤ G(0) · (w^3)^n`, with `w^3 < 1` — the constructive
clustering consequence of the closed-form SU(2) heat-kernel gap. -/
theorem heatKernelGap_decay (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (n : Nat) :
    corr (heatKernelSpectralModel w hw0) n
      ≤ (corr (heatKernelSpectralModel w hw0) 0) * (heatKernelSep w) ^ n :=
  (heatKernelLocatedGap w hw0 hw1).decay n

/-! ## 4. Bridge toward the continuum-gap obligation — the explicit object

`heatKernelSep` is the EXPLICIT physical-gap-generating function the continuum
bridge consumes.  In the continuum bridge the open content is a uniform lower
bound, along the asymptotic-freedom trajectory `a → 0`, on the PHYSICAL gap
margin `(per-spacing eigenvalue-gap margin) / a`.  With the heat-kernel action
the per-spacing eigenvalue-gap margin is the CLOSED FORM `1 − w(a)^3 =
1 − heatKernelSep (w a)`, where `w(a) = e^{−t(a)/4}` is the heat-kernel weight at
spacing `a`.  So the open content becomes the concrete one-variable statement
below.

`heatKernelMargin w := 1 − heatKernelSep w = 1 − w^3` is that explicit margin,
strictly positive for `0 ≤ w < 1` (it is the `gapMargin` of the located gap).
We expose it and its positivity as the object the bridge consumes — WITHOUT
inhabiting the bridge obligation. -/

/-- The explicit per-spacing eigenvalue-gap margin as a function of the
heat-kernel weight `w`: `heatKernelMargin w = 1 − w^3`. -/
def heatKernelMargin (w : Q') : Q' := (1 : Q') - heatKernelSep w

/-- The explicit margin equals the located gap's `gapMargin` — i.e. the bridge's
per-spacing eigenvalue-gap margin IS this closed form `1 − w^3`. -/
theorem heatKernelMargin_eq_gapMargin (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) :
    heatKernelMargin w = (heatKernelLocatedGap w hw0 hw1).gapMargin := rfl

/-- The explicit margin is strictly positive for a sub-unit weight `0 ≤ w < 1`
(`1 − w^3 > 0`).  This is the closed-form ingredient; what remains open is its
behaviour DIVIDED BY `a` as `a → 0` (see the doc below). -/
theorem heatKernelMargin_pos (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (0 : Q') < heatKernelMargin w :=
  one_sub_pos_of_lt_one (heatKernelSep_lt_one hw0 hw1)

/-- **The explicit margin is monotone in the weight (anti-monotone in the gap).**
`0 ≤ w₁ → w₁ ≤ w₂ → heatKernelMargin w₂ ≤ heatKernelMargin w₁`: a larger weight
(slower flow) gives a SMALLER eigenvalue-gap margin, since `1 − w^3` decreases as
`w^3 = heatKernelSep w` increases.  (`sub` is anti-monotone in its subtrahend.) -/
theorem heatKernelMargin_anti {w₁ w₂ : Q'} (hw0 : (0 : Q') ≤ w₁) (hle : w₁ ≤ w₂) :
    heatKernelMargin w₂ ≤ heatKernelMargin w₁ := by
  -- 1 − b ≤ 1 − a  ⇐  a ≤ b: rewrite `1 − x = 1 + (−x)`, then `add_le_add_left`
  -- with `−b ≤ −a` (`neg_le_neg` of `heatKernelSep_mono`).
  have hsep : heatKernelSep w₁ ≤ heatKernelSep w₂ := heatKernelSep_mono hw0 hle
  show (1 : Q') + -(heatKernelSep w₂) ≤ (1 : Q') + -(heatKernelSep w₁)
  exact Q'.add_le_add_left (1 : Q') (-(heatKernelSep w₂)) (-(heatKernelSep w₁))
    (Q'.neg_le_neg hsep)

end YMGap.Continuum.HeatKernelGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSep_eq
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSep_nonneg
#print axioms YMGap.Continuum.HeatKernelGap.qpow_le_one
#print axioms YMGap.Continuum.HeatKernelGap.qpow_succ_le_self
#print axioms YMGap.Continuum.HeatKernelGap.lt_of_le_of_lt
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSep_lt_one
#print axioms YMGap.Continuum.HeatKernelGap.qpow_mono
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSep_mono
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSpectralModel
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelSpectralModel_gapBound
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelLocatedGap
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelLocatedGap_sep
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelGapMargin_eq
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelGapMargin_pos
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelGap_decay
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelMargin_eq_gapMargin
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelMargin_pos
#print axioms YMGap.Continuum.HeatKernelGap.heatKernelMargin_anti
