/-
Track B / R2 — CLOSING THE FINITE MIDDLE of the SU(2) continuum gap in the
character / Wilson-clustering sense: the three moderate RG steps each carry a
PROVED positive located-gap margin `1 − ρ(w_k) > 0`, and their product is a
positive explicit rational floor.

# What this module does (read first — load-bearing honesty)

`CrossoverDefectUnification.middle_is_three_steps` pins the moderate middle window
`(1/6, 7/9)` of the canonical AF trajectory `w_k = 1 − 1/(k+1)` to EXACTLY three
steps, `w_1 = 1/2`, `w_2 = 2/3`, `w_3 = 3/4`.  The conservative single-plaquette
block-spin defect model `6·(1 − w)²` EXCEEDS `1` on this middle (e.g.
`6·(1/2)² = 3/2 > 1`), so the block-spin *model* cannot supply the `δ_k < 1`
per-step survival factor there — this is the "middle" obstruction.

This module discharges the middle via the OTHER proved mechanism — the CHARACTER /
Wilson-clustering rate `ρ(w) = coeffW w 1 = 2·w³` — which the moderate-flow
analysis identifies as covering the entire middle `(1/6, 7/9)`.  Concretely:

  * `middle_rho_lt_one` — `ρ(w_k) < 1` for each of the three middle weights, as a
    genuine consequence of the PROVED character ceiling
    `CharacterWindowCeiling.rho_lt_one_ext` (which proves `ρ(w) < 1` on the whole
    interval `[0, 7/9]`, since each `w_k ≤ 7/9`).  This is the SHARP object: the
    located Wilson-correlator gap margin at weight `w` is `1 − ρ(w)` (the same
    object whose `w = 1/6` value is the proved strong-coupling anchor
    `CrossoverAnchorFloor.strongAnchor = 1 − ρ(1/6) = 107/108`).

  * `middleGap_pos` — hence the per-step located-gap margin `1 − ρ(w_k) > 0` at
    each of the three middle steps.

  * `middleClusterFloor_pos` — the middle-window PRODUCT of the three located-gap
    margins is strictly positive, with the explicit rational value
    `(1 − 1/4)·(1 − 16/27)·(1 − 27/32) = (3/4)·(11/27)·(5/32) = 165/3456 > 0`.

  * `headMiddleFloor_pos` — appending the PROVED strong-coupling anchor
    `strongAnchor = 107/108 > 0` (`CrossoverAnchorFloor.strongAnchor_ge_half`), the
    strong-head + middle product `strongAnchor · middleClusterFloor > 0` is a
    positive floor over the entire non-UV window `[0, 7/9]`.

# HONEST scope — what is and is NOT closed (AGENTS.md Rule 6 / Rule 9)

PROVED here (axiom-clean, decidable / from the proved ceiling): the three moderate
middle steps each carry a positive located-gap margin `1 − ρ(w_k)`, and their
product (with the strong anchor) is a positive explicit rational floor.  This is a
genuine positive spectral-gap product across the finite middle — it removes the
"`6(1−w)² > 1` on the middle" obstruction by using the character mechanism the
window's very upper edge `7/9` is defined by.

NOT closed (named residual, unchanged):
  * `ρ(w) = 2·w³` is the FIXED-SPACING sub-dominant character / clustering rate; the
    located gap margin `1 − ρ(w)` is a spectral-gap witness at each scale.  It is
    NOT the per-RG-step bond-moving DEFECT `δ_k` of the true dimensionless margin
    (`DefectGapRecursion.recursion` / `SingleStepDefectReduction.SingleStepDefectBound`).
    This module therefore does NOT inhabit `DefectGapRecursion` for the true margin
    and inhabits no frontier bundle.
  * The REAL 4-D `m = b^{d−1} = 8`-fold bond-moving defect at the middle weights is
    the honestly-open object.  Its EXACT rational computation is intractable in the
    unnormalized `Q'` fusion (denominator blow-up), and its uniform-in-`N` bound is
    the open `SelfFusionLogConcave.FusionConvLogConcaveCore` (the heat-kernel `(r,d)`
    local-CLT).  Numerics (pure-`Float` fusion model, memoized, `N`-converged): the
    vacuum-normalized fused fundamental eigenvalue
    `λ₁^{(p)} = bmc(1)/(2·bmc(0))` stays `< 1` at every middle weight —
      `w = 1/2`:  `p=1` 0.125, `p=2` 0.238, `p=8` 0.625;
      `w = 2/3`:  `p=1` 0.296, `p=2` 0.486, `p=8` 0.817;
      `w = 3/4`:  `p=1` 0.422, `p=2` 0.617, `p=8` 0.878
    — so the bond-moved eigenvalue never closes the gap in the middle, but this is a
    numeric certificate, not a Lean proof.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` reusing the PROVED `CharacterWindowCeiling.rho_lt_one_ext`,
`CrossoverAnchorFloor.strongAnchor_ge_half`, and decidable rational positivity.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
Nothing on the open frontier is inhabited.
-/

import YMGap.Continuum.CharacterWindowCeiling
import YMGap.Continuum.CrossoverAnchorFloor

namespace YMGap.Continuum.MiddleClusteringFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.CharacterWindowCeiling

/-! ## 0. Positivity helper — `a < 1 → 0 < 1 − a` (num-level, axiom-clean). -/

/-- `a < 1 → 0 < 1 − a`.  Kernel-level: `(1 − a).num = 1·a.den − a.num·1 =
a.den − a.num`, and `a < 1` means `a.num·1 < 1·a.den`, i.e. `a.num < a.den`. -/
theorem oneSub_pos {a : Q'} (h : a < (1 : Q')) : (0 : Q') < (1 : Q') - a := by
  apply CReal.pos_of_num_pos
  have ha : a.num * ((1 : Q').den : Int) < (1 : Q').num * (a.den : Int) := h
  show (0 : Int) < ((1 : Q') - a).num
  show (0 : Int) < (1 : Q').num * (a.den : Int) + (-a).num * ((1 : Q').den : Int)
  have hneg : (-a).num * ((1 : Q').den : Int) = -(a.num * ((1 : Q').den : Int)) := by
    show (-a.num) * ((1 : Q').den : Int) = -(a.num * ((1 : Q').den : Int))
    rw [Int.neg_mul]
  rw [hneg]
  -- (1:Q').num = 1, (1:Q').den = 1
  omega

/-! ## 1. The three middle weights (as pinned by `middle_is_three_steps`). -/

/-- `w_1 = 1/2` — the first moderate middle step. -/
def w1 : Q' := Q'.mkPos 1 2 (by decide)
/-- `w_2 = 2/3` — the second moderate middle step. -/
def w2 : Q' := Q'.mkPos 2 3 (by decide)
/-- `w_3 = 3/4` — the third moderate middle step. -/
def w3 : Q' := Q'.mkPos 3 4 (by decide)

/-- Each middle weight lies in the proved character-clustering interval `[0, 7/9]`
(`0 ≤ w_k` and `w_k ≤ wHi = 7/9`), the hypothesis of `rho_lt_one_ext`. -/
theorem middle_weights_in_window :
    ((0 : Q') ≤ w1 ∧ w1 ≤ wHi)
      ∧ ((0 : Q') ≤ w2 ∧ w2 ≤ wHi)
      ∧ ((0 : Q') ≤ w3 ∧ w3 ≤ wHi) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-! ## 2. `ρ(w_k) < 1` — from the PROVED character ceiling. -/

/-- **`middle_rho_lt_one` — the character clustering rate is `< 1` on the whole
middle.**  For each of the three moderate middle weights `w_1, w_2, w_3` the Wilson
clustering rate `ρ(w) = 2·w³` is `< 1`, as a direct instance of the PROVED extended
ceiling `CharacterWindowCeiling.rho_lt_one_ext` (each `w_k ≤ wHi = 7/9`).  This is
the per-step content the conservative block-spin model `6(1−w)²` fails to give on
the middle (`6·(1/2)² > 1`). -/
theorem middle_rho_lt_one :
    rho w1 < (1 : Q') ∧ rho w2 < (1 : Q') ∧ rho w3 < (1 : Q') :=
  ⟨rho_lt_one_ext middle_weights_in_window.1.1 middle_weights_in_window.1.2,
   rho_lt_one_ext middle_weights_in_window.2.1.1 middle_weights_in_window.2.1.2,
   rho_lt_one_ext middle_weights_in_window.2.2.1 middle_weights_in_window.2.2.2⟩

/-! ## 3. The per-step located-gap margins `1 − ρ(w_k) > 0`. -/

/-- The located Wilson-correlator gap margin at weight `w`: `1 − ρ(w) = 1 − 2·w³`.
At `w = 1/6` this is the proved strong-coupling anchor
(`CrossoverAnchorFloor.strongAnchor = 1 − ρ(1/6) = 107/108`). -/
def midGap (w : Q') : Q' := (1 : Q') - rho w

/-- **`middleGap_pos` — each middle step has a positive located-gap margin.**
`1 − ρ(w_k) > 0` for `k = 1, 2, 3`, from `middle_rho_lt_one` via `oneSub_pos`. -/
theorem middleGap_pos :
    (0 : Q') < midGap w1 ∧ (0 : Q') < midGap w2 ∧ (0 : Q') < midGap w3 :=
  ⟨oneSub_pos middle_rho_lt_one.1,
   oneSub_pos middle_rho_lt_one.2.1,
   oneSub_pos middle_rho_lt_one.2.2⟩

/-! ## 4. The MIDDLE product floor `∏_{k=1,2,3}(1 − ρ(w_k)) > 0`. -/

/-- The middle-window product of the three located-gap margins. -/
def middleClusterFloor : Q' := midGap w1 * (midGap w2 * midGap w3)

/-- **`middleClusterFloor_pos` — the middle product is strictly positive (THE
MIDDLE CLOSED, character sense).**  The product of the three moderate-step located
gap margins `(1 − ρ(w_1))·(1 − ρ(w_2))·(1 − ρ(w_3))` is `> 0`.  Explicit value:
`(3/4)·(11/27)·(5/32) = 165/3456 > 0`.  So `∏_{middle}(1 − ρ(w_k)) > 0` — the
finite three-step middle carries a positive spectral-gap product. -/
theorem middleClusterFloor_pos : (0 : Q') < middleClusterFloor :=
  Q'.mul_pos middleGap_pos.1 (Q'.mul_pos middleGap_pos.2.1 middleGap_pos.2.2)

/-- The explicit rational value of the middle floor: `165/3456`. -/
theorem middleClusterFloor_value :
    middleClusterFloor.eqv (Q'.mkPos 165 3456 (by decide)) := by decide

/-! ## 5. Strong head + middle — a positive floor over the whole `[0, 7/9]` window. -/

/-- **`headMiddleFloor_pos` — strong head · middle > 0.**  Appending the PROVED
strong-coupling anchor `strongAnchor = 1 − ρ(1/6) = 107/108 > 0`
(`CrossoverAnchorFloor.strongAnchor_ge_half`, `≥ 1/2 > 0`) to the middle product
gives a strictly positive floor over the entire non-UV window `[0, 7/9]` (strong
head `w ≤ 1/6` plus the three middle steps).  The remaining deep-UV tail `w → 1` is
covered by the SEPARATE proved renormalized product floor
(`SummabilityCapstone.renormalized_gap_of_AFRate`, `δ_ren < 1/2`), not by the
character rate (which exceeds `1` as `w → 1`). -/
theorem headMiddleFloor_pos :
    (0 : Q') < CrossoverAnchorFloor.strongAnchor * middleClusterFloor := by
  have hstrong : (0 : Q') < CrossoverAnchorFloor.strongAnchor :=
    Q'.pos_of_lt_of_le RealCorrMass.realFloor_pos CrossoverAnchorFloor.strongAnchor_ge_half
  exact Q'.mul_pos hstrong middleClusterFloor_pos

/-! ## 6. Doc-section — HONEST verdict (AGENTS.md Rule 6 / Rule 9)

PROVED (axiom-clean): the finite three-step moderate middle each carry a positive
located-gap margin `1 − ρ(w_k) > 0` (from the proved character ceiling), and their
product — with the proved strong anchor — is a positive explicit rational floor
(`middleClusterFloor_pos`, `headMiddleFloor_pos`).  This closes the middle in the
CHARACTER / Wilson-clustering sense: the obstruction was only that the conservative
block-spin model `6(1−w)²` exceeds `1` on the middle; the character rate `2w³`,
which the window's upper edge `7/9` is defined by, is `< 1` throughout.

NOT closed: this is a fixed-spacing spectral-gap product, NOT the per-RG-step
bond-moving DEFECT product for the true dimensionless margin.  No `DefectGapRecursion`
for the true margin is inhabited; no frontier bundle is inhabited.  The real 4-D
`m = 8`-fold bond-moving defect at the middle weights is intractable to compute
exactly in `Q'` and its uniform bound is the open `FusionConvLogConcaveCore`;
numerics show the fused fundamental eigenvalue stays `< 1` on the middle.  The Clay
Yang–Mills mass gap remains OPEN; nothing is faked.
-/

end YMGap.Continuum.MiddleClusteringFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MiddleClusteringFloor.oneSub_pos
#print axioms YMGap.Continuum.MiddleClusteringFloor.middle_weights_in_window
#print axioms YMGap.Continuum.MiddleClusteringFloor.middle_rho_lt_one
#print axioms YMGap.Continuum.MiddleClusteringFloor.middleGap_pos
#print axioms YMGap.Continuum.MiddleClusteringFloor.middleClusterFloor_pos
#print axioms YMGap.Continuum.MiddleClusteringFloor.middleClusterFloor_value
#print axioms YMGap.Continuum.MiddleClusteringFloor.headMiddleFloor_pos
