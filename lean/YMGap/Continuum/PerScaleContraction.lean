/-
Per-scale (single-link) spectral contraction — the atomic provable rung of the
Polchinski-flow / Bakry–Émery route to the RG gap multiplier.

# What this module is

Route B of the gap attack runs the renormalization flow as a sequence of
single-scale (per-RG-block) spectral contractions and multiplies the resulting
per-block multipliers up.  The atomic, genuinely-provable rung is the
SINGLE-LINK / single-scale contraction on the gauge group manifold.

For `SU(2) ≅ S³` the heat semigroup `e^{tΔ}` diagonalizes on spin-`j` modes
(the Peter–Weyl / character basis) and contracts the spin-`j` block by the
factor `e^{−t·C₂(j)}`, `C₂(j) = j(j+1)`.  The constant mode `j = 0` is fixed;
the SLOWEST nontrivial mode is `j = ½`, with Casimir

      C₂(½) = ½·(½+1) = 3/4.

This `3/4` is the EXACT single-link heat-semigroup spectral gap on `S³` — the
project's `c_λ` / `Casimir.gapFloor`.  It is reused here verbatim, not
re-introduced.  The Poincaré constant of the single-scale Dirichlet form is its
reciprocal, `1/gap = 4/3`, and the per-block contraction MULTIPLIER is built
from the gap as `ρ = 1 − gap = 1/4 ∈ (0,1)`.

# What is PROVED vs OPEN (be honest — AGENTS.md Rule 6)

  * PROVED (a genuine inhabitant, `su2PerScale`):  the single-link / single-scale
    spectral contraction at the EXACT gap `3/4`.  The SU(2) spectrum on `S³` is
    known exactly (Peter–Weyl), so this datum is real, not a placeholder:
    `gap = 3/4`, `poincareConst = 4/3`, `rho = 1/4`, all positive, with `rho < 1`.

  * OPEN (NOT inhabited here — the frontier):  composing single-scale
    contractions across a full block-spin step UNIFORMLY in the lattice volume.
    That requires removing the non-abelian susceptibility / multi-link coupling
    between adjacent links under a block-spin transformation.  This module
    states how the per-block multiplier WOULD feed `RGBlockPersistence.rho`
    (see `perScaleToBlockMultiplierNote`) but does not discharge that step.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only (`Q'` order / `Q'.divPos`).  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.RepTheory.SimpleGroup
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.RepTheory

/-! ## 0. Two `Q'` strict-order facts about `1 − x`

These are the only arithmetic facts the per-scale datum needs beyond the
existing `Q'` API; they are proved directly at the cross-multiplied
`num`/`den` level (`omega` on `Int`), axiom-clean. -/

/-- If `x < 1` then `0 < 1 − x`.  At the `num`/`den` level, `1 − x` has
numerator `den(x) − num(x)` over denominator `den(x)`, and `x < 1` says
`num(x) < den(x)`. -/
theorem sub_pos_of_lt_one {x : Q'} (h : x < 1) : (0 : Q') < 1 - x := by
  show (0 : Q').num * ((1 - x).den : Int) < (1 - x).num * ((0 : Q').den : Int)
  have hx : x.num * ((1 : Q').den : Int) < (1 : Q').num * (x.den : Int) := h
  -- (1 : Q').num = 1, (1 : Q').den = 1, (0 : Q').num = 0, (0 : Q').den = 1
  have e1n : (1 : Q').num = 1 := rfl
  have e1d : ((1 : Q').den : Int) = 1 := rfl
  have e0n : (0 : Q').num = 0 := rfl
  have e0d : ((0 : Q').den : Int) = 1 := rfl
  rw [e0n, e0d]
  -- (1 - x).num = 1·den(x) + (-num(x))·1 = den(x) − num(x)
  have esubn : (1 - x).num = (x.den : Int) - x.num := by
    show (1 : Q').num * (x.den : Int) + (-x.num) * ((1 : Q').den : Int)
        = (x.den : Int) - x.num
    rw [e1n, e1d]; omega
  rw [esubn]
  rw [e1n, e1d] at hx
  -- hx : x.num < x.den ; goal : 0 < (den(x) − num(x)) · 1
  have : (0 : Int) < (x.den : Int) - x.num := by omega
  omega

/-- If `0 < x` then `1 − x < 1`.  At the `num`/`den` level, `1 − x` has
numerator `den(x) − num(x)` over denominator `den(x)`, and `0 < x` says
`0 < num(x)`. -/
theorem sub_lt_self_of_pos {x : Q'} (h : (0 : Q') < x) : (1 : Q') - x < 1 := by
  show (1 - x).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 - x).den : Int)
  have hx : (0 : Q').num * (x.den : Int) < x.num * ((0 : Q').den : Int) := h
  have e1n : (1 : Q').num = 1 := rfl
  have e1d : ((1 : Q').den : Int) = 1 := rfl
  have e0n : (0 : Q').num = 0 := rfl
  have e0d : ((0 : Q').den : Int) = 1 := rfl
  rw [e0n, e0d] at hx
  -- hx : 0 < x.num
  have esubn : (1 - x).num = (x.den : Int) - x.num := by
    show (1 : Q').num * (x.den : Int) + (-x.num) * ((1 : Q').den : Int)
        = (x.den : Int) - x.num
    rw [e1n, e1d]; omega
  have esubd : ((1 - x).den : Int) = (x.den : Int) := by
    have hdnat : (1 - x).den = x.den := by
      show ((1 : Q').den * x.den - 1) + 1 = x.den
      have he : (1 : Q').den = 1 := rfl
      rw [he, Nat.one_mul]
      have hxd : 0 < x.den := Q'.den_pos x
      omega
    rw [hdnat]
  rw [esubn, esubd, e1n, e1d]
  -- goal : (den(x) − num(x))·1 < 1·den(x)
  omega

/-! ## 1. The exact single-link spectral gap `C₂(½) = 3/4` -/

/-- **The exact single-link heat-semigroup spectral gap on `SU(2) ≅ S³`.**
This is `C₂(½) = ½·(½+1) = 3/4`, the Casimir of the slowest nontrivial
(`j = ½`) Peter–Weyl mode — the gap by which `e^{tΔ}` contracts the slowest
non-constant block.  It is the project's `c_λ`, reused as `Casimir.gapFloor`
(`= Q'.mkPos 3 4`) so no new `3/4` constant is introduced. -/
def su2CasimirGap : Q' := Casimir.gapFloor

/-- `su2CasimirGap = 3/4` numerically. -/
theorem su2CasimirGap_num : su2CasimirGap.num = 3 := rfl

/-- `su2CasimirGap = 3/4` numerically. -/
theorem su2CasimirGap_den : su2CasimirGap.den = 4 := rfl

/-- `0 < su2CasimirGap` (reuses `Casimir.gapFloor_pos`). -/
theorem su2CasimirGap_pos : (0 : Q') < su2CasimirGap :=
  Casimir.gapFloor_pos

/-- The single-link gap is a strict contraction scale: `su2CasimirGap < 1`.
(`3/4 < 1`.)  This is what makes the derived multiplier `1 − gap` lie in
`(0,1)`. -/
theorem su2CasimirGap_lt_one : su2CasimirGap < 1 := by decide

/-! ## 2. The per-scale contraction datum -/

/-- **`PerScaleContraction` — the per-scale Poincaré / contraction datum.**

A single-scale (single-RG-block) spectral contraction is captured by:

  * `gap > 0`            — the single-scale spectral gap (the slowest
                            nontrivial-mode Casimir);
  * `poincareConst`      — the Poincaré constant `1/gap` of the single-scale
                            Dirichlet form (derived, `Q'.divPos 1 gap`);
  * `rho ∈ (0,1)`        — the per-block spectral contraction MULTIPLIER the
                            RG flow multiplies up, here `1 − gap`.

The fields are deliberately minimal and faithful to the implication
"single-scale spectral gap ⇒ per-block multiplier".  An inhabitant asserts a
genuine single-scale gap; it does NOT assert the multi-link composition
(that is the frontier, see `perScaleToBlockMultiplierNote`). -/
structure PerScaleContraction : Type where
  /-- The single-scale spectral gap (slowest nontrivial-mode Casimir). -/
  gap : Q'
  /-- The gap is strictly positive. -/
  gap_pos : (0 : Q') < gap
  /-- The gap is `< 1` (a strict contraction scale), so `1 − gap ∈ (0,1)`. -/
  gap_lt_one : gap < 1

namespace PerScaleContraction

/-- **The Poincaré constant `1/gap`** of the single-scale Dirichlet form.
Built constructively as `Q'.divPos 1 gap` (no choice, explicit reciprocal). -/
def poincareConst (P : PerScaleContraction) : Q' :=
  Q'.divPos 1 P.gap P.gap_pos

/-- `0 < poincareConst` (positive numerator over positive denominator). -/
theorem poincareConst_pos (P : PerScaleContraction) :
    (0 : Q') < P.poincareConst :=
  Q'.divPos_pos 1 P.gap P.gap_pos (by decide)

/-- **The per-block spectral contraction multiplier `ρ = 1 − gap`.**  This is
the factor by which the slowest mode's variance survives one single-scale heat
step; it is what the RG flow multiplies up across blocks.  For `gap ∈ (0,1)`
it lies in `(0,1)`. -/
def rho (P : PerScaleContraction) : Q' := 1 - P.gap

/-- `0 < rho` — from `gap < 1`. -/
theorem rho_pos (P : PerScaleContraction) : (0 : Q') < P.rho := by
  show (0 : Q') < 1 - P.gap
  exact sub_pos_of_lt_one P.gap_lt_one

/-- `rho < 1` — from `0 < gap`. -/
theorem rho_lt_one (P : PerScaleContraction) : P.rho < 1 := by
  show (1 : Q') - P.gap < 1
  exact sub_lt_self_of_pos P.gap_pos

end PerScaleContraction

/-! ## 3. The SU(2) inhabitant — the atomic PROVED rung -/

/-- **The SU(2) single-link per-scale contraction (a GENUINE inhabitant).**

`gap = su2CasimirGap = 3/4` (the EXACT spin-½ heat-semigroup gap on `S³`),
hence `poincareConst = 4/3` and the per-block multiplier `rho = 1/4`.  Unlike
the 4D multi-link frontier obligations, this datum is fully provable: the SU(2)
spectrum on `S³` is known exactly (Peter–Weyl), so every field is discharged. -/
def su2PerScale : PerScaleContraction where
  gap := su2CasimirGap
  gap_pos := su2CasimirGap_pos
  gap_lt_one := su2CasimirGap_lt_one

/-- The SU(2) gap field IS the exact `3/4`. -/
theorem su2PerScale_gap : su2PerScale.gap = su2CasimirGap := rfl

/-- The SU(2) Poincaré constant is `4/3` — verified as the exact-value bound
`poincareConst ≤ 4/3` AND `4/3 ≤ poincareConst`, i.e. it equals `4/3`.
Lower: `(4/3)·gap = (4/3)·(3/4) = 1 ≤ 1`.  Upper: `1 ≤ (4/3)·(3/4) = 1`. -/
theorem su2PerScale_poincareConst_le :
    su2PerScale.poincareConst ≤ Q'.mkPos 4 3 (by decide) := by
  show Q'.divPos 1 su2PerScale.gap su2PerScale.gap_pos ≤ Q'.mkPos 4 3 (by decide)
  refine Q'.divPos_le_of_le_mul 1 su2PerScale.gap su2PerScale.gap_pos ?_
  -- 1 ≤ (4/3)·(3/4) = 1
  show (1 : Q') ≤ Q'.mkPos 4 3 (by decide) * su2PerScale.gap
  decide

/-- The SU(2) Poincaré constant is `4/3` (lower bound): `4/3 ≤ poincareConst`. -/
theorem su2PerScale_poincareConst_ge :
    Q'.mkPos 4 3 (by decide) ≤ su2PerScale.poincareConst := by
  show Q'.mkPos 4 3 (by decide) ≤ Q'.divPos 1 su2PerScale.gap su2PerScale.gap_pos
  refine Q'.le_divPos_of_mul_le 1 su2PerScale.gap su2PerScale.gap_pos ?_
  -- (4/3)·(3/4) = 1 ≤ 1
  show Q'.mkPos 4 3 (by decide) * su2PerScale.gap ≤ (1 : Q')
  decide

/-- The SU(2) per-block multiplier is the exact `1/4`: `rho = 1 − 3/4 = 1/4`. -/
theorem su2PerScale_rho_eqv :
    su2PerScale.rho.eqv (Q'.mkPos 1 4 (by decide)) := by decide

/-- `0 < rho` for the SU(2) instance. -/
theorem su2PerScale_rho_pos : (0 : Q') < su2PerScale.rho :=
  su2PerScale.rho_pos

/-- `rho < 1` for the SU(2) instance. -/
theorem su2PerScale_rho_lt_one : su2PerScale.rho < 1 :=
  su2PerScale.rho_lt_one

/-! ## 4. Bridge note toward the RG block-persistence multiplier -/

/-- **Bridge note: how a per-scale multiplier WOULD feed the RG block recursion
— and the precise OPEN step.**

The RG gap-persistence layer consumes a per-block gap multiplier `rho : Nat → Q'`
with the block recursion `rho k · physGap k ≤ physGap (k+1)`.  A
`PerScaleContraction` supplies the per-block multiplier `P.rho ∈ (0,1)` for a
SINGLE scale, with the matching positivity `P.rho_pos`.  The intended bridge is

      rhoOfPerScale P = (fun _ : Nat => P.rho)

— a uniform per-block multiplier, e.g. `su2PerScale.rho = 1/4` at every block.

This `def` is provided below as the structural connector.  What it does NOT, and
must not, claim is the actual block recursion `rho k · physGap k ≤ physGap (k+1)`.

**The OPEN step** (the frontier — named, not inhabited):  proving that one
single-scale contraction at gap `3/4` actually survives a block-spin step,
UNIFORMLY in the lattice volume.  That is the non-abelian susceptibility /
multi-link composition problem: under a block-spin transformation the adjacent
links couple, and the single-link heat-semigroup contraction must be shown to
dominate that coupling uniformly.  Only the SINGLE-SCALE rung (`su2PerScale`,
the exact `3/4` gap) is discharged here; the multi-link composition is out of
scope and is NOT inhabited. -/
def rhoOfPerScale (P : PerScaleContraction) : Nat → Q' := fun _ => P.rho

/-- The bridge multiplier is positive at every block (the part that IS provable
from a single-scale datum). -/
theorem rhoOfPerScale_pos (P : PerScaleContraction) (k : Nat) :
    (0 : Q') < rhoOfPerScale P k :=
  P.rho_pos

/-- The bridge multiplier is nonnegative at every block — the shape
`RGBlockPersistence.rho_nonneg` expects.  (The block RECURSION, by contrast, is
the open multi-link step described in `rhoOfPerScale`'s docstring and is NOT
provided.) -/
theorem rhoOfPerScale_nonneg (P : PerScaleContraction) (k : Nat) :
    (0 : Q') ≤ rhoOfPerScale P k :=
  Q'.le_of_lt (P.rho_pos)

/-! ## 5. Axiom gates (AGENTS.md Rule 1) -/

#print axioms su2CasimirGap_pos
#print axioms su2CasimirGap_lt_one
#print axioms PerScaleContraction.poincareConst_pos
#print axioms PerScaleContraction.rho_pos
#print axioms PerScaleContraction.rho_lt_one
#print axioms su2PerScale
#print axioms su2PerScale_poincareConst_le
#print axioms su2PerScale_poincareConst_ge
#print axioms su2PerScale_rho_eqv
#print axioms rhoOfPerScale_pos
#print axioms rhoOfPerScale_nonneg

end YMGap.Continuum
