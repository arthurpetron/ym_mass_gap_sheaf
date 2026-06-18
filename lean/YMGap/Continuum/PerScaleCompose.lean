/-
Per-scale COMPOSITION ALGEBRA — turning a sequence of single-scale spectral
contractions into the per-block-persistence product structure.

# What this module is

Route B of the gap attack runs the renormalization flow as a SEQUENCE of
single-scale (per-RG-block) spectral contractions and multiplies the resulting
per-block multipliers up.  The atomic, genuinely-provable rung — the single-link
heat-semigroup contraction at the exact spin-½ gap `C₂(½) = 3/4` — is supplied
elsewhere as `PerScaleContraction` / `su2PerScale`.  The per-block-persistence
form `RGBlockPersistence` consumes a per-block multiplier sequence `rho k`, the
block recursion `rho k · physGap k ≤ physGap (k+1)`, an anchor `g0 ≤ physGap 0`,
and a uniform PRODUCT FLOOR `prodFloor ≤ (∏_{i<k} rho i) · g0`.  From those it
derives `prodFloor ≤ physGap k` for all `k`, hence a positive continuum floor.

This module is the COMPOSITION ALGEBRA between the two: it bundles a per-scale
family of contractions into a tower carrying the block recursion and the
product floor, and PROVES

      PerScaleTower → RGBlockPersistence → RGGapPersistence → physGapMin > 0.

The structural composition (assembling `RGBlockPersistence` from the tower and
chaining the existing reductions) is GENUINELY proved.

# What is PROVED vs the NAMED OPEN input (be honest — AGENTS.md Rule 6)

  * PROVED — the COMPOSITION ALGEBRA.  Given a `PerScaleTower` (which already
    carries, as a SUPPLIED field, the uniform product floor), the assembly
    `PerScaleTower → RGBlockPersistence` is verbatim; composing with the existing
    `RGBlockPersistence.toUniform` and `physGapMin_pos_of_persistence` yields
    `PerScaleTower → physGapMin > 0` (`physGapMin_pos_of_tower`).  This is the
    structural multi-link composition: per-scale contractions, GIVEN the uniform
    product floor, yield the persistence.

  * NAMED OPEN INPUT — the uniform product floor itself.  The tower's
    `prodFloor`/`prodFloor_pos`/`prodFloor_le` fields are SUPPLIED, not derived.
    They assert that the per-block multipliers' running product
    `(∏_{i<k} rho i) · g0` stays bounded below by a single positive constant
    UNIFORMLY in `k`.  That is the multi-link / non-abelian susceptibility
    frontier — the survival of the gap multiplier across all scales — and it is
    NOT proved here.

  * THE HONEST CRUX (§3).  A CONSTANT per-scale multiplier `ρ < 1` (e.g.
    `su2PerScale.rho ≃ 1/4`) makes the running product `(∏_{i<k} ρ) · g0`
    STRICTLY DECREASE at every step: after one step it is already `ρ · g0 < g0`,
    and after each further step it shrinks again by the factor `ρ < 1`.  So a
    constant single-scale contraction does NOT by itself supply the product
    floor — the product collapses.  The product floor requires the multipliers
    to APPROACH 1 along the flow (`ρ_k → 1` fast enough), which is exactly the
    dimensional-transmutation content.  The open input is therefore not "each
    scale contracts" but "the contraction multipliers' product stays bounded
    below."  §4 makes this concrete: the constant-`su2PerScale` tower is
    structurally well-formed up to the product-floor field, which is precisely
    the obligation the constant `1/4` multiplier cannot discharge.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms`; permitted output
is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  Every modulus / constant is `Type`-level data.
-/

import YMGap.Continuum.PerScaleContraction
import YMGap.Continuum.RGGapPersistence

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RGGapPersistence

/-! ## 1. The composition input — `PerScaleTower`

A `PerScaleTower` bundles a per-scale family of single-scale contractions with
the block-recursion / anchor data the per-block-persistence form needs, PLUS the
SUPPLIED uniform product floor (the named open input).  Its per-block multiplier
sequence is `rho j := (scales j).rho`, the genuine per-scale multipliers. -/

/-- **`PerScaleTower` — the per-scale composition input.**

Carries:

  * `scales : Nat → PerScaleContraction` — the per-scale (per-RG-block)
    single-scale spectral contractions; each `scales j` is a genuine
    single-scale gap datum, with multiplier `(scales j).rho ∈ (0,1)`.
  * the spacing tower (`spacing`, `spacing_pos`, `atSpacing`) and ceiling
    (`ceilConst`, `physCeil`) — the non-open finite-data half;
  * the anchor (`anchor`, `anchor_pos`, `anchor_le`) — `g0 ≤ physGap 0`;
  * the block recursion (`recursion`) — `(scales k).rho · physGap k ≤
    physGap (k+1)`, written with the per-scale multiplier `(scales k).rho`;
  * **the NAMED OPEN INPUT** — `prodFloor`, `prodFloor_pos`, `prodFloor_le`:
    a SUPPLIED uniform product floor `c > 0` with
    `c ≤ (∏_{i<k} (scales i).rho) · g0` for all `k`.  This is the running
    product of the per-block multipliers staying bounded below uniformly in `k`
    — the multi-link / non-abelian susceptibility frontier (survival of the gap
    multiplier across all scales).  It is NOT proved here; an inhabitant of
    `PerScaleTower` ASSERTS it.

The per-block multiplier sequence `towerRho` below is `fun j => (scales j).rho`. -/
structure PerScaleTower : Type where
  /-- The per-scale single-scale spectral contractions. -/
  scales : Nat → PerScaleContraction
  /-- The lattice spacings `a_j`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j : Nat, (0 : Q') < spacing j
  /-- The fixed-spacing cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- A uniform physical ceiling. -/
  ceilConst : Q'
  /-- The physical gap is bounded above by the ceiling. -/
  physCeil : ∀ j : Nat,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ ceilConst
  /-- The anchor physical gap floor `g0 > 0`. -/
  anchor : Q'
  /-- The anchor floor is strictly positive. -/
  anchor_pos : (0 : Q') < anchor
  /-- **The anchor bound:** `g0 ≤ physGap 0`. -/
  anchor_le : anchor ≤
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  /-- **The block recursion** in terms of the per-scale multiplier:
  `(scales k).rho · physGap k ≤ physGap (k+1)`. -/
  recursion : ∀ k : Nat,
    (scales k).rho *
      Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k)
      ≤ Q'.divPos ((atSpacing (k + 1)).floorRate) (spacing (k + 1)) (spacing_pos (k + 1))
  /-- **NAMED OPEN INPUT** — the uniform product floor `c > 0`. -/
  prodFloor : Q'
  /-- The product floor is strictly positive. -/
  prodFloor_pos : (0 : Q') < prodFloor
  /-- **NAMED OPEN INPUT** — the uniform product bound:
  `c ≤ (∏_{i<k} (scales i).rho) · g0` for all `k`, i.e. the running product of
  the per-block multipliers stays bounded below uniformly in `k`.  This is the
  multi-link / susceptibility frontier; it is SUPPLIED, not proved. -/
  prodFloor_le : ∀ k : Nat,
    prodFloor ≤ prodPrefix (fun j => (scales j).rho) k * anchor

namespace PerScaleTower

/-- **The per-block multiplier sequence of a tower**, `towerRho T j = (scales j).rho`
— the genuine per-scale multipliers, each in `(0,1)`. -/
def towerRho (T : PerScaleTower) : Nat → Q' := fun j => (T.scales j).rho

/-- Each per-block multiplier is strictly positive (from `PerScaleContraction.rho_pos`). -/
theorem towerRho_pos (T : PerScaleTower) (k : Nat) : (0 : Q') < T.towerRho k :=
  (T.scales k).rho_pos

/-- Each per-block multiplier is nonnegative — the shape `RGBlockPersistence`
expects — from `rho_pos`. -/
theorem towerRho_nonneg (T : PerScaleTower) (k : Nat) : (0 : Q') ≤ T.towerRho k :=
  Q'.le_of_lt ((T.scales k).rho_pos)

/-- Each per-block multiplier is `< 1` (from `PerScaleContraction.rho_lt_one`):
each scale is a genuine strict contraction. -/
theorem towerRho_lt_one (T : PerScaleTower) (k : Nat) : T.towerRho k < 1 :=
  (T.scales k).rho_lt_one

end PerScaleTower

/-! ## 2. The composition theorem — `PerScaleTower ⇒ RGBlockPersistence ⇒ physGapMin > 0`

Assemble the `RGBlockPersistence` term from the tower's fields VERBATIM:
`rho := towerRho` (`= fun j => (scales j).rho`), `rho_nonneg := towerRho_nonneg`
(from per-scale `rho_pos`), the product floor and recursion copied directly.
Then chain the existing `RGBlockPersistence.toUniform` and
`physGapMin_pos_of_persistence`. -/

/-- **The composition (block-persistence construction).**  From a `PerScaleTower`
CONSTRUCT a `RGBlockPersistence` whose per-block multipliers are the per-scale
multipliers `(scales k).rho`, whose `rho_nonneg` is `towerRho_nonneg` (from
per-scale `rho_pos`), and whose product floor and recursion are the tower's
SUPPLIED fields verbatim.  Pure assembly — the structural multi-link composition.

Note `prodPrefix (towerRho T) = prodPrefix (fun j => (scales j).rho)`
definitionally, so `prodFloor_le` matches the tower's field directly. -/
def PerScaleTower.toBlockPersistence (T : PerScaleTower) : RGBlockPersistence where
  spacing := T.spacing
  spacing_pos := T.spacing_pos
  atSpacing := T.atSpacing
  ceilConst := T.ceilConst
  physCeil := T.physCeil
  rho := T.towerRho
  rho_nonneg := T.towerRho_nonneg
  anchor := T.anchor
  anchor_pos := T.anchor_pos
  anchor_le := T.anchor_le
  recursion := T.recursion
  prodFloor := T.prodFloor
  prodFloor_pos := T.prodFloor_pos
  prodFloor_le := T.prodFloor_le

/-- The constructed block-persistence form keeps the tower's per-block
multipliers. -/
@[simp] theorem PerScaleTower.toBlockPersistence_rho (T : PerScaleTower) :
    T.toBlockPersistence.rho = T.towerRho := rfl

/-- The constructed block-persistence form keeps the tower's product floor. -/
@[simp] theorem PerScaleTower.toBlockPersistence_prodFloor (T : PerScaleTower) :
    T.toBlockPersistence.prodFloor = T.prodFloor := rfl

/-- **Tower ⇒ uniform persistence.**  Compose the block-persistence assembly
with the existing `RGBlockPersistence.toUniform`: a `PerScaleTower` distils to
the single uniform open inequality `RGGapPersistence`, with `floorConst =
prodFloor`. -/
def PerScaleTower.toUniform (T : PerScaleTower) : RGGapPersistence :=
  T.toBlockPersistence.toUniform

/-- The distilled uniform floor is the tower's product floor. -/
@[simp] theorem PerScaleTower.toUniform_floorConst (T : PerScaleTower) :
    T.toUniform.floorConst = T.prodFloor := rfl

/-- **THE COMPOSITION HEADLINE: `PerScaleTower ⇒ physGapMin > 0`.**

Composing the block-persistence assembly, `RGBlockPersistence.toUniform`, and the
existing `physGapMin_pos_of_persistence`: a `PerScaleTower` yields a
strictly-positive continuum physical-gap floor.  This is the structural
multi-link composition — per-scale contractions, GIVEN the SUPPLIED uniform
product floor, yield the persistence.  (The product floor is the NAMED OPEN
input; see §3 for why a constant contraction does NOT supply it.) -/
theorem physGapMin_pos_of_tower (T : PerScaleTower) :
    (0 : Q') < (toScalingBand T.toUniform).physGapMin :=
  physGapMin_pos_of_persistence T.toUniform

/-- **The continuum gap SURVIVES `a → 0`, from a tower.**  Every physical gap
dominates the positive constant `ofQ' physGapMin`, uniformly in `j` — composing
the tower with `continuum_gap_of_RGGapPersistence`. -/
theorem continuum_gap_of_tower (T : PerScaleTower) (j : Nat) :
    ofQ' (toScalingBand T.toUniform).physGapMin ≤
      ofQ' ((toScalingBand T.toUniform).physGap j) :=
  continuum_gap_of_RGGapPersistence T.toUniform j

/-! ## 3. The honest gap, isolated — a constant contraction does NOT supply the floor

The composition theorem CONSUMES the product floor; it does not PRODUCE it.  The
crux: a CONSTANT per-scale multiplier `ρ < 1` makes the running product
`(∏_{i<k} ρ) · g0` STRICTLY DECREASE at every step, so no constant contraction
can supply a uniform product floor.  We make this precise without invoking any
limit: the product at step `k+1` is strictly below the product at step `k`
(`prodPrefix_const_strict_decrease`), and after one step it is already strictly
below the anchor `g0`.

The open input is therefore NOT "each scale contracts" (constant `ρ < 1`) but
"the contraction multipliers' product stays bounded below," i.e. `ρ_k → 1` fast
enough — the dimensional-transmutation content. -/

/-- For a CONSTANT multiplier family `fun _ => ρ`, the prefix product is just
the iterated product `prodPrefix _ (k+1) = prodPrefix _ k * ρ`.  (This is the
defining recursion of `prodPrefix`, recorded for use below.) -/
theorem prodPrefix_const_succ (ρ : Q') (k : Nat) :
    prodPrefix (fun _ => ρ) (k + 1) = prodPrefix (fun _ => ρ) k * ρ := rfl

/-- **The honest crux (general step).**  If `0 < ρ`, `ρ < 1`, and the prefix
product `prodPrefix (fun _ => ρ) k` is strictly positive, then the running
product STRICTLY DECREASES at step `k`:

      prodPrefix (fun _ => ρ) (k+1)  <  prodPrefix (fun _ => ρ) k.

So a constant contraction never holds the product at a floor — at every step it
strictly shrinks by the factor `ρ < 1`.  Proof: `p · ρ < p · 1 = p` by
strict multiplication on the left by the positive `p`. -/
theorem prodPrefix_const_strict_decrease (ρ : Q') (hρ1 : ρ < 1)
    (k : Nat) (hpk : (0 : Q') < prodPrefix (fun _ => ρ) k) :
    prodPrefix (fun _ => ρ) (k + 1) < prodPrefix (fun _ => ρ) k := by
  rw [prodPrefix_const_succ]
  -- Abbreviate the running product.  Goal: `p * ρ < p`.
  -- Cross-multiplied:  (p*ρ).num * p.den  <  p.num * (p*ρ).den, i.e.
  -- (p.num*ρ.num)*p.den < p.num*(p.den*ρ.den).
  show (prodPrefix (fun _ => ρ) k * ρ).num * ((prodPrefix (fun _ => ρ) k).den : Int)
      < (prodPrefix (fun _ => ρ) k).num
          * ((prodPrefix (fun _ => ρ) k * ρ).den : Int)
  have hpn : 0 < (prodPrefix (fun _ => ρ) k).num := Q'.num_pos_of_pos hpk
  have hpd : (0 : Int) < ((prodPrefix (fun _ => ρ) k).den : Int) := by
    exact_mod_cast (prodPrefix (fun _ => ρ) k).den_pos
  -- ρ < 1  at the num/den level, with (1).num = 1, (1).den = 1, gives ρ.num < ρ.den.
  have hr1 : ρ.num * ((1 : Q').den : Int) < (1 : Q').num * (ρ.den : Int) := hρ1
  have e1n : (1 : Q').num = 1 := rfl
  have e1d : ((1 : Q').den : Int) = 1 := rfl
  rw [e1n, e1d] at hr1
  have hrho : ρ.num < (ρ.den : Int) := by
    have := hr1; rw [Int.mul_one, Int.one_mul] at this; exact this
  -- Rewrite product num/den.
  rw [show (prodPrefix (fun _ => ρ) k * ρ).num
        = (prodPrefix (fun _ => ρ) k).num * ρ.num from rfl,
      Q'.mul_den_cast (prodPrefix (fun _ => ρ) k) ρ]
  -- Goal: (p.num*ρ.num)*p.den < p.num*(p.den*ρ.den).
  -- Both = (p.num*p.den)*{ρ.num,ρ.den}; strict from ρ.num < ρ.den times (p.num*p.den)>0.
  have hfac : (0 : Int) < (prodPrefix (fun _ => ρ) k).num
                * ((prodPrefix (fun _ => ρ) k).den : Int) := Int.mul_pos hpn hpd
  have hmul : ((prodPrefix (fun _ => ρ) k).num * ((prodPrefix (fun _ => ρ) k).den : Int)) * ρ.num
            < ((prodPrefix (fun _ => ρ) k).num * ((prodPrefix (fun _ => ρ) k).den : Int)) * (ρ.den : Int) :=
    Int.mul_lt_mul_of_pos_left hrho hfac
  have lhs_eq : ((prodPrefix (fun _ => ρ) k).num * ρ.num)
                  * ((prodPrefix (fun _ => ρ) k).den : Int)
              = ((prodPrefix (fun _ => ρ) k).num * ((prodPrefix (fun _ => ρ) k).den : Int)) * ρ.num := by
    ac_rfl
  have rhs_eq : (prodPrefix (fun _ => ρ) k).num
                  * (((prodPrefix (fun _ => ρ) k).den : Int) * (ρ.den : Int))
              = ((prodPrefix (fun _ => ρ) k).num * ((prodPrefix (fun _ => ρ) k).den : Int)) * (ρ.den : Int) := by
    ac_rfl
  rw [lhs_eq, rhs_eq]; exact hmul

/-! ## 4. Connection to `su2PerScale` — the frontier made concrete

A `PerScaleTower` built from the CONSTANT `su2PerScale` family (`scales := fun _
=> su2PerScale`, so `towerRho = fun _ => 1/4`) is structurally well-formed up to
the product-floor field: the per-scale contractions are genuine and the spacing /
ceiling / anchor / recursion shapes typecheck.  But its product floor CANNOT be
discharged by the constant `1/4` multiplier — the running product strictly
decreases, by §3.  We exhibit this concretely.

We use the per-block multiplier sequence `su2TowerRho := fun _ => su2PerScale.rho`,
which is `prodPrefix`'s argument for any constant-`su2PerScale` tower. -/

/-- The constant `su2PerScale` per-block multiplier sequence: `fun _ => 1/4`. -/
def su2TowerRho : Nat → Q' := fun _ => su2PerScale.rho

/-- `su2TowerRho k = su2PerScale.rho` (the constant `1/4`) at every block. -/
theorem su2TowerRho_eq (k : Nat) : su2TowerRho k = su2PerScale.rho := rfl

/-- The prefix product of the constant `su2PerScale` family is strictly positive
at every step (product of positives). -/
theorem su2_prodPrefix_pos (k : Nat) : (0 : Q') < prodPrefix su2TowerRho k := by
  induction k with
  | zero => show (0 : Q') < (1 : Q'); decide
  | succ n ih =>
      show (0 : Q') < prodPrefix su2TowerRho n * su2TowerRho n
      exact Q'.mul_pos ih su2PerScale_rho_pos

/-- **The frontier, concretely (the constant `su2PerScale` family collapses).**
For the constant `1/4` multiplier, the running product STRICTLY DECREASES at
every step:

      prodPrefix su2TowerRho (k+1)  <  prodPrefix su2TowerRho k.

Hence multiplying `by anchor > 0` it also strictly decreases, so NO positive
`prodFloor` can satisfy `prodFloor ≤ prodPrefix su2TowerRho k · g0` uniformly:
the constant `1/4` contraction does NOT supply the product floor.  This is the
named open obligation, made concrete on `su2PerScale`. -/
theorem su2_prodPrefix_strict_decrease (k : Nat) :
    prodPrefix su2TowerRho (k + 1) < prodPrefix su2TowerRho k :=
  prodPrefix_const_strict_decrease su2PerScale.rho su2PerScale_rho_lt_one k
    (su2_prodPrefix_pos k)

/-- **Concrete first-step collapse below the anchor.**  With anchor `g0 = 1` the
running product after one step is already strictly below `g0`:
`prodPrefix su2TowerRho 1 · 1 = 1/4 < 1`.  A single constant `1/4` contraction
drops the product below the anchor — there is no constant-`ρ` product floor.
(`decide` on the concrete `1/4`.) -/
theorem su2_prodPrefix_one_lt_anchor :
    prodPrefix su2TowerRho 1 * (1 : Q') < (1 : Q') := by decide

/-- **The honest summary lemma.**  The constant-`su2PerScale` running product is
BOTH strictly positive at every step AND strictly decreasing at every step.  The
composition algebra (`physGapMin_pos_of_tower`) needs a UNIFORM lower bound on
this product; strict positivity at each finite step does NOT provide one, and
strict decrease shows a constant contraction actively works against it.  The
uniform product floor — `ρ_k → 1` at the RG rate — is the NAMED OPEN input. -/
theorem su2_product_floor_is_open (k : Nat) :
    (0 : Q') < prodPrefix su2TowerRho k ∧
      prodPrefix su2TowerRho (k + 1) < prodPrefix su2TowerRho k :=
  ⟨su2_prodPrefix_pos k, su2_prodPrefix_strict_decrease k⟩

/-! ## 5. Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms PerScaleTower.towerRho_pos
#print axioms PerScaleTower.towerRho_nonneg
#print axioms PerScaleTower.towerRho_lt_one
#print axioms PerScaleTower.toBlockPersistence
#print axioms PerScaleTower.toBlockPersistence_rho
#print axioms PerScaleTower.toBlockPersistence_prodFloor
#print axioms PerScaleTower.toUniform
#print axioms PerScaleTower.toUniform_floorConst
#print axioms physGapMin_pos_of_tower
#print axioms continuum_gap_of_tower
#print axioms prodPrefix_const_succ
#print axioms prodPrefix_const_strict_decrease
#print axioms su2TowerRho_eq
#print axioms su2_prodPrefix_pos
#print axioms su2_prodPrefix_strict_decrease
#print axioms su2_prodPrefix_one_lt_anchor
#print axioms su2_product_floor_is_open

end YMGap.Continuum
