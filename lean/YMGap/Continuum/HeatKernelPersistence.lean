/-
Track B / R2 — the continuum-gap obligation made CONCRETE in the closed-form
heat-kernel margin `1 − w³`.

# What this module is

The abstract continuum-gap obligation packages the open content as a uniform
lower bound on the PHYSICAL gap `m_lat(a_j) / a_j`, where `m_lat(a_j)` is the
per-spacing lattice-unit clustering floor.  That abstract obligation consumes a
`RegUniformClusterBound` at each spacing and asks only that the resulting
physical quotient stay bounded below by a single positive constant `c > 0`
uniformly along `a_j → 0`.

This module makes the lattice floor `m_lat(a_j)` EXPLICIT.  With the SU(2)
heat-kernel (Villain / Manton) action the transfer operator diagonalizes in the
spin-`s` character basis: the vacuum is `s = 0` (eigenvalue `1`), the first
excited mode is `s = 1` (eigenvalue `w³`), so the per-spacing eigenvalue-gap
margin is the CLOSED FORM `m_lat = 1 − w³`, with `w = w(a)` the heat-kernel
weight at spacing `a`.  The module:

  * builds, for a sub-unit weight `0 ≤ w < 1`, a `RegUniformClusterBound`
    (`heatKernelClusterBound`) whose finite-volume located gaps are the
    closed-form `heatKernelLocatedGap` (a constant-in-volume family) and whose
    uniform clustering floor `floorRate` is EXACTLY `1 − w³`;

  * packages the open content as `HeatKernelPersistence`, carrying a weight
    sequence `w_j`, a spacing sequence `a_j`, and the EXPLICIT inequality
    `c ≤ (1 − w_j³)/a_j` for all `j`;

  * proves the reduction `HeatKernelPersistence → RGGapPersistence`, hence
    `HeatKernelPersistence → physGapMin > 0`.  After this reduction the abstract
    open inequality is, definitionally, the explicit one-variable statement
    `c ≤ (1 − w_j³)/a_j`.

# What is genuine — and what remains OPEN (honest)

The closed-form lattice floor `1 − w³`, its positivity, its realization as the
`floorRate` of a genuine `RegUniformClusterBound`, and the reduction of the
abstract continuum obligation to the explicit inequality are all PROVED here.
This REDUCES the abstract obligation to the SINGLE explicit one-variable
inequality

    ∃ c > 0,  ∀ j,   (1 − w_j³) / a_j  ≥  c,

along the asymptotic-freedom trajectory `w_j = w(a_j) = e^{−t(a_j)/4}`.  This
module does NOT inhabit that inequality: the `w(a) ↔ a` asymptotic-freedom
relation is the remaining open frontier, so NO inhabitant of
`HeatKernelPersistence` for 4D Yang–Mills is provided.  It exposes the explicit
object the obligation consumes and states precisely the one inequality that
remains.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural assembly over the reused located-gap,
cluster-bound, and `divPos` data.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  Every witness (the cluster
bound, the persistence datum, the reduction) is `Type`-level data.
-/

import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.RGGapPersistence
import YMGap.Continuum.RegularContinuumPipeline
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.HeatKernelPersistence

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RGGapPersistence

/-! ## 1. The per-scale heat-kernel cluster bound — `floorRate = 1 − w³`

For a sub-unit weight `0 ≤ w < 1`, the closed-form heat-kernel located gap
`heatKernelLocatedGap w` has separator `sep = w³` and margin `1 − w³`.  We
package it as a `RegUniformClusterBound` whose finite-volume located family is
CONSTANT in the volume `Λ` (every volume carries the same closed-form located
gap), so its gap-margin sequence is the constant `1 − w³` and is trivially
Cauchy (outer modulus `M ε = 0`).  Its uniform clustering floor `floorRate` is
set to `heatKernelMargin w = 1 − w³`; the `uniform_floor` field is then the
reflexive `(1 − w³) ≤ (located Λ).gapMargin`, since `(located Λ).gapMargin` IS
`1 − w³` (`heatKernelMargin_eq_gapMargin`). -/

/-- **The per-scale heat-kernel cluster bound.**  A `RegUniformClusterBound`
whose finite-volume located gaps are the closed-form heat-kernel located gap
`heatKernelLocatedGap w` (constant in the volume `Λ`) and whose uniform
clustering floor is EXACTLY the closed-form margin `floorRate = heatKernelMargin
w = 1 − w³`.  The outer Cauchy modulus is trivial (`M ε = 0`) because the
gap-margin sequence is the constant `1 − w³`. -/
def heatKernelClusterBound (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    RegUniformClusterBound where
  gaps := fun _ => heatKernelSpectralModel w hw0
  located := fun _ => heatKernelLocatedGap w hw0 hw1
  floorRate := heatKernelMargin w
  floorRate_pos := heatKernelMargin_pos w hw0 hw1
  uniform_floor := fun Λ =>
    -- floorRate = heatKernelMargin w = (heatKernelLocatedGap w hw0 hw1).gapMargin
    Q'.le_of_eqv (Q'.eqv_of_eq (heatKernelMargin_eq_gapMargin w hw0 hw1))
  M := fun _ => 0
  Mmono := fun _ _ _ _ => Nat.le_refl 0
  bound := by
    intro ε hε i j _ _
    -- The located family is constant, so margin_i = margin_j = 1 − w³; each is
    -- ≤ itself + ε.
    exact ⟨Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε),
           Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)⟩

/-- **The per-scale cluster bound's clustering floor is the closed form `1 − w³`.**
`(heatKernelClusterBound w …).floorRate = heatKernelMargin w = 1 − w³`. -/
@[simp] theorem heatKernelClusterBound_floorRate (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) :
    (heatKernelClusterBound w hw0 hw1).floorRate = heatKernelMargin w := rfl

/-- The per-scale cluster bound's located gap at each volume is the closed-form
heat-kernel located gap (separator `w³`). -/
@[simp] theorem heatKernelClusterBound_located (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (Λ : Nat) :
    (heatKernelClusterBound w hw0 hw1).located Λ = heatKernelLocatedGap w hw0 hw1 :=
  rfl

/-! ## 2. The explicit open content — `HeatKernelPersistence`

`HeatKernelPersistence` packages the spacing tower with the open inequality made
FULLY EXPLICIT in `(w_j, a_j)`.  It carries a heat-kernel weight sequence `w_j`
(with `0 ≤ w_j < 1`), the spacings `a_j > 0`, and the single open estimate

    `physFloor : ∀ j,  c ≤ Q'.divPos (heatKernelMargin (w j)) (a j) _`,

i.e. `c ≤ (1 − w_j³)/a_j` for all `j`.  This is the abstract physical-gap-floor
inequality with the lattice floor SPECIALIZED to its closed heat-kernel form.
A uniform ceiling is carried so the reduction can supply the (non-open) upper
bound.

NO inhabitant for 4D Yang–Mills: `c > 0` with `c ≤ (1 − w_j³)/a_j` surviving
`a_j → 0` along `w_j = w(a_j)` is exactly the open content. -/

/-- **The explicit heat-kernel persistence obligation.**

Carries, indexed by refinement step `j` (spacing `a_j → 0`):

  * `w`, `w_nonneg`, `w_lt_one` — the heat-kernel weights `w_j` with
    `0 ≤ w_j < 1` (so the closed-form margin `1 − w_j³` is strictly positive);
  * `spacing`, `spacing_pos` — the lattice spacings `a_j > 0`;
  * `floorConst`, `floorConst_pos` — the uniform PHYSICAL gap floor `c > 0`;
  * `ceilConst` — a uniform physical ceiling `C` (the finiteness half);
  * `physFloor` — **the OPEN content, fully explicit:** `c ≤ (1 − w_j³)/a_j`
    for all `j` (`Q'.divPos (heatKernelMargin (w j)) (a j) _`);
  * `physCeil` — `(1 − w_j³)/a_j ≤ C` for all `j` (the uniform ceiling).

NO inhabitant for 4D Yang–Mills — `physFloor` with `floorConst > 0` is precisely
the explicit one-variable dimensional-transmutation inequality along the
asymptotic-freedom relation `w_j = w(a_j)`. -/
structure HeatKernelPersistence : Type where
  /-- The heat-kernel weights `w_j`, indexed by refinement step `j`. -/
  w : Nat → Q'
  /-- Each weight is nonnegative. -/
  w_nonneg : ∀ j : Nat, (0 : Q') ≤ w j
  /-- Each weight is strictly sub-unit (so the margin `1 − w_j³ > 0`). -/
  w_lt_one : ∀ j : Nat, w j < (1 : Q')
  /-- The lattice spacings `a_j`, indexed by refinement step `j`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j : Nat, (0 : Q') < spacing j
  /-- The uniform PHYSICAL gap floor `c`. -/
  floorConst : Q'
  /-- The floor is strictly positive — the dimensional-transmutation witness. -/
  floorConst_pos : (0 : Q') < floorConst
  /-- A uniform PHYSICAL gap ceiling `C` (the finiteness half). -/
  ceilConst : Q'
  /-- **The OPEN content, fully explicit:** the physical gap `(1 − w_j³)/a_j` is
  bounded below by the single positive constant `c`, uniformly in `j` — the
  closed-form heat-kernel dimensional-transmutation inequality. -/
  physFloor : ∀ j : Nat,
    floorConst ≤ Q'.divPos (heatKernelMargin (w j)) (spacing j) (spacing_pos j)
  /-- The physical gap is bounded above by `C`, uniformly in `j`. -/
  physCeil : ∀ j : Nat,
    Q'.divPos (heatKernelMargin (w j)) (spacing j) (spacing_pos j) ≤ ceilConst

/-! ## 3. The reduction map — `HeatKernelPersistence ⇒ RGGapPersistence`

This is the headline.  A `HeatKernelPersistence` term supplies precisely the
data a `RGGapPersistence` needs, with the per-spacing cluster bound taken to be
`heatKernelClusterBound (w j) …`.  By `heatKernelClusterBound_floorRate` the
abstract lattice floor `(atSpacing j).floorRate` reduces DEFINITIONALLY to the
closed form `heatKernelMargin (w j) = 1 − w_j³`, so the abstract physical
quotient `divPos ((atSpacing j).floorRate) (a j) _` IS the explicit
`divPos (1 − w_j³) (a j) _`.  Hence `physFloor` / `physCeil` transfer verbatim. -/

/-- **The reduction.**  From the explicit `HeatKernelPersistence` CONSTRUCT a
`RGGapPersistence` whose per-spacing cluster bounds are the closed-form
`heatKernelClusterBound (w j) …` (so each `(atSpacing j).floorRate = 1 − w_j³`
definitionally) and whose floor / ceiling estimates are carried verbatim.  After
this reduction the abstract continuum obligation's open quotient
`divPos ((atSpacing j).floorRate) (a j) _` IS the explicit
`divPos (1 − w_j³) (a j) _`. -/
def toRGGapPersistence (H : HeatKernelPersistence) : RGGapPersistence where
  spacing := H.spacing
  spacing_pos := H.spacing_pos
  atSpacing := fun j =>
    heatKernelClusterBound (H.w j) (H.w_nonneg j) (H.w_lt_one j)
  floorConst := H.floorConst
  floorConst_pos := H.floorConst_pos
  ceilConst := H.ceilConst
  -- `(atSpacing j).floorRate = heatKernelMargin (w j)` definitionally, so the
  -- abstract `physFloor` IS the explicit closed-form one.
  physFloor := H.physFloor
  physCeil := H.physCeil

/-- The reduced obligation's per-spacing lattice floor is the closed form
`1 − w_j³` — i.e. the abstract `RGGapPersistence` produced by the reduction has
`(atSpacing j).floorRate = heatKernelMargin (w j)`. -/
@[simp] theorem toRGGapPersistence_floorRate (H : HeatKernelPersistence) (j : Nat) :
    ((toRGGapPersistence H).atSpacing j).floorRate = heatKernelMargin (H.w j) :=
  rfl

/-- The reduced obligation's physical floor constant is `floorConst`. -/
@[simp] theorem toRGGapPersistence_floorConst (H : HeatKernelPersistence) :
    (toRGGapPersistence H).floorConst = H.floorConst := rfl

/-! ## 4. The headline composites — explicit closed-form ⇒ continuum gap

Composing the reduction with the abstract continuum reduction
`physGapMin_pos_of_persistence` makes "the continuum mass gap is positive" a
PROVED CONSEQUENCE of the EXPLICIT inequality `c ≤ (1 − w_j³)/a_j`. -/

/-- **The headline: explicit heat-kernel persistence ⇒ continuum gap positive.**
From the EXPLICIT inequality `HeatKernelPersistence` the continuum physical-gap
floor (the constructed band's `physGapMin`) is strictly positive.  Hence the
continuum mass-gap positivity is a PROVED CONSEQUENCE of the single explicit
closed-form one-variable inequality `c ≤ (1 − w_j³)/a_j`. -/
theorem physGapMin_pos_of_heatKernelPersistence (H : HeatKernelPersistence) :
    (0 : Q') < (toScalingBand (toRGGapPersistence H)).physGapMin :=
  physGapMin_pos_of_persistence (toRGGapPersistence H)

/-- **The continuum gap SURVIVES `a → 0`, from the explicit inequality.**  Every
physical gap of the constructed band, as a regular real, dominates the single
positive constant `ofQ' floorConst`, uniformly in `j` — built entirely from the
explicit heat-kernel inequality. -/
theorem continuum_gap_of_heatKernelPersistence (H : HeatKernelPersistence)
    (j : Nat) :
    ofQ' (toScalingBand (toRGGapPersistence H)).physGapMin
      ≤ ofQ' ((toScalingBand (toRGGapPersistence H)).physGap j) :=
  continuum_gap_of_RGGapPersistence (toRGGapPersistence H) j

/-- The reduction also delivers the uniform finiteness half from the explicit
data: every physical gap is bounded above by `ofQ' ceilConst`. -/
theorem continuum_gap_le_ceiling_of_heatKernelPersistence
    (H : HeatKernelPersistence) (j : Nat) :
    ofQ' ((toScalingBand (toRGGapPersistence H)).physGap j)
      ≤ ofQ' (toScalingBand (toRGGapPersistence H)).physGapMax :=
  continuum_gap_le_ceiling_of_RGGapPersistence (toRGGapPersistence H) j

/-! ## 5. The residual — the sole open inequality, stated precisely

After the reduction above, the abstract continuum-gap obligation
`RGGapPersistence` is, definitionally in its lattice floor, the EXPLICIT
closed-form heat-kernel inequality.  The sole remaining open content is the
existence of an inhabitant of `HeatKernelPersistence` for 4D Yang–Mills, i.e.
the single explicit one-variable inequality

    ∃ c > 0,  ∀ j,   (1 − w_j³) / a_j  ≥  c,

along the asymptotic-freedom trajectory `w_j = w(a_j) = e^{−t(a_j)/4}`, where
`w(a)` is the heat-kernel weight at spacing `a`.  Concretely, with
`s_j := w_j³ = heatKernelSep (w_j)` the spin-`1` excited transfer eigenvalue, the
inequality is `c ≤ (1 − s_j)/a_j`, a uniform lower bound on the per-spacing
eigenvalue-gap margin DIVIDED by the spacing.

`HeatKernelResidual` names this exact open content as a `Type`-level predicate on
a weight sequence `w` and a spacing sequence `a`.  NO inhabitant is provided —
the `w(a) ↔ a` relation (asymptotic freedom) is the open frontier.  Its precise
shape is: a positive `c` together with the uniform bound `c ≤ (1 − w_j³)/a_j`.

Physical interpretation (telescoping).  The physical gap `(1 − w_j³)/a_j` is the
discrete difference quotient of the lattice gap margin; a uniform lower bound on
it across the refinement tower is the dimensional-transmutation statement that
the physical mass `m = Δ(a)` stays bounded below as `a → 0`, which is exactly the
Clay-relevant survival of the mass gap. -/

/-- **The residual open inequality (named, NOT inhabited).**  Given a weight
sequence `w` and a spacing sequence `a` (with `0 ≤ w_j < 1`, `a_j > 0`), the sole
open content of the heat-kernel continuum bridge: a strictly-positive `c`
together with the explicit uniform lower bound `c ≤ (1 − w_j³)/a_j` for all `j`.
This is the concrete one-variable (in `w` vs `a`) dimensional-transmutation
inequality along asymptotic freedom; NO inhabitant is provided. -/
structure HeatKernelResidual
    (w a : Nat → Q')
    (hw0 : ∀ j : Nat, (0 : Q') ≤ w j)
    (hw1 : ∀ j : Nat, w j < (1 : Q'))
    (ha : ∀ j : Nat, (0 : Q') < a j) : Type where
  /-- The uniform physical-gap floor `c`. -/
  c : Q'
  /-- The floor is strictly positive. -/
  c_pos : (0 : Q') < c
  /-- **The open inequality:** `c ≤ (1 − w_j³)/a_j` for all `j`. -/
  bound : ∀ j : Nat, c ≤ Q'.divPos (heatKernelMargin (w j)) (a j) (ha j)

/-- **The residual is EXACTLY the open content of `HeatKernelPersistence`.**
An inhabitant of `HeatKernelResidual w a …` (the explicit inequality) supplies,
together with a uniform ceiling `C` with `(1 − w_j³)/a_j ≤ C`, a full
`HeatKernelPersistence` — hence (via §4) the continuum gap.  This confirms the
named residual is precisely the remaining open obligation, no more.  NO
inhabitant of `HeatKernelResidual` is provided. -/
def HeatKernelResidual.toPersistence
    {w a : Nat → Q'}
    {hw0 : ∀ j : Nat, (0 : Q') ≤ w j} {hw1 : ∀ j : Nat, w j < (1 : Q')}
    {ha : ∀ j : Nat, (0 : Q') < a j}
    (R : HeatKernelResidual w a hw0 hw1 ha)
    (ceil : Q')
    (hceil : ∀ j : Nat,
      Q'.divPos (heatKernelMargin (w j)) (a j) (ha j) ≤ ceil) :
    HeatKernelPersistence where
  w := w
  w_nonneg := hw0
  w_lt_one := hw1
  spacing := a
  spacing_pos := ha
  floorConst := R.c
  floorConst_pos := R.c_pos
  ceilConst := ceil
  physFloor := R.bound
  physCeil := hceil

end YMGap.Continuum.HeatKernelPersistence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelPersistence.heatKernelClusterBound
#print axioms YMGap.Continuum.HeatKernelPersistence.heatKernelClusterBound_floorRate
#print axioms YMGap.Continuum.HeatKernelPersistence.heatKernelClusterBound_located
#print axioms YMGap.Continuum.HeatKernelPersistence.toRGGapPersistence
#print axioms YMGap.Continuum.HeatKernelPersistence.toRGGapPersistence_floorRate
#print axioms YMGap.Continuum.HeatKernelPersistence.toRGGapPersistence_floorConst
#print axioms YMGap.Continuum.HeatKernelPersistence.physGapMin_pos_of_heatKernelPersistence
#print axioms YMGap.Continuum.HeatKernelPersistence.continuum_gap_of_heatKernelPersistence
#print axioms YMGap.Continuum.HeatKernelPersistence.continuum_gap_le_ceiling_of_heatKernelPersistence
#print axioms YMGap.Continuum.HeatKernelPersistence.HeatKernelResidual.toPersistence
