/-
The **Wilson-loop AREA LAW** (confinement / static-potential side) — stated
GENERALLY over abstract loop shapes, with the rectangular loop DEMOTED to a
derived measurement lemma.

# What this module is, and — emphatically — what it is NOT

This file formalizes the CONFINEMENT observable: the Wilson-loop AREA LAW
`|⟨W(C)⟩| ≤ e^{−σ·Area(C)} · perimeterCorrection`, the statement that large
loops are suppressed by their ENCLOSED AREA at a spacing-uniform positive
string tension `σ`.  This is the static-quark-potential / flux-tube content.

It is a **DIFFERENT theorem** from the mass gap.  The three objects

  * the MASS GAP            — exponential decay of the two-point / connected
    correlator, a spectral statement about `H = −log T` (handled ELSEWHERE,
    via correlation decay / clustering);
  * the AREA LAW            — `⟨W(C)⟩ ≤ e^{−σ·Area}`, the confinement /
    string-tension statement formalized HERE;
  * the FLUX-TUBE picture   — the geometric visualization of the confining
    string,

are RELATED but NOT the same theorem.  Conflating them is a category error.
To structurally PREVENT conflation this module:

  1. states the area law over an ABSTRACT Wilson field `W : Scale → LoopShape
     → CReal` (an arbitrary gauge-invariant loop observable), so nothing here
     is tied to the transfer-matrix spectrum / gap;
  2. provides NO bridge `areaLaw ⟹ massGap` or `massGap ⟹ areaLaw` — the two
     are carried as INDEPENDENT premises (`areaLaw_massGap_independence`);
  3. demotes the rectangular `m×n` loop from "the theorem" to a DERIVED
     measurement lemma (`rectangularWilsonAreaLaw_of_general`): it is merely a
     convenient way to MEASURE `σ`, a special case of the general law.

# The open confinement input vs. the fixed-spacing building block

  * `ScaleCovariantWilsonAreaLaw` — the GENERAL, SCALE-COVARIANT area law
    (a positive string tension `σ`, the bound uniform in the spacing `a`).
    This is the OPEN continuum confinement input: it is a `Type`-level
    premise and is left UNINHABITED here (no constructor is provided).  Its
    negative-exponential envelope `E : CReal → CReal` (the constructive
    `e^{−·}`) is itself part of the open input — the repo's `ExpNeg.expNeg`
    realizes `e^{−·}` for RATIONAL exponents (all of `[0,∞)`), and
    `Constructive.CRealExp.expNegC` realizes it for CReal exponents on the
    `[0,1]` window; a full-range CReal exponential is an open construction.

  * `StrongCouplingPlaquetteActivity` — the GENUINE fixed-spacing
    building block that DOES exist in the repo: at strong coupling
    `0 ≤ w ≤ 1/2` the single-plaquette excited-rep activity is bounded by
    `4w³` uniformly in the truncation (`PlaquetteActivity.plaqActivity_le`).
    `strongCoupling_areaLaw` re-exports it.  This is the per-plaquette weight
    from which an area law is BUILT (`⟨W(C)⟩ ~ activity^(#plaquettes)`); the
    cluster-expansion ASSEMBLY into a loop bound, and the scale-covariant
    `σ > 0` uniform-in-`a` law, are the remaining open steps.

# Axiom-gate (AGENTS.md Rule 1)

`[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.ExpNeg
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.WilsonAreaLaw

open YMGap.Constructive
open YMGap.Continuum

/-! ## 0. Basic objects: the lattice scale, loop shapes, and the Wilson field -/

/-- The lattice SPACING (scale) `a`, a rational.  Scale-covariance = the area
law holding uniformly over these. -/
abbrev Scale := Q'

/-- A **general planar loop shape** `C`: it carries its enclosed `area` and a
`perimeterCorrection` prefactor (both `CReal`).  This is deliberately NOT a
rectangle — the area law is a statement about the enclosed area of an ARBITRARY
loop; the rectangle is one special case (`rectShape`). -/
structure LoopShape where
  /-- The enclosed area `Area(C)` (physical units). -/
  area : CReal
  /-- The enclosed area is nonnegative. -/
  area_nonneg : CReal.ofQ' 0 ≤ area
  /-- The perimeter-correction prefactor multiplying the area-decay envelope. -/
  perimeterCorrection : CReal

/-- The **Wilson observable field**: `W a C = ⟨W(C)⟩` at spacing `a` for the
loop shape `C`.  Kept fully ABSTRACT — an arbitrary gauge-invariant loop
functional — so that NOTHING in this module ties the area law to the
transfer-matrix spectrum / mass gap. -/
def WilsonField : Type := Scale → LoopShape → CReal

/-- A **negative-exponential envelope** `E`, the constructive `e^{−·}` on
`CReal`.  (Realized by `ExpNeg.expNeg` for rational exponents on all of
`[0,∞)`, and by `CRealExp.expNegC` for CReal exponents on `[0,1]`; a
full-range CReal exponential is part of the open continuum input.) -/
def NegExpEnvelope : Type := CReal → CReal

/-! ## 1. The GENERAL scale-covariant area law (the open confinement input)

`ScaleCovariantWilsonAreaLaw W` says: there is a spacing-uniform positive
string tension `σ` and a negative-exponential envelope `E` such that for EVERY
spacing `a` and EVERY loop shape `C`,

    |⟨W(C)⟩|  ≤  E(σ · Area(C)) · perimeterCorrection(C).

The bound is UNIFORM in `a` (scale-covariant): the SAME `σ` and `E` control the
loop expectations at every spacing.  This structure is the OPEN confinement
physics — it is left UNINHABITED (no constructor supplied); inhabiting it is the
continuum confinement problem, DISTINCT from the mass gap. -/
structure ScaleCovariantWilsonAreaLaw (W : WilsonField) : Type where
  /-- The spacing-uniform string tension. -/
  σ : CReal
  /-- The string tension is strictly positive (genuine confinement). -/
  σ_pos : CReal.IsPositive σ
  /-- The negative-exponential area-decay envelope `E ≈ e^{−·}`. -/
  E : NegExpEnvelope
  /-- The area-law bound, uniform in the spacing `a` and the loop shape `C`. -/
  bound : ∀ (a : Scale) (C : LoopShape),
    CReal.abs (W a C)
      ≤ CReal.mul (E (CReal.mul σ C.area)) C.perimeterCorrection

/-! ## 2. The rectangular loop shape and the DERIVED measurement lemma

The `m × n` rectangle, at spacing `a`, encloses area `m·n·a²` (and we take a
unit perimeter correction, so the derived bound reads exactly
`⟨W(m,n)⟩ ≤ e^{−σ·mn·a²}`).  It is ONE loop shape among many. -/

/-- Local `ofNat` nonnegativity (`0 ≤ Q'.ofNat k`). -/
theorem qofNat_nonneg (k : Nat) : (0 : Q') ≤ Q'.ofNat k := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.ofNat k).num
  have : (Q'.ofNat k).num = (k : Int) := rfl
  rw [this]; exact Int.natCast_nonneg k

/-- The rectangular area `m·n·a²` as a `Q'`. -/
def rectAreaQ (m n : Nat) (a : Scale) : Q' := Q'.ofNat (m * n) * (a * a)

/-- `0 ≤ m·n·a²` for `0 ≤ a`. -/
theorem rectAreaQ_nonneg (m n : Nat) (a : Scale) (ha : (0 : Q') ≤ a) :
    (0 : Q') ≤ rectAreaQ m n a :=
  Q'.mul_nonneg _ _ (qofNat_nonneg (m * n)) (Q'.mul_nonneg _ _ ha ha)

/-- The **rectangular `m×n` loop shape** at spacing `a`: enclosed area `m·n·a²`,
unit perimeter correction.  A special case of `LoopShape`. -/
def rectShape (m n : Nat) (a : Scale) (ha : (0 : Q') ≤ a) : LoopShape where
  area := CReal.ofQ' (rectAreaQ m n a)
  area_nonneg := CReal.ofQ'_le_ofQ' (rectAreaQ_nonneg m n a ha)
  perimeterCorrection := CReal.ofQ' 1

/-- **The rectangular Wilson-loop area law, DERIVED from the general law.**

Given ANY inhabitant `law : ScaleCovariantWilsonAreaLaw W` of the general
scale-covariant area law, the rectangular `m×n` bound

    |⟨W(m,n)⟩|  ≤  E(σ · m·n·a²) · 1        (= e^{−σ·mn·a²})

is an immediate SPECIAL CASE: instantiate `law.bound` at the rectangular loop
shape.  This is the DEMOTION of the rectangle from "the theorem" to a way to
MEASURE the string tension `σ` — no independent content beyond the general
area law. -/
theorem rectangularWilsonAreaLaw_of_general
    {W : WilsonField} (law : ScaleCovariantWilsonAreaLaw W)
    (m n : Nat) (a : Scale) (ha : (0 : Q') ≤ a) :
    CReal.abs (W a (rectShape m n a ha))
      ≤ CReal.mul (law.E (CReal.mul law.σ (CReal.ofQ' (rectAreaQ m n a))))
          (CReal.ofQ' 1) :=
  law.bound a (rectShape m n a ha)

/-! ### The concrete area-decay value (envelope realizability on the rectangle)

The envelope `E` is abstract in the open general law, but on the rectangle it
is genuinely REALIZABLE at rational string tension and spacing: `e^{−σ·mn·a²}`
is a bona fide `CReal` via the full-range rational-exponent `ExpNeg.expNeg`
(defined on ALL of `[0,∞)`, so no small-area restriction).  This exhibits a
concrete witness for the RHS shape, independent of the open full-range CReal
exponential. -/

/-- `e^{−σ·mn·a²}` as a genuine `CReal`, for rational string tension `σ ≥ 0`
and spacing `a ≥ 0`. -/
def rectDecay (σ a : Q') (hσ : (0 : Q') ≤ σ) (ha : (0 : Q') ≤ a) (m n : Nat) :
    CReal :=
  ExpNeg.expNeg (σ * rectAreaQ m n a)
    (Q'.mul_nonneg _ _ hσ (rectAreaQ_nonneg m n a ha))

/-! ## 3. The fixed-spacing strong-coupling building block (genuine, re-exported)

At strong coupling `0 ≤ w ≤ 1/2` the single-plaquette excited-rep activity is
bounded, uniformly in the truncation, by `4w³` (`PlaquetteActivity.plaqActivity_le`).
This is the per-plaquette weight from which a loop area law is assembled
(`⟨W(C)⟩ ~ activity^(#plaquettes)`).  It is re-exported here as the fixed-spacing
CONFINEMENT building block.

Honest scope: this is NOT itself the assembled loop area law — turning the
per-plaquette activity into `⟨W(C)⟩ ≤ decay^Area` is the cluster-expansion step,
and the SCALE-COVARIANT `σ > 0` uniform-in-`a` law
(`ScaleCovariantWilsonAreaLaw`) is a further, distinct open input. -/

/-- **Fixed-spacing strong-coupling per-plaquette activity certificate.**  At
strong coupling `0 ≤ w ≤ 1/2` the single-plaquette excited activity is `≤ 4w³`
uniformly in the truncation `M`. -/
structure StrongCouplingPlaquetteActivity : Type where
  /-- The plaquette activity parameter `w` (small at strong coupling). -/
  w : Q'
  /-- `0 ≤ w`. -/
  w_nonneg : (0 : Q') ≤ w
  /-- Strong coupling: `w ≤ 1/2`. -/
  w_strong : w ≤ Q'.mkPos 1 2 (by decide)
  /-- The genuine per-plaquette activity bound `plaqActivity w M ≤ 4w³`. -/
  activity_bound : ∀ M : Nat,
    PlaquetteActivity.plaqActivity w M
      ≤ Q'.ofNat 4 * HeatKernelGap.heatKernelSep w

/-- **Re-export of the genuine fixed-spacing building block.**  For any strong
coupling `0 ≤ w ≤ 1/2`, the proved plaquette-activity bound inhabits
`StrongCouplingPlaquetteActivity`.  (The scale-covariant continuum area law
`ScaleCovariantWilsonAreaLaw` remains the open input, uninhabited.) -/
def strongCoupling_areaLaw {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) : StrongCouplingPlaquetteActivity where
  w := w
  w_nonneg := hw0
  w_strong := hw
  activity_bound := fun M => PlaquetteActivity.plaqActivity_le hw0 hw M

/-! ## 4. Structural SEPARATION from the mass gap (the deliverable)

The whole point of this module is the SEPARATION: `mass gap ≠ area law ≠
flux-tube`.  We encode it structurally.  The confinement premise
(`ScaleCovariantWilsonAreaLaw W`) and any mass-gap premise (`MassGap`, an
ABSTRACT `Type`) are carried as two INDEPENDENT inputs of a product; there is
NO field of one defined in terms of the other, and this module exposes NO
function `ScaleCovariantWilsonAreaLaw W → MassGap` or its converse. -/

/-- The confinement premise and a mass-gap premise, bundled as INDEPENDENT
inputs.  `MassGap` is an abstract external `Type` — this module knows nothing
about it, which is precisely why no `areaLaw ⟹ gap` bridge can exist here. -/
structure AreaLawAndMassGap (W : WilsonField) (MassGap : Type) : Type where
  /-- The confinement (area-law) premise. -/
  confinement : ScaleCovariantWilsonAreaLaw W
  /-- The mass-gap premise (supplied INDEPENDENTLY). -/
  massGap : MassGap

/-- **Independence / separation.**  From a bundle you can recover EACH premise,
but ONLY because both were supplied: `massGap` is a projection, never a
derivation from `confinement` (and vice versa).  Since `MassGap` is an
arbitrary abstract `Type`, no map `ScaleCovariantWilsonAreaLaw W → MassGap` is
— or could be — provided by this module.  This records the three-way
distinction `gap / area law / flux tube` as the deliverable: confinement and
the mass gap are DISTINCT premises with no implication either way here. -/
def areaLaw_massGap_independence
    {W : WilsonField} {MassGap : Type}
    (both : AreaLawAndMassGap W MassGap) :
    ScaleCovariantWilsonAreaLaw W × MassGap :=
  ⟨both.confinement, both.massGap⟩

end YMGap.Continuum.WilsonAreaLaw

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonAreaLaw.rectangularWilsonAreaLaw_of_general
#print axioms YMGap.Continuum.WilsonAreaLaw.rectDecay
#print axioms YMGap.Continuum.WilsonAreaLaw.strongCoupling_areaLaw
#print axioms YMGap.Continuum.WilsonAreaLaw.areaLaw_massGap_independence
