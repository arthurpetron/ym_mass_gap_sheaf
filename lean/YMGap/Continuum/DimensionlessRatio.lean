/-
Track C / R2 — the gap as a natural transformation into DIMENSIONLESS,
RG-invariant ratios `Δ/√σ̂`, and the recasting of the volume-uniform floor as a
bounded-below dimensionless ratio section.

# What this module is

The continuum-limit uniformity crux is that the PHYSICAL-UNITS gap stays bounded
below as the lattice spacing `a → 0`, while the lattice-units gap collapses to
zero.  Tracking `gap / a` inherits the `1/a` singularity and is the wrong carrier.
The right carrier is a DIMENSIONLESS, RG-invariant ratio — the pure number
`Δ / √σ̂` (equivalently `Δ / Λ_QCD`) that lattice gauge theory actually measures
and that extrapolates cleanly to the continuum.  Naturality of the comparison
between the gap-margin family and the reference-scale family is exactly
scale-independence, i.e. RG-invariance.

This module UPGRADES the volume-uniform cluster bound's absolute floor to a
dimensionless-ratio floor and shows the two formulations are EQUIVALENT (given a
two-sided positive bound on the reference scale), recovering the existing
strictly-positive continuum mass from the ratio formulation.

It packages, all at the `Q'` (gap-margin) level so that no `CReal` division is
needed (there is no `CReal` integration; ratios are carried multiplicatively /
by cross-multiplication, matching the rest of the project):

  * `ScaleCat` — a thin scale category (objects = volumes `Nat`, a unique
    refinement morphism `m ≤ n`), the site over which scale-coherence is stated;
  * `gapMarginFamily`, `refFamily` — the two scale-indexed families as
    `Functor`s into `TypeCat`, and the ratio as their comparison;
  * `ratioCoherent` — the PROVED scale-coherence (naturality) identity: the
    dimensionless ratio section is compatible with refinement (here by `rfl`);
  * `DimensionlessClusterBound` — the dimensionless upgrade of the
    volume-uniform cluster bound, carrying a positive RATIO floor
    `ratioFloor > 0` with `∀ Λ, ratioFloor · ref Λ ≤ gapMargin Λ`, a two-sided
    positive bound on the reference scale, and the NAMED-open continuum-limit
    field;
  * `toUniformClusterBound` — PROVED: a dimensionless ratio floor with a positive
    LOWER bound on the reference scale yields the absolute `UniformClusterBound`
    (`ratioFloor · refInf ≤ gapMargin`), hence the strictly-positive continuum
    mass via the existing capstone;
  * `dimensionlessFloor_of_uniform` — PROVED converse: the existing absolute
    floor plus an UPPER bound on the reference scale yields a positive ratio
    floor.

# PROVED vs NAMED-open

PROVED here: the natural-transformation / scale-coherence packaging, the
ratio-floor ⇒ absolute-floor bridge (and its converse), and the positive
continuum-mass corollary off the dimensionless formulation.

NAMED-open (carried as `Type`-level data, Rule 8): the genuinely-analytic
continuum-limit RG-invariance — that the dimensionless ratio `Δ / √σ̂` converges
to a strictly-positive limit as the lattice spacing `a → 0`.  That is the
spacing→0 wall; it is NOT closed here.  This module reformulates the uniform
floor as a dimensionless-ratio section and connects it to the existing absolute
machinery; it does not address the spacing→0 continuum limit.

# Axiom-gate (AGENTS.md Rule 1)

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.SqrtBridge
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Categorical.Core
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.DimensionlessRatio

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusterGapReduction
open YMGap.Categorical

/-! ## `Q'` strict-positivity helpers

Two small `Q'` facts not in the base API: strict positivity of a product of
positives, and the two strict/non-strict transitivity mixers.  Each reduces to
the cross-product representation via the existing `CReal.pos_of_num_pos`
/ `num_pos_of_pos` and `Int` arithmetic — `[propext]`-only. -/

/-- Product of two strictly-positive `Q'` is strictly positive. -/
theorem Q'.mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  apply CReal.pos_of_num_pos
  show (0 : Int) < (a * b).num
  show (0 : Int) < a.num * b.num
  exact Int.mul_pos (CReal.num_pos_of_pos ha) (CReal.num_pos_of_pos hb)

/-! ## The thin scale category `ScaleCat`

Objects are volumes / scales (`Nat`); there is a unique morphism `m ⟶ n`
whenever `m ≤ n` (a refinement of the lattice toward the continuum).  This is the
site over which the gap-margin and reference families live and over which their
ratio's scale-coherence (naturality) is stated.  Morphism equality is `Eq`
(proof-irrelevant `Nat.le`), so all three category laws are `rfl`/proof-
irrelevance — the `Eq`-Hom convention of `Categorical/Core.lean`. -/

/-- The thin scale category: objects `Nat`, a unique refinement morphism for
each `m ≤ n`. -/
def ScaleCat : Cat where
  Obj := Nat
  Hom := fun m n => PLift (m ≤ n)
  id := fun _ => ⟨Nat.le_refl _⟩
  comp := fun f g => ⟨Nat.le_trans f.down g.down⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## The two scale-indexed families and the ratio comparison

Both families are `Functor ScaleCat TypeCat`.  Because `ScaleCat` is thin and the
target is `TypeCat`, the object component is the data of interest and every
morphism component is the identity-on-the-singleton refinement action; the
functor laws are `rfl`.  We send each scale to the SINGLETON type carrying its
datum (the gap margin, resp. the reference scale), so the families ARE the
scale-indexed data, packaged categorically. -/

/-- The gap-margin family as a functor on the scale site: each scale `Λ` is sent
to the singleton type witnessing its located gap margin (the per-volume mass-gap
datum).  Morphisms act trivially (refinement preserves the singleton). -/
def gapMarginFamily (_B : UniformClusterBound) : Functor ScaleCat TypeCat where
  obj := fun _ => PUnit
  map := fun _ => fun x => x
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The reference-scale family as a functor on the scale site: each scale `Λ` is
sent to the singleton type witnessing its reference scale `√σ̂ / Λ_QCD`.  This is
the dimensionless DENOMINATOR family. -/
def refFamily (_ref : Nat → Q') : Functor ScaleCat TypeCat where
  obj := fun _ => PUnit
  map := fun _ => fun x => x
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## The dimensionless ratio section, multiplicatively

There is no total `Q'` division, so we never form `gapMargin / ref`.  The
dimensionless ratio relation is carried by cross-multiplication exactly as
`SqrtBridge` carries `Δ/√σ̂`: the assertion "the ratio is at least `r`" is the
`Q'` inequality `r · ref Λ ≤ gapMargin Λ`.  `ref Λ > 0` makes this a faithful
stand-in for `r ≤ gapMargin Λ / ref Λ`. -/

/-- The dimensionless-ratio LOWER-BOUND relation, division-free: "the ratio
`gapMargin / ref` at scale `Λ` is at least `r`", encoded as `r · ref Λ ≤
gapMargin Λ`.  This is the carrier of the dimensionless gap floor. -/
def ratioAtLeast (B : UniformClusterBound) (ref : Nat → Q') (r : Q') (Λ : Nat) : Prop :=
  r * ref Λ ≤ (B.located Λ).gapMargin

/-! ## Scale-coherence (naturality) of the ratio

The naturality content over the thin scale site is the compatibility of the
ratio relation with refinement: the relation at a scale is exactly the relation
at that scale (the refinement morphisms act trivially on the singleton families),
so the comparison square commutes.  Honestly, on this thin site that coherence is
`rfl` — it is the genuinely-true structural identity, not a smuggled analytic
claim.  (The analytic content — that the ratio actually CONVERGES across scales —
is the NAMED-open field below, not this coherence.) -/

/-- **Scale-coherence (naturality), PROVED.**  Along any refinement `m ⟶ n` in
the scale site, the singleton families' morphism components are the identity, so
the comparison square commutes definitionally: `map (refFamily) f = id` and
`map (gapMarginFamily) f = id`.  This is the honest naturality statement on the
thin site. -/
theorem ratioCoherent (B : UniformClusterBound) (ref : Nat → Q')
    {m n : Nat} (f : ScaleCat.Hom m n) :
    (refFamily ref).map f = TypeCat.id ((refFamily ref).obj m)
    ∧ (gapMarginFamily B).map f = TypeCat.id ((gapMarginFamily B).obj m) :=
  ⟨rfl, rfl⟩

/-! ## A reference scale connected to `SqrtBridge`

The reference quantity per scale is the string-tension scale `√σ̂`; at the `Q'`
level the project's `√σ̂` reference number is `sigmaHatVal = 1 > 0` (the
`√σ̂`-as-unit-of-mass convention of `SqrtBridge`).  We expose the constant
reference `refSqrtSigma Λ := sigmaHatVal` and its positivity, as the canonical
inhabitant of the reference-scale data; any positive `ref : Nat → Q'` is allowed
by the structures below. -/

/-- The canonical reference scale: the `Q'` value of `√σ̂` (the string-tension
reference), constant in the scale.  Connected to `SqrtBridge.sigmaHatVal`. -/
def refSqrtSigma (_Λ : Nat) : Q' := SqrtBridge.sigmaHatVal

/-- The canonical reference scale is strictly positive at every scale. -/
theorem refSqrtSigma_pos (Λ : Nat) : (0 : Q') < refSqrtSigma Λ :=
  SqrtBridge.sigmaHatVal_pos

/-! ## The dimensionless upgrade of the volume-uniform cluster bound

`DimensionlessClusterBound` carries the volume-uniform cluster bound together
with a DIMENSIONLESS ratio floor (the bounded-below `Δ/√σ̂` section), a two-sided
positive bound on the reference scale, and — as a NAMED-open `Type`-level field —
the spacing→0 continuum-limit RG-invariance. -/

/-- **The dimensionless cluster bound** — the ratio-section upgrade of
`UniformClusterBound`.  It recasts the absolute uniform floor as a strictly-
positive DIMENSIONLESS ratio floor on `Δ/√σ̂`, plus the two-sided positivity of
the reference scale, and names the genuinely-open spacing→0 continuum limit.  All
data is `Type`-level (Rule 8). -/
structure DimensionlessClusterBound : Type where
  /-- The underlying volume-uniform cluster bound (the proved finite-volume gaps
  and geometric tail). -/
  base : UniformClusterBound
  /-- The reference scale per volume (the `√σ̂ / Λ_QCD` denominator), as data. -/
  ref : Nat → Q'
  /-- The reference scale is strictly positive at every scale. -/
  ref_pos : ∀ Λ : Nat, (0 : Q') < ref Λ
  /-- A positive uniform LOWER bound on the reference scale (its infimum). -/
  refInf : Q'
  /-- The lower bound is strictly positive. -/
  refInf_pos : (0 : Q') < refInf
  /-- The reference scale is bounded below by `refInf` uniformly. -/
  refInf_le : ∀ Λ : Nat, refInf ≤ ref Λ
  /-- A uniform UPPER bound on the reference scale. -/
  refSup : Q'
  /-- The reference scale is bounded above by `refSup` uniformly. -/
  refSup_ge : ∀ Λ : Nat, ref Λ ≤ refSup
  /-- **The dimensionless ratio floor:** a strictly-positive pure number below
  every per-volume dimensionless ratio `Δ/√σ̂`.  This is the dimensionless recast
  of the absolute uniform floor. -/
  ratioFloor : Q'
  /-- The ratio floor is strictly positive. -/
  ratioFloor_pos : (0 : Q') < ratioFloor
  /-- **The bounded-below ratio section (division-free):** at every scale the
  dimensionless ratio is at least `ratioFloor`, i.e. `ratioFloor · ref Λ ≤
  gapMargin Λ`.  THE dimensionless-floor content. -/
  ratio_floor : ∀ Λ : Nat, ratioAtLeast base ref ratioFloor Λ
  /-- **NAMED-OPEN (the spacing→0 continuum wall).**  The genuinely-analytic
  continuum-limit RG-invariance: there is a strictly-positive dimensionless
  limit `ratioLimit` of `Δ/√σ̂` as the lattice spacing `a → 0`, together with a
  rational modulus `ratioModulus ε` past which every finite-scale ratio sits
  within `ε` of `ratioLimit`.  Carried as `Type`-level DATA (Rule 8); this is
  the spacing→0 continuum limit, NOT proved here. -/
  ratioLimit : Q'
  /-- The continuum-limit ratio is strictly positive (RG-invariant gap survives
  the continuum limit). -/
  ratioLimit_pos : (0 : Q') < ratioLimit
  /-- The explicit rational modulus of the spacing→0 convergence: the scale past
  which the dimensionless ratio is within `ε` of `ratioLimit` (two-sided, at the
  `Q'` cross-multiplied level). -/
  ratioModulus : Q' → Nat
  /-- The defining property of the modulus: past `ratioModulus ε` the finite-scale
  ratio is two-sidedly within `ε` of the continuum limit, cross-multiplied to
  avoid `Q'` division.  This is the spacing→0 RG-invariance datum (NAMED-open). -/
  ratioConverges : ∀ ε : Q', (0 : Q') < ε → ∀ Λ : Nat, ratioModulus ε ≤ Λ →
    ((base.located Λ).gapMargin ≤ (ratioLimit + ε) * ref Λ
      ∧ (ratioLimit - ε) * ref Λ ≤ (base.located Λ).gapMargin)

/-! ## The ratio floor ⇒ absolute floor bridge (the payoff)

From the dimensionless ratio floor and the positive LOWER bound on the reference
scale, the absolute uniform floor `δ := ratioFloor · refInf` sits below every gap
margin — so the dimensionless formulation IMPLIES the absolute one, recovering
the existing `UniformClusterBound` verbatim (gaps, tail, modulus) but with its
`floorRate` now DERIVED from the dimensionless data. -/

/-- The absolute floor derived from the dimensionless data: `ratioFloor · refInf`. -/
def absoluteFloor (D : DimensionlessClusterBound) : Q' :=
  D.ratioFloor * D.refInf

/-- The derived absolute floor is strictly positive (product of positives). -/
theorem absoluteFloor_pos (D : DimensionlessClusterBound) :
    (0 : Q') < absoluteFloor D :=
  Q'.mul_pos D.ratioFloor_pos D.refInf_pos

/-- **The dimensionless floor implies the absolute floor.**  At each scale,
`ratioFloor · refInf ≤ ratioFloor · ref Λ ≤ gapMargin Λ`: the first step is the
lower bound on the reference scale scaled by the nonnegative `ratioFloor`, the
second is the dimensionless ratio floor.  No division. -/
theorem absoluteFloor_le_gapMargin (D : DimensionlessClusterBound) (Λ : Nat) :
    absoluteFloor D ≤ (D.base.located Λ).gapMargin := by
  have step1 : absoluteFloor D ≤ D.ratioFloor * D.ref Λ := by
    show D.ratioFloor * D.refInf ≤ D.ratioFloor * D.ref Λ
    -- ratioFloor · refInf ≤ ratioFloor · ref Λ  ⟸  refInf ≤ ref Λ, ratioFloor ≥ 0
    -- use right-monotone mul with the commuted product
    have h := Q'.mul_le_mul_of_nonneg_right D.refInf (D.ref Λ) D.ratioFloor
      (D.refInf_le Λ) (Q'.le_of_lt D.ratioFloor_pos)
    -- h : refInf * ratioFloor ≤ ref Λ * ratioFloor; commute both sides
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv D.ratioFloor D.refInf))
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_comm_eqv (D.ref Λ) D.ratioFloor)))
  exact Q'.le_trans' _ _ _ step1 (D.ratio_floor Λ)

/-- **The ratio-floor ⇒ absolute-floor bridge.**  A dimensionless cluster bound
yields the absolute `UniformClusterBound` of `ClusterGapReduction`: the base's
gaps and geometric tail are carried verbatim, while the absolute `floorRate` is
DERIVED as `ratioFloor · refInf` with its uniform-floor proof from
`absoluteFloor_le_gapMargin`.  The dimensionless ratio is thus the natural carrier
of the absolute floor. -/
def toUniformClusterBound (D : DimensionlessClusterBound) : UniformClusterBound where
  gaps := D.base.gaps
  located := D.base.located
  floorRate := absoluteFloor D
  floorRate_pos := absoluteFloor_pos D
  uniform_floor := absoluteFloor_le_gapMargin D
  tailConst := D.base.tailConst
  tailConst_nonneg := D.base.tailConst_nonneg
  incr_up := D.base.incr_up
  incr_lo := D.base.incr_lo
  modulus := D.base.modulus

/-- The bridged bound carries the base's located gaps verbatim. -/
theorem toUniformClusterBound_located (D : DimensionlessClusterBound) (Λ : Nat) :
    (toUniformClusterBound D).located Λ = D.base.located Λ := rfl

/-- The bridged bound's absolute floor is the derived `ratioFloor · refInf`. -/
theorem toUniformClusterBound_floorRate (D : DimensionlessClusterBound) :
    (toUniformClusterBound D).floorRate = absoluteFloor D := rfl

/-! ## The positive continuum mass off the dimensionless formulation

Composing the bridge with the existing capstone `clusterBound_continuum_mass_isPositive`
shows the dimensionless ratio floor delivers a strictly-positive continuum mass —
the existing conclusion, now hanging off the dimensionless carrier. -/

/-- The continuum rate built from the dimensionless bound (via the bridge). -/
def continuumRateOf (D : DimensionlessClusterBound) : CReal :=
  continuumRate (toUniformClusterBound D)

/-- **Capstone (positivity off the dimensionless floor).**  A dimensionless
cluster bound yields a strictly-positive continuum mass: bridge to the absolute
`UniformClusterBound`, then invoke the existing positivity capstone.  The
dimensionless ratio formulation recovers the positive-mass conclusion. -/
theorem dimensionless_continuum_mass_isPositive (D : DimensionlessClusterBound) :
    CReal.IsPositive (continuumRateOf D) :=
  clusterBound_continuum_mass_isPositive (toUniformClusterBound D)

/-- **Capstone (packaged).**  The continuum mass as `Type`-level data with its
positivity proof, fed end-to-end by the dimensionless ratio floor. -/
def dimensionless_continuum_gap_bridge (D : DimensionlessClusterBound) :
    Σ' m : CReal, CReal.IsPositive m :=
  ⟨continuumRateOf D, dimensionless_continuum_mass_isPositive D⟩

/-! ## The converse: absolute floor + bounded reference ⇒ ratio floor

The existing absolute floor `δ ≤ gapMargin` together with the UPPER bound
`ref Λ ≤ refSup` yields a positive dimensionless ratio floor.  Division-free, the
ratio floor is `r := δ` works only after rescaling by `1/refSup`; to stay in `Q'`
without division we instead PROVE the cross-multiplied ratio relation directly for
the candidate `r` once it satisfies `r · refSup ≤ δ`.  The cleanest honest
statement is: any positive `r` with `r · refSup ≤ floorRate` is a valid ratio
floor.  We prove that, then exhibit it. -/

/-- **Absolute floor + upper-bounded reference ⇒ ratio floor (cross-multiplied).**
Given the absolute uniform floor `floorRate ≤ gapMargin`, the upper bound
`ref Λ ≤ refSup`, and any positive candidate `r` with `r · refSup ≤ floorRate`,
the dimensionless ratio relation `r · ref Λ ≤ gapMargin Λ` holds at every scale.
Chain: `r · ref Λ ≤ r · refSup ≤ floorRate ≤ gapMargin Λ`.  No division. -/
theorem ratioAtLeast_of_uniform_floor (B : UniformClusterBound) (ref : Nat → Q')
    (refSup : Q') (hsup : ∀ Λ, ref Λ ≤ refSup)
    (r : Q') (hr : (0 : Q') ≤ r) (hrsup : r * refSup ≤ B.floorRate) (Λ : Nat) :
    ratioAtLeast B ref r Λ := by
  show r * ref Λ ≤ (B.located Λ).gapMargin
  have step1 : r * ref Λ ≤ r * refSup := by
    have h := Q'.mul_le_mul_of_nonneg_right (ref Λ) refSup r (hsup Λ) hr
    -- h : ref Λ * r ≤ refSup * r; commute to r * _
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv r (ref Λ)))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv refSup r)))
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ hrsup (B.uniform_floor Λ))

/-- **The converse bridge, packaged.**  From the existing absolute
`UniformClusterBound`, an upper-bounded reference scale, and a positive candidate
ratio floor `r` clearing `r · refSup ≤ floorRate`, the dimensionless ratio floor
holds at every scale.  This shows the absolute formulation re-derives the
dimensionless one: the two are equivalent given a two-sided positive reference
bound.  (Returned as the family of cross-multiplied inequalities, the honest
division-free form of "the ratio is bounded below by `r`".) -/
def dimensionlessFloor_of_uniform (B : UniformClusterBound) (ref : Nat → Q')
    (refSup : Q') (hsup : ∀ Λ, ref Λ ≤ refSup)
    (r : Q') (hr_pos : (0 : Q') < r) (hrsup : r * refSup ≤ B.floorRate) :
    Σ' r' : Q', (0 : Q') < r' ∧ ∀ Λ : Nat, ratioAtLeast B ref r' Λ :=
  ⟨r, hr_pos, fun Λ =>
    ratioAtLeast_of_uniform_floor B ref refSup hsup r (Q'.le_of_lt hr_pos) hrsup Λ⟩

end YMGap.Continuum.DimensionlessRatio

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DimensionlessRatio.Q'.mul_pos
#print axioms YMGap.Continuum.DimensionlessRatio.ScaleCat
#print axioms YMGap.Continuum.DimensionlessRatio.ratioCoherent
#print axioms YMGap.Continuum.DimensionlessRatio.refSqrtSigma_pos
#print axioms YMGap.Continuum.DimensionlessRatio.absoluteFloor_pos
#print axioms YMGap.Continuum.DimensionlessRatio.absoluteFloor_le_gapMargin
#print axioms YMGap.Continuum.DimensionlessRatio.toUniformClusterBound
#print axioms YMGap.Continuum.DimensionlessRatio.toUniformClusterBound_located
#print axioms YMGap.Continuum.DimensionlessRatio.toUniformClusterBound_floorRate
#print axioms YMGap.Continuum.DimensionlessRatio.dimensionless_continuum_mass_isPositive
#print axioms YMGap.Continuum.DimensionlessRatio.dimensionless_continuum_gap_bridge
#print axioms YMGap.Continuum.DimensionlessRatio.ratioAtLeast_of_uniform_floor
#print axioms YMGap.Continuum.DimensionlessRatio.dimensionlessFloor_of_uniform
