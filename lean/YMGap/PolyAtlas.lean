/-
NON-LOAD-BEARING expository closure (excluded from the YMGap.lean aggregator); builds on demand.

The polymer atlas P_k as a concrete Q'-rational structure.

Milestone 2.2-closure of `work_plan.md` (authorized 2026-05-26):
**closes the polymer-atlas open question** flagged in
`formal/inductive-state.tex` §5.

# Background

`InductiveState.lean` carries the polymer atlas as a polymorphic
type parameter `PolyAtlas : Type`, with the deferred-representation
note that downstream concrete uses would commit to a specific
representation.  This module provides that commitment:
`CanonicalPolyAtlas` is a concrete `structure` at Q' realizing
the four design choices of `computations/inductive_state.py::PolyAtlas`:

  1. **Smallness parameter** δ_k = g_k (α = 1 convention; outline §6.4
     permits α ∈ (0, 1); α = 1 keeps δ_k Q'-rational at every pilot).
  2. **Plaquette enumeration cutoff** `n_max : Nat` (default 16).
  3. **Shape classifier**: partition of unity into three classes
     (filament, intermediate, ball) by aspect ratio.  Realized as
     an inductive type `ShapeClass`.
  4. **Gribov-region classifier**: three-region atlas (sf, buffer, lf)
     by maximum-plaquette geodesic distance to identity, with
     thresholds δ_k/2 and 2·δ_k.

The Lean structure mirrors the Python `PolyAtlas` dataclass.

# What this closes vs. what stays open

  * **Closes**: the manuscript's "open question" about the
    representation of `𝒫_k`.  `CanonicalPolyAtlas` is a concrete,
    well-typed structure with explicit Q' fields and decidable
    classifiers.  `formal/inductive-state.tex` §5 is reformulated
    from "open question" to "concrete commitment".
  * **Stays open** (NOT load-bearing): the actual *enumeration* of
    polymers — the Lean polymer-counting infrastructure of
    [Brydges–Federbush 1978] is not formalized; we record the cutoff
    `n_max` as data and rely on the Python pilot's polymer-sum
    bounds via the KP certificates (T8.1–T8.3).  This is the same
    boundary as the rest of the project: structural commitments are
    Lean-formal; numerical bounds are Python-computed with Q'
    surrogates.

# Cross-references

  * `computations/inductive_state.py::PolyAtlas` — Python mirror.
  * `lean/YMGap/RG/InductiveState.lean` — the abstract
    `PolyAtlas : Type` parameter (unchanged; this module provides
    one concrete instance, not a breaking change).
  * `formal/inductive-state.tex` §5 — the manuscript open question
    (now closed).
  * `docs/outline.md` Part B §21 Chapter 3 — updated to remove the
    "open 𝒫_k" annotation.

# Axiom-gate (AGENTS.md Rule 1)

All load-bearing theorems report `[propext]` only or empty.  The
`ShapeClass` and `GribovRegion` inductive types have decidable
equality.  The classifier functions are total and computable.
-/

import YMGap.Constructive.Rationals

namespace YMGap.PolyAtlas

open YMGap.Constructive

/-! ## Shape classes — partition of unity over admissible polymers -/

/-- Shape class of an admissible polymer: a partition of unity into
three classes determined by aspect ratio.

  * `filament` — aspect ratio ≥ 0.8 (extended polymer).
  * `intermediate` — between extremes.
  * `ball` — aspect ratio ≤ 0.2 (compact polymer).

Every admissible polymer is in exactly one class. -/
inductive ShapeClass : Type where
  | filament
  | intermediate
  | ball
  deriving DecidableEq

/-! ## Gribov regions — three-region atlas matching the sheaf cover -/

/-- Gribov-region tag for a polymer: determined by its maximum-plaquette
geodesic distance to identity.  Matches the three-element cover
`{Ω_k^sf, Ω_k^lf, Ω_k^∩}` of `formal/sheaf-framework.tex` Definition 2.2. -/
inductive GribovRegion : Type where
  | sf      -- clearly small-field: max_p d < δ_k / 2
  | buffer  -- buffer / overlap:    δ_k / 2 ≤ max_p d ≤ 2 · δ_k
  | lf      -- clearly large-field: max_p d > 2 · δ_k
  deriving DecidableEq

/-! ## The α exponent and plaquette cutoff -/

/-- The α exponent in `δ_k = g_k^α`.  Project commits to α = 1
(see module docstring); kept as a documentation marker. -/
def alpha_value : Nat := 1

/-- Default plaquette enumeration cutoff: 16. -/
def n_max_default : Nat := 16

/-! ## The concrete polymer atlas structure -/

/-- **The canonical polymer atlas at scale k** (closes Milestone 2.2's
open question).

Fields:
  * `g_k : Q'` — running gauge coupling.
  * `delta_k : Q'` — smallness parameter (under α = 1, equal to g_k).
  * `n_max : Nat` — plaquette enumeration cutoff.
  * `g_k_pos`, `delta_k_pos` — positivity hypotheses.
  * `alpha_one_consistent` — coherence: `delta_k = g_k` (the α = 1 convention).

The two classifiers (`shape_class`, `gribov_region`) are defined as
functions outside the structure since they take additional inputs
(aspect ratio / max distance). -/
structure CanonicalPolyAtlas where
  g_k : Q'
  delta_k : Q'
  n_max : Nat := n_max_default
  g_k_pos : (0 : Q') < g_k
  delta_k_pos : (0 : Q') < delta_k
  /-- α = 1 coherence: δ_k = g_k. -/
  alpha_one_consistent : delta_k = g_k

/-! ### Shape classifier thresholds (Q'-rational, partition of unity)

The shape class is determined by aspect ratio thresholds at 0.2 and
0.8.  We use Q'-rational thresholds for decidability. -/

/-- Lower threshold for "filament" classification: aspect ratio ≥ 4/5. -/
def filament_threshold : Q' := Q'.mkPos 4 5 (by decide)

/-- Upper threshold for "ball" classification: aspect ratio ≤ 1/5. -/
def ball_threshold : Q' := Q'.mkPos 1 5 (by decide)

namespace CanonicalPolyAtlas

/-- Construct the canonical polymer atlas at coupling `g` (with
`α = 1`, so `δ_k = g`).  Requires a proof that `g > 0`. -/
def at_scale (g : Q') (h_g_pos : (0 : Q') < g) :
    CanonicalPolyAtlas :=
  { g_k := g,
    delta_k := g,
    n_max := n_max_default,
    g_k_pos := h_g_pos,
    delta_k_pos := h_g_pos,
    alpha_one_consistent := rfl }

/-- Classify a polymer by aspect ratio (Q'-decidable). -/
def shape_class (_atlas : CanonicalPolyAtlas) (aspect_ratio : Q') : ShapeClass :=
  if filament_threshold ≤ aspect_ratio then
    ShapeClass.filament
  else if aspect_ratio ≤ ball_threshold then
    ShapeClass.ball
  else
    ShapeClass.intermediate

/-! ### Gribov-region classifier (three-region atlas) -/

/-- Classify a polymer by Gribov region using its maximum-plaquette
geodesic distance.  Decidable since Q' has decidable order. -/
def gribov_region (atlas : CanonicalPolyAtlas) (max_distance : Q') : GribovRegion :=
  -- Compute δ_k / 2 as a Q' rational via the half function from Reals.lean.
  -- We use a direct comparison: max_distance < δ_k / 2 iff 2 · max_distance < δ_k.
  if (2 : Q') * max_distance < atlas.delta_k then
    GribovRegion.sf
  else if (2 : Q') * atlas.delta_k < max_distance then
    GribovRegion.lf
  else
    GribovRegion.buffer

end CanonicalPolyAtlas

/-! ## Concrete pilot instances

Two concrete `CanonicalPolyAtlas` values at the SU(2) pilot operating
points, matching `Sheaf.SU2KP.g_canonical_squared` and `g_wilson_squared`
(via square roots: `g_canonical = 3/10`, `g_wilson = 1/2`). -/

/-- The canonical polymer atlas at SU(2) canonical pilot
(`g_0 = 3/10`). -/
def canonical_su2_pilot : CanonicalPolyAtlas :=
  CanonicalPolyAtlas.at_scale (Q'.mkPos 3 10 (by decide)) (by decide)

/-- The canonical polymer atlas at SU(2) Wilson pilot (`g_0 = 1/2`). -/
def canonical_su2_wilson_pilot : CanonicalPolyAtlas :=
  CanonicalPolyAtlas.at_scale (Q'.mkPos 1 2 (by decide)) (by decide)

/-! ## Sanity-check theorems -/

/-- The α = 1 convention is reflected in the canonical pilot: `δ_k = g_k`. -/
theorem canonical_pilot_alpha_one :
    canonical_su2_pilot.delta_k = canonical_su2_pilot.g_k := rfl

/-- Wilson pilot also has δ_k = g_k. -/
theorem wilson_pilot_alpha_one :
    canonical_su2_wilson_pilot.delta_k = canonical_su2_wilson_pilot.g_k := rfl

/-- Default `n_max` is 16. -/
theorem canonical_pilot_n_max_16 : canonical_su2_pilot.n_max = 16 := rfl

/-- The shape classifier returns `filament` at aspect ratio 1 (= the
fully-extended-polymer extreme). -/
theorem shape_class_one_is_filament :
    canonical_su2_pilot.shape_class (1 : Q') = ShapeClass.filament := by
  show (if filament_threshold ≤ (1 : Q') then ShapeClass.filament
        else if (1 : Q') ≤ ball_threshold then ShapeClass.ball
        else ShapeClass.intermediate) = ShapeClass.filament
  -- 4/5 ≤ 1: cross-product 4 · 1 ≤ 1 · 5, i.e. 4 ≤ 5. ✓
  rw [if_pos (by decide : filament_threshold ≤ (1 : Q'))]

/-- The shape classifier returns `ball` at aspect ratio 0 (= the
fully-compact-polymer extreme). -/
theorem shape_class_zero_is_ball :
    canonical_su2_pilot.shape_class (0 : Q') = ShapeClass.ball := by
  show (if filament_threshold ≤ (0 : Q') then ShapeClass.filament
        else if (0 : Q') ≤ ball_threshold then ShapeClass.ball
        else ShapeClass.intermediate) = ShapeClass.ball
  -- 4/5 ≤ 0 fails; then 0 ≤ 1/5 succeeds.
  rw [if_neg (by decide : ¬ (filament_threshold ≤ (0 : Q')))]
  rw [if_pos (by decide : (0 : Q') ≤ ball_threshold)]

/-- The Gribov classifier returns `sf` at distance 0 (= identity plaquette). -/
theorem gribov_region_zero_is_sf :
    canonical_su2_pilot.gribov_region (0 : Q') = GribovRegion.sf := by
  show (if (2 : Q') * (0 : Q') < canonical_su2_pilot.delta_k then GribovRegion.sf
        else if (2 : Q') * canonical_su2_pilot.delta_k < (0 : Q') then GribovRegion.lf
        else GribovRegion.buffer) = GribovRegion.sf
  -- canonical_su2_pilot.delta_k = 3/10 > 0 = 2 · 0.
  rw [if_pos]
  decide

/-! ## Sentinel: the polymer atlas is concretely committed

A single packaged statement exposing the closure of Milestone 2.2's
polymer-atlas open question: the canonical pilot atlas is a
concrete `CanonicalPolyAtlas` with the four design choices realized. -/

/-- **Polymer atlas concrete commitment (Milestone 2.2 closure).**

Packages:
  1. α = 1 convention (δ_k = g_k) at the canonical pilot.
  2. n_max = 16 plaquette enumeration cutoff.
  3. Shape classifier (filament / intermediate / ball) at aspect-ratio
     extremes.
  4. Gribov-region classifier (sf / buffer / lf) at distance zero.

This is the Lean realization of `formal/inductive-state.tex` §5
**closed** (was "open question"). -/
theorem poly_atlas_concrete_commitment :
    (canonical_su2_pilot.delta_k = canonical_su2_pilot.g_k) ∧
    (canonical_su2_pilot.n_max = 16) ∧
    (canonical_su2_pilot.shape_class (1 : Q') = ShapeClass.filament) ∧
    (canonical_su2_pilot.shape_class (0 : Q') = ShapeClass.ball) ∧
    (canonical_su2_pilot.gribov_region (0 : Q') = GribovRegion.sf) :=
  ⟨canonical_pilot_alpha_one,
   canonical_pilot_n_max_16,
   shape_class_one_is_filament,
   shape_class_zero_is_ball,
   gribov_region_zero_is_sf⟩

end YMGap.PolyAtlas

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.PolyAtlas.CanonicalPolyAtlas.at_scale
#print axioms YMGap.PolyAtlas.canonical_pilot_alpha_one
#print axioms YMGap.PolyAtlas.wilson_pilot_alpha_one
#print axioms YMGap.PolyAtlas.canonical_pilot_n_max_16
#print axioms YMGap.PolyAtlas.shape_class_one_is_filament
#print axioms YMGap.PolyAtlas.shape_class_zero_is_ball
#print axioms YMGap.PolyAtlas.gribov_region_zero_is_sf
#print axioms YMGap.PolyAtlas.poly_atlas_concrete_commitment
