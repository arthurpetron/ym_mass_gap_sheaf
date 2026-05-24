/-
Domination gluing on the buffer overlap, and the named compatibility
predicate.

The buffer Ω_k^∩ is where the small-field and large-field bounds
must be reconciled.  Context.md §3.1 frames this as a *cocycle*
problem: the two bounds are not restrictions of a single function
to two subsets, they are two distinct upper bounds derived under
two different approximations, and "gluing" them on the overlap is
by domination (pointwise sup), not equality.

This file:

  * defines `domGlue` — the pointwise sup of two sections, which is
    the structural shape of the buffer-overlap glue;
  * proves `domGlue` dominates both input sections;
  * defines `CompatibilityRule` — the named predicate type binding
    sections of 𝒜_k to KP certificates of 𝒮_k, where the analytic
    content of the framework lives (per outline.md §8.5 and
    Definition 5.1 of `formal/sheaf-framework.tex`).

Concrete compatibility predicates for the three regimes appear in
Milestones 3.1–3.3.

Mirror: `formal/sheaf-framework.tex` Sections 5 and 6 (Definitions
5.1, 6.1, Proposition 6.2).
-/

import YMGap.Sheaf.Site
import YMGap.Sheaf.BoundWitness
import YMGap.Sheaf.Summability
import YMGap.Constructive.Rationals

namespace YMGap.Sheaf

open YMGap.Constructive

/-! ## Domination gluing -/

/-- The pointwise sup of two bound-witness sections: the structural
shape of the buffer-overlap glue.

In the math paper, with sections in `ℝ̄≥0`, this is
`s^∩(u) = max(s^sf(u), s^lf(u))`.  Here it is binary `sup` at the
abstract value-type level (typeclass `BoundValues T`). -/
def domGlue {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : Section Config T :=
  Section.sup sf lf

/-- The domination glue dominates the small-field input section. -/
theorem domGlue_dominates_sf {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : sf ≤ domGlue sf lf :=
  Section.le_sup_left sf lf

/-- The domination glue dominates the large-field input section. -/
theorem domGlue_dominates_lf {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : lf ≤ domGlue sf lf :=
  Section.le_sup_right sf lf

/-- Universal property: any section dominating both `sf` and `lf`
also dominates their domination glue. -/
theorem domGlue_le {Config T : Type} [BoundValues T]
    {sf lf u : Section Config T}
    (hsf : sf ≤ u) (hlf : lf ≤ u) : domGlue sf lf ≤ u :=
  Section.sup_le hsf hlf

/-- Σ-form witness: given a small-field section, exhibit a
buffer-overlap section dominating it. -/
def domGlue_witness {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) :
    Σ' g : Section Config T, sf ≤ g ∧ lf ≤ g :=
  ⟨domGlue sf lf, domGlue_dominates_sf sf lf, domGlue_dominates_lf sf lf⟩

/-! ## Compatibility — the named definition

The bound from 𝒜_k(U, X) and the KP datum from 𝒮_k(U, X) are bound
together by a regime-specific predicate.  Concrete predicates are
supplied per regime by Milestones 3.1–3.3.  Here we fix only the
TYPE of compatibility predicates: a binary relation between a
bound-witness section and a KP certificate.

This is the "compatibility condition between 𝒜_k and 𝒮_k" required
as a NAMED DEFINITION by Milestone 2.1 (work_plan.md L191–195) and
`formal/sheaf-framework.tex` Definition 5.1. -/

/-- The type of compatibility rules between bound-witness sections
and KP certificates.  A specific compatibility rule is a binary
predicate; the three regimes (small-field, large-field, overlap)
have their own concrete instances in Milestones 3.1–3.3. -/
def CompatibilityRule (Config T V : Type) [BoundValues T]
    (P : V → V → Prop) : Type :=
  Section Config T → KPCertificate V P → Prop

/-- Given a compatibility rule, the predicate "section `s` is
compatible with KP certificate `c`". -/
def Compatible {Config T V : Type} [BoundValues T] {P : V → V → Prop}
    (rule : CompatibilityRule Config T V P)
    (s : Section Config T) (c : KPCertificate V P) : Prop :=
  rule s c

/-! ## Summability preservation under domination gluing

The load-bearing claim of the buffer mechanism: given KP
certificates `(ρ_sf, K_sf)` and `(ρ_lf, K_lf)` for the small-field
and large-field families, the buffer-glued family admits a KP
certificate `(ρ_∩, K_∩)` with the explicit constants

    ρ_∩ = min(ρ_sf, ρ_lf),    K_∩ ≤ K_sf + K_lf.

This is the union-bound estimate from `max(a, b) ≤ a + b`.

Mirror: `formal/sheaf-framework.tex` Proposition 7.1
(`prop:summability-preservation`).

## [P2.1] part (a) closure — explicit-hypothesis form

The original `[P2.1]` part-(a) sorry was a placeholder for "the
predicate `P` holds at the buffer constants".  Constructively, this
is exactly a closure-under-glue hypothesis on `P`: given
``P ρ_a K_a`` and ``P ρ_b K_b``, derive ``P (min ρ_a ρ_b) (K_a + K_b)``.
The 3.3 polymer-KP form of this is Bałaban-style union-bound on the
polymer sum; here we expose it as an EXPLICIT HYPOTHESIS, making the
closure mechanical and the analytic content (the closure proof itself)
a first-class input to the gluing.

The closure also needs reflexivity of ``≤`` on ``V`` to discharge the
``K_cap ≤ K_sf + K_lf`` inequality when ``K_cap`` is chosen *equal*
to ``K_sf + K_lf``.  The abstract typeclasses ``[Min V] [Add V] [LE V]``
do not provide reflexivity, so we take it as a separate hypothesis.

Both hypotheses are discharged for ``V = Q'`` via ``Q'.le_refl'`` and a
chosen concrete ``P_glue``; concrete-instance specializations follow
the main theorem below. -/

/-- **Summability preservation under domination gluing** (closed form).

Given:
  * a predicate ``P : V → V → Prop`` with a closure-under-glue proof
    ``P_glue : P ρ_a K_a → P ρ_b K_b → P (min ρ_a ρ_b) (K_a + K_b)``,
  * reflexivity ``le_refl_V : ∀ x : V, x ≤ x`` of the value-type ``≤``,
  * two KP certificates ``c_sf c_lf : KPCertificate V P``,

exhibit a buffer certificate ``c_cap : KPCertificate V P`` with the
Proposition 7.1 constants:

    c_cap.rho = min c_sf.rho c_lf.rho,   c_cap.K ≤ c_sf.K + c_lf.K.

The construction is the identity union bound saturated:
``c_cap.K := c_sf.K + c_lf.K`` (so the ``≤`` becomes reflexivity).
``c_cap.satisfies`` is supplied by ``P_glue`` applied to the input
certificates' own ``satisfies`` fields.

This is `[P2.1]` part (a), **closed**.  Part (b) (Conjecture 7.4
tightness — that the additive ``K_∩ ≤ K_sf + K_lf`` is not lossy by
a fat band) is a separate empirical question against concrete polymer
activities and is not discharged here. -/
def domGlue_preserves_KP
    {V : Type} [Min V] [Add V] [LE V]
    {P : V → V → Prop}
    (P_glue : ∀ ρ_a K_a ρ_b K_b : V,
              P ρ_a K_a → P ρ_b K_b → P (min ρ_a ρ_b) (K_a + K_b))
    (le_refl_V : ∀ x : V, x ≤ x)
    (c_sf c_lf : KPCertificate V P) :
    Σ' c_cap : KPCertificate V P,
      c_cap.rho = min c_sf.rho c_lf.rho ∧ c_cap.K ≤ c_sf.K + c_lf.K :=
  ⟨{ rho := min c_sf.rho c_lf.rho,
     K := c_sf.K + c_lf.K,
     satisfies := P_glue c_sf.rho c_sf.K c_lf.rho c_lf.K c_sf.satisfies c_lf.satisfies },
    rfl,
    le_refl_V _⟩

/-! ## Concrete predicate instances at `V = Q'`

Two specializations of `domGlue_preserves_KP` at `V = Q'`, each
supplying a concrete predicate `P` and its closure-under-glue proof.
Both are fully closed (no `sorry`) and demonstrate the framework
working at the Q'-rational layer where the Python `computations/`
produce their values. -/

/-- The trivial predicate: every `(ρ, K)` satisfies `P_trivial`.

Useful as a smoke test that the gluing framework discharges
constructively against the simplest possible predicate. -/
@[inline] def P_trivial (_ _ : Q') : Prop := True

/-- `P_trivial` is closed under buffer-glue: trivially. -/
theorem P_glue_trivial :
    ∀ ρ_a K_a ρ_b K_b : Q',
      P_trivial ρ_a K_a → P_trivial ρ_b K_b →
      P_trivial (min ρ_a ρ_b) (K_a + K_b) :=
  fun _ _ _ _ _ _ => trivial

/-- `domGlue_preserves_KP` at `V = Q'`, `P = P_trivial`: fully closed
smoke test of the buffer-glue framework. -/
def domGlue_preserves_KP_trivial
    (c_sf c_lf : KPCertificate Q' P_trivial) :
    Σ' c_cap : KPCertificate Q' P_trivial,
      c_cap.rho = min c_sf.rho c_lf.rho ∧ c_cap.K ≤ c_sf.K + c_lf.K :=
  domGlue_preserves_KP P_glue_trivial Q'.le_refl' c_sf c_lf

/-- The nonnegativity predicate: `P_nonneg ρ K := 0 ≤ ρ ∧ 0 ≤ K`.

A substantive Bishop-constructive predicate: positivity (or zero) of
both KP constants is the minimal *useful* property for a KP certificate
to have (a negative `ρ` would make `e^{ρ|X|}` blow up; a negative `K`
would be a meaningless amplitude).  This is the simplest concrete
predicate where `P_glue` is non-trivial. -/
@[inline] def P_nonneg (ρ K : Q') : Prop := (0 : Q') ≤ ρ ∧ (0 : Q') ≤ K

/-- `P_nonneg` is closed under buffer-glue: ``min`` of nonnegatives is
nonnegative (`Q'.zero_le_min`), sum of nonnegatives is nonnegative
(`Q'.zero_le_add`). -/
theorem P_glue_nonneg :
    ∀ ρ_a K_a ρ_b K_b : Q',
      P_nonneg ρ_a K_a → P_nonneg ρ_b K_b →
      P_nonneg (min ρ_a ρ_b) (K_a + K_b) := by
  intro ρ_a K_a ρ_b K_b h_a h_b
  exact ⟨Q'.zero_le_min ρ_a ρ_b h_a.1 h_b.1,
         Q'.zero_le_add K_a K_b h_a.2 h_b.2⟩

/-- `domGlue_preserves_KP` at `V = Q'`, `P = P_nonneg`: fully closed
substantive instance.  Given two nonnegative KP certificates, produces
the buffer certificate with nonnegative `(ρ_∩, K_∩)` satisfying the
Proposition 7.1 constants relationship. -/
def domGlue_preserves_KP_nonneg
    (c_sf c_lf : KPCertificate Q' P_nonneg) :
    Σ' c_cap : KPCertificate Q' P_nonneg,
      c_cap.rho = min c_sf.rho c_lf.rho ∧ c_cap.K ≤ c_sf.K + c_lf.K :=
  domGlue_preserves_KP P_glue_nonneg Q'.le_refl' c_sf c_lf

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms domGlue_dominates_sf
#print axioms domGlue_dominates_lf
#print axioms domGlue_le
#print axioms domGlue_witness
#print axioms domGlue_preserves_KP
#print axioms P_glue_trivial
#print axioms domGlue_preserves_KP_trivial
#print axioms P_glue_nonneg
#print axioms domGlue_preserves_KP_nonneg

end YMGap.Sheaf
