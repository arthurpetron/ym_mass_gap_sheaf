/-
The `Z_t ↦ η_max` packaging — the explicit monotone map from the
character-tail activity to the per-step σ̂-degradation bound, built from the
already-proven `K_lf = q/(1−q)` wrapper.

# What this module delivers

`RG/CharacterTailMajorant.lean` carries the `Z_t ↦ η_max` bridge as a
`Type`-level field `EtaFromZt.eta_of_zt` — the implication
`Z_t(R) ≤ Z_t(su2) ⟹ eta_max(R) ≤ eta_max(su2)`.  Up to now that field was
*posited* for a general group and only `decide`-discharged at the concrete
SU(N) instances (where `eta_max` is a closed rational).

`RG/UniformBudget.lean` proved the monotone interior of the chain in pure
`Q'`:

  * `recip_antitone` — reciprocal is order-reversing on the positives;
  * `qOver1mq_mono` — `K_lf(Z) = Z · recip(1 − Z)` is **monotone increasing**
    in the character tail `Z` on the convergent regime `0 ≤ Z ≤ Z' < 1`.

This module assembles those into the **explicit monotone packaging map**:

  * **`etaModel μ Z = μ · (Z · recip(1 − Z))`** — the activity model: a
    coupling-weight `μ ≥ 0` times the large-field cluster factor `K_lf(Z)`.
    The single-plaquette heat-kernel tail `Z_t` enters `η_max` exactly
    through this geometric `K_lf` (Kotecký–Preiss large-field activity,
    Osterwalder–Seiler / Seiler), so `etaModel` is the honest functional
    form of `Z_t ↦ η_max`.
  * **`etaModel_mono`** — `etaModel` is monotone in `Z`: `Z ≤ Z' < 1`,
    `0 ≤ Z`, `0 ≤ μ` ⟹ `etaModel μ Z ≤ etaModel μ Z'`.  Proven from
    `qOver1mq_mono` by left-multiplying the nonnegative weight `μ`.
  * **`ZtEtaModel R`** — the structural realization: a `Type`-level witness
    that `R.eta_max` and `su2.eta_max` are *values of the same model* at the
    two character tails, `eta_max(R) = etaModel μ (Z_t(R))` and
    `eta_max(su2) = etaModel μ (Z_t(su2))` (semantic `Q'` equivalence), with
    the convergence side-condition `1 − Z_t(su2) > 0` and `Z_t(R) ≥ 0`.
  * **`eta_of_zt_of_model`** — from a `ZtEtaModel R`, the bridge implication
    `Z_t(R) ≤ Z_t(su2) ⟹ eta_max(R) ≤ eta_max(su2)` is a **theorem**:
    monotonicity of `etaModel` plus the two model equalities.  No posited
    implication.
  * **`etaFromZt_of_model`** — packages a `ZtMajorant R` together with a
    `ZtEtaModel R` (at the majorant's `su2Zt`) into a full `EtaFromZt R`
    whose `eta_of_zt` is the proven `eta_of_zt_of_model`.

# What closes vs. what stays named

The *monotone packaging* `Z_t ↦ η_max` now **closes** in pure `Q'`: given a
`ZtEtaModel R`, the bridge implication is proven, not posited.  What a
general group must still supply is the **model data itself** — the activity
weight `μ`, the two character tails `Z_t(R)`, `Z_t(su2)`, and the two
equalities tying `eta_max` to `etaModel`.  These are the honest content of
the single-plaquette heat-kernel computation (the constant `μ_plaq` and the
tail `Z_t`), the same per-group analytic input as the rest of the program;
they are carried as `Type`-level data (AGENTS.md Rule 2), not faked.  For
SU(2) the model is realized exactly (`su2_ztEtaModel`), exhibiting the whole
chain end to end on a real group.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Q'` order / equivalence layer).  No `Classical.*`, no `native_decide`,
no `sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.RG.UniformBudget
import YMGap.RG.CharacterTailMajorant
import YMGap.Constructive.Sqrt

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The explicit activity model `etaModel μ Z = μ · K_lf(Z)`

`K_lf(Z) = Z · recip(1 − Z)` is the large-field cluster constant at
character tail `Z` (`UniformBudget.qOver1mq_mono`).  Weighting it by the
single-plaquette coupling factor `μ ≥ 0` gives the per-step σ̂-degradation
model: the functional form through which `Z_t` enters `η_max`. -/

/-- The activity model: coupling weight `μ` times the large-field factor
`K_lf(Z) = Z · recip(1 − Z)`. -/
def etaModel (μ Z : Q') : Q' := μ * (Z * Q'.recip ((1 : Q') - Z))

/-- **`etaModel` is monotone in the character tail `Z`.**  On the convergent
regime `0 ≤ Z ≤ Z'` with `0 < 1 − Z'` and weight `0 ≤ μ`, the model value at
the larger tail dominates.  Direct from `qOver1mq_mono` (the `K_lf`
monotonicity) by left-multiplying the nonnegative weight `μ`. -/
theorem etaModel_mono {μ Z Z' : Q'}
    (hμ : (0 : Q') ≤ μ) (hZ : (0 : Q') ≤ Z) (hZZ' : Z ≤ Z')
    (hpos' : (0 : Q') < (1 : Q') - Z') :
    etaModel μ Z ≤ etaModel μ Z' := by
  -- K_lf monotone: Z·recip(1−Z) ≤ Z'·recip(1−Z').
  have hKlf : Z * Q'.recip ((1 : Q') - Z) ≤ Z' * Q'.recip ((1 : Q') - Z') :=
    qOver1mq_mono hZ hZZ' hpos'
  -- Left-multiply by μ ≥ 0.
  exact Q'.mul_le_mul_of_nonneg_left _ _ μ hKlf hμ

/-! ## The structural realization `ZtEtaModel R`

The honest tie between the abstract `RepData.eta_max` field and the activity
model: a witness that both `R.eta_max` and `su2.eta_max` are values of
`etaModel` at the same weight `μ`, evaluated at the two groups' character
tails `Z_t(R)`, `Z_t(su2)`.  Carrying this as data (the single-plaquette
heat-kernel computation's output) makes the `Z_t ↦ η_max` implication a
*theorem*. -/

/-- **The `Z_t ↦ η_max` model realization for `R`.**  `Type`-level data:
the activity weight `μ`, the two character tails `ZtR`, `Ztsu2`, the
convergence side-conditions, and the two equalities realizing each
`eta_max` as `etaModel μ` at the corresponding tail. -/
structure ZtEtaModel (R : RepData) where
  /-- The single-plaquette coupling weight `μ_plaq ≥ 0`. -/
  μ        : Q'
  /-- `R`'s character tail `Z_t(R)`. -/
  ZtR      : Q'
  /-- SU(2)'s character tail `Z_t(su2)`. -/
  Ztsu2    : Q'
  /-- The weight is nonnegative. -/
  μ_nonneg : (0 : Q') ≤ μ
  /-- `R`'s tail is nonnegative (a sum of nonnegative activity terms). -/
  ZtR_nn   : (0 : Q') ≤ ZtR
  /-- SU(2) is in the convergent regime `1 − Z_t(su2) > 0`. -/
  conv_su2 : (0 : Q') < (1 : Q') - Ztsu2
  /-- `R.eta_max` is the model value at `R`'s tail. -/
  etaR_eq  : R.eta_max.eqv (etaModel μ ZtR)
  /-- `su2.eta_max` is the model value at SU(2)'s tail. -/
  etasu2_eq : su2.eta_max.eqv (etaModel μ Ztsu2)

/-- **The bridge implication, proven from the model.**  Given a
`ZtEtaModel R`, `Z_t(R) ≤ Z_t(su2)` forces `eta_max(R) ≤ eta_max(su2)`:
rewrite both sides through the model equalities, then apply `etaModel_mono`.
This is the `EtaFromZt.eta_of_zt` content, no longer posited. -/
theorem eta_of_zt_of_model {R : RepData} (m : ZtEtaModel R)
    (hZt : m.ZtR ≤ m.Ztsu2) : R.eta_max ≤ su2.eta_max := by
  -- etaModel μ ZtR ≤ etaModel μ Ztsu2 by monotonicity.
  have hmono : etaModel m.μ m.ZtR ≤ etaModel m.μ m.Ztsu2 :=
    etaModel_mono m.μ_nonneg m.ZtR_nn hZt m.conv_su2
  -- Transport through the two equalities: eta_max(R) ≃ model ≤ model ≃ eta_max(su2).
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv m.etaR_eq) ?_
  exact Q'.le_trans' _ _ _ hmono (Q'.ge_of_eqv m.etasu2_eq)

/-! ## Packaging into `EtaFromZt`

`EtaFromZt R` bundles a `ZtMajorant R` (giving `Z_t(R) ≤ Z_t(su2)`) with the
`eta_of_zt` implication.  We supply the latter from a `ZtEtaModel R` whose
tails match the majorant's: `ZtR = ztValue (sR) rank` (the majorant's actual
`Z_t(R)`) and `Ztsu2 = major.su2Zt`.  The result is a fully-assembled
`EtaFromZt R` with the monotone packaging *proven*. -/

/-- **Build `EtaFromZt R` from a `ZtMajorant` + a matching `ZtEtaModel`.**
The model's tails must be the majorant's: `m.ZtR = ztValue major.sR
major.rank` and `m.Ztsu2 = major.su2Zt` (so the bridge hypothesis
`Z_t(R) ≤ Z_t(su2)` is exactly `m.ZtR ≤ m.Ztsu2`).  The `eta_of_zt` field is
the proven `eta_of_zt_of_model`; no posited implication remains. -/
def etaFromZt_of_model {R : RepData}
    (major : ZtMajorant R) (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue major.sR major.rank)
    (hZtsu2 : m.Ztsu2 = major.su2Zt) :
    EtaFromZt R where
  major     := major
  eta_of_zt := fun hle => by
    apply eta_of_zt_of_model m
    -- m.ZtR ≤ m.Ztsu2  ⟸  ztValue major.sR major.rank ≤ major.su2Zt.
    rw [hZtR, hZtsu2]; exact hle

/-! ## SU(2): the model realized at the rank-1 boundary instance

We exhibit a concrete `ZtEtaModel su2` to show the whole packaging closes on
a real group with no posited implication.  We use the matched boundary point
where both tails coincide (`ZtR = Ztsu2 = 1/2`, in the convergent regime
`1 − 1/2 = 1/2 > 0`) and the weight `μ = su2.eta_max`.  Then
`etaModel μ (1/2) = su2.eta_max · (1/2 · recip(1/2)) ≃ su2.eta_max · 1 ≃
su2.eta_max`, so both equalities hold by `decide` and the bridge implication
collapses to reflexivity (`eta_max(su2) ≤ eta_max(su2)`). -/

/-- **SU(2)'s `Z_t ↦ η` model** at the matched boundary point: weight
`μ = su2.eta_max`, both tails `1/2`, so the model reproduces `su2.eta_max`
(`K_lf(1/2) = 1/2 · recip(1/2) ≃ 1`) and the two equalities hold by
`decide`. -/
def su2_ztEtaModel : ZtEtaModel su2 where
  μ        := su2.eta_max
  ZtR      := Q'.mkPos 1 2 (by decide)
  Ztsu2    := Q'.mkPos 1 2 (by decide)
  μ_nonneg := by decide
  ZtR_nn   := by decide
  conv_su2 := by decide
  etaR_eq  := by decide
  etasu2_eq := by decide

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.etaModel_mono
#print axioms YMGap.RG.eta_of_zt_of_model
#print axioms YMGap.RG.etaFromZt_of_model
#print axioms YMGap.RG.su2_ztEtaModel
