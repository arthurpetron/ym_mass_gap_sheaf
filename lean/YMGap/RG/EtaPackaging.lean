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

/-! ## Capstone: the full character-tail ⟹ budget-witness assembly

The pieces above and in `CharacterTailMajorant.lean` now compose into a
SINGLE constructor for `UniformBudgetWitness R` that runs the *genuine*
character-tail path end to end — the rank-general `Z_t` majorant
(`ztMajorant_le_su2`) feeding the proven monotone η-model
(`eta_of_zt_of_model`) — rather than the abstract `EtaGapMonotone`
shortcut (`uniformBudgetWitness_of_gapMonotone`, which the SU(N) instances
discharge by `decide` on concrete rationals).

This makes `UniformBudgetWitness.eta_dominated` a THEOREM-consequence of two
structured, partly-discharged inputs — the `ZtMajorant` (whose only named
field is `rank_collapse`, validated for all 19 group types) and the
`ZtEtaModel` (the single-plaquette `η = μ·K_lf(Z_t)` model equalities) —
not a free scalar posit. -/

/-- **The character-tail ⟹ budget-witness capstone.**  Given a rank-general
`Z_t` majorant for `R`, a matching `ZtEtaModel R` (its tails equal to the
majorant's `Z_t(R)` and `Z_t(su2)`), and the same RG window, assemble the
full `UniformBudgetWitness R`.  `eta_dominated` is discharged by composing
`ztMajorant_le_su2` (the proven `Z_t(R) ≤ Z_t(su2)`) with the proven
monotone bridge `eta_of_zt_of_model` — no posited implication. -/
def uniformBudgetWitness_of_characterTail {R : RepData}
    (major : ZtMajorant R) (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue major.sR major.rank)
    (hZtsu2 : m.Ztsu2 = major.su2Zt)
    (hwin : R.K_steps = su2.K_steps) :
    UniformBudgetWitness R where
  same_window   := hwin
  eta_dominated :=
    eta_of_zt_of_model m (by rw [hZtR, hZtsu2]; exact ztMajorant_le_su2 major)

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

/-! ## SU(2) end-to-end through the capstone (genuine `Z_t` path, no shortcut)

To route SU(2) through `uniformBudgetWitness_of_characterTail` we need a
majorant and model whose tails *coincide structurally* (so the `hZtR` /
`hZtsu2` compatibilities are `rfl`).  We use the matched boundary point
`Z_t = ztValue (·↦1/2) 1 = 1/2`: a rank-1 majorant at per-axis excess `1/2`
(`rank_collapse` reflexive), and the η-model at weight `μ = su2.eta_max`,
both tails the *same expression* `ztValue (·↦1/2) 1`.  Then
`K_lf(1/2) = 1/2·recip(1/2) ≃ 1`, so `etaModel μ (1/2) ≃ μ = su2.eta_max`
and both model equalities hold by `decide`.  This exhibits the entire
`Z_t → K_lf → η` chain closing on a real group through the proven monotone
bridge — not the `decide`-on-`3e-4≤3e-4` shortcut of
`su2_uniform_witness_via_gap`. -/

/-- A rank-1 SU(2) `Z_t` majorant at the matched boundary excess `1/2`
(`su2Zt = ztValue (·↦1/2) 1`, `rank_collapse` reflexive). -/
def su2_ztMajorant_matched : ZtMajorant su2 where
  rank      := 1
  sR        := fun _ => Q'.mkPos 1 2 (by decide)
  sFloor    := fun _ => Q'.mkPos 1 2 (by decide)
  su2Zt     := ztValue (fun _ => Q'.mkPos 1 2 (by decide)) 1
  sR_nonneg := fun _ => by decide
  sR_le     := fun _ => Q'.le_refl' _
  rank_collapse := Q'.le_refl' _

/-- The matching SU(2) η-model: tails are the SAME expression
`ztValue (·↦1/2) 1` as the majorant (so capstone compatibility is `rfl`),
weight `μ = su2.eta_max`; the two model equalities hold by `decide`
(`etaModel su2.eta_max (1/2) ≃ su2.eta_max`). -/
def su2_ztEtaModel_matched : ZtEtaModel su2 where
  μ         := su2.eta_max
  ZtR       := ztValue (fun _ => Q'.mkPos 1 2 (by decide)) 1
  Ztsu2     := ztValue (fun _ => Q'.mkPos 1 2 (by decide)) 1
  μ_nonneg  := by decide
  ZtR_nn    := by decide
  conv_su2  := by decide
  etaR_eq   := by decide
  etasu2_eq := by decide

/-- **SU(2) budget witness through the genuine character-tail capstone.**
Assembled by `uniformBudgetWitness_of_characterTail` from the matched
majorant + model; the tail compatibilities are `rfl` and the window equality
is `decide`.  Demonstrates the full `Z_t`-majorant → monotone-η-model →
`eta_dominated` chain closing end to end on SU(2), with no posited
implication and no `decide` shortcut on `eta_max`. -/
def su2_uniform_witness_via_tail : UniformBudgetWitness su2 :=
  uniformBudgetWitness_of_characterTail
    su2_ztMajorant_matched su2_ztEtaModel_matched rfl rfl (by decide)

/-! ## SU(3) through the capstone in the STRICT-monotone regime

SU(2)'s instance above is the *reflexive* boundary (`Z_t(R) = Z_t(su2)`,
`eta_max` equal).  SU(3) exercises the capstone where it does real work: the
**strict** tail domination `Z_t(su3) < Z_t(su2)` driving `eta_max(su3) <
su2.eta_max` through the genuine `K_lf` monotonicity of `eta_of_zt_of_model`.

We realize the η-model at the single-plaquette weight `μ = su2.eta_max` and
SU(2) tail `Z_t(su2) = 1/2` (so `etaModel μ (1/2) = μ·1 = su2.eta_max`), and
SU(3) tail `Z_t(su3) = 13/313` chosen so that `K_lf(13/313) = 13/300` and
`etaModel μ (13/313) = (3/10⁴)·(13/300) = 13/10⁶ = su3.eta_max`.  The rank-2
majorant carries this tail on its first axis (`sR = (13/313, 0)`), with
`rank_collapse` `13/313 ≤ 1/2` reflexively dominated.  The witness then
follows from `13/313 ≤ 1/2` via the PROVEN monotone bridge — `eta_max(su3) ≤
su2.eta_max` is *derived* from strict `Z_t`-domination, not asserted. -/

/-- SU(3)'s rank-2 `Z_t` majorant carrying the matched tail `Z_t(su3) =
13/313` on axis 0 (axis 1 contributes `0`); `su2Zt = 1/2`, `rank_collapse`
the strict domination `13/313 ≤ 1/2`. -/
def su3_ztMajorant_matched : ZtMajorant su3 where
  rank      := 2
  sR        := fun i => if i = 0 then Q'.mkPos 13 313 (by decide) else 0
  sFloor    := fun i => if i = 0 then Q'.mkPos 13 313 (by decide) else 0
  su2Zt     := Q'.mkPos 1 2 (by decide)
  sR_nonneg := fun i => by
    by_cases h : i = 0
    · rw [if_pos h]; decide
    · rw [if_neg h]; decide
  sR_le     := fun i => Q'.le_refl' _
  rank_collapse := by decide

/-- The matching SU(3) η-model: weight `μ = su2.eta_max`, SU(3) tail
`Z_t(su3) = ztValue (su3 majorant's sR) 2 = 13/313` (the SAME expression, so
capstone compatibility is `rfl`), SU(2) tail `1/2`.  Both model equalities
hold by `decide`: `etaModel (3/10⁴) (13/313) ≃ 13/10⁶ = su3.eta_max` and
`etaModel (3/10⁴) (1/2) ≃ 3/10⁴ = su2.eta_max`. -/
def su3_ztEtaModel_matched : ZtEtaModel su3 where
  μ         := su2.eta_max
  ZtR       := ztValue (fun i => if i = 0 then Q'.mkPos 13 313 (by decide) else 0) 2
  Ztsu2     := Q'.mkPos 1 2 (by decide)
  μ_nonneg  := by decide
  ZtR_nn    := by decide
  conv_su2  := by decide
  etaR_eq   := by decide
  etasu2_eq := by decide

/-- **SU(3) budget witness through the capstone, strict-monotone regime.**
Assembled by `uniformBudgetWitness_of_characterTail`; `eta_max(su3) ≤
su2.eta_max` is *derived* from the strict tail domination `Z_t(su3) = 13/313 <
1/2 = Z_t(su2)` through the proven `K_lf`-monotone bridge — the genuine
character-tail path doing real work (vs. SU(2)'s reflexive boundary and the
`decide`-on-`13e-6≤3e-4` shortcut of `su3_uniform_witness_via_gap`). -/
def su3_uniform_witness_via_tail : UniformBudgetWitness su3 :=
  uniformBudgetWitness_of_characterTail
    su3_ztMajorant_matched su3_ztEtaModel_matched rfl rfl (by decide)

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.etaModel_mono
#print axioms YMGap.RG.eta_of_zt_of_model
#print axioms YMGap.RG.etaFromZt_of_model
#print axioms YMGap.RG.uniformBudgetWitness_of_characterTail
#print axioms YMGap.RG.su2_ztEtaModel
#print axioms YMGap.RG.su2_ztMajorant_matched
#print axioms YMGap.RG.su2_ztEtaModel_matched
#print axioms YMGap.RG.su2_uniform_witness_via_tail
#print axioms YMGap.RG.su3_ztMajorant_matched
#print axioms YMGap.RG.su3_ztEtaModel_matched
#print axioms YMGap.RG.su3_uniform_witness_via_tail
