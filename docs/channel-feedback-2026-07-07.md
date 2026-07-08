# CHANNEL FEEDBACK — the true-margin recursion, re-based and pinned

> **STATUS — IMPLEMENTED + INDEPENDENTLY VERIFIED.** `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean`
> is in the tree and wired into `YMGap.lean`. Coordinator re-verification (not trusting
> the sub-agent): full `lake build` = **763 jobs green**, frontier guard **OK at 5**
> (no Clay-frontier type inhabited), the six load-bearing decls
> (`looseMagnitude_satisfiable`, `defectRecursion_of_looseBound`, `fullFloor_of_looseBound`,
> `looseRecursion_on_surrogate`, `looseRecursion_of_surrogateDomination`,
> `perScale_not_recursion_reexport`) all `#print axioms` ⊆ `{propext, Quot.sound}`, and the
> loop-counter **C = 18 unchanged** (no `:= SingleStepDefectBound` alias — a structural
> move, not a re-derivation). `SingleStepDefectBoundLoose` is a NEW loose scaffold and is
> **uninhabited** (its `recursion` field stays open), which is why the guard correctly does
> not move. NOTE: this file landed on the agent's *second* pass — an earlier coordinator
> snapshot saw the build still at 762 with the file not yet written; the state recorded here
> is the re-verified final tree. The load-bearing takeaway is the VERDICT in §"HONEST VERDICT":
> the true-margin recursion is the irreducible interacting effective action, pinned to
> `SurrogateDomination` (the located-2nd-eigenvalue Rayleigh domination) / the backreaction
> block `B_k = ⟨s=1 | coarse-grained action | s≥2⟩`; next front = Osterwalder–Seiler reflection
> positivity + min-max, NOT a per-scale estimate (that route is now provably a loop). The 4D
> YM mass gap remains OPEN — the `SurrogateDomination` field is not inhabited.

Target: the now-isolated binding core of the 4D SU(N) YM continuum mass gap — the
**true-margin RECURSION** `(1 − realδ_k)·tm_k ≤ tm_{k+1}`, the step-to-step degradation
of the physical margin under the real interacting block-spin.

Date: 2026-07-07. Lean-core (`Q'`/`CReal`), axiom gate `propext`/`Quot.sound`, guard 5.
DESIGN ONLY — see status banner above.

---

## 0. The state we inherited (yesterday, `RealDefectConstruction.lean`)

Three machine-checked facts fixed the frontier:

1. `realDefectRen w Cdef := dfreeExpr w + Cdef` — the **concrete** interacting per-scale
   defect: transverse free part `δ_free(w) = 2(1−w)²(2+w) = bondMovingDeltaRen 1 1 w`
   PLUS the connected `m`-fold fusion remainder `Cdef ≥ 0`. Genuinely from the interacting
   measure, not the model.

2. `honest_realDefect_exceeds_tight` — since `Cdef ≥ 0`, the honest `realδ = δ_free + Cdef`
   **overshoots** the TIGHT model `afDefectSeq = δ_free` (concrete witness at `w = 9/10`).
   So the existing `SingleStepDefectBound`, wired to compare `realδ ≤ afDefectSeq`, is
   **unsatisfiable for the genuine defect**.

3. `perScale_not_recursion` — even the FULL per-scale bound `∀k realδ_k ≤ 6(1−w_k)²` does
   **not** yield the recursion `(1 − realδ_k)·tm_k ≤ tm_{k+1}` (witness: saturating `realδ`,
   `tm = (1,0,0,…)`). The recursion carries strictly more content than any per-scale defect
   magnitude bound — it depends on the free margin `tm`.

These pin two problems: (A) the tight wiring is unsatisfiable; (B) the recursion is a
genuinely separate object. Both are addressed below.

---

## MOVE 1 — the re-basing (achieved, machine-checked)

**File:** `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean`.

### The tight→loose re-base

The tight model `afDefectSeq = δ_free = 2(1−w)²(2+w)` is exactly saturated by `δ_free`, so
`realδ = δ_free + Cdef` cannot fit under it. The LOOSE model

  `modelExpr(w) = 6(1−w)²  =  δ_free(w) + slackExpr(w)`,   `slackExpr(w) = 2(1−w)³`

(the exact decomposition `dfree_add_slack_eqv_model`) carries a **cubic slack** `2(1−w)³`
precisely to absorb the connected remainder `Cdef`. Re-basing the per-step comparison onto
`modelExpr` makes the magnitude piece SATISFIABLE while keeping the product floor summable.

`SingleStepDefectBoundLoose` (new `Type`, UNINHABITED) carries:
* `afr`, `realδ`, `trueMargin`, `trueMargin_nonneg`, `trueMargin0_pos`;
* `magnitude : ∀k, realδ_k ≤ modelExpr(w_{c+k})`  — the loose per-scale bound (SATISFIABLE);
* `recursion : ∀k, (1 − realδ_k)·tm_k ≤ tm_{k+1}`  — **THE SOLE OPEN RESIDUAL.**

### Magnitude is now satisfiable (the decisive contrast)

`looseMagnitude_satisfiable (afr) : Σ' realδ, ∀k, realδ_k ≤ modelExpr(w_{c+k})` is
**inhabited** by the concrete interacting `m = 1` construction
`realδ_k := realDefectRen (w_{c+k}) (cdef1 (w_{c+k}))`, via `realDefect_m1_closed`. This is
the exact object that `honest_realDefect_exceeds_tight` proved does NOT fit the tight model.
The re-basing converts the magnitude piece from **unsatisfiable** (tight) to **inhabited**
(loose) — genuine forward progress isolating the recursion as the only remaining field.

### The loose product floor (new summability, genuine)

The Grönwall fold `DefectGapRecursion → fullFloor` needs `∏(1 − modelExpr(w_k)) > 0`. Built
from the generic engine `sum_loss_to_productFloor_exp` fed with the loose sequence, using:

* **Majorant** `model_le_two_renDefect`: `modelExpr(w_k) ≤ 2·renDefect afr 1 k`. Proof:
  `renDefect ≃ 2·(1−w)²·(2+w)` (via `renDefect_factor`), and `6 ≤ 2·2·(2+w) = 8+4w` for
  `w ≥ 0`. Hence the loose defect is `O(1/k²)`-summable with doubled constant.
* **Deeper cutoff** `looseCutoff afr := 4·(Aconst afr 1).num.toNat` and
  `renDefect_le_quarter` (mirror of `renDefect_le_half` with the cross-product
  `A.num·4 ≤ den·(k+2)`), giving `modelExpr(w_k) ≤ 2·(1/4) = 1/2` on the tail — the
  `(1−ρ) ≤ 1/2` hypothesis the engine requires.
* **Loose summability** `loose_lossSum_le`: `Σ modelExpr ≤ 2·(Aconst·pot 2 looseCutoff)`,
  via termwise majorant + `lossSum_two_mul` (a `2·Σ = Σ2·` induction) + `renDefect_summable`.

`defectRecursion_of_looseBound : SingleStepDefectBoundLoose → DefectGapRecursion` fills
EVERY `DefectGapRecursion` field from proved lemmas (defect `= modelExpr∘w`, nonneg / `≤1` /
positive product floor `looseFloorEps·tm0`), with the `recursion` field discharged from
`magnitude` + the structure's `recursion` (`realδ ≤ modelExpr` ⟹ `1−modelExpr ≤ 1−realδ`,
times `tm ≥ 0`). `fullFloor_of_looseBound` then yields the entire positive continuum floor
for the true margin. **So the whole continuum gap now rests on the ONE `recursion` field**,
with the magnitude piece proved satisfiable and the floor proved summable — cleanly
isolated, guard still 5 (no full inhabitant of `SingleStepDefectBoundLoose` is produced).

---

## MOVE 2 — the recursion itself: constructed on a regime, and the exact residual pinned

`MarginRecursion realδ tm := ∀k, (1 − realδ_k)·tm_k ≤ tm_{k+1}`.

### (2a) The recursion IS constructible when `tm` is the RG-transported gap

`looseRecursion_on_surrogate`: with `tm := looseSurvival afr k = ∏_{j<k}(1 − modelExpr(w_{c+j}))`
(the RG survival product itself), `MarginRecursion (modelExpr∘w) (looseSurvival)` holds — as
an **equality** (the `prodPrefix` step is `looseSurvival_k·(1−modelExpr_k)`). So the recursion
is a THEOREM when the margin is the RG-transported survival product. The gap between this and
the physical statement is exactly the identification of the true margin with (a lower bound by)
the RG-transported gap — i.e. the located-2nd-eigenvalue perturbation content.

### (2b) The EXACT s≥2 → s=1 coupling object (pinned)

`SurrogateDomination afr tm := ∀k, afSurvivalSeq afr (c+k)·tm_k ≤ tm_{k+1}`, where
`afSurvivalSeq = 1 − δ_ren(w_k)` is the **located-2nd-eigenvalue survival factor** of the
transfer operator. This is the exact interacting object: *the true dimensionless margin
contracts under one block-spin step by no more than the transfer-operator survival factor
`1 − δ_ren(w_k)`.* Genuine reduction proved:

  `looseRecursion_of_surrogateDomination : SurrogateDomination afr tm ∧ (tm ≥ 0) → MarginRecursion (modelExpr∘w) tm`

(uses `afDefectSeq ≤ modelExpr`, i.e. `δ_free ≤ 6(1−w)²` from `2+w ≤ 3`, so
`1−modelExpr ≤ 1−δ_free = afSurvival`). Thus the loose recursion follows from
`SurrogateDomination`, and `SurrogateDomination` is the pinned residual.

`SurrogateDomination` unfolds as: for the fundamental (`s = 1`) test state carried across one
block-spin step, the coarse-grained transfer operator `T_{k+1}` satisfies the Rayleigh lower
bound `⟨v, T_{k+1} v⟩ ≥ (1 − δ_ren(w_k))·λ₂(T_k)·⟨v,v⟩`. The `δ_ren(w_k)` is the operator
norm of the **backreaction** `B_k : (s≥2 excited channel) → (s=1 fundamental channel)` that
the block-spin generates and the next step integrates out. The coupling object is precisely
this off-diagonal block `B_k` of the interacting coarse-grained action.

### (2c) Adversarial: this object is strictly stronger than any per-scale bound

`perScale_not_recursion_reexport` re-establishes that `∀k realδ_k ≤ modelExpr(w_k)` does NOT
imply `MarginRecursion` — so `SurrogateDomination` (equivalently the recursion) is NOT a
consequence of the magnitude piece. The two pieces are genuinely independent:
magnitude = "the backreaction is *small*" (proved at `m=1`); recursion/`SurrogateDomination`
= "the backreaction is *sign-controlled / dominated* in the 2nd-eigenvalue sense" (open).

---

## HONEST VERDICT — is the recursion constructible, or the irreducible interacting action?

**The recursion is the irreducible interacting content — but it is now sharply pinned to a
single, standard-shaped object.** Specifically:

* It is **NOT** derivable from the per-scale defect magnitude (`perScale_not_recursion`, re-
  proved). Any attack that only bounds `realδ_k` (transverse quadratic, connected slack,
  local-CLT for `Cdef`) provably cannot close it. This kills the "bound the defect harder"
  route as a loop.

* It **IS** constructible whenever the margin is the RG-transported survival product (2a) —
  so the obstruction is not the recursion's *algebra* but the *identification of the physical
  margin with (a lower bound by) the transfer-operator spectrum*.

* The exact missing object is `SurrogateDomination`: the per-step domination of the true
  margin by the located-2nd-eigenvalue survival factor `1 − δ_ren(w_k)`. Its inhabitant
  requires a **reflection-positivity / min-max operator domination** for the block-spin:
  `T_{k+1} ⪰ (1 − δ_ren(w_k))·U_k T_k U_k^*` for the block-spin isometry `U_k`, i.e. the
  sign-definiteness of the s≥2→s=1 backreaction block `B_k`. That is the interacting
  effective action's content — the non-perturbative RG map — **not** anything reducible to a
  per-scale magnitude.

**So the answer to the posed dichotomy:** the true-margin recursion is the irreducible
interacting effective action, and the exact s≥2→s=1 coupling object is the backreaction
block `B_k = ⟨s=1 | (block-spin coarse-grained action) | s≥2⟩`, whose operator norm is
`δ_ren(w_k)` (bounded — the magnitude piece) and whose *sign-controlled domination*
(`SurrogateDomination`, a 2nd-eigenvalue Rayleigh lower bound via reflection positivity) is
the sole open field. The magnitude is satisfiable; the domination is the wall. The standard
route to it is Osterwalder–Seiler reflection positivity of the block-spin measure + min-max
— that is the concrete next front, not a per-scale defect estimate.

---

## What this increment contains — IMPLEMENTED and VERIFIED

File `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean` (new; one import line added to
`lean/YMGap.lean`). 20 load-bearing declarations, all machine-checked:

Re-basing (Move 1): `SingleStepDefectBoundLoose` (magnitude on `6(1−w)²`), the two-sided
comparison `model_le_two_renDefect` / `renDefect_le_model`, the deeper cutoff
`renDefect_le_quarter` → `model_le_half`, the loose summability `loose_lossSum_le`, the
strictly-positive loose product floor `looseFloorData` / `looseFloorEps_le_prod`, the builder
`defectRecursion_of_looseBound`, and `fullFloor_of_looseBound`. The magnitude piece is proved
SATISFIABLE by `looseMagnitude_satisfiable` (the interacting `m=1` construction) — the decisive
contrast with the tight model (`honest_realDefect_exceeds_tight`).
Recursion (Move 2): `looseRecursion_on_surrogate` (constructed on the RG survival regime),
`SurrogateDomination` (the pinned s≥2→s=1 object) + the genuine reduction
`looseRecursion_of_surrogateDomination`, and the refutation `perScale_not_recursion_reexport`.

### VERIFIED STATUS (independent audit)

* `lake build` → exit 0, "Build completed successfully (763 jobs)".
* Frontier guard → "frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited"
  (unchanged; no guarded type inhabited).
* `#print axioms` on all 20 declarations → `[propext]` or `[propext, Quot.sound]` only;
  no `sorryAx`/`Classical`/`Choice` anywhere.
* No `sorry`/`admit`/`native_decide`/`ring`/`nlinarith`/`linarith`.
* No `:= SingleStepDefectBound` alias (loop-counter C unchanged) — a structural frontier move
  (magnitude unsatisfiable→satisfiable; recursion isolated and reduced to the named
  `SurrogateDomination`), not a re-derivation of the same core.
* `SingleStepDefectBoundLoose` is only CONSUMED (by `defectRecursion_of_looseBound`), never
  constructed; its `recursion` field stays open. Every declaration is a genuine `Q'`/`CReal`
  proof — non-vacuous.

The 4D YM mass gap remains OPEN; the sole open residual is now the true-margin recursion,
equivalently `SurrogateDomination` (the located-2nd-eigenvalue transfer-factor domination /
the backreaction block `B_k`). Nothing committed. Nothing faked.
