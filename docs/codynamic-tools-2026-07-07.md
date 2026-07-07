# Codynamic tools — Lean transpose (deliverable summary)

Faithful, axiom-clean Lean-core transposition of the machine-verified Agda
`Codynamic.*` development into reusable YM-proof infrastructure.

## Files (all in the MAIN tree, wired into `lean/YMGap.lean`)

- `lean/YMGap/CodynamicCore.lean` (692 lines) — the tool library.
- `lean/YMGap/CodynamicCoreTest.lean` (147) — non-vacuous computed test (toy `Nat`).
- `lean/YMGap/CodynamicCoreYMDemo.lean` (109) — real-`Q'` instantiation + RG η-model tie-in.

Namespace: `YMGap.CodynamicCore` (test/demo in `.Test` / `.YMDemo`).

## Which Agda modules were transposed → Lean names

| Agda source | Agda item | Lean name |
|---|---|---|
| Signature.agda | `Color`,`Profile`,`Signature`,`TypedSet` | `Color`,`Profile`,`Signature`,`TypedSet` |
| Metric.agda | `Costs` (ordered additive w/ joins) | `Costs` (structure) |
| Metric.agda | `MetricVal` (Val/point/⟦⟧/d + d-refl/sym/triangle/nonneg) | `MetricVal` |
| Metric.agda | `eval`/`evalAll` | `eval`/`evalAll` |
| Metric.agda | `dAll`/`dAll-refl` | `dAll`/`dAll_refl` (+ new `dAll_nonneg`) |
| Metric.agda | `maxOver`/`maxOver-ub`/`maxOver-nonneg` | `maxOver`/`maxOver_ub`/`maxOver_nonneg` |
| Metric.agda | `Lipschitz` (scale/scale-mono/scale-0/lip) | `Lipschitz` |
| Metric.agda | `εX`/`εX-nonneg`, `wdef` | `epsX`/`epsX_nonneg`, `wdef` |
| Metric.agda | `ExactlySound` | `Priced.sound` field |
| Metric.agda | `stepBound`/`step-d` (+nonneg, +allStep) | `stepBound`/`step_d` (+`_nonneg`,+`allStep_`) |
| Metric.agda | `derivBound`, **`deriv-d`** (defect propagation) | `derivBound`, **`deriv_d`** |
| Metric.agda | `eqBound`, `eq-d`, **`eqBound-◅◅`** (compositional error law) | `eqBound`, `eq_d`, **`eqBound_append`** |
| Metric.agda | **`unit-defect`** (reflection-unit defect) | **`unit_defect`** |
| Term.agda | `Term`,`Assignment`,`subst`/`substAll`,`size#` | `Term`,`Assignment`,`subst`/`substAll`,`tsize`/`sizeAll` |
| Rewrite.agda | `Star`/`◅◅`, `_↝_`/`AllStep`, `Normal`, `Tame`, `Normalize` | `Star`/`Star.append`, `CStep`/`CAllStep`, `Normal`, `Tame`, `normFuel`/`normalize` |
| Rewrite.agda | `Presentation`, `PresRoot`, `_∪ʳ_` | `Presentation`, `PresRoot`, `RootUnion` |
| Completion.agda | `Point`/`pointVar`, `Witness`,`wlhs`/`wrhs`,`Trace`,`TraceRoot`,`SymClosure`,`≈` | same names; `≈` = `CEq` |
| Trajectory.agda | `Pos`/`fill`/`dAll-fill` | `Pos`/`fill`/`dAll_fill` |
| Trajectory.agda | `Step`/`Linked`/`Traj`, `run`/`endRec` | `Step`/`Linked`/`Traj`, `run`/`endRec` |
| Trajectory.agda | `NStep.nBound`, `nBound-mono`, **`nstep-d`** (n-step Grönwall) | `nBound`, `nBound_mono`, **`nstep_d`** |

Faithfulness kept where it matters: the monotone-modulus form (`scale : Q→Q`,
NOT hard-coded multiplication); `nstep_d` as the left-fold `nBound` + its
correctness proof; the compositional error law derived, not assumed.

## The `Q'` instantiation of `Costs` (`qCosts`)

`Costs` fields ← existing repo `Q'` lemmas (no arithmetic rebuilt):

- `Q:=Q'`, `zero:=0`, `add:=(·+·)`, `max:=Q'.max'`, `le:=(·≤·)`, `eqv:=Q'.eqv`
- `le_refl/le_trans` ← `Q'.le_refl'`/`le_trans'`
- `add_mono` ← `Q'.add_le_add_right` ∘ `add_le_add_left` (+ `le_trans'`)
- `eqv_refl/symm/trans` ← `Q'.eqv_refl`/`eqv_symm`/`eqv_trans`
- `add_congr_right` ← `Q'.add_eqv_congr_left`; `add_assoc` ← `Q'.add_assoc_eqv`
- `zero_add` ← `Q'.zero_add'`
- `le_max_left/right`, `max_lub` ← reproved locally (few `Int` lines) to avoid
  the heavy `RegularCReal` import; equivalent to `RegularCRealArith`'s
  `le_max'_left/right`/`max'_le_iff'`.

**Setoid note (design decision):** the Agda `Costs` used propositional `≡`
for `+#-assoc`/`+#-identityˡ`. On `Q'`, addition is unnormalized, so those
laws hold only up to the semantic setoid `Q'.eqv`, NOT structural `Eq`.
Per AGENTS.md Rule 8 ("`Q'` with `eqv` already IS a setoid"), `Costs` carries
`eqv` and phrases the equational laws — and the conclusion of `eqBound_append`
— w.r.t. it. All ordering stays in `le`.

## Non-vacuous test result

Toy instance (one color, unary `f`+constant `k`, two-point carrier, toy `Nat`
costs with trivial order — exactly Agda `toyC`), values genuinely COMPUTED and
asserted by `rfl` (kernel executes them):

- `tsize (f d0) = 2`, `tsize k = 1`
- `eval (f (f d0)) = 2`, `eval k = 7`
- `run 0 tr2 = 2`, `endRec 0 tr2 = 9`, **`nBound 0 0 tr2 = 9`** (= Agda `test-16`)
- `nstep_d` and `nBound_mono` instantiate against the computed fold values.

YM-flavored (`CodynamicCoreYMDemo.lean`), over the REAL constructive cost:
- `qCosts` + a `Q'`-valued metric model + a **total linear RG damping modulus**
  `scale Z = (3/4)·Z` as `Lipschitz` (scale_mono via `Q'.mul_le_mul_of_nonneg_left`,
  lip via `dAll_nonneg`) → `nstep_d` yields a real `Q'`-order Grönwall certificate.
- An `example` shows the block-spin η-model `RG.etaModel_mono` has exactly the
  `Lipschitz.scale_mono` shape on the convergence cone `1−Z'>0` — a real YM RG
  modulus is an instance of the abstraction these tools consume. (η is monotone
  only on `[0,1)` so it can't fill `scale_mono` unconditionally; the linear
  modulus is the total instance actually plugged in.)

## Build / guard / axiom status

- `lake build`: **green, 749 jobs.**
- `lake build YMGapGuard`: **"5 Clay-frontier types unconditionally uninhabited"**
  — unchanged (this work inhabits no frontier type).
- `#print axioms` (all ⊆ {propext, Quot.sound}; most axiom-free):
  - `nstep_d`, `nBound`, `nBound_mono`, `maxOver_ub`, `dAll_fill`, `dAll_refl`
    — **no axioms at all**.
  - `qCosts`, `qM`, `qL` — `[propext]` only.
  - `deriv_d`, `eqBound_append`, `unit_defect` — `[propext, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`ring`/`nlinarith`/`Classical`.
- MLTT/HoTT (Rule 8): all witnesses (`All`, `Term`, `Star`, `Step`, `Traj`,
  derivations) are `Type`-valued inductives; only `le`/`eqv` live in `Prop`.

## How to use these for YM

- Instantiate `MetricVal.interp` with the **block-spin coarse-graining** ⟦block⟧,
  `MetricVal.d` with the physical distance, `MetricVal.Val` with the RG state.
- Instantiate `Lipschitz.scale` with the **RG modulus** (e.g. the η-model
  `RG.etaModel μ` on the cone via `etaModel_mono`, or a linear contraction as in
  the demo) — the monotone-modulus form covers nonlinear moduli with no
  multiplication assumed.
- A `Traj` is the **RG flow**; `nstep_d` transports an initial-discrepancy
  certificate `d(v,y) ≤ b` to a final-discrepancy certificate bounded by the
  fold `nBound` — the discrete-Grönwall accumulation `(∏L)·b + Σ(∏L)·η`, but
  as the fold (the object) with the closed form as its afterimage.
- The reflection unit φ = normal form (`normalize`); `unit_defect` prices the
  distance from a polynomial to its lawful representative by its own
  normalizer certificate — the "true by construction" defect, checked.
- `eqBound_append` gives the compositional (additive-up-to-setoid) error law for
  composing derivations/flows; `deriv_d` bounds a chain's endpoint discrepancy
  by its summed step weights (`εX` for trace instances, `scale ω` under a symbol).
