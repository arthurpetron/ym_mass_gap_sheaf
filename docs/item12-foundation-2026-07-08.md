# Item 12 FOUNDATION — certified-arithmetic RG route to `singleStep`

**Status: IN PLACE, machine-checked, axiom-clean, honest.** Two new Lean files,
full `lake build` exit 0 (784 jobs), frontier guard = 5 (unchanged), statement
guard OK (no drift). Nothing inhabits `singleStep` or any Clay-frontier type.

Files (both MAIN tree, imported in `lean/YMGap.lean`):
- `lean/YMGap/Continuum/IntervalArithmetic.lean` — the SOUND Q' interval kernel
- `lean/YMGap/Continuum/TruncatedBlockSpinContraction.lean` — certified truncated
  contraction + named truncation-error residual + composition

---

## 1. The Q' interval-arithmetic kernel — SOUND (enclosure preserved)

`structure QI where lo hi : Q'; le : lo ≤ hi` — an exact-rational enclosure
(`lo`,`hi` are Type-level data; `le` a propositional side condition; `contains i x
:= i.lo ≤ x ∧ x ≤ i.hi`). Because Q' is exact, outward rounding is automatic — the
part Koch–Wittwer built by hand is free here.

Certified ops with GENUINELY PROVED soundness (enclosure preservation):
- `contains_add`, `contains_neg`, `contains_sub` — [propext]
- `contains_mul` — the classic **4-corner rule** (`prod4min`/`prod4max` over the
  four endpoint products); soundness proved via one-factor monotone-enclosure
  lemmas `mul_mem_left`/`mul_mem_right` (constructive split on `0 ≤ c` / `c ≤ 0`,
  using a locally-proved `mul_le_mul_of_nonpos_right` and `Q'.le_total` from
  `Int.le_total`). — [propext]
- `contains_scale` (via `mul` with a point interval) — [propext]
- `certifiedLt` / `certifiedLe` / `certifiedLowerLe` — a `decide`-checkable endpoint
  fact (`i.hi < c` / `i.hi ≤ c`) certifies the bound on EVERY enclosed value: the
  mechanism by which a `decide` on rational endpoints discharges an analytic
  inequality. — [propext]
- `width i := i.hi - i.lo`.

All soundness theorems are `#print axioms`-gated at [propext] only. No Mathlib
(core-only; note `set` is Mathlib and was avoided), no `native_decide`, no `sorry`,
no Classical.

## 2. The certified truncated block-spin contraction — REAL machine-checked bound

Pilot model (scouting scheme: transverse bond-moving MK): `N = 4` SU(2) character
channels `j ∈ {0,½,1,3/2}` at crossover coupling `w = 4/5` (margin `m = 1/5`), each
channel a rational coefficient ENCLOSURE with genuine width (rounded
super-geometrically-decaying fused coefficients). `truncatedDefect : QI` is COMPUTED
by the interval kernel (`QI.mul` of coefficient intervals with `mSqInt = QI.mul
(point m)(point m)`, accumulated by `QI.add`).

- `truncatedDefect_le_six : truncatedDefect.hi ≤ 6·(1−w)²`  — **by `decide`** on the
  exact rational endpoints. The `singleStep`-shaped quadratic bound, a genuine
  interval computation, NOT assumed. [propext]
- `truncatedDefect_le_four : truncatedDefect.hi ≤ 4·(1−w)²` — sharper (actual constant
  ≈ 39/10 < 4): genuine slack, the bound is not rigged tight. [propext]
- `enclosed_defect_le_six` — `certifiedLe` transfers the endpoint bound to the
  (unknown, enclosed) true defect: `∀ x, contains truncatedDefect x → x ≤ 6·(1−w)²`.
- `mPilot_pos` — non-vacuity (`m > 0`, the bound is not `0 ≤ 0`).

## 3. The ONE analytic residual — NAMED-OPEN (not faked)

```
structure TruncationTailBound (afr : AFRateModulus) (N : Nat) (tailDefect : Nat → Q') : Type where
  tail_quad : ∀ k, tailDefect k ≤ 2·(1 − afr.w k)²
```
The single lemma where the Balaban hardness concentrates: super-geometric Bessel
decay of the SU(2) heat-kernel coefficients bounds the DISCARDED high-`j` channels'
per-step defect contribution by the `2·m²` slack. `tailDefect` is an
**externally-given** parameter (the real tail of the true fused sequence — NOT a
free field settable to 0), so inhabiting it for the real map is exactly the open
analytic estimate (item 12 step 3, the collaborator target). Scouting pins
`N ≈ 26` for a `1e-6` tail (`N = 18` for `1e-3`), documented in the module. Uninhabited.
(A degenerate `tailDefect ≡ 0` witness is recorded ONLY as a not-false-as-stated
check, Rule 9.1, and closes nothing.)

## 4. Composition toward the Grönwall fold

- `fullDefect_quad_of_certified_and_tail` — (certified truncated `≤ 4·m²`, from the
  interval kernel) + (`TruncationTailBound`, tail `≤ 2·m²`) ⟹ full per-step defect
  `≤ 6·(1−w_k)²` = the `HierarchicalMassGap.EuclideanExtraRequirements` (E1)
  quadratic-defect input. BOTH hypotheses load-bearing (`4m²+2m²=6m²` closes only
  with tail control; `four_add_two_mul_eqv` proves the coefficient identity).
- `certified_route_to_floor` — bundles (E1 reproduced from interval+tail) with the
  4D positive continuum floor `0 < prodFloor ∧ ∀k, prodFloor ≤ trueMargin k`,
  delivered by the PROVED fold `SingleStepDefectReduction.fullFloor_of_singleStep`
  from the `singleStep` (E2) bound. — [propext, Quot.sound]

## Honest verdict — is the FOUNDATION in place?

**Yes.** Interval kernel SOUND (enclosure genuinely proved for add/neg/sub/mul/scale);
a REAL machine-checked (`decide`) interval contraction bound on the truncated map;
the one analytic residual sharply named-open; composition wired into the existing
Grönwall fold. Axiom gate ⊆ {propext, Quot.sound} throughout; guard stays 5 (nothing
closed).

**What REMAINS (explicitly):**
1. **Full `N ≈ 26` certification** — the pilot `decide` is proved at ONE margin
   (`w = 4/5`) and `N = 4`; the `htrunc : ∀ k, truncDefect k ≤ 4·(1−w_k)²` hypothesis
   (all AF scales, all 26 fused channels) is the remaining interval-arithmetic work —
   each scale a further `decide`. Cloud caveat from scouting: the transverse-scheme
   ε-summability is FAVORED but unconfirmed below `1−w ≈ 0.28`.
2. **The truncation-error lemma** `TruncationTailBound` itself — the single analytic
   super-geometric Bessel-decay estimate (item 12 step 3).
3. **E2 = `singleStep`** — unchanged; the certified route reproduces E1 independently
   but does not close E2.
