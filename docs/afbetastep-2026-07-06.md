# AFBetaStep discharged for the concrete canonical AF trajectory

**Date:** 2026-07-06
**File:** `lean/YMGap/Continuum/AFBetaStepCanonical.lean` (new, imported in `YMGap.lean`)
**Build:** full `lake build` green (694 jobs, incl. `YMGapGuard` frontier guard). Axiom-clean.

---

## 1. The obligation (exact statement)

`EigenvalueShiftBound.AFBetaStep afr : Type` carries two fields along the AF flow `w_k`:

```
mono     : ∀ n, afr.w n ≤ afr.w (n+1)
betaStep : ∀ n, afr.w (n+1) − afr.w n ≤ Q'.ofNat 2 * ((1 − afr.w n) * (1 − afr.w n))
```

i.e. `w_{n+1} − w_n ≤ 2·(1 − w_n)²`. It is consumed by the **conditional** producer
`eigenvalueShiftDefect_of_betaStep : AFBetaStep afr → EigenvalueShiftDefect afr`
(pins `eigShift := eigShiftSeq afr.w = w_{k+1}³ − w_k³`, bound from `cube_diff_le_envelope`).

The `mono` half was already proved for the canonical trajectory (`afBetaStep_mono_canonical`).
This work proves the `betaStep` half and **inhabits `AFBetaStep afRateModulus_canonical`**.

## 2. The concrete trajectory + arithmetic (verified exact)

Canonical trajectory `afRateModulus_canonical.w k = 1 − Q'.invSucc k = 1 − 1/(k+1) = k/(k+1)`,
so `1 − w_k = 1/(k+1)`. Then

```
w_{k+1} − w_k = 1/(k+1) − 1/(k+2) = 1/((k+1)(k+2))
2·(1 − w_k)²  = 2/(k+1)²
```

Claim `1/((k+1)(k+2)) ≤ 2/(k+1)²` ⟺ `(k+1)² ≤ 2(k+1)(k+2)` ⟺ `(k+1) ≤ 2(k+2)` ⟺ `0 ≤ k+3` (always).

- **sympy exact slack (canonical):** `2(1−w_k)² − (w_{k+1}−w_k) = (k+3)/((k+1)²(k+2)) ≥ 0`.
- **fractions-exact numeric:** verified `k = 0 … 1999`, 0 failures.
- **general `1−w_k = A/(k+B)`:** closed-form slack `A·(2A(k+1+B) − (k+B)) / ((k+B)²(k+1+B))`.
  For `A ≥ 1/2`: `2A(k+1+B) − (k+B) ≥ (k+1+B) − (k+B) = 1 > 0`, so slack `≥ 0` for **all** `A ≥ 1/2, B ≥ 0`
  (at `A = 1/2` the numerator factor is exactly `1`; verified numerically for
  `(A,B) ∈ {(1/2,1),(1/2,1/2),(1,1),(2,1),(3/2,2),(1/2,3)}`, 0 failures). `A=B=1` is the canonical case.

## 3. The Lean proof (LEAN-CORE only: `Q'`/`Nat`, no Mathlib/ring, no native_decide)

The degree-5 cross-multiplication is avoided via the **telescoping-product identity**:

```
invSucc_diff_eq_prod :  1/(n+1) − 1/(n+2)  ≃  (1/(n+1))·(1/(n+2))          -- EXACT eqv
invSucc_step_le      :  1/(n+1) − 1/(n+2)  ≤  2·(1/(n+1))²
                        via  A·B ≤ A·A  (invSucc_antitone + nonneg)  and  A·A ≤ 2·A·A  (1 ≤ 2)
betaStep_canonical   :  w_{n+1} − w_n  ≤  2·(1 − w_n)²
                        (cancel the two constant 1's on the LHS; one_sub_one_sub_eqv on the RHS)
```

`invSucc_diff_eq_prod` is the only cross-product step and is an **equality** (both numerators `1`,
both denominators `(n+1)(n+2)`), closed by `omega` after `Q'.invSucc_num`/`Q'.invSucc_den`.

Inhabitants:
```
afBetaStep_canonical          : AFBetaStep afRateModulus_canonical            := ⟨mono, betaStep⟩
eigenvalueShiftDefect_canonical : EigenvalueShiftDefect afRateModulus_canonical
                                := eigenvalueShiftDefect_of_betaStep afBetaStep_canonical
```

## 4. `#print axioms` (all 5 load-bearing declarations)

```
invSucc_diff_eq_prod          : [propext, Quot.sound]
invSucc_step_le               : [propext, Quot.sound]
betaStep_canonical            : [propext, Quot.sound]
afBetaStep_canonical          : [propext, Quot.sound]
eigenvalueShiftDefect_canonical: [propext, Quot.sound]
```

Axiom gate PASSES (propext / Quot.sound only). No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`.

## 5. Guard / STOP status (task condition ii) — NO guard tripped

`AFBetaStep` is a **named Rule-6a input**, not a guarded frontier bundle.
`EigenvalueShiftDefect` (inhabited here for the canonical trajectory) is **documented as a NODE**
in `RouteIEigenvalueDefect`/`BlockSpinMarginConstruction`: `eigShift_to_fullRange` reaches only the
free-field node `FullRangeFusedDefect`, and there is **no existing lemma** producing
`SingleStepDefectBound` / `TrueMarginRecursion` / `UniformSpacingFloor` / `Tier0Scorecard` /
`ClayTarget` / `ClayTargetPinned` / `FrontierDAG` from it.

The **full `lake build` including `YMGapGuard` is green** — the frontier-uninhabitedness guard
confirms no guarded/Clay-frontier type became inhabited. This is a **standalone-node advance**, not a
cascade to a guarded bundle. No STOP condition tripped.

## 6. Adversarial checks

- **Genuinely satisfied?** Yes. The `betaStep` inequality is verified numerically (fractions-exact,
  k=0..1999) and the sympy slack `(k+3)/((k+1)²(k+2))` is manifestly positive. The Lean proof is a
  chain of exact identities + monotonicities, not a weakening.
- **Genuine AF trajectory, not a fudge?** Yes. `1 − w_k = 1/(k+1)` has the correct asymptotic-freedom
  `1/k` scaling (`≍ g_k² ≍ 1/k`). It is `afRateModulus_canonical`, the codebase's concrete AFRateModulus
  inhabitant, with the two-sided AF band satisfied exactly (`A=A'=B=1`).
- **Not free from `AFRateModulus`?** Confirmed. AFBetaStep is a genuine EXTRA input: at `k=8`, a sequence
  inside the two-sided band `[A'/(k+B), A/(k+B)]` (with `A'=1/2, A=1, B=1`) can have
  step `w_9 − w_8 = 11/180 ≈ 0.061 > 2(1−w_8)² = 2/81 ≈ 0.025` — violating `betaStep`. So the abstract
  band does **not** imply the two-loop step; the concrete trajectory does.

## 7. Physics verdict — is `A ≥ 1/2` physical or a scheme choice?

**The `1/k` scaling is physical and scheme-independent** (asymptotic freedom: `1 − w_k ~ g_k² ~ 1/(β₀ · s · k)`
where `s = ln b` is the log of the block factor per RG step). **The prefactor `A = 1/(β₀ s)` is
scheme-dependent.** The condition `A ≥ 1/2 ⟺ β₀ s ≤ 2` depends on:

1. the **block factor** `b` (each blocking step advances `ln μ` by `ln b`, so `s = ln b` rescales the
   effective per-step coefficient — halving/doubling `b` moves `A`);
2. the **coupling normalization** and the precise definition of the heat-kernel weight `w` vs `g²`
   (the map `1 − w ↔ g²` carries a scheme-dependent Jacobian near the fixed point);
3. the **subtraction scheme** for the two-loop coefficient.

So `A ≥ 1/2` is **achievable in a genuine scheme (a scheme choice), not a scheme-independent invariant.**
Honestly: one can always pick a blocking/normalization scheme that lands `A` in `[1/2, ∞)` (e.g. the
canonical `A=1`), and the two-loop `betaStep` inequality then holds by §2's general `A≥1/2` bound. The
canonical `A=1` trajectory is a **valid AF trajectory with the correct scaling**, so inhabiting
`AFBetaStep` with it is genuine (not a degenerate/vacuous witness).

What this does **not** establish: that the **real 4D SU(2) block-spin flow's** actual `w_k` sits on a
trajectory with `A ≥ 1/2`. That is the residual physical content — now sharpened to "the real flow
realizes a scheme with `β₀ · ln b ≤ 2`," a concrete, checkable RG-scheme statement rather than an
opaque bound.

## 8. HONEST VERDICT

- **AFBetaStep is DISCHARGED on the concrete canonical AF trajectory** — proven (not assumed),
  axiom-clean, non-vacuous, with the correct `1/k` AF scaling. It is a genuine input (a `k=8`
  band counterexample shows it is not free from `AFRateModulus`), and it is now shown **satisfiable**
  by a real AF-scaling trajectory, dissolving any worry that it is an unsatisfiable/vacuous obstruction.
- **Clay-core status:** at the eigenvalue-shift-bound layer, EigenvalueShiftBound reduced Clay input (1)
  to **two** named inputs — `AFBetaStep` and `SingleCouplingFormPreservation`. This work discharges the
  first for the concrete trajectory. The **residual** for the physical 4D flow is: (i) that the real flow's
  `w_k` obeys the two-loop `betaStep` (i.e. realizes a scheme with `A ≥ 1/2` — a scheme choice, physical
  and checkable, here proven only for the canonical toy), and (ii) `SingleCouplingFormPreservation`.
- **The 4D Yang–Mills mass gap remains OPEN.** No guarded frontier bundle is inhabited; nothing faked;
  no `δ := 0` free-field trick. The advance is a clean, machine-checked discharge of a standalone named node.
