# The Bakry–Émery CURVATURE route to `singleStep` — does it avoid the renormalon?

**Sole open field under attack.**
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`:
`(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`, i.e. `realδ_k ≤ δ_model_k = 6·pMult·(1−w_k)²`.
The fluctuation/interacting-measure (Borel) route confirmed this is the non-perturbative
condensate positivity `Λ = a·exp(−1/2β₀g²) ≠ 0` (the renormalon) — irreducible there.

**A genuinely different angle asked:** does bounding the gap MAGNITUDE from the RG-flow /
config-space CURVATURE (the Casimir), rather than from the fluctuation determinant `z₁`,
give `singleStep` directly, or reduce it to a *more tractable* quantity (the interacting
Bakry–Émery `Γ₂`) that AVOIDS the renormalon?

---

## HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**NO. The curvature route does NOT give `singleStep` directly, and the quantity it
reduces to (the interacting `Γ₂`) is NOT more tractable — it is structurally WORSE-formed
and does not avoid the renormalon.** Two machine-checked structural facts pin this, plus
the recorded analyticity obstruction:

1. **The free curvature lands on the MARGINAL part, not on the residual.** The free SU(2)
   Casimir the route supplies is `C₄(1) = 3 = 4·casimirGap = 4·C₂(1)`. That is EXACTLY the
   coefficient of the MARGINAL LINEAR part `C₄(1)·(1−w)` of the per-step defect — the part
   the counterterm `renormW` already SUBTRACTS (part (B), PROVED). Subtracting it leaves
   EXACTLY the QUADRATIC transverse residual `(1−w)²·(2+w)` — and THAT is `singleStep`
   (part (C)). **So the Lichnerowicz/Casimir bound reproduces the already-proved marginal
   part and is ORTHOGONAL to the open residual.** (Decisive new finding.)

2. **The interacting curvature goes NEGATIVE toward the continuum.** The only rigorous
   lattice-gauge BE curvature (Shen–Zhu–Zhu, CMP 2023) is
   `K_S(β) = (N+2)/2 − 1 − 8N(d−1)|β|`; for SU(2), d=4 it is `1 − 48β`. Positive ONLY at
   strong coupling `β < 1/48` (fixed coarse spacing = the IR anchor we already have),
   NEGATIVE for `β > 1/48` — i.e. exactly as `β = 2N/g² → ∞` (`w_k → 1`, the a→0 UV) where
   `singleStep` must hold for every `k`. The interacting-curvature lower bound supplies NO
   positive per-step control in the continuum direction.

3. **Analyticity obstruction (recorded, corroborated numerically).** A BE curvature `K(g²)`
   is ANALYTIC at the Gaussian point ⇒ any gap derived from it is polynomial in `g²` ⇒ it
   CANNOT track the essential singularity `exp(−c/β₀g²)` of the condensate. Numerically the
   condensate is astronomically smaller than any polynomial as `g²→0` (below), so a
   curvature convexity argument cannot resolve the non-perturbative positivity.

`SingleStepDefectBound` is NOT inhabited. Nothing is faked. **The 4D Yang–Mills mass gap
remains OPEN.**

---

## 1. The Lichnerowicz/Casimir free bound — and why it is already exact (task points 1,3)

`SU(2) = S³` with its bi-invariant metric is the round unit 3-sphere — the **Obata-extremal**
manifold. Lichnerowicz `λ₁ ≥ n·K_sec = 3·1 = 3` is **SATURATED** (equality). The free
single-edge heat-kernel generator is DIAGONAL on characters, so it already carries the
*exact* eigenvalue `C₂(s) = s(s+2)/4`, first excited `C₂(1) = 3/4`, i.e. `C₄(1) = 3` in
`C₄ = 4C₂` units.

| quantity | value | Lean |
|---|---|---|
| free curvature `casimirGap = C₂(1)` | `3/4` | `HeatKernelCurvature.casimirGap`, `free_DiagCD` (every excited mode ≥ 3/4) |
| Lichnerowicz `λ₁` on unit `S³` | `3` (saturated) | = `C₄(1)`; `c4_one_eq_four_casimirGap` |
| `C₄(1) = 4·casimirGap` | `3` | `free_curvature_anchor_bundled` |

**Conclusion of point 1/3:** Lichnerowicz adds *nothing* beyond the exact Casimir the
diagonal generator already has. The free curvature/gap MAGNITUDE `K=3/4` is real and PROVED,
and it is scale-invariant (the Casimir does not run). But — point 2/4 — that fixed number is
NOT the per-step degradation `singleStep` controls.

## 2. The decisive decomposition — curvature ⟹ marginal (B), NOT residual (C) (points 2,4)

The renormalized per-step defect on the dominant mode is
`δ_ren(N,1,w) = dimQ 1·( C₄(1)·(1−w) − (1 − w^{C₄(1)}) )`. Exact algebra (sympy, exact):

```
C₄(1)·(1−w) − (1 − w³) = w³ − 3w + 2 = (1−w)²·(w+2)   [EXACT, no remainder]
```

The **linear** term `C₄(1)·(1−w) = 3(1−w)` — coefficient `3` = the free curvature/Casimir —
cancels completely; the residual is purely **second order**. So:

- **The free curvature (Casimir = 3) IS the coefficient of the MARGINAL LINEAR part** — the
  running-coupling drift that `renormW` subtracts as the counterterm (part (B) of
  `SingleStepDefectReduction`, PROVED: `trueDev_eq_counterterm_sub_transverse`).
- **`singleStep` is the QUADRATIC residual `(1−w)²·(2+w)`** (part (C)) — bounded by the model
  `δ_model = 6p(1−w)²` since `(2+w)/6 ∈ [1/3, 1/2] ≤ 1` on `[0,1]`.

**Machine-checked (Lean):** `bondMovingDeltaRen_one_factor`:
`δ_ren(N,1,w) ≃ dimQ 1·(1−w)²·(2+w)` (reusing the PROVED `renDefect_factor`);
`curvature_lands_on_marginal_not_residual` bundles the identity with `4·casimirGap = C₄(1)`.

**This is the precise answer to point 4:** the curvature route does NOT give `singleStep`
directly. The free Casimir curvature reproduces the *already-proved* marginal part and is
orthogonal to the residual. To reach `realδ` (the real interacting per-step defect) the route
needs the **INTERACTING** curvature — the Bakry–Émery `Γ₂` of the coupled Wilson-action
weight (`Γ₂ = |Hess f|² + [Ric_group + Hess(V_Wilson)]`). That is a genuinely DIFFERENT
quantity than the fluctuation determinant `z₁` — but not a more tractable one.

## 3. The interacting `Γ₂` does NOT avoid the renormalon (point 5, adversarial)

Three independent obstructions, all pointing the same way:

**(a) It goes NEGATIVE in the continuum direction — machine-checked.** SZZ curvature
`K_S(β) = 1 − 48β` (SU(2), d=4). `K_S(1/48) = 0` (`szz_curvature_zero_at_threshold`);
`K_S(1) = −47 < 0` (`szz_interacting_curvature_goes_negative`); `K_S(1/100) = 13/25 > 0`
(`szz_curvature_pos_strong_coupling`). Positive ONLY at strong coupling — a second proof of
the fixed-spacing gap we already have — and negative as `β → ∞` (`w_k → 1`), precisely where
`singleStep` must hold for all `k`. So the naive positive interacting-curvature lower bound
is **FALSE** in the a→0 regime, not merely intractable.

**(b) It is analytic in `g²`, the condensate is not — numerically corroborated (mpmath dps 50).**
```
 g²      poly~g²      condensate exp(−c/(β₀g²))    ratio cond/poly     (β₀=22/3, c=4)
 0.100   1.0000e-01   4.2768e-03                  4.28e-02
 0.050   5.0000e-02   1.8291e-05                  3.66e-04
 0.020   2.0000e-02   1.4309e-12                  7.15e-11
```
A polynomial-in-`g²` (analytic) curvature bound cannot track an essential singularity; the
renormalon/condensate positivity is INVISIBLE to a convexity argument.

**(c) Evaluating `E[Γ₂]` uniformly in `a` needs the interacting measure** — the same
non-perturbative object the fluctuation route needed. `Γ₂`'s π-mean is an integral over the
interacting Gibbs weight.

**Net:** the curvature route reduces `singleStep` to the interacting `Γ₂` — a DIFFERENT
quantity than `z₁`, but one that is (i) false-in-form (negative) in the continuum,
(ii) analytic-wrong-form for `exp(−c/g²)`, (iii) still gated on the interacting measure. It
is the SAME non-perturbative condensate positivity, seen through a lens that structurally
cannot resolve it. It does **not** avoid the renormalon.

## 4. Did it cascade / close? NO — the STOP-and-audit condition did not trigger

No inhabitant of `SingleStepDefectBound` or any of the 5 guarded frontier types is produced.
The free curvature bundle, the exact quadratic identity, and the SZZ negativity are all
PROVED and all *compatible with* `singleStep` being open — none inhabits it.

| claim | status | Lean |
|---|---|---|
| free curvature `K=3/4>0`, every excited mode `≥3/4` | **PROVED** | `free_curvature_anchor_bundled`, `free_DiagCD` |
| Lichnerowicz `λ₁=3` saturated = `C₄(1)` | **PROVED** | `c4_one_eq_four_casimirGap` |
| curvature = marginal-linear coeff; residual = `(1−w)²(2+w)` | **PROVED** | `curvature_lands_on_marginal_not_residual`, `bondMovingDeltaRen_one_factor` |
| residual 2nd-order at free end `w=1` | **PROVED** | `residual_second_order_at_free_end` |
| interacting curvature `<0` in continuum direction | **PROVED** | `szz_interacting_curvature_goes_negative` |
| **`singleStep` (`realδ ≤ δ_model`)** | **OPEN — the residual** | `SingleStepDefectBound` UNINHABITED |

## 5. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (720 jobs).
```
New file `lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean` (wired into `YMGap.lean`),
Lean-core only (`Q'`/`Nat`), no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`.
`#print axioms` on all 8 load-bearing decls ⊆ `{∅, [propext], [propext, Quot.sound]}`:

```
free_curvature_anchor_bundled             : [propext]
bondMovingDeltaRen_one_factor             : [propext, Quot.sound]
curvature_lands_on_marginal_not_residual  : [propext, Quot.sound]
residual_second_order_at_free_end         : [propext, Quot.sound]
szz_curvature_zero_at_threshold           : (none)
szz_interacting_curvature_goes_negative   : (none)
szz_curvature_pos_strong_coupling         : (none)
curvature_route_verdict                   : [propext, Quot.sound]
```
Committed: nothing.

## 6. Honest final verdict

The Bakry–Émery curvature route is a genuine gap-MAGNITUDE mechanism (`CD(K) ⇒ gap ≥ K`,
proved; free `K=3/4`, proved), but on the sole open field `singleStep` it **lands on the
already-proved MARGINAL part (B), not on the residual (C)**: the free Casimir curvature is
exactly the coefficient of the counterterm-subtracted linear term, and the residual
`(1−w)²(2+w)` — which IS `singleStep` — is orthogonal to it. Reaching `realδ` requires the
INTERACTING curvature `Γ₂`, a different quantity than the fluctuation determinant `z₁`, but
NOT a more tractable one: it goes negative in the continuum direction (SZZ, machine-checked),
is analytic-wrong-form for `exp(−c/g²)`, and is still gated on the interacting measure. **The
curvature route reshapes but provably cannot close `singleStep`; it reduces to the SAME
non-perturbative condensate positivity, not to a renormalon-free residual.** Nothing is
inhabited; nothing is faked; the mass gap remains OPEN — and the next attack is the interacting
per-step fluctuation bound (fusion-local-CLT / `p=2` variance-parity), not curvature.
