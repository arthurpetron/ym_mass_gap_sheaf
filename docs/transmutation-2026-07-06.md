# Dimensional transmutation — the dimensionless physical margin, its multiplicative recursion, and the uniform continuum floor

**Deliverables.** `lean/YMGap/Continuum/DimensionlessMarginTransmutation.lean` (full
`lake build` green, frontier-guard **OK at 5**, axiom-clean `[propext, Quot.sound]`),
this report, `validate.py` (mpmath dps 50). **Committed: nothing** (per instructions).

---

## 0. Headline

The dimensional-transmutation **kinematics are now constructed and machine-checked**:
the genuine dimensionless margin `m_lat(a_k)/a_k` is built as a concrete
constructive-real sequence, proved **conserved to a positive constant** along a
**real irrational self-similar RG flow**, and proved to **satisfy the multiplicative
single-step recursion the eroding lattice margin machine-FAILED**, with a **uniform
positive continuum floor**. The exp-on-CReal residual (Λ = exp) is **discharged**
(the separators are honest irrational `e^{-…}` reals).

**This does NOT close the mass gap.** The constructed margin is the **zero-defect
idealization** (perfectly self-similar), so its multiplicative recursion holds for
*any* defect `0 ≤ δ ≤ 1` — the `ε ≡ 0` multiplicative surrogate. The genuine open
Clay residual is the **real 4D SU(2) block-spin flow's deviation from
self-similarity** (the additive erosion `ε_k`), untouched. **No guarded bundle is
inhabited.** The 4D Yang–Mills mass gap remains **OPEN**.

---

## 1. The obligation and the crux it exposed

`BlockSpinMarginConstruction` machine-refuted (kernel `decide`, zero axioms) the
naive identification: the fixed-spacing eigenvalue margin `1 − w_k³` (in **lattice
units**) erodes to `0` as `w_k → 1`, so it **cannot** satisfy the multiplicative
recursion `(1−δ_k)·m_k ≤ m_{k+1}` with a positive floor. The missing ingredient is
the **dimensionful spacing rescaling** `b^k` (accumulated block factor) turning the
eroding lattice gap into the RG-invariant **dimensionless** margin `m_lat(a_k)/a_k`.

### The reconciliation the task asked for (numerically validated)

For `(lattice gap)·b^k → m_phys > 0` the lattice gap must decay **exponentially**
`~ b^{−k}`, **not** power-law. The construction doc's `1 − w_k³ ~ 3/k` (the
canonical AF *coupling* running `1−w ~ 1/k`) is power-law, so `·b^k` **diverges** —
confirmed in `validate.py`:

```
naive 1-w_k^3 (canonical AF):  k=10 → 0.2487   k=100 → 0.0294   k=1000 → 0.00299  (~3/k, power-law)
```

The **genuine** lattice mass gap is `m_lat·a = exp(−1/(2β₀g²)) ~ b^{−k}`
(EXPONENTIAL, because `1/g² ~ k`). That exponential is exactly the **self-similar
separator flow** `sep_k = e^{−(e^{-1})/(b+1)^k}` — and *that* is what transmutes.
This is the resolution: **transmutation lives in the exponential lattice gap, not
in the polynomial eigenvalue margin.**

---

## 2. The construction (concrete constructive-real)

Along a self-similar CReal flow `s : ℕ → CReal` (`sep k ≈ (sep(k+1))^(b+1)`), define
the **dimensionless margin**

```
dimMargin b s N  :=  (1 − s N) · ∏_{j=1}^{N} geomSumC(s j, b+1)
```

— the eroding lattice margin `1 − s N → 0` **times** the accumulated spacing
rescaling `∏ geomSumC ≈ (b+1)^N = 1/a_N`. This is the `m_lat(a_N)/a_N` the eigenvalue
margin lacked. (`geomSumC(x, b+1) = 1 + x + … + x^b`, the exact
`(1−x^{b+1})/(1−x)` factor; for `b=1` it is `1 + x`.)

The whole existing backbone (reused, not re-proved):
`CodynamicCRealFlow.marginInvariantC`, `.geomSumC`, `.cprodTail`,
`Constructive.SelfSimilarFlow.concreteTowerE`, `CodynamicCRealFlow.concreteCRealFlowE`.

---

## 3. What is PROVED (this module, all `[propext, Quot.sound]` or fewer)

| theorem | statement |
|---|---|
| `dimMargin_conserved` | `dimMargin b s N ≃ 1 − s 0` — **the transmutation identity** (from `marginInvariantC`) |
| `dimMargin_step_equiv` | `dimMargin b s N ≃ dimMargin b s (N+1)` (scale-invariant) |
| `scalarMul_le_add` | pure `Q'`: `0≤c≤1, 0≤a+ε ⟹ c·a ≤ a+ε` (the recursion engine, `[propext]`) |
| `scalar_le_self` | `0≤c≤1, geRat A 0 ⟹ leEv (c·A) A` |
| **`dimMargin_multiplicative_recursion`** | **`(1−δ_N)·dimMargin N ≤ dimMargin (N+1)`** (eventual order `leEv`), **∀ `0≤δ≤1`** — the recursion the lattice margin FAILED |
| **`uniformContinuumFloor`** | **`∃ c>0, ∀N, c ≤ dimMargin b s N`** — the uniform positive continuum floor |
| `*_concreteE` (4 thms) | all of the above **UNCONDITIONAL** along the irrational `e^{-1}`-seeded flow `concreteCRealFlowE 1` |

The concrete versions are unconditional because `baseMargin_posC_concreteE` and
`marginBudget_posC_concreteE` (the base UV margin `1 − sep 0 > 0` and per-scale
positivity, from the discharged `e^{−1} > 0`) are unconditional.

### Numeric validation (`validate.py`, mpmath dps 50), flow `b=1`, `sep_k = e^{−e^{-1}/2^k}`

```
 N   1-sepN(erode)    prodTail(resc)       dimMargin           |dimMargin-(1-sep0)|
 0     0.30779937          1.0             0.3077993724446536      0
 8     0.001435997         214.34541       0.3077993724446536      1.0e-50
32     8.565e-11           3.59e+9         0.3077993724446536      2.3e-42
64     1.994e-20           1.54e+19        0.3077993724446536      7.2e-33
128    1.081e-39           2.85e+38        0.3077993724446536      1.8e-13 (fp)

m_phys = 1 - sep_0 = 1 - e^{-1/e} = 0.30779937244465364613...
flow-law  sep_k = (sep_{k+1})^2  max err over k<40:  1.3e-51
```

The eroding lattice margin (→0) times the diverging rescaling (→∞) is the **constant
positive** `m_phys = 0.30780` at every scale (residual = pure float noise). This is
dimensional transmutation, exactly.

---

## 4. Adversarial verdict — is it genuine, or a relabeling that hides the exponential?

**Genuine, on three counts:**

1. **The spacing rescaling is REAL, not a free parameter.** `∏ geomSumC(s j, b+1)`
   is built from the block factor `b` (each factor `= 1 + s_j + … + s_j^b`, the
   exact finite-geometric term of the `b`-fold decimation) — it is `≈ (b+1)^N = 1/a_N`
   **because** the flow is self-similar with that same `b`. There is no dialed
   constant; `m_phys = 1 − s_0` **emerges** from the telescoping (`marginInvariantC`),
   it is not defended.

2. **The exponential is REAL and constructive, not hidden.** The separators
   `sep_k = e^{−(e^{-1})/(b+1)^k}` are genuine **irrational** constructive reals
   (`concreteTowerE`), and the flow law `sep k ≈ (sep(k+1))^(b+1)` — which **no
   rational flow can satisfy** (`polyFlow_not_selfSimilar`, decidable) — holds
   exactly (`concreteSelfSimilarFlowE`). **The exp-on-CReal / Λ = exp residual is
   discharged**: the lattice gap `1 − sep_k` really does decay exponentially, and the
   rescaling really does undo it.

3. **The transmutation captures the physics the eigenvalue margin missed.** The
   eigenvalue margin's failure was diagnosed as the missing `a_k` denominator; here it
   is supplied by `∏ geomSumC`, and the resulting object is conserved — the RG
   invariant. The power-law-vs-exponential reconciliation (§1) is the physical content.

**But it is the ZERO-DEFECT idealization — the honest limit of this construction:**

- `dimMargin` is **perfectly conserved** (`dimMargin N ≃ dimMargin (N+1)`), so
  `dimMargin_multiplicative_recursion` holds for **any** `0 ≤ δ ≤ 1`, including
  `δ ≡ 0`. That universality is precisely the **"multiplicative surrogate `ε ≡ 0`"**
  that `TrueMarginRecursionPhysical` (`CAPSTONE §3/§5`) flags as **evading** the real
  physics. The ideal self-similar flow has **no block-spin defect**; the real 4D SU(2)
  flow **deviates** from self-similarity, and that deviation is the **additive erosion
  `ε_k`** — the genuine open residual, untouched here.

So this module constructs the transmutation **mechanism** and proves the
multiplicative recursion is satisfiable by the **right** (dimensionless, conserved)
object — converting the construction doc's negative (`1 − w_k³` fails) into a positive
(`dimMargin` succeeds) — **without** closing the gap. The residual moves cleanly from
"the eigenvalue margin lacks the `a_k` denominator" to "the real block-spin flow's
deviation from the ideal self-similar flow is summable and anchor-dominated"
(`TrueMarginRecursionPhysical`).

---

## 5. Guard / STOP check (task condition (ii)) — nothing guarded inhabited

`dimMargin` is **`CReal`-valued** (the ideal irrational flow) — it is **NOT** the
rational `SingleStepDefectBound.trueMargin : ℕ → Q'`, **NOT** tied to `afDefectSeq`,
and does **NOT** map into `TrueMarginRecursion` / `UniformSpacingFloor` /
`FrontierDAG` / `ClayTarget(Pinned)` / `Tier0Scorecard`. Full build:

```
YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                 uninhabited across YMGap.*
Build completed successfully (691 jobs).
```

**The `ε ≡ 0` fake that WOULD trip the guard — deliberately refused.** A rational
**constant** surrogate `trueMargin := fun _ => c` with `0 < c < 1 − sep_0` trivially
satisfies the multiplicative `SingleStepDefectBound.singleStep`
(`(1−δ_k)·c ≤ c ⟺ δ_k ≥ 0`), hence would inhabit `SingleStepDefectBound →
TrueMarginRecursion`. That is exactly the `ε ≡ 0` surrogate the CAPSTONE warns
against; it is **not written** (Rule 9(1)). No cascade to any guarded bundle occurs.

`#print axioms` for all 11 load-bearing declarations: `[propext]`,
`[propext, Quot.sound]`, or empty (`leEv_of_equiv` depends on no axioms). No
`Classical.*`, no `native_decide`, no `sorry`.

---

## 6. Honest one-line verdict

The dimensional-transmutation kinematics are **constructed, machine-checked, and
axiom-clean**: the dimensionless margin `(1−sep_N)·(b+1)^N` is conserved to
`m_phys = 1 − sep_0 > 0` along a real irrational constructive-real self-similar flow,
satisfies the multiplicative single-step recursion the eroding lattice margin
provably failed, and carries a uniform positive continuum floor — with the exp-on-CReal
residual discharged. But it is the **zero-defect idealization**: the multiplicative
recursion holds for *any* defect, i.e. it is the `ε ≡ 0` surrogate, so the genuine
Clay residual — the **real 4D block-spin flow's additive deviation `ε_k` from
self-similarity, summable and anchor-dominated** (`TrueMarginRecursionPhysical`) —
remains open. **No guarded bundle is inhabited; nothing is faked; the 4D Yang–Mills
mass gap remains OPEN.**
