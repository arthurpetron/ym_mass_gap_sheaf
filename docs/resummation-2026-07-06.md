# The terminal resummation test — does (R1) resummation + (R2) a→0 renormalization reduce to the PROVED KP cluster bound + the PROVED field-space/AF renormalization, closing z_n?

**Deliverable Lean file:** `lean/YMGap/Continuum/TerminalResummationTest.lean` (wired into `YMGap.lean`;
full `lake build` **green = 714 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier types
unconditionally uninhabited). Numerics `resum_numerics.py` (mpmath dps 45, sympy exact). Commits: none.
MAIN tree, NEW file, Lean-core only (`Q'`/`Nat`, no Mathlib/`ring`/`native_decide`; axiom gate
propext/Quot.sound only).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean)

**The reduction FAILS. Neither (R1) nor (R2) closes. z_n is NOT fully constructed. No cascade to any
guarded bundle. The 4D Yang–Mills mass gap remains OPEN.**

The KP cluster bound and the AF/field-space renormalization are genuinely PROVED — but each is the
**wrong-side half** of its residual. They are the *consequences* of the resummation/renormalization
(given the resummed single-polymer activity `z_1 ≤ g²` and the renormalized continuum measure), not the
*producers* of it. The exact open seam is machine-located below. **This is the honest terminal outcome:
the free-field dodge was refuted, and now this closure attempt is refuted too — the residual survives
intact, sharply named.**

---

## 1. (R1) — THE RESUMMATION DOES NOT REDUCE TO THE KP CLUSTER BOUND

### The index gap (the decisive adversarial finding)

The two expansions carry **different organizing indices**, verified numerically (`resum_numerics.py`):

| expansion | index | growth | status |
|---|---|---|---|
| Isserlis **perturbative** series | order `k` in `g²` | **factorial** (radius 0, Dyson) | DETERMINED (Isserlis), asymptotic |
| KP **cluster** (Ursell) series | cluster size `n` | **geometric** `(μg²)^n` | PROVED bound `amplitude_le` |

- **Test 1** (zero-dim φ⁴ partition function `Z(g)=Σ a_k g^k`): `|a_{k+1}/a_k| = 0.73, 1.38, 2.03, 2.69,
  3.35, 4.02, 4.68, …` → ∞. **Radius of convergence 0** (Dyson). This is the DETERMINED-coefficient
  growth, indexed by ORDER `k`.
- The KP bound `|z_n| ≤ (μg²)^n` (`KPFieldAmplitude.amplitude_le`, combinatorially PROVED via
  Penrose/Cayley/Euler) bounds the connected Ursell amplitude indexed by CLUSTER SIZE `n`, and is
  **DRIVEN by the single-polymer activity `z_1 ≤ g²`** (`KPFieldAmplitude.SinglePolymerActivity`,
  `single_le_g2` field). It bounds the RESUMMED cluster amplitude *given* that `z_1` is already a finite
  number `≤ g²`. **It does not resum the order-`k` factorial series — it consumes the resummation's
  output.** The combinatorial scaffold (tree-graph domination) is proved; the analytic content — that the
  determined factorial series Borel-resums to the finite `z_1`, and that `z_1 ≤ g²` for the real
  non-Gaussian su(2)/Wilson activity — is exactly `pertRep` / `SinglePolymerActivity`, UNINHABITED.

### Machine-checked: the factorial series admits NO genuine resummation

`TerminalResummationTest.factorialSeries_no_genuineResummation` (axiom-clean) proves
`GenuineResummation dysonDiag → False`, where:

- `GenuineResummation diag` carries an honest **shrinking Cauchy modulus** `|diag K| ≤ 1/(m+1)` for
  `K ≥ order m` (forcing the terms to 0 = the partial sums to be Cauchy). This is the non-vacuous form of
  `IsserlisGaussianBase.PerturbativeResummation` (whose own docstring flags it as fakeable by a large
  constant tolerance, Rule 9(6)). `increment_eq_coeff` proves the coefficient `diag K` IS the partial-sum
  increment (faithfulness to `PerturbativeResummation` via `feynTrunc_increment`).
- `dysonDiag k = (k+1)!` models the factorial growth of the DETERMINED Isserlis coefficients.
  `dysonDiag_ge_one`: every term `≥ 1`.
- Refutation: `GenuineResummation` at `m=1` would force `|dysonDiag K| ≤ 1/2`, but every term is `≥ 1 >
  1/2`. So the determined factorial coefficients do **not** resum by any Cauchy modulus — a
  Borel/nonperturbative prescription is required, which the KP combinatorial scaffold does NOT supply.
- Contrast `freeDodge_genuineResummation`: the zero sequence DOES resum trivially. So the residual is
  genuine **only for the physical (Isserlis-determined, factorial) coefficients** — exactly the
  determination-vs-resummation split (`isserlis_refutes_free_dodge`).

### The single-mode toy is not the real activity (why `ExactSinglePolymerActivity` does not close R1)

`ExactSinglePolymerActivity.z1Exact_leRat_g2` proves `z_1 = 1 − e^{−t}(1−2t) ≤ g² = 4t` to all orders.
But **Test 2**: this single-MODE Gaussian `z_1` is an **entire** function of `t` (Taylor coeffs `3, −2.5,
1.17, −0.375, … ` DECAY) — its series CONVERGES; it has no factorial problem. The real 4D su(2)/Wilson
single-polymer activity carries the full non-Gaussian loop structure where the Dyson factorial growth
lives. Moreover the theorem proves the LOOSER `z_1 ≤ g² = −log w`, not the `z_1 ≤ 1−w` that
`SinglePolymerActivity.z1_le_g2` demands (**Test 3**; numerically the tighter also holds, ratio → 3/4, but
it is not the theorem proved). So `ExactSinglePolymerActivity` inhabits **no** KP structure — confirmed by
its own honest-scope docstring.

**(R1) verdict: does NOT close.** The KP bound is the RIGHT half (cluster → geometric convergence, given
`z_1`); the LEFT half (factorial order-`k` series → finite `z_1 ≤ g²` for the real activity) is
`SinglePolymerActivity`/`pertRep`, UNINHABITED, and `GenuineResummation` of the factorial series is PROVED
uninhabitable.

---

## 2. (R2) — THE a→0 RENORMALIZATION IS CONDITIONAL ON THE (UNINHABITED) INTERACTING CONTINUUM MEASURE

- The AF running `g² → 0` is PROVED only for the **canonical toy trajectory** `w_k = 1 − 1/(k+1)`
  (`AFBetaStepCanonical.betaStep_canonical`; its own docstring: the REAL 4D block-spin flow obeying the
  two-loop rate is the open physical content). The field-space activity `1−w → 0` is PROVED
  (`FieldSpaceCluster`). **Test 4**: `μ(1−w) = 0.6, 0.06, 0.006` as `w = 0.9, 0.99, 0.999` — the KP cluster
  SUM improves, as claimed.
- **But** the a→0 limit of the RESUMMED interacting `z_n` as a renormalized continuum amplitude is
  `ContinuumFieldMeasure.InteractingContinuumMeasure` — UNINHABITED. `TerminalResummationTest.terminal_zAmp_free`
  (re-export of `interacting_zAmp_free_dodge`) proves its `z_n` is a **FREE field**: `zAmp ≡ 0` inhabits the
  letter (Gaussian free field, no interaction). `terminal_amplitude_conditional` proves the full amplitude
  bound `|z_n| ≤ (μg²)^n` flows from the interacting measure but as a **CONDITIONAL producer with an open
  binder**. Plugging `g² → 0` into the fixed-`a` bound does NOT construct the renormalized continuum
  covariance (the non-abelian wavefunction/coupling renormalization).

**(R2) verdict: does NOT close.** AF/field-space give the RIGHT half (coupling → 0, cluster sum improves);
the LEFT half (fixed-`a` resummed `z_n` → renormalized continuum amplitude) is `InteractingContinuumMeasure`,
UNINHABITED, `z_n` free.

---

## 3. THE DECISIVE CHECK — z_n is NOT fully constructed

z_n is DETERMINED at finite order (Isserlis, PROVED) and BOUNDED above by the PROVED KP scaffold, but its
full value requires BOTH:
- **(R1)** the resummation of the factorial series to the finite `z_1 ≤ g²` — `SinglePolymerActivity` /
  `pertRep`, UNINHABITED; `GenuineResummation dysonDiag` PROVED uninhabitable;
- **(R2)** the a→0 renormalized interacting measure — `InteractingContinuumMeasure`, UNINHABITED, `z_n` free.

Neither is a proved piece. **z_n stays underdetermined (bounded, not constructed).** No `zAmp` value is
produced unconditionally.

---

## 4. Cascade / STOP audit (mandatory — this is the mass gap)

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

- The new module proves theorems ABOUT the resummation seam and re-exports the CONDITIONAL amplitude
  producer. It inhabits NONE of the 5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`,
  `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) — the frontier chain to `FrontierDAG.trueMargin` is NOT
  reached. It produces NO unconditional inhabitant of `SinglePolymerActivity`, `InteractingContinuumMeasure`,
  or `GenuineResummation dysonDiag` (the latter PROVED uninhabitable). Full build:
  `frontier-guard OK: 5 … unconditionally uninhabited`, **714 jobs** (713 → 714 = the +1 module).
- Because z_n is NOT fully constructed (§3), the STOP-and-exhaustively-audit condition of the task
  (triggered only if z_n cascades to a guarded bundle) is **not** met. There is nothing to stop on: the
  attempt to close via the proved KP + AF pieces is refuted at the named seam.

**`#print axioms`** for all 7 load-bearing decls ∈ {∅, `[propext]`, `[propext, Quot.sound]`}. Axiom-free:
`increment_eq_coeff`, `fact_pos`. No `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit`.

---

## 5. Numeric validation (`resum_numerics.py`, mpmath dps 45, sympy exact) — ALL PASS

1. Perturbative coeffs `a_k` of `Z(g)`: ratios `→ ∞` (factorial, radius 0 — Dyson). Index = ORDER `k`.
2. Single-mode `z_1 = 1 − e^{−t}(1−2t)`: entire (Taylor coeffs decay); `z_1 ≤ 4t` for all `t∈(0,4)`,
   0 violations, worst ratio 0.749 (→ 3/4).
3. Direction gap: proved `z_1 ≤ −log w` vs needed `z_1 ≤ 1−w`; `z_1/(1−w) → 3/4`.
4. KP geometric `μ(1−w) = 0.6/0.06/0.006` at `w=0.9/0.99/0.999`: cluster SUM converges, indexed by `n`.

---

## 6. What is PROVED in Lean-core (`TerminalResummationTest.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `GenuineResummation` | honest shrinking Cauchy modulus `\|diag K\| ≤ 1/(m+1)` (non-vacuous R1 form) | — |
| `increment_eq_coeff` | coefficient = partial-sum increment (faithfulness) | none |
| `fact_pos` | `(n)! > 0` | none |
| `dysonDiag_ge_one` | every Dyson term `≥ 1` | propext |
| **`factorialSeries_no_genuineResummation`** | **the factorial series admits NO genuine resummation** | propext |
| `freeDodge_genuineResummation` | free dodge trivially resums (Rule 9(6) contrast) | propext |
| `terminal_amplitude_conditional` | KP bound flows from interacting measure (CONDITIONAL) | propext, Quot.sound |
| `terminal_zAmp_free` | interacting `z_n` is a FREE field (`zAmp ≡ 0` inhabits) | propext, Quot.sound |

---

## 7. HONEST FINAL VERDICT

The terminal test is **negative, precisely and machine-checkedly**. The KP cluster bound and the
AF/field-space renormalization are PROVED, but they sit on the *output* side of each residual:

- **(R1)** the KP bound bounds the cluster amplitude `z_n` (index `n`, geometric) GIVEN the finite
  single-polymer activity `z_1 ≤ g²`; the Isserlis-determined perturbative series (index `k`, factorial,
  radius 0) does NOT reduce to it — `factorialSeries_no_genuineResummation` proves the determined factorial
  coefficients admit no Cauchy-modulus resummation, so the reorganization asymptotic→cluster needs a
  Borel/nonperturbative prescription (`SinglePolymerActivity`/`pertRep`) the scaffold does not supply. The
  single-mode Gaussian `z_1` that IS resummable is an entire toy, not the real su(2)/Wilson activity.
- **(R2)** AF gives `g² → 0` (toy trajectory) controlling the cluster SUM; the a→0 renormalized continuum
  amplitude is `InteractingContinuumMeasure`, UNINHABITED, `z_n` free.

**z_n is DETERMINED (finite order) + BOUNDED (KP), but NOT CONSTRUCTED.** No guarded frontier bundle is
inhabited; the free-field dodge is refused; `GenuineResummation dysonDiag` is PROVED uninhabitable; nothing
is faked; the 4D Yang–Mills mass gap remains OPEN. The exact remaining residual is the pair
{**(R1)** Borel/nonperturbative resummation of the factorial series to `z_1 ≤ g²` for the real non-Gaussian
activity ; **(R2)** the a→0 renormalized interacting continuum covariance}.

---

## 8. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (714 jobs).
```

`TerminalResummationTest.lean`, 7 load-bearing decls, `#print axioms ∈ {∅, [propext], [propext,
Quot.sound]}`. Lean-core only; reuses PROVED `IsserlisGaussianBase.feynTrunc`/`feynTrunc_increment`,
`KPFieldAmplitude`, `ContinuumFieldMeasure`, `InteractingMeasureReduction`, `TreeGraphBoundProgress.ofNat_le_ofNat`,
`Q'.abs`/`le_abs_self`, `Q'.invSucc`. All witnesses `Type`-level.
