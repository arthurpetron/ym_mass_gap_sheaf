# Q'-vs-CReal representability audit of every open frontier atom

**Date:** 2026-07-08
**Scope:** one-pass batch review of every open Clay-frontier atom, asking of each: is the
**physical/mathematical object** it stands for representable at the **precision level** of
its current Lean type? The precision levels are:

- **Q'** — exact rational (finite character sums, combinatorial counts, rational
  inequalities, dimension-weighted `6j²`, signed integer telescopes);
- **CReal** — constructive real (irrationals: `θ₄`, `exp`, `√`, a genuine `6j = Q'·√Q'`,
  a convergent-series/product *limit* or *equivalence*, a self-adjoint operator, `−log`);
- **interval / rational-bracket** — the object is irrational but the atom needs only a
  *certified rational bound* on it (alternating-series Leibniz bracket, majorant).

**Why this audit exists.** The `SixJPentagon` refutation established the failure mode: an
atom whose physical content is **signed irrational data** (`Q'·√Q'`, the genuine Wigner
`6j`) was typed with a `Q'` kernel and demanded an exact rational equality to it — making
the type uninhabitable *for the wrong reason* (a representability bug, not depth). This
pass checks whether any surviving open atom carries the same latent bug.

---

## Methodology

For each atom I read the Lean `structure`/`def`, identified (a) the physical object, (b) its
intrinsic precision, (c) the atom's current Lean type precision, and applied the verdict:

- **OK** — type precision ≥ object precision, *and* the atom does not demand an exact
  rational equality to a genuinely irrational value.
- **MISMATCH (hard)** — type is `Q'` but the atom demands equality/kernel-membership for a
  genuinely irrational/signed-`√` object → latent SixJPentagon-style uninhabitability.
- **MISMATCH (soft / fidelity)** — type is self-consistently `Q'`, but the *physical*
  object it claims to measure is irrational (`√Q'`), and the majorization/identification
  bridge from the rational surrogate to the real object is implicit, not proved.

The decisive discriminator for a **hard** mismatch is the pattern
`field : (rational expr) .eqv (genuinely irrational value)`. I grepped every open-atom
`structure` field for `.eqv`/`Equiv` against `sqrt`/`CReal`/irrational constants: **no
open-atom field demands `eqv` to a bare irrational.** The only atom whose open content is a
`CReal.Equiv` is `DiffJTP`, which is correctly *typed* at `CReal`.

---

## The audit table

| # | Atom (field / residual) | Physical / math object | Req. precision | Current Lean type | Verdict |
|---|---|---|---|---|---|
| 1 | `bulkCtrl` — `SpectralLocalization.bulk_shift` | bulk eigenvalue-shift ≤ 1/12 on bond-moved transfer spectrum | Q' (bound) | `Q'` (`eig'`,`shift`,`eigA=w^{C₄}`) | **OK** (surrogate spectrum, see §A) |
| 2 | `singleStep` — `SingleStepDefectBound.singleStep` | per-step true-margin defect `(1−δ)·m_k ≤ m_{k+1}` | Q' (rational floor) | `Q'` (`trueMargin:ℕ→Q'`) | **OK** (see §B) |
| 3 | `tTree` (T′) — `TreeGraphBound.tree_graph` | Penrose spanning-tree `|φ^T(Y)| ≤ e^{|Y|}` | Q' (`e`←3 surrogate) | `Q'` | **OK** |
| 4 | `d1Mayer` (D1) — `BridgeDecomposition.decompose` | absolute Mayer–Ursell cluster expansion | Q' (finite sums) | `Q'` | **OK** |
| 5 | `d2Sep` (D2) — `SepLatticeZ4` | plaquette-graph BFS metric (inhabited DATA) | Nat/Q' | `Type` (metric data) | **OK** |
| 6 | `UrsellPinConst` | Ursell↔graph identity `n!·|φ^T| = |C(adjGraph)|` | Q'/Int (combinatorial) | `Q'`/`Int` | **OK** |
| 7 | Cayley (C) / `CubicEulerBound` (A) | `treeCount ≤ n^{n−2}`, `(1+1/n)^n ≤ 3` | Q'/Nat | `Q'`/`Nat` | **OK** |
| 8 | `a2Racah` (A2-L1) — `RacahProb` | dim-absorbed **rational** Racah prob `P=(2e+1)(2f+1){6j}²` | **Q'** | `Q'` kernel | **OK** — the SixJ fix (see §C) |
| 9 | `a2Pentagon` (A2-L2) — `PentagonNumericCore` | fractional pinning `P(smallestTetra)=1/4` | **Q'** | `Q'` (`.eqv 1/4`) | **OK** (see §C) |
| 10 | `CoupledCreativeTelescoping` (=`guardedBEDougall`) | dim-absorbed **rational** Biedenharn–Elliott sum rule | Q'/Int | `Q'` (`.eqv` rational) | **OK** (see §C) |
| 11 | `SliceInnerCollapse` | guarded rational Racah slice = signed-`Int` telescope | Q'/Int | `Q'` (`.eqv` `ofInt`) | **OK** |
| 12 | streaming normaliser — `RingNormaliser` | integer/rational polynomial (Vandermonde/Saalschütz) identities | Q'/Int | `Int` kernel | **OK** (residual = rational-fn identities, still Q') |
| 13 | `coreB` — `FiniteSMargin.margin` | finite-`s` θ-autoconvolution margin ≥ rational floor `40000/22801` | **Q'** (finite trunc.) | `Q'` (`acN`) | **OK** (see §D) |
| 14 | `UniformCurvatureEnvelope` — `CurvatureEnvelope` | R1 curvature `Δ²V+2 ≥ (144/25)w²(1−w²)` | **Q'** (finite `acNfull`) | `Q'` (Prop) | **OK** (see §D) |
| 15 | `Theta4QuarterAnchor` (PROVED) | `θ₄(1/4)⁴ ≤ 7/100` — irrational value, rational **bound** | interval/bracket | `Q'` alt-series bracket | **OK** — correct constructive bracket (see §E) |
| 16 | `edgeShift` — `EdgeShiftResidual` (`hId`,`hLin`) | `s=1` eigenvalue-shift ↔ bond-moving defect dictionary | Q' (bound) | `Q'` | **OK** (surrogate, §A) |
| 17 | `hadd` — `SpectralMarginInput.hadd` | located-2nd-eigenvalue ↔ physical-margin dictionary | Q' (bound) | `Q'` (`floorRate/spacing`) | **OK** (surrogate, §A) |
| 18 | `trueMargin` — `TrueMarginRecursion` | dimensionless margin `m_lat(a_k)/a_k` recursion | Q' (rational floor) | `Q'` (`trueMargin:ℕ→Q'`) | **OK** (§B) |
| 19 | `boundedH` — `BoundedFunctionalCalculusResidual` | self-adjoint additive `H`, `e^{−H}=T`, gap `Δ=−log sep` | **CReal** | **`CReal`** (`RC`,`cinner`,`IsPositive`) | **OK** — correctly CReal (see §F) |
| 20 | `o4` — `CouplingRunning` | RG coupling flow + AF β-sign `β(g_k) ≤ 0` | Q' (β-sign is rational ineq) | `Q'` (`g`,`betaDrop`) | **OK** (surrogate, §A/§B) |
| 21 | **ε_k summability** — `EpsilonSummability` | `Σ_k |√χ_blk(2,2) − √χ_fine(2,2)| < ∞` | **√Q' (CReal) object** | `Q'` surrogate `bondMovingDelta(Ren)` | **SOFT MISMATCH** (see §G) |
| 22 | `DiffJTP` | differentiated Jacobi-triple-product `Σ n a^{n²} sin nθ = (½ sinθ)ϑ₃ S` | **CReal** | **`CReal.Equiv`** | **OK** — correctly CReal (see §F) |
| 23 | `BulkCtrlToHlocalizeBridge` (DAG bridge) | per-mode → per-scale localization | Q' (both sides surrogate) | `Type` (function) | **OK** |
| 24 | `CoreBBridge` (DAG bridge) | `FiniteSMargin w → CrossRatioMonotone w` | Q' | `Type` (function) | **OK** |
| 25 | `general_be` — `BiedenharnElliottGeneral` | genuine **signed** `6j = Q'·√Q'` recoupling identity | **CReal (√Q')** | **`CReal`/`sqrtPos`** | **OK** — the anti-SixJ (see §C) |

Guard-protected **bundle** types (`Tier0Scorecard`, `UnifiedContinuumFloor.UniformSpacingFloor`,
`ClayScorecard.ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) are products whose precision is
the max over their member atoms above; they carry no representability content of their own.
`UniformSpacingFloor`/`QFloor` are `Q'` bundles (a rational `floor` + a `≤` inequality) — OK.

---

## MISMATCHES

### Hard mismatches (latent SixJPentagon-style uninhabitability): **NONE**

No open atom demands an exact rational equality to a genuinely irrational value. The SixJ
lesson is **fully absorbed** across the whole frontier:

- the **genuine signed 6j** (`Q'·√Q'`) lives at **CReal** via `sqrtPos`/`extract3` in
  `BiedenharnElliottGeneral` (atom #25) — exactly the representation SixJ got wrong;
- every **Q'-typed 6j atom** (#8 `RacahProb`, #9 `PentagonNumericCore`, #10 `guardedBEDougall`,
  #11 `SliceInnerCollapse`) carries only the **dim-absorbed square** `P = dim·dim·{6j}²`,
  which is provably **rational** (the square of a `Q'·√Q'` is `Q'`), and the pinning value
  `P(smallestTetra) = 3·3·(1/6)² = 1/4` is an exact rational — so `Q'` is correct, not a bug.

### Soft mismatch / fidelity flag (1): **ε_k summability** (atom #21)

`EpsilonSummability` is the binding `Σε_k < ∞` linchpin. The **physical** leakage it targets
is the matched estimator `ε_k = |√χ_blk(2,2) − √χ_fine(2,2)(β_p)|` — a **difference of square
roots of character sums**, i.e. genuinely **signed `√Q'` (CReal) data**. The **typed** Lean
summand is the *rational* character-coefficient surrogate `bondMovingDelta` /
`bondMovingDeltaRen` (`epsBare ≤ 6p(1−w)` linear, `epsRen ≤ 6p(1−w)²` quadratic). The
`Q'`-typed summability question (harmonic-divergence vs Basel-convergence) is internally sound
and correctly typed *for the surrogate*, but the **bridge** "character-coefficient deviation
majorizes the `√χ`-level deviation" is **implicit, not a Lean theorem**. This is not an
uninhabitability bug (nothing demands `eqv` to a `√`), but it is the one place where a
genuinely `√Q'` physical object is being tracked by a rational proxy without a proved
majorant. **Recommended fix:** state and prove `|√χ_blk − √χ_fine| ≤ bondMovingDeltaRen …`
(a CReal-to-Q' majorant lemma) so the summability of the rational bound actually implies
summability of the physical `ε`. Until then, treat #21's `Q'` typing as a **surrogate**, and
the `√χ`-to-coefficient step as an unlisted open sub-obligation.

### Pervasive surrogate-spectrum caveat (§A): not a mismatch, but note it

Atoms #1 `bulkCtrl`, #16 `edgeShift`, #17 `hadd`, and the floor `heatKernelMargin w = 1 − w³`
model the **real transfer-operator spectrum** by *rational character monomials*
(`eigA w s = w^{C₄(s)}`, gap edge `w³`). The physical heat-kernel eigenvalues are irrational.
`Q'` is adequate to hold these surrogates and the atoms only ever assert **inequalities**
(bounds), never equalities to the real spectrum — so there is no representability bug. The
genuine identification "rational surrogate = physical spectrum" is itself open **reconstruction
content**, and it is carried at the **correct** precision (`CReal`) exactly where an exact
spectral object is needed: `boundedH` (#19, `cinner`, `−log sep`, `IsPositive`). So the split
is principled: rational surrogate for the *bounds*, CReal for the *object*.

---

## Notes keyed from the table

- **§A (surrogate spectrum)** — see the pervasive caveat above. Verdict OK; the surrogate is
  bound-only, and the real spectral object is CReal-typed in `boundedH`.
- **§B (rational floor for a real ratio)** — #2/#18/#20: the physical margin/coupling is real,
  but each atom only needs a **rational lower floor** `> 0` to force gap-positivity; a rational
  floor is the correct constructive target (`decide`-friendly, `> 0`). OK.
- **§C (the 6j fix, cross-referenced to SixJ)** — the Wigner `6j` is `Q'·√Q'` (signed
  irrational). Its **square**, and hence `P = dim·dim·{6j}²`, is **rational**. All Q'-typed
  recoupling atoms carry `P` (or its Biedenharn–Elliott/Saalschütz consequences), never the
  bare `6j`; the bare signed `6j` is at CReal (`BiedenharnElliottGeneral`, atom #25). This is
  precisely the corrected design after the SixJ refutation. OK.
- **§D (finite rational truncation of a θ-limit)** — #13/#14: the *limiting* object
  (`L_even(w)`, the θ-autoconvolution variance/curvature) is irrational, but the atoms are
  stated on **finite rational autoconvolutions** `acN`/`acNfull` compared to a **rational**
  floor. Each instance is a rational inequality; the difficulty is **uniformity in `s`**, not
  representability. OK.
- **§E (rational bracket of an irrational)** — #15: `θ₄(1/4)⁴` is irrational, but the anchor
  only certifies a **rational upper bound** `≤ 7/100` via an alternating (Leibniz) partial-sum
  bracket. This is the textbook constructive way to bound a CReal by a `Q'`; the value is
  never claimed rational. OK — and note this is *better* than typing it CReal, since a bound
  is all downstream needs.
- **§F (correctly CReal)** — #19 `boundedH` (self-adjoint `H`, `e^{−H}=T`, `Δ=−log sep`) and
  #22 `DiffJTP` (a `CReal.Equiv` between a heat-kernel series and a differentiated θ-product)
  are the two genuinely CReal-precision open objects, and both are typed at CReal. OK.
- **§G (ε_k)** — see the soft-mismatch entry.

---

## Honest verdict

**Are all open atoms typed at adequate precision?** — With **one soft exception**, yes.

1. **No hard representability mismatch survives.** No open frontier atom repeats the SixJ bug:
   none demands an exact rational equality to a genuinely irrational/`signed-√` value. The
   signed `6j` is CReal; the Q'-typed `6j` atoms carry only the rational dim-absorbed square;
   `θ₄`, `exp`, `−log`, and the differentiated θ-product are all CReal or correctly rational-
   bracketed. The codebase has demonstrably internalized the SixJ lesson.

2. **One soft (fidelity) mismatch — `EpsilonSummability` (#21).** The physical `ε_k` is a
   difference of square roots (`√Q'` / CReal), but the typed summability object is a rational
   character-coefficient surrogate, with the majorization bridge unproved. This is the single
   representability *risk* on the list — not a broken type, but an unlisted CReal→Q' majorant
   obligation hiding under a `Q'` surrogate. It sits on the **binding** a→0 wall, so it is the
   highest-value item: **add and prove `|√χ_blk − √χ_fine| ≤ bondMovingDeltaRen`** to make the
   rational summability genuinely control the physical leakage.

3. **A principled surrogate-spectrum pattern (not a bug).** The transfer spectrum is modeled
   throughout by rational monomials for the *bounds*, while the exact spectral object is CReal
   in `boundedH`. This is the right precision split; the surrogate→physical identification is
   correctly carried as open reconstruction content, not silently rational-ized.

**Bottom line:** the frontier is precision-clean except for the ε_k √χ-vs-rational fidelity
gap. The batch pass found **0 latent SixJPentagon-style refutations** and **1 majorant
obligation to make now** (the ε_k CReal→Q' bridge). The Clay problem remains OPEN; nothing in
this audit closes or fakes any atom.
