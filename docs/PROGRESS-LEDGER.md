# Forward-Progress Ledger — YM mass-gap solve

**Purpose.** Measure genuine forward progress toward the *solve* and detect
mathematical-theory **loops** (re-deriving the same irreducible obligation from a
new angle). Run `bash computations/progress_metric.sh` each iteration.

## The metric (three counters + a status ladder)

| Symbol | Meaning | Moves how |
|---|---|---|
| **D** | Critical-path obligations **DISCHARGED** (a load-bearing type newly inhabited axiom-clean **and the frontier guard drops below 5**). | **TRUE NORTH.** Solve done when the goal obligation is discharged. |
| **F** | Distinct **OPEN** obligations *not provably equivalent* to the current core. | Shrinks on discharge; may split (a real reduction) into strictly-weaker pieces. |
| **C** | **Confirmation aliases** `X := SingleStepDefectBound`. | A **LOOP counter.** C++ with no change to F or D = a loop. |

**singleStep status ladder** (the whole continuum gap is proved conditional on it):
0 conjectured → 1 numerically verified TRUE → 2 decomposed into strictly-weaker
sub-obligations → 3 sub-obligations discharged → 4 fully proved (guard breaks).

## Baseline (commit 05ae807, 2026-07-07)

- **D = 0** — nothing on the critical path is discharged; guard = 5 (intact).
- **F = 3** — `{ uniform_in_m_variance_monotonicity, channel_feedback, real_defect_identification }`.
- **C = 14** — fourteen modules reduced to `singleStep`.
- **singleStep at status 2** (verified true, safety factor 45; decomposed — but two of
  the three pieces are UNVERIFIED as strictly-weaker).

## What this reveals (honest)

The `C=14` is the loop, quantified. Roughly the last ~20 agent-rounds each applied a
new tool (curvature, OS/confinement, RG, OPE, reflection positivity, Simon–Lieb,
Schwinger–Dyson, Wetterich, instanton, MK, Birkhoff, …), and each ended by emitting a
`… := SingleStepDefectBound` alias — i.e. **re-deriving the same obligation**. Those
rounds produced genuine *side* theorems and a genuine *obstruction map* (real value),
but they did **not** move D and did **not** shrink the hard core.

**Genuine forward moves that DID happen** (these are the template for what counts):
1. The whole continuum gap became conditional on `singleStep` *alone* (F: many → 1).
2. `singleStep` moved 0 → 1 (numerically **verified true**, safety factor 45, via the
   `m`-fold concentration — refuting the old "linear-in-`m`" wall).
3. `singleStep` moved 1 → 2 (**decomposed**), and one piece (uniform-in-`m`) reduced to
   a single-functional statement `Var_m(cosθ) ≤ Var_2` that is genuinely strictly weaker.

## ADJUDICATION (2026-07-07, `SingleStepDecompositionAdjudication.lean`): the decomposition was FAKE — **F = 1, atomic core**

Machine-checked verdict (build 744, guard OK, axiom-clean; **no new alias — C accurate = 18**):
- **`channel_feedback` = DEFINITIONAL ALIAS** of `singleStep` (`channelFeedback_iff_singleStep := Iff.rfl`).
- **`real_defect_identification` = LOGICALLY EQUAL** (bi-implication proved; the model defect is
  itself a legal witness, so it adds nothing).
- **`uniform_in_m` = strictly weaker but proved NOT core-shrinking** — it is `afr`/fusion-only and
  never mentions the free margin `tm`; `singleStep`'s truth varies with `tm` at fixed `afr`
  (`singleStep_satisfiable_zero` / `singleStep_falsifiable`), so no `afr`-only statement implies it.
- `decomposition_collapses_to_singleStep` derives `singleStep` using ONLY the alias conjunct.

**Consequence:** `singleStep` is **atomic beyond `uniform_in_m`**. Honest **F = 1**. Closing
`uniform_in_m` (which itself reduces to the open local-CLT wall `FusionConvLogConcaveCore`) is a
genuine partial result that does **not** shrink the hard core. **No strictly-weaker reduction
below `singleStep` is known** — every prior "tool" (MK, Birkhoff, Simon–Lieb, RG-flow, multiscale
polymer, Wetterich, instanton, OPE, …) reduces *to* it (C = 18 aliases), never below.

**The only honest remaining moves:** (a) prove atomic `singleStep` directly = construct/bound the
real 4D block-spin per-step defect over the full RG recursion (the foundational constructive
continuum-limit problem); or (b) discover a genuinely-new strictly-weaker reduction (none known).
Both are legitimate under the anti-loop rule; **spawning any further tool that reduces to
`singleStep` is now a provable loop and is forbidden.**

## Critical-path DAG (proved reductions ⇒, open leaves in **bold**)

```
mass_gap  ⇐  rgFlow_gap_conditional ∧ MultiScalePolymerExpansion  (PROVED assembly)
          ⇐  additiveErosion_uniform_floor  (PROVED: floor given summable defect + anchor-dominance)
          ⇐  singleStep : realδ_k ≤ 6(1−w_k)²   (status-2 core)
                 ├─ **uniform_in_m_variance_monotonicity**  (Var_m(cosθ) ≤ Var_2 ; STRICTLY WEAKER — attackable)
                 ├─ **channel_feedback**       (s≥2 → next-scale s=1 ; NOT YET shown strictly weaker)
                 └─ **real_defect_identification** (real 4D block-spin defect = fusion object ; NOT YET shown strictly weaker)
```

## DIRECT-CONSTRUCTION increment (2026-07-07, `PushedReconTransferGap.lean`)

Front (a) — direct construction of the real defect — made genuine progress (deliverable
class (ii)+(iii); build 753, guard OK, axiom-clean, C=18 unchanged, no alias):
- **Proved range EXTENDED** `[0, 1/2] → [0, 2^{−1/3})`: `reconTransfer_located_gap_gen`
  removes the `w ≤ 1/2` gate — the real reconstructed single-edge transfer margin
  `reconMargin w = 1 − 2w³` (the genuine Wilson correlator gap, `wilsonG_eqv_reconTransfer_corr`,
  not a model) has a located gap for every `w` with `rho w = 2w³ < 1`. Concrete witness
  `w₀ = 0.793` (`reconMargin ≈ 0.00265 > 0`), within `7×10⁻⁴` of the character radius.
- **Residual pinned SHARP** (`located_gap_window_sharp` + `no_located_gap_above_ceiling`):
  the single-edge located-gap window is EXACTLY `[0, 2^{−1/3})`; for every `w ≥ 2^{−1/3}`
  the reconstructed operator has **no** located gap (`rho ≥ 1`). The AF flow drives
  `w_k → 1` across `w*`; the `[2^{−1/3}, 1)` window provably needs the interacting
  **multi-plaquette block-spin effective action** (the unconstructed `a→0` object). A
  physical ceiling (the character/strong radius), not a proof weakness.

So the exact remaining obstruction is now: **construct a located transfer gap on
`[2^{−1/3}, 1)` via the multi-plaquette effective action** — the sharpest statement yet
of the atomic core's analytic content.

## MULTI-PLAQUETTE increment (2026-07-07, `MultiPlaquetteEffectiveTransfer.lean`)

Front (a) — the `[w*,1)` residual above — CONSTRUCTED (deliverable class (ii)+(iii);
full build GREEN 754 jobs, guard OK at 5, axiom-clean `[propext(,Quot.sound)]`, C=18
unchanged, NO alias):

- **Multi-plaquette (block-spin renormalized) effective transfer BUILT** (`effTransfer`):
  degeneracy `dimQ r` moved from the eigenvalue (`reconTransfer`'s `2w³`, degeneracy
  compounding per link) into the **multiplicity/amplitude**, so the per-step rate is the
  resummed heat-kernel ratio `w^{C₄(r)}` — leading `μ_1 = w³ = heatKernelSep w`, exactly
  the codebase's documented "genuine gap" separator.
- **Gap bounded on the ENTIRE `[w*,1)`** (`effTransfer_located_gap`, PROVED): for every
  `0<w<1`, located gap with `sep = w³ < 1` (`heatKernelSep_lt_one`), margin `1−w³>0`.
  Clustering `eff_corr_cluster` proved from scratch. Concrete PROVED witnesses at
  `w = 4/5, 9/10, 99/100` (all ABOVE `w*`, where `reconTransfer` has NO gap): margins
  `0.488, 0.271, 0.0297`.
- **Crossover matched** (`resummation_is_the_residual`): `rho w = dimQ 1 · effLam 0 = 2w³`
  exactly; single-edge closes at `w*` (`2w³=1`), resummed open (`w³=1/2`). Consistency
  `eff_corr_le_recon_corr`: resummed is the lower correlator envelope.
- **Residual pinned** (`fullWindow_gap_of_resummed_clustering`, conditional producer, NOT
  a `singleStep` alias): the sole open identification is the **degeneracy-resummation** —
  that the real block transfer clusters at rate `w^{C₄}` (once) vs `dimQ·w^{C₄}` (per link),
  numerically the factor `dimQ 1 = 2` (`2w³` vs `w³`). This is the sharp, numerically-pinned
  form of the atomic `singleStep` core. Deliverable: `job tmp/multiplaquette.md`.

## RESUMMATION-RESIDUAL ADJUDICATION (2026-07-07, `ResummationAdjudication.lean`): EQUI-INHABITS — **F = 1 stands**

Machine-checked verdict (full build GREEN 755 jobs, guard OK at 5, axiom-clean `[propext(,Quot.sound)]`;
**no new alias — C unchanged = 18**). Adjudicates the multi-plaquette conditional producer's hypothesis
(`fullWindow_gap_of_resummed_clustering`), formalized precisely as `ResummedClustering S w` (the real block
correlator clusters at the resummed rate `w³` not the per-plaquette `2w³`):

- **DIRECTION A (producer, PROVED):** `gap_of_resummedClustering : ResummedClustering S w → LocatedSpectralGap S`,
  margin `1 − w³ > 0` on all `(0,1)`. Non-vacuous: the model `effTransfer` inhabits it (`resummedClustering_effTransfer`).
- **NON-FREE (PROVED refutation — the physics check):** `reconTransfer_not_resummedClustering` — the naive
  per-plaquette (degeneracy-compounding) REAL single-edge / Wilson correlator VIOLATES `ResummedClustering`
  (leading eigenvalue `coeffW w 1 = dimQ 1·w³ = 2w³ > w³`). So the resummed rate `w³` is NOT a free
  heat-kernel fact; attaining it is the genuinely INTERACTING block-spin resummation — the same content as
  `singleStep`'s `realδ ≤ δ_model`. `resummation_gap_is_dimQ` (axiom-free) pins the gap to the factor `dimQ 1 = 2`.
- **INCOMPARABLE to `singleStep` (PROVED, `tm`-independence):** `ResummedClustering` is transfer-side/single-scale
  and never mentions the free margin `tm`; `singleStep`'s truth varies with `tm` at fixed `afr`
  (`singleStep_satisfiable_zero`/`_falsifiable` reused). Exactly as for `uniform_in_m`, no transfer-side statement
  implies/equals `singleStep` — it is NOT a strictly-weaker sub-obligation below the core.
- **DOES NOT bypass `singleStep` (PROVED, decidable):** `resummed_margin_not_uniform` — the per-scale margin
  `1 − w³` decreases toward `0` as `w→1`, so the per-scale gaps are LATTICE units and do NOT supply the uniform
  PHYSICAL floor (that still needs the `tm`-recursion `singleStep`).

**Consequence:** the resummed-clustering residual **EQUI-INHABITS** the atomic core `singleStep` as a sharp,
numerically-pinned (factor `dimQ 1 = 2`) RE-FRAMING. It is neither a free/computable `F`-node nor a strictly-weaker
sub-obligation nor a core-bypassing parallel obligation. **`F = 1` stands**; the multi-plaquette construction did
NOT move the core (it added a per-scale lattice-units construction increment). Deliverable: `job tmp/resummation_adjudication.md`.

## PETER–WEYL RESUMMATION — PROVED (2026-07-07, `PeterWeylEigenvalueResummation.lean`)

The user-pinned identity (real transfer resums the degeneracy: rate `w³`, not `2w³`) is **PROVED
as a Peter–Weyl spectral fact** — outcome (A), a fixed-spacing construction increment + a
correction (build 756, guard OK at 5, axiom-clean, C=18, no alias):
- `pwChain_step_is_peterWeyl_orthogonality`: the genuine per-step transfer EIGENVALUE is
  `w^{C₄(r)}` (= `coeffW · haarSubKernel`, the real `δ/dim` Schur orthogonality); `2w³ = coeffW w 1`
  is the CHARACTER (`= dim × eigenvalue`, trace). `reconTransfer`'s `2w³` was a
  character-vs-eigenvalue misidentification — it used the **bare Kronecker δ**, dropping the
  Peter–Weyl `1/dim`, over-counting by `dim` per step (`connChain_eq_dimPow_pwChain`).
- `peterWeyl_resummedClustering` + `peterWeyl_gap_of_physical`: the physical `δ/dim` transfer
  **discharges `ResummedClustering` UNCONDITIONALLY** → `LocatedSpectralGap`, separator `w³`,
  margin `1−w³ > 0`, for **every** `0 < w < 1` (concrete at `9/10, 99/100`). So the
  `MultiPlaquetteEffectiveTransfer` gap is now UNCONDITIONAL on all `(0,1)` — the `w*` ceiling was
  an artifact of the bare-δ.
- **Correction to `ResummationAdjudication`:** its Point C (`reconTransfer` "non-free", `2w³ > w³`)
  was a fixed-spacing misidentification (the genuine free transfer clusters at `w³`) — corrected.
  Its Point D (`tm`-independence + non-uniform margin) **STANDS**: `fixedSpacing_margin_not_uniform`
  proves `1−w³ → 0` as `w→1`, so the fixed-spacing lattice gaps do NOT give the uniform physical
  floor.

**Net:** fixed-spacing gap unconditional at every coupling; the CONTINUUM core `singleStep` (the
`tm`-recursion summability, `1−w³→0`) stands — **F=1, D=0, guard=5** (fixed-spacing ≠ continuum;
NOT Clay closure).

## Anti-loop rule (enforced before spawning any attack)

Predict the attack's honest outcome. **If it is "produces another
`:= SingleStepDefectBound` alias" / "reduces to `singleStep`," it is a LOOP — do not
spawn it.** "The honest expectation is another confirmation" *is* the loop signal.

Only spawn an attack that would:
- **(a)** DISCHARGE a bold frontier obligation (inhabit it axiom-clean → D++, guard reacts), or
- **(b)** DECOMPOSE a frontier obligation into strictly-weaker *independent* pieces with a
  PROVED `(⋀ pieces) → parent` **and** a certificate that ≥1 piece is strictly weaker
  (single-scale/finite vs all-scale/uniform/continuum), or
- **(c)** REFUTE a genuinely-live candidate route (kills a branch, not a re-confirmation).

## SITE-1 per-MOVE decomposition — machine-checked COLLAPSE (2026-07-07, `SITE1PerMoveDefect.lean`)

The one ledger-legal codynamic move (`docs/codynamic-uplift-master-map-2026-07-07.md`
SITE-1: derive the per-BLOCK `singleStep` defect as a free Grönwall fold of per-MOVE
defects, one scale finer) is **adjudicated and COLLAPSES** (task criterion (iii);
build green, guard OK at 5, axiom-clean; NOT a `:= SingleStepDefectBound` alias — a
distinct multi-field structure, collapse *proved*).

- **FREE fold PROVED:** `fold_margins` (axiom-free `blockProd` survival fold) +
  `singleStep_of_perMove : PerMoveDefectBound → SingleStepDefectBound` — the intra-block
  per-move recursions fold to the block estimate for free, at arbitrary `m`.
- **COLLAPSE PROVED:** `perMove_of_singleStep : SingleStepDefectBound → PerMoveDefectBound`
  — a genuine `m=2` per-move structure built from `singleStep` by the island-loaded
  scheme (`CodynamicHierarchical.exactLoss=0`: one loaded move `σ=1−δ_block`, one free
  move `σ=1`). Both maps ⟹ **equi-inhabitation** at the finer per-move scale.
- **Concentration escape REFUTED:** `additive_perMove_insufficient` (axiom-free) — the
  additive/union per-move fold of the raw seed `bondMovingDelta w 1 ≤ 6(1−w)` sums to
  the **linear-in-m wall** `6m(1−w)` (semigroup `2−ρ^free_m=6mε`, not the concentrating
  fusion), `24 > 3/2` at `w=1/2, m=8` — strictly too weak for the block quadratic
  `6(1−w)²`. Plus `singleStep_falsifiable`/`_satisfiable_zero`: an `afr`-only per-move
  envelope can't determine the `tm`-dependent `singleStep`.
- **Dichotomy:** every per-move candidate is either too weak to imply `singleStep`
  (additive/afr-only → linear wall) or equi-inhabiting (carries the block-assembly
  product). No strictly-weaker-AND-implying per-move object exists. Concentration
  `ρ_m < m·ρ_1` is real physics but supplies the SAME logical strength.

**Consequence:** the finer per-move scale — the master map's "single place with a
ledger-legal chance to move F below the core" — is a COLLAPSE, closing the last
codynamic hope. `F` stays 1, `singleStep` atomic. Attacks on the per-move fold are now
provably loops. The only honest attacks remain (a) direct atomic `singleStep` (the
true-margin construction + real per-step recursion) or (b) a genuinely-new
strictly-weaker reduction (none known).

## Fixed-block terminal compression increment (2026-08-06)

This increment moves the active block-compatible `CanonicalBulkControl`
frontier without claiming an inhabitant of its remaining analytic fields.

- The terminal outer factor is converted exactly to the integer-theta
  endpoint term, and a fixed-block convex chord is proved below the complete
  physical theta sum.
- Zeroth, first, and second geometric moments now have exact dyadic doubling
  recurrences.  A length-`2^k` block is represented in `k` checked state
  transitions, and the state is proved equal to the literal finite sum.
- Fixed-block soundness is generic in the block count.  The physical identity
  `L_k = 320 * 2^(k-6)` yields a refined 320-block carrier that compiles back
  to the theta factorization, coefficient sandwich, and existing physical
  consumer.
- All exported gates are `[propext, Quot.sound]`.  The uniform terminal
  inequality, trapezoid exchange, radial factor bound, and fine reserve remain
  open, so this is a complexity-reduction/decomposition move rather than a
  critical-path discharge.

## Terminal outer and radial fields discharged (2026-08-06)

The fixed-block compression has now produced two physical all-scale
certificates rather than only a smaller conditional carrier.

- The terminal outer field is proved for every `k >= 7` by the exact 640-step
  endpoint table, a uniform Bernoulli power ceiling, and a kernel-checked
  fixed-point witness.
- The radial field is reduced by the exact identity
  `radial + M4 + (2*L^2-1)*d0 = (4*L^2-2)*D + (2*L+1)*dN`.
  Its complementary coefficient is exactly `159/125`, and
  `159/125 + 341/125 = 4`, so the fourth-moment inequality compiles to the
  required `radial <= (341/125)*L^2*D` estimate without budget loss.
- A generic common-denominator floor/ceiling evaluator proves binary powers in
  logarithmically many rounded multiplication steps.  It replaces direct
  normalization of giant rational powers with a small proof about the
  computation itself.
- The physical proof uses an exact 640-entry certificate at `k=7`.  For
  `k>=8`, the identity `L=1280*2^(k-8)`, Bernoulli and reciprocal-Bernoulli base
  bounds, and fixed-point second/fourth/terminal moment witnesses transport one
  1280-block certificate to every scale.
- `terminalRadial_fromSeven` proves the original radial field at every physical
  scale `k>=7`.  `BlockCompatibleP2PostRadialTailFromSeven` is therefore the
  new honest carrier, with exactly two analytic fields: the nonpositive
  trapezoid exchange and the independent fine even/odd reserve.
- The exported load-bearing declarations check with
  `[propext, Quot.sound]`; no full-project audit or remote CI run was used.

This is a real frontier discharge, but not a Yang--Mills solution.  The two
remaining normalized-deficit fields, the deeper-interior strong-Turan family,
the physical margin recursion, continuum construction, and O(4) restoration
remain open.

## Exact physical `k=7` fine reserve discharged (2026-08-06)

The independent fine even/odd reserve now has an exact physical base cell at
`k=7`.  This closes the finite head of that field; it does not yet prove its
uniform tail.

- A generic fixed-point interval-energy layer bounds squared differences from
  lower/upper rational enclosures.  The physical path-energy expressions can
  therefore be certified without normalizing the full closed rational terms.
- Binary floor/ceiling power tables and a proved 32-term block compiler replace
  the depth-1280 evaluation by logarithmic power proofs and fixed-size checked
  range sums.
- Four large physical `Q'` expressions are connected by structural equality to
  irreducibly sealed atoms.  This is essential because `Q'.le` is represented
  by an inline cross-product order: leaving the expressions transparent forces
  reduction of their enormous numerators and denominators before theorem reuse.
- Five exact numeral witnesses bound the two mass and two path-energy atoms.
  The exact identity between the checked debt `1/754974720` and
  `blockParityDebt 7` then proves the doubled reserve inequality.
- Exact `P1 = 2*T1` and `P4 = 2*T4` identities, followed by constructive
  cancellation of the positive factor two, produce the original physical
  reserve theorem and inhabit `FineSevenPhysicalReserveCertificate`.
- The exported load-bearing declarations check with
  `[propext, Quot.sound]`.  No full-project audit or remote CI run was used.

Honest frontier: the physical `k=7` fine-reserve cell is closed.  The uniform
`k>=8` transport, nonpositive trapezoid exchange, deeper-interior strong-Turan
family, and physical margin recursion remain open.  This is not a proof of the
Yang--Mills Millennium problem.

## Checked `k=7` reserve installed in the physical frontier (2026-08-06)

The exact base cell is now consumed downstream, so it is no longer duplicated
as a caller-supplied assumption.

- `blockFineReserve_seven` states the checked certificate directly over the
  repository's physical `blockWeight`, `blockNcut`, `coordNormSq`,
  `coefficientDeficit`, and `blockParityDebt` definitions.
- `BlockCompatibleP2PostRadialTailFromEight` asks for trapezoid exchange from
  `k>=7`, but asks for the fine reserve only from `k>=8`.  Its compiler fills
  the missing `k=7` branch with `blockFineReserve_seven`.
- Combined with the weighted-box coefficient carrier, the reduced frontier
  constructs an actual all-cutoff `pGamma=2` `CanonicalBulkControlFamily` and
  proves the generic `pGamma>=2` condition.  Its `finePin` is selected by the
  canonical fusion spectrum, its `imagePin` comes from `BlockingStep.step`, and
  the existing mode-one quotient compiler reaches the genuine
  `BlockingStep.Phi` defect-power identity and uniform half-loss gate.
- The focused source check and monitored module target are green.  All
  exported declarations use only `[propext, Quot.sound]`; no full-project audit
  and no remote CI run were used.

This is a strict premise reduction, not an inhabitant of the full frontier.
The all-scale weighted-box strong-Turan family, trapezoid exchange from seven,
fine reserve from eight, loss summability, physical margin recursion,
continuum construction, and physical O(4) restoration remain open.  It is not
a solution of the Yang--Mills Millennium problem.

## Dead routes (refuted — do not re-attempt)

- **`Var_m(cosθ)` monotonicity → uniform-in-`m`** — REFUTED (`VarianceMonotonicity.lean`,
  `varMono_insufficient_for_uniform`). `Var_m` monotone-decreasing is TRUE and its exact
  identity is proved, but `Cdef = 4·Var + F(μ)` and the `F`-gap cancels the variance gap:
  concrete counterexample `w=0.6`, `Var_3<Var_2` yet `Cdef_3>Cdef_2`. So variance
  monotonicity does **not** yield `Cdef_m ≤ Cdef_2`. Also **corrects** the earlier
  `sup_m Cdef_m = Cdef_2` claim (deep-UV-only; false at strong coupling — sup at `m=3` for
  `w=0.6`). The uniform bound `Cdef_m ≤ 6(1−w)²` itself still holds with large margin, but
  its rigorous proof remains the open local-CLT wall `FusionConvLogConcaveCore`.

## Re-oriented plan (only F-moving work)

1. **Discharge uniform-in-`m`** (variance monotonicity `Var_m ≤ Var_2`). In flight. If
   proved: D-partial, F: 3 → 2 for that branch.
2. **Adjudicate the other two pieces.** Before attacking them, PROVE whether
   `channel_feedback` and `real_defect_identification` are (i) strictly weaker than
   `singleStep` (legit F-nodes) or (ii) logically **equal** to `singleStep` (in which case
   the "decomposition" is fake — record it, and the only honest attack left is on
   `singleStep` head-on or a declaration that it is the irreducible Clay core).
3. **No more new-tool sweeps** whose predicted outcome is a confirmation alias.
