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

## Exact `k=7` trapezoid exchange discharged and installed (2026-08-06)

The second residual theta head is now closed.  The physical frontier no
longer asks callers to provide either `k=7` theta inequality.

- The exact comparison is
  `fixedCutoffTrapezoidCross (blockWeight 7) (qpow (blockWeight 8) 4) 639 <= 0`.
  Its relative margin is too small for coarse analytic rounding, so the proof
  uses the same high-precision scale as the fine-reserve certificate.
- Binary floor/ceiling powers enclose both coefficient rows.  A generic
  32-term blocked-sum compiler bounds the low adjacent sum and high trapezoid
  norm from above, and the high adjacent sum and low trapezoid norm from
  below.  Four 639-term natural table equalities are kernel-checked without
  axioms; one final integer cross product proves the sign.
- `blockTrapezoidExchange_seven` states the result over the repository's raw
  physical definitions.  `BlockCompatibleP2PostRadialTailStrictFromEight`
  inserts that theorem and the previously checked fine-reserve head, so both
  remaining theta fields are requested only for `k>=8`.
- With the still-open weighted-box strong-Turan family, the strict carrier
  exposes the actual all-cutoff `pGamma=2` `CanonicalBulkControlFamily`, its
  generic `pGamma>=2` condition, selected-spectrum `finePin` and `imagePin`,
  the genuine `BlockingStep.Phi` defect-power identity, and the constructive
  half-loss gate.
- Focused checks and both monitored module targets are green.  All exported
  load-bearing declarations use only `[propext, Quot.sound]`; no full audit,
  remote push, or GitHub CI run was used.

Honest frontier: the weighted-box strong-Turan family, uniform trapezoid and
fine-reserve transports from `k>=8`, loss summability, physical recursion,
continuum construction, and O(4) restoration remain open.  This is not a
solution of the Yang--Mills Millennium problem.

## Block-compatible strong-Turan route refuted and repointed (2026-08-06)

The coefficient premise used by the recent strict physical carriers has now
been tested at its first adverse schedule cell and constructively refuted.

- At `k=2`, the physical schedule has `N=19` and `w=191/192`.  The proposed
  strengthened dimension-weighted Turan inequality is false at `s=2`.
- A generic common-denominator reconstruction transports any proof of that
  physical `Q'` inequality to one cleared natural-number comparison.  Kernel
  `decide` refutes that comparison exactly; the load-bearing declarations use
  only `[propext, Quot.sound]`.
- Consequently both `BlockCompatibleP2StrongTuranData` and its weighted-box
  predecessor `BlockCompatibleP2BoxStrongTuranData` are constructively empty.
  The previously checked downstream `CanonicalBulkControl`, `finePin`,
  `imagePin`, and genuine `BlockingStep.Phi` results remain valid conditional
  compilers, but cannot be inhabited through that premise.
- A first repair, `P2RetunedHeadThreeTuran`, supplied the actual adjacent
  inequalities at `s=1,2,3` and began strengthened Turan propagation at
  `s=3`.  Reconnaissance exposed the same alternating defect at `s=4`.
  The generic exact scale-two reconstruction now proves that cell false as
  well, so both head-three schedule carriers are constructively empty.  They
  remain only as valid conditional compilers and a fenced historical route.
- `P2BlockCompatibleIntegralTailCertificate` now targets the actual adjacent
  inequality directly.  One generic common-denominator theorem handles
  arbitrary rational heat and retuned weights, turning each physical `Q'`
  target into a single natural-number comparison.
- Axiom-free Boolean checks discharge every supported adjacent atom at the
  first four physical scales: 7 atoms at `k=0,N=4`, 17 at `k=1,N=9`, 37 at
  `k=2,N=19`, and 77 at `k=3,N=39`.  The honest schedule-wide coefficient
  carrier is therefore `BlockCompatibleP2CoeffTailFromFour`, with input only
  for `k>=4`.
- `BlockCompatibleP2PhysicalFrontierRepointed` carries this exact repair
  through the physical consumer boundary.  Combined directly with the strict
  `k>=8` theta tail, it constructs the reviewed all-cutoff `pGamma=2` family,
  selected-spectrum `finePin` and `imagePin`, the genuine
  `BlockingStep.Phi` quotient defect-power identity, and the half-loss gate.
  No downstream theorem passes through either empty sufficient carrier.

The next coefficient atom is an analytic proof of the exact adjacent family
from `k>=4`; extending the cubic-size Boolean scan is evidence, not an
all-scale argument.  The two uniform `k>=8` theta transports, loss summability,
physical recursion, continuum construction, and O(4) restoration also remain
open.  No full audit, remote push, or GitHub CI run was used, and this is not a
solution of the Yang--Mills Millennium problem.

## Physical coefficient tail in closed all-scale coordinates (2026-08-06)

The scale-varying rational bookkeeping in the remaining coefficient frontier
has been eliminated without enlarging the claim.

- `P2BlockCompatibleScheduleClosed` defines `D_k=12*4^k` and proves for every
  scale that the physical margin is `1/D_k`, the heat weight is
  `(D_k-1)/D_k`, and the canonical two-fold retune is
  `(2D_k-1)/(2D_k)`.  These are semantic equalities in the constructive
  rational substrate, not normalization assumptions or per-scale evaluation.
- `physicalIntegralTailAt k s` is therefore the exact adjacent coefficient
  target in pure natural-number coordinates.  Its soundness theorem restores
  the physical `Q'` inequality using the generic common-denominator compiler.
- `BlockCompatibleP2IntegralTailFromFour` now states the whole remaining
  coefficient frontier with no rational fields: for every `k>=4` and every
  supported `1<=s<2*blockNcut k`, prove `physicalIntegralTailAt k s`.  A checked
  compiler turns that family into `BlockCompatibleP2CoeffTailFromFour` and
  hence the actual all-cutoff `CanonicalBulkControl` consumer.
- This is a structural reduction of the real theorem, not its discharge.  It
  makes the next analytic attack precise: prove the natural inequality by the
  even/odd heat-exchange or ballot/interlacing machinery, instead of extending
  the cubic fusion-table scan or introducing another false Turan premise.

Focused monitored checks are green and exported declarations use only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Physical coefficient parity-strand compiler (2026-08-06)

The exact `k>=4` adjacent family has been replaced by a smaller true
proof-about-computation interface, without claiming the remaining analytic
inequalities are proved.

- For abstract positive states `L_s`, `R_s`, one odd head, a two-step odd
  cross law, and a bridge from each preceding odd cell to the following even
  cell constructively imply `L_s <= R_s` throughout `1<=s<2N`.
- On the physical coefficient row,
  `L_s=(s+1)g_(s+1)` and
  `R_s=q^(2s+3)(s+2)g_s`.  Full Clebsch-support positivity supplies every
  cancellation used by the compiler.
- Common heat powers are removed exactly.  The odd transition retains only
  `q^4`; the even insertion retains only `q^2` and is the old strengthened
  Turan law at the true odd-index subset:
  `(s+1)^2 g_(s-1)g_(s+1) <= q^2 s(s+2)g_s^2` for even `s`.
  The odd transition is the paired product law that cancels the individually
  false even-index Turan atom.
- Exact Peter--Weyl reconstruction transports the fixed-power carrier to
  `boxSum`, so the remaining producer is stated in the repository's existing
  ballot/even-odd weighted-box coordinates.
- `BlockCompatibleP2BoxCoreParityStrandFromFour` combines these laws only for
  `k>=4` with the checked 138-atom integral prefix.  The reviewed
  `BlockCompatibleP2PhysicalFrontierRepointed` now consumes this carrier and
  reaches the all-cutoff `pGamma=2` canonical family, `finePin`, `imagePin`,
  the genuine `BlockingStep.Phi` defect-power identity, and the half-loss
  gate without passing through either constructively empty all-index
  strong-Turan carrier.
- An untrusted floating-point scout checks the invariant through `k=6` and
  records the asymptotically tight parity cells.  It also rejected the first
  attempted following-odd bridge near the support edge before that false
  strengthening entered the formal frontier.  This numerical evidence is not
  used as a Lean proof.

Focused monitored checks are green and all new load-bearing gates use only
`[propext, Quot.sound]`.  The uniform head, odd-pair, and even-insertion
inequalities from `k>=4` remain the honest analytic coefficient frontier.
No full audit, remote push, or GitHub CI run was used.

## Exact parity heads through physical scale seven (2026-08-06)

The parity carrier now separates its head-free transition automaton from the
single seed.  This lets exact finite work advance without duplicating or
weakening the actual all-scale analytic premises.

- Kernel `decide` certificates prove `physicalIntegralTailAt 4 1` and
  `physicalIntegralTailAt 5 1`; the existing common-denominator soundness
  theorem transports them to the exact weighted-box head inequalities.
- `P2BlockCompatibleHeadLinearCertificate` proves that channel one is exactly
  one adjacent band and channel two exactly one diagonal plus two oriented
  distance-two bands after common-denominator clearing.  This reduces the
  head evaluator from a Clebsch double sum to three linear finite sums.
- The sparse evaluator proves the formerly intractable physical heads at
  `k=6` and `k=7` by axiom-free kernel `decide`; its reconstruction and
  transport theorems use only `[propext, Quot.sound]`.
- `BlockCompatibleP2BoxParityTransitionsFromFourHeadFromEight` requests the odd
  two-step and preceding-odd insertion laws from `k>=4`, but requests the sole
  head only from `k>=8`.  Exact case analysis inserts the four head cells before
  compiling to the reviewed all-cutoff coefficient family.
- The physical `CanonicalBulkControl`, `finePin`, `imagePin`, genuine
  `BlockingStep.Phi` defect power, and half-loss consumer has been repointed to
  this sharper interface.  Its focused monitored check is green and its gates
  remain `[propext, Quot.sound]`.
- Direct evaluation of the unreduced `k=6` head exhausted the monitored Lean
  memory ceiling and was safely stopped.  The sparse representation replaces
  that failed route: `k=6` checks in seconds and `k=7` in under two minutes on
  one monitored worker without memory pressure.  Extending finite evaluation
  indefinitely is not the proof; the honest next head step is an analytic
  schedule induction on the sparse bands.

No full audit, remote push, or GitHub CI run was used.  The head from `k>=8`,
the transition laws from `k>=4`, and the two uniform `k>=8` theta transports
remain open.

## All-cutoff sparse-head Dirichlet compiler (2026-08-06)

The residual parity head now has an exact cutoff-uniform positive-energy
normal form, replacing direct evaluation of the growing rational sums.

- `P2BlockCompatibleHeadDirichletCompiler` proves that twice the bare head
  slack is exactly two distance-two path energies minus three adjacent path
  energies plus the four endpoint squares
  `c_0^2 + 2c_1^2 + 2c_(N-1)^2 - c_N^2`.
- The retuned weighted-box head follows from two smaller named inequalities:
  the two-step energy pays three halves of the adjacent energy, and the
  explicit endpoint reserve pays the `6*(1-q^5)*A_N` retune debt.
- Every nonlinear rearrangement is certified by the constructive reflective
  polynomial normalizer.  Splitting the cutoff induction into constant-size
  successor certificates reduced the focused monitored check from a
  deterministic heartbeat timeout to 1.25 seconds.
- Both exported theorems are kernel-checked with exactly
  `[propext, Quot.sound]`; there is no `sorry`, custom axiom, classical choice,
  `native_decide`, or noncomputable declaration.

No full audit, remote push, or GitHub CI run was used.  The honest next step is
to discharge the two physical schedule inequalities uniformly for `k >= 8`.

## Physical all-cutoff retuned-head boundary (2026-08-06)

The endpoint/debt half of the sparse-head Dirichlet data is now discharged
uniformly at every open scale `k = r + 8`.

- `P2BlockCompatibleScheduleClosed` proves the exact coordinate identity
  `25 D_k = 12 (N_k+1)^2`.
- `P2BlockCompatibleHeadPhysicalFloor` replaces the growing endpoint power by
  34 identical Bernoulli chunks.  The only closed computation is the fixed
  rational certificate `(15/16)^34 >= 1/9`; this gives
  `c_(N-1) >= N/9` at every scale.
- `P2BlockCompatibleHeadPhysicalBoundary` bounds the retune debt by its exact
  endpoint cubic, clears that comparison through the physical coordinate,
  and uses reciprocal Bernoulli to prove the terminal coefficient is
  descending.  Hence the endpoint floor square lies inside the genuine
  `headBoundary`, and `physical_head_boundary` pays the full retune debt for
  every `k >= 8`.
- The focused monitored module build is green.  Every exported load-bearing
  theorem has exactly the allowed `[propext, Quot.sound]` gate.

No full audit, remote push, or GitHub CI run was used.  The remaining head
field is the uniform energy comparison
`3*dirichletEnergy <= 2*headTwoStepEnergy`; it is not being conflated with the
completed boundary payment.

## Physical half-time high-shift sector (2026-08-06)

The schedule-native half-time route now has a strict analytic reduction, not
just a change of coordinates.

- The exact sharp-cutoff line sum is decomposed into common-shift
  autoconvolution rows.
- A generic proof-about-computation theorem turns the weighted successor
  ratio of a whole row into one adjacent coefficient comparison.
- Reciprocal Bernoulli pays that comparison for every
  `r >= ceil((5*2^k+s)/2)` at every physical scale and cutoff.
- The high-shift rows are summed constructively, and a certificate for only
  the complementary low prefix compiles back through the reviewed
  `CanonicalBulkControl` route.
- The removed tail is provably nonempty in channel one at every scale, so the
  new residual is genuinely smaller.  All exported gates are exactly
  `[propext, Quot.sound]`.

No full audit, remote push, or GitHub CI run was used.  The honest remaining
half-time input is the signed low/high balance for the physical `k >= 4`
schedule.  The independent low-prefix inequality is only a stronger
compatibility route and is not treated as the sharp frontier.

The subsequent debt/reserve normalization makes that balance exact.  Define
the low debt as `lowL-lowR` and the high reserve as `highR-highL`.  Lean now
proves both directions between `lowDebt <= highReserve` and the original
line-sum ratio, then expands `highReserve` into a finite sum of constant-shape
row atoms.  The schedule-wide reserve carrier compiles directly to the
reviewed all-scale control family.  This is the appropriate interface for a
symbolic pairing theorem or an externally generated certificate whose
soundness is proved once in Lean; the actual all-scale reserve domination is
still open.

The proof-about-computation boundary is now sharper still.  Summing the same
local atoms over *all* cutoff rows gives `physicalFullLocalReserveSum`; Lean
proves this is exactly the signed reserve of the original line-sum inequality
and constructs both directions of the equivalence.  Since `Q'` denominators
are structurally positive, `physicalFullLocalReserveAt` reduces each channel
to the sign of one integer numerator.  A family of those integer signs for
all `k >= 4` compiles end-to-end to the reviewed `CanonicalBulkControl`
consumer.  This is a compiler closure, not the missing all-scale sign proof.

The first load-bearing energy atom is also now explicit:
`P2BlockCompatibleHeadPhysicalEnergy.physical_coeff_reverse_curvature` proves
for every `k>=8` and `s>=1` that
`(7/8)c_(s+1)^2 <= c_s*c_(s+2)`.  Its proof uses the exact physical lower
weight `w_k>=127/128`, the exact heat curvature factor `w_k^2`, the dimension
ratio lower bound `8/9`, and the fixed 64-unit cleared slack in
`7/8 <= (8/9)(127/128)^2`.  This rules out the narrow log-concave spike that
makes the desired energy inequality false for generic log-concave strings;
the remaining work is the finite-path charge/summation theorem that consumes
this broad-peak atom and the endpoint slopes.

The endpoint-shell certificate route now has an all-depth arithmetic core.
The number of ordered parity-triangle cells above increment thresholds is a
closed product of two half-depth factors, and a parity split proves the sharp
adjacent-depth coefficient inequality once for every depth.  A reflected
generator constructs the corresponding endpoint quadratic form and its
manifest nonnegative slack.  Regression certificates at depths eight and
nine pass, and depth ten is the first new ratio checked without a handwritten
slack polynomial.  This removes certificate-size growth from the route, but
does not yet discharge the physical tenth shell: its exact box support,
schedule-specific coefficient descent, and heat transport remain the active
bridge.  Consequently the honest physical carrier still stops at
`s+9<2*N_k`.  No full audit, remote push, or GitHub CI run was used.

## Compiler-driven tenth physical half-time shell (2026-08-06)

The endpoint-shell route now has both halves of a scalable compiler.  The
new all-depth support theorem identifies every sharp-cutoff endpoint box with
the generated reflected expression, while the prefix certificate theorem
consumes only the endpoint increments needed at the requested depth.  At
depth ten, Lean checks `6*E_9 <= 5*E_10` without a handwritten support list or
slack polynomial.

The physical bridge proves `c_(N-9) <= c_(N-10)`, transports the `5/6` heat
floor to exponent `2*N-8`, and carries the result through the exact
box/line-sum reindex.  The common physical carrier is kernel-checked with the
strictly smaller residual domain `k>=4`, `2<=s`, `s+10<2*N_k`; all exported
gates are `[propext, Quot.sound]`.  The deeper interior reserve, theta tail,
and later constructive Yang--Mills layers remain open.  No full audit,
remote push, or GitHub CI run was used.

## All-depth semantic endpoint-ratio compiler (2026-08-06)

The fixed reflected polynomial certificates are no longer load-bearing for
endpoint ratios.  `P2HalfTimeEndpointSemanticCompiler` proves, for arbitrary
depth, the increment expansion, common-bound threshold reindex, fourfold
finite Fubini permutation, exact parity-row and parity-triangle counts, and
the translation identity
`endpointThresholdMultiplicity m a b ≃ ofNat (thresholdTriangleCount m a b)`.
The closed Nat coefficient inequality therefore lifts once to the table-free
semantic theorem `(R+1)*E_(m-1) <= R*E_m` for every positive `m<=2*R` and
every nonnegative increment prefix.  The checked tenth-shell physical
consumer now uses this all-depth theorem instead of
`endpointRatio_ten_prefix`.

This closes certificate-size growth and arbitrary-depth endpoint semantics;
it does **not** assert physical coefficient descent beyond depth ten.  The
honest physical residual domain remains `k>=4`, `2<=s`, `s+10<2*N_k` until a
uniform schedule-specific descent/heat transport theorem or the interior
reserve proof discharges the remaining cells.  All new exported gates are
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Macroscopic physical endpoint band and genuine consumer (2026-08-06)

The physical schedule identity `25*D_k = 12*(N_k+1)^2` now supplies the
uniform schedule-specific theorem missing from the preceding entry.  Lean
proves coefficient descent at every endpoint depth `m` with `2*m<=N_k`, then
feeds the resulting nonnegative increment environment into the all-depth
semantic endpoint-ratio compiler.  A variable-depth constructive Bernoulli
argument pays the heat factor under the exact cover
`(m+1)*(2*N_k-m+2)<=D_k`; `5*(m+1)<=N_k+1` is retained as a simple sufficient
corollary.  The exact box/line reindex therefore proves the complete half-time
cell `s=2*N_k-m` throughout that growing endpoint band.

The new residual carrier asks for a full-local Nat numerator sign only when
`k>=4`, `2<=s<2*N_k`, and the conjunction
`2*(2*N_k-s)<=N_k`, `(2*N_k-s+1)*(s+2)<=D_k` does not hold.  It coarsens into the existing reviewed physical
carrier, and Lean checks the resulting `pGamma>=2`, `finePin`, `imagePin`,
genuine `BlockingStep.Phi` trajectory defect-power law, and half-loss bound.
All new gates are `[propext, Quot.sound]`.  No full audit, remote push, or
GitHub CI run was used.

## Endpoint-spliced parity proof about computation (2026-08-06)

The alternating parity compiler now supports a decidable family of cells
proved by a direct theorem.  Its structural induction branches at each target:
inside the direct region it consumes that cell immediately; outside it uses
the appropriate odd two-step or even bridge and recursively proves the
predecessor.  This theorem replaces a full-support transition scan by exactly
the transitions whose targets remain unresolved.

For the physical schedule, the direct predicate is the exact endpoint cover
`2*m<=N_k`, `(m+1)*(s+2)<=D_k`, with `m=2*N_k-s`.  The resulting pure-Nat
frontier requests `physicalHalfTimeBoxOddTransitionAt` and
`physicalHalfTimeBoxEvenTransitionAt` only when their target is off-cover,
then compiles through the exact A1 reindex to the common physical carrier.
All new gates are `[propext, Quot.sound]`.  No full audit, remote push, or
GitHub CI run was used.

## Complete physical scale-four row and residual `k>=5` splice (2026-08-06)

The first unresolved physical cutoff is now discharged rather than left in
the all-scale transition premise.  At `k=4`, the closed schedule gives
`N_4=79` and `w_4=3071/3072`.  A generic Boolean block scanner proves a
theorem about computation: if its bounded scan succeeds, every direct
half-time cell in that interval holds.  Nine independently compiled blocks
close `s=2..136`; process isolation keeps each kernel normalization below the
per-process memory ceiling.  The existing physical head theorem closes
`s=1`, and the symbolic endpoint-cover theorem closes `s=137..157`.

The resulting theorem proves the genuine bond-moved coefficient inequality
for every supported scale-four mode.  Exact A1 setoid transport moves that
row to lag-correlation coordinates.  A dependent all-cutoff compiler now
uses the direct row at `k=4` and requests off-cover odd/even transition atoms
only for `k>=5`.  This smaller honest input reaches the same reviewed
`CanonicalBulkControlFamily`, proves `pGamma>=2`, and retains `finePin`,
`imagePin`, the genuine `BlockingStep.Phi` quotient defect-power law, and the
half-loss estimate.  The `k>=5` off-cover transition family and the `k>=8`
theta tail remain open.  Every new load-bearing gate is
`[propext, Quot.sound]`; each concrete Boolean block theorem is axiom-free.
No full audit, remote push, or GitHub CI run was used.

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

## Completed BF4/AF geometry and reduced operator RG residue (2026-08-20)

`Z4HalfTimeReflectionStrictJointCompletedBF4RGReduction` factors the previously
monolithic `CompletedWeakToStrongRGBridge` boundary along a causal line.  From
an existing `BF4FarautQuarterPhysicalSeparatorProducer` and its exact
two-loop-AF schedule identification, `BF4GeometryCompiler.ofProducer`
constructs the coupling-to-zero schedule, quadratic-envelope spacing and its
Type-level zero modulus, Faraut depth `46*bits+3`, positive uniformly bounded
physical block length, and the honest same-object grouped rate `1/4`.

The remaining `CompletedBF4RGOperatorRealization` contains only genuinely
operator-level data: a completed scale carrier and transfer, an isometric map
to the proved strong Z4 endpoint, exact block-transfer intertwining, vacuum
complement preservation, realization of the finite BF4 rate probe, and the
same-probe correlation-square/Cauchy--Schwarz handoff.  These fields imply the
completed block squared-norm contraction at `(1/16)^2`; combined with the
existing factor-four BF4 sharpness pin they reconstruct
`separator^depth <= 1/4`, hence the positive physical margin floor
`(1-1/4)/L` along the explicit vanishing-spacing trajectory.

This does **not** inhabit either the BF4 producer or the completed operator
realization.  In particular, the SU2 physical completed carrier, its
same-object transfer/correlator identification, and the exact cross-model
blocking map into the strong Z4 endpoint remain open.  No continuum measure,
OS reconstruction of the physical weak-coupling theory, limit-stable gap, or
Clay theorem follows.  The focused monitored Lean check reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## Exact physical BF4 macro-transfer `L2` contraction (2026-08-20)

`BF4PhysicalMarkovL2Contraction` closes the finite norm estimate needed before
the literal physical BF4 Markov operator can be lifted to the constructive GNS
completion.  It first proves a generic exact-rational Jensen theorem for a
nonnegative finite row of total mass one by expanding its manifest weighted
variance.  Applied to `centralPhysicalConditionalKernel`, this gives the
rowwise square bound.  Exact preservation of
`centralPhysicalStationaryMean` then contracts the physical marginal-weighted
norm:

`<centralPhysicalMarkovApply f, centralPhysicalMarkovApply f> <= <f,f>`.

This also corrects the causal interpretation of the preceding reduced RG
residue.  `centralPhysicalMarkovApply` is the already-composed physical
**macro** transfer represented by the slab conditional law; the Faraut depth
belongs to its local-density construction and must not be applied again to
this macro operator.  The next interface therefore needs one macro-transfer
intertwining law, not an additional depth iterate.

No strict contraction is proved here: Jensen supplies norm nonexpansion only.
The physical GNS datum, completion lift, vacuum/correlator realization, honest
macro comparison map, continuum limit, and Clay theorem remain open.  The
focused single-worker build completed 1128 jobs and reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## Constructive completion of the physical BF4 macro transfer (2026-08-20)

`BF4PhysicalMarkovGNSCompletion` now equips the literal finite BF4 observable
carrier with its stationary marginal-weighted GNS form and descends the
physical macro Markov action through the repository's explicit CReal Cauchy
completion.  Exact pointwise rational linearity and the preceding Jensen
estimate make a contractive diagonal transfer symbol.  On the completion, its
transfer is self-adjoint, positive, and norm-nonexpanding.

The constant observable gives a unit stationary vacuum.  Because the form only
sees positive-marginal states, zero-marginal rows need not fix that observable
pointwise; the proof instead shows that the discrepancy belongs to the GNS
radical and therefore vanishes in the quotient.  Self-adjointness and vacuum
fixation then prove that the completed vacuum complement is transfer-invariant.
This is the actual physical finite-BF4 GNS carrier and completed macro transfer,
not a placeholder realization and not a Faraut-depth re-iteration.

No strict vacuum-complement contraction is proved.  The next frontier is the
same-object realization identifying the completed matrix coefficient of the
physical separator probe with the already-proved finite joint quadratic and
macro correlation.  After that, the exact one-macro-step comparison map into
the strong endpoint, uniform strict gap, limit stability, continuum theory,
and Clay theorem remain open.  The focused single-worker build completed 1129
jobs and every exported declaration reports only `[propext, Quot.sound]`; no
full audit, remote push, or GitHub CI run was used.

## Same-object physical BF4 correlator in the completion (2026-08-20)

`BF4PhysicalCompletedMacroCorrelator` closes the next unconditional GNS edge.
Every finite stationary-mean-zero BF4 observable now embeds into the actual
completed physical vacuum complement.  Its one-macro-step completed matrix
coefficient is exactly the normalized symmetric BF4 joint quadratic.  Finite
OS positivity makes that quadratic nonnegative, so the existing same-object
pin identifies the completed coefficient itself--not merely an unrelated
absolute-value bound--with the selected physical connected correlation.

For the producer's rate probe, the module constructs the literal completed
vector, proves vacuum orthogonality and squared norm at most one, and identifies
its same-object connected correlation with its completed autocorrelation.
Constructive completed Cauchy--Schwarz then proves the correlation-square bound
by the squared norm after one physical macro transfer.  That handoff is thus a
theorem and should not remain an independent field in the residual RG operator
interface.

This still does not provide the cross-model map into the strong endpoint or a
strict physical vacuum-complement contraction.  The remaining comparison must
intertwine one already-composed physical macro transfer with the strong
two-step endpoint transfer; the Faraut local-density depth must not iterate the
physical macro transfer again.  Uniform limit stability, continuum existence,
and the Clay theorem remain open.  The focused single-worker build completed
1142 jobs and every exported declaration reports only `[propext, Quot.sound]`;
no full audit, remote push, or GitHub CI run was used.

## Corrected one-macro-step endpoint comparison residue (2026-08-20)

`BF4PhysicalCompletedMacroEndpointIntertwiner` replaces the earlier
over-expanded `CompletedBF4RGOperatorRealization` boundary with the actual
remaining cross-model datum.  Its physical carrier, physical transfer,
vacuum complement, rate probe, same-object coefficient, normalization, and
Cauchy--Schwarz estimate are no longer fields: they are the concrete objects
and theorems constructed in the two preceding modules.

The corrected residual has four fields only: a map from each concrete physical
BF4 GNS completion to the constructed strong endpoint, exact squared-norm
identification, intertwining of **one** already-composed physical macro step
with one strong two-step transfer, and preservation of the vacuum complement.
Given those four fields, the proved endpoint theorem imports a uniform strict
completed physical vacuum-complement norm gap with rate `1/16`; the same-probe
correlation-square-to-strict-norm chain follows automatically.

No inhabitant of this four-field cross-model intertwiner is constructed.  It
is now the immediate analytic bridge: prove the exact blocking map and its
three laws without a spurious Faraut-depth iterate.  Even after that finite
completed gap, thermodynamic and continuum limit stability, the continuum QFT
construction, and the Clay theorem remain open.  The focused single-worker
build completed 1230 jobs and every exported declaration reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## Dense-stage construction of the completed endpoint map (2026-08-20)

`BF4PhysicalDenseMacroEndpointLift` moves the remaining comparison boundary
off arbitrary completed maps and onto finite dense-stage data.  A supplied map
from finite physical BF4 observables to strict-cylinder stages is lifted
termwise to physical GNS Cauchy representatives and then through both quotient
completions.  Exact dense squared-distance and bilinear-form identities prove
that the resulting completed map preserves the full inner product.  Dense
radical identities for one macro time step and for the vacuum descend to exact
completed transfer intertwining, vacuum identification, and preservation of
the vacuum complement.  These theorems construct the corrected four-field
`CompletedBF4MacroEndpointIntertwiner` automatically.

The construction exposes one genuinely constructive interface mismatch.  The
physical `CauchyNull` relation stores `forall epsilon, exists N` in `Prop`,
whereas the strong seminorm completion requires a Type-valued modulus function
`epsilon -> Nat`.  Eliminating `Prop` into that function would be a choice
step forbidden by the axiom gate.  The dense lift therefore asks explicitly
for `nullModulusTransport`, a dependent-pair witness carrying exactly those
moduli.  This is separate from the still-open analytic dense stage map, exact
distance/inner identities, one-macro radical law, and vacuum radical law.

No inhabitant of the dense comparison data is constructed, so the strict
physical completed gap remains conditional on that bridge.  Thermodynamic and
continuum stability and the Clay theorem remain open.  The focused
single-worker build completed 1231 jobs and every exported declaration reports
only `[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was
used.

## Type-modulated GNS null completion (2026-08-20)

`GNSModulusCompletion` repairs the constructive interface exposed by the dense
endpoint lift.  Its `CauchyNullModulus` retains `epsilon -> Nat` as Type-level
data, and reflexivity, symmetry, and quarter-tolerance transitivity construct
their output moduli explicitly.  Quotienting by `Nonempty` such data gives
`ModulatedGNSCompletionSpace`; the existing representative inner-product limit
descends to it without new analytic assumptions.

There is a canonical inner-preserving map from the modulated completion to the
legacy `GNSCompletionSpace`, obtained by forgetting the null modulus.  No
inverse is asserted: the legacy relation contains only the proposition
`forall epsilon, exists N`, and recovering a modulus function from it is the
choice-like Prop-to-Type step forbidden by the project gate.  This makes the
direction of future physical refactoring precise: construct the physical
transfer and endpoint lift on the modulated carrier, rather than postulating a
selector for the legacy quotient.

This foundational construction does not supply the analytic BF4-to-strong
dense stage map, so it does not yet inhabit the endpoint comparison or prove a
physical strict gap.  Thermodynamic/continuum stability and the Clay theorem
remain open.  The focused single-worker build completed 66 jobs and all
exported declarations stay within `[propext, Quot.sound]`; no full audit,
remote push, or GitHub CI run was used.

## Physical BF4 macro transfer on the modulated completion (2026-08-20)

`BF4PhysicalMarkovModulusCompletion` specializes the Type-modulated quotient
to the exact stationary physical BF4 form.  The finite Markov squared-distance
contraction transports every supplied null modulus termwise, so the already-
composed physical macro transfer descends directly to the modulated carrier.
The canonical forgetful map to the legacy completion exactly intertwines the
two macro transfers and preserves the full completed inner form.

Those compatibility theorems import self-adjointness, positivity, and norm
nonexpansion to the modulated carrier.  The constant physical observable is a
unit vacuum, is fixed modulo the explicit null relation, and its completed
orthogonal complement is invariant.  Thus choosing the Type-modulated carrier
does not sacrifice any previously proved finite physical operator law, while
it removes the forbidden need to select a modulus from a Prop-level null proof.

No strict physical gap or dense BF4-to-strong stage comparison is constructed.
The next bridge should be formulated directly from the modulated physical
carrier, where exact dense squared-distance preservation automatically carries
the required null moduli.  Thermodynamic/continuum stability and the Clay
theorem remain open.  The focused single-worker build completed 1131 jobs and
all exported declarations report only `[propext, Quot.sound]`; no full audit,
remote push, or GitHub CI run was used.

## Choice-free modulated dense endpoint compiler (2026-08-20)

`BF4PhysicalModulatedDenseEndpointComparison` moves the dense BF4-to-strong
comparison onto the Type-modulated physical carrier.  The remaining analytic
input is now exactly five finite-stage laws: a map from physical observables
to strict-cylinder stages, exact squared-distance preservation, exact full
inner-form preservation, a one-macro-step radical intertwining law, and a
vacuum radical law.

Squared-distance preservation automatically transports each supplied physical
null modulus to the strong completion with the same modulus.  Consequently no
`Prop`-to-`Type` selector remains in the interface.  From the five laws the
module constructs the completed map, proves full completed inner preservation,
one-macro/two-step transfer intertwining, vacuum identification, and vacuum-
complement preservation, then imports the endpoint's uniform strict completed
norm gap with rate `1/16` to the actual modulated physical BF4 carrier.

No inhabitant of the five dense analytic laws is constructed, so the strict
physical completed gap remains conditional.  The immediate mathematical
frontier is the cross-model finite-stage map and its four identities, not any
further completion or choice infrastructure.  Thermodynamic/continuum
stability, continuum QFT existence, and the Clay theorem remain open.  The
focused single-worker build completed 1230 jobs; the forbidden-token scan was
empty and every exported declaration reports only `[propext, Quot.sound]`.
No full audit, remote push, or GitHub CI run was used.

## Completed Cauchy--Schwarz for the physical Markov form (2026-08-20)

`BF4PhysicalCompletedMarkovFormCauchySchwarz` starts a direct physical-gap
route that does not require an isometric BF4-to-strong-Z4 embedding.  The
positive one-macro form `B_T(left,right) = <T left,right>` is packaged as an
actual rational `SmulGNSData`; its symmetry is the proved physical detailed-
balance law and its positivity is the proved finite OS/Markov positivity.
The generic constructive GNS algebra then supplies sharp finite Cauchy--
Schwarz for `B_T`.

Termwise rational Cauchy--Schwarz is passed through the explicit CReal pairing
limits, giving the completed inequality

`<Tx,y>^2 <= <Tx,x> * <Ty,y>`.

This is the operator-algebra engine needed to upgrade a completed physical
form gap to a squared-norm gap without a spectral theorem or square root.  It
does not yet pass the producer's finite centered `1/16` estimate to every
completed vacuum-orthogonal vector; stagewise centering and that limit passage
are the next frontier.  Thermodynamic/continuum stability, continuum QFT
existence, and the Clay theorem remain open.  The focused single-worker build
completed 1195 jobs; the forbidden-token scan was empty and every exported
declaration reports only `[propext, Quot.sound]`.  No full audit, remote push,
or GitHub CI run was used.

## Completed physical BF4 centered form gap (2026-08-20)

`BF4PhysicalCompletedCenteredFormGap` closes the next direct finite physical
bridge.  It centers every finite-stage observable by its exact stationary
row-marginal mean, proves that the centered observable is mean zero, and proves
both algebraic correction identities

`||center f||^2 = ||f||^2 - mean(f)^2`,

`<T center f,center f> = <Tf,f> - mean(f)^2`.

For a Cauchy representative of a completed vacuum-orthogonal vector, the
stage means converge to zero.  Therefore the centered stage norms and Markov
forms converge respectively to the ordinary completed norm and completed
matrix coefficient.  Passing the producer's finite mean-zero `1/16` bound
through those two limits proves

`<T v,v> <= (1/16) <v,v>`

on the entire completed physical vacuum complement at every matched scale.
This route uses the actual stationary BF4 carrier and needs no BF4-to-strong-
Z4 stage map or endpoint-comparison laws.

The theorem is parametrized by an inhabitant of
`BF4QuarterPhysicalSeparatorProducer`; this module does not construct that
analytic producer.  It is consequently a genuine compilation theorem from
the named finite producer data, not an unconditional Yang--Mills result.  The
next finite operator frontier is to combine this form gap with completed
Markov-form Cauchy--Schwarz and positivity to obtain the squared-norm/operator
gap, then transport it to the Type-modulated carrier.  Thermodynamic and
continuum stability, continuum QFT existence, and the Clay theorem remain
open.  The focused single-worker build completed 1201 jobs; the forbidden-
token scan was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Completed physical BF4 operator-norm gap (2026-08-20)

`BF4PhysicalCompletedOperatorNormGap` contracts the completed centered form
gap and completed positive-Markov-form Cauchy--Schwarz into the actual
completed operator estimate.  For a vacuum-orthogonal vector `v`, apply the
Markov-form Cauchy--Schwarz inequality to `(v,Tv)` and the form gap to `Tv`:

`||Tv||^4 <= <Tv,v> <T^2v,Tv> <= <Tv,v> (q ||Tv||^2)`.

Constructive nonnegative-factor cancellation, with no division by
`||Tv||^2`, gives `||Tv||^2 <= q <Tv,v>`.  Applying the form gap once more
gives

`||Tv||^2 <= q^2 ||v||^2`, with `q = 1/16`.

The module packages the reusable completed physical form-gap contract, proves
the square-form and norm-gap upgrades for any nonnegative strict rate, and
then instantiates them from each `BF4QuarterPhysicalSeparatorProducer`.  It
also defines the concrete completed macro-transfer powers and proves geometric
squared-norm decay `((1/16)^2)^n` on the invariant vacuum complement.

As before, the result is conditional on an inhabitant of the named physical
producer structure; it does not construct that analytic producer.  It is a
finite-cutoff completed operator theorem, not thermodynamic or continuum
stability and not the Clay result.  The next representation frontier is to
transport this now-direct physical gap to the Type-modulated completion; the
next analytic frontier after that is uniform limit stability.  The focused
single-worker build completed 1231 jobs; the forbidden-token scan was empty
and every exported declaration reports only `[propext, Quot.sound]`.  No full
audit, remote push, or GitHub CI run was used.

## Type-modulated physical BF4 operator-norm gap (2026-08-20)

`BF4PhysicalModulatedOperatorNormGap` transfers the direct completed physical
gap to the choice-free Type-modulated carrier.  Modulated vacuum orthogonality
maps to legacy vacuum orthogonality; the forgetful map preserves the full
completed inner form and exactly intertwines the macro transfer.  Rewriting
the already-proved legacy inequalities therefore gives, on the modulated
vacuum complement,

`<T v,v> <= (1/16) <v,v>`,

`||T v||^2 <= (1/16)^2 ||v||^2`.

The module also defines modulated transfer powers, proves that forgetting the
explicit null modulus commutes with every power, and imports the geometric
squared-norm decay `((1/16)^2)^n`.  No BF4-to-strong-Z4 stage map and no
Prop-to-Type modulus selector is used.

This completes the representation-theoretic finite-cutoff gap compilation
from an inhabitant of `BF4QuarterPhysicalSeparatorProducer` to both available
completed physical carriers.  It does not construct that analytic producer,
nor does it prove stability of the carriers or transfers as volume and cutoff
vary.  The causal frontier is now the uniform thermodynamic/continuum limit
interface, followed by OS/QFT reconstruction in that limit; the Clay theorem
remains open.  The focused single-worker build completed 1234 jobs; the
forbidden-token scan was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Physical BF4 graph-norm limit stability (2026-08-20)

`BF4PhysicalModulatedGapLimitStability` factors and proves the first honest
finite-to-continuum operator bridge.  At each matched cutoff it exposes an
explicit `CauchyGNS` representative, its literal constructive-real squared
norm, and the squared norm after the actual finite physical macro transfer.
The completed modulated theorem then rewrites to the representative-level
inequality

`||T_j v_j||^2 <= (1/16)^2 ||v_j||^2`.

`BF4WilsonGraphNormLimitApproximation` records the nontrivial remaining limit
data without assuming that conclusion: explicit approximants for every vector
of a selected continuum Wilson carrier, preservation of the finite vacuum
complement, constructive convergence of both graph-norm components, exact
class identifications with the continuum inner products, and identification
of the selected continuum macro separator with `1/16`.  Passing the uniform
finite inequality through the two supplied limits constructs
`WilsonOperatorNormGapPin`; the continuum operator gap is a theorem, not a
field.  The AF/Faraut producer feeds this compiler through its already-proved
conversion to `BF4QuarterPhysicalSeparatorProducer`.

No inhabitant of the graph-norm approximation record is constructed, and the
record still presupposes a genuine continuum Yang--Mills/OS/Wilson carrier.
The macro separator also still needs a correct physical-time interpretation
before it yields the dimensionful generator gap.  Thus this closes the formal
inequality-persistence compiler while leaving the analytic thermodynamic and
continuum construction, the physical semigroup/generator identification, and
the Clay theorem open.  The focused single-worker build completed 1261 jobs;
the forbidden-token scan was empty and every exported declaration reports
only `[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was
used.

## AF/Faraut graph-norm continuum integration (2026-08-20)

`BF4FarautGraphNormContinuumRealization` installs the new limit compiler in
the existing same-object AF/Faraut endpoint.  Its
`ContinuumWilsonGraphNormResidualData` retains genuine continuum Yang--Mills
existence, the selected Wilson/OS carrier, and convergence of the exact
physical-rate family to that reconstruction's logarithmic gap, but replaces
the former freely supplied `WilsonOperatorNormGapPin` with the explicit BF4
graph-norm limit record.  The module derives the old minimal bounded residual
and therefore constructs `WilsonMinimalBoundedMassGap` on the same continuum
object.  An adapter starts from the stronger projective OS residual without
adding a separate operator-gap hypothesis.

This proves the causal contraction

`finite BF4 norm gap + graph-norm convergence + exact-rate reconstruction`

`-> positive exact-log continuum rate + Wilson operator norm gap`.

It does not inhabit the AF/Faraut producer, continuum existence, projective
OS realization, exact-rate reconstruction, or graph-norm convergence.  The
first graph-norm interface also provides finite approximants as a function of
arbitrary quotient points; although this is explicit Type-level data rather
than hidden choice, the next refinement is to quantify over continuum Cauchy
representatives and prove the quotient-level statement by induction into
`Prop`.  The focused single-worker build completed 1322 jobs; the forbidden-
token scan was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Choice-free representative graph-norm limit (2026-08-20)

`BF4PhysicalModulatedGapLimitStability` now provides the sharper
`BF4WilsonRepresentativeGraphNormLimitApproximation`.  It is indexed by
explicit `CauchyGNS` representatives of the continuum Wilson completion,
rather than by arbitrary quotient points.  Its new
`transferredRepresentative` field is the honest representative-level lift of
the selected continuum transfer, with an exact quotient-class equation.  The
finite approximants and both norm-convergence laws are likewise attached to
the explicit continuum representative.

The module proves the `CReal` limit inequality on each representative and
then constructs `WilsonOperatorNormGapPin` for every completed vector by
`Quotient.inductionOn` into the proposition expressing the norm inequality.
No quotient representative is selected into `Type`, so the earlier
choice-like point-to-approximant function is absent from the endpoint route.
`BF4FarautGraphNormContinuumRealization` now consumes this representative-level
record.

The remaining analytic burden is consequently sharper: construct the
continuum transfer at representative level, construct finite BF4
approximants of every continuum Cauchy representative, preserve vacuum
orthogonality, and prove the two effective graph-norm convergence laws.  None
of those fields, the continuum carrier, or the physical producer is inhabited
here.  The focused single-worker build completed 1322 jobs; the forbidden-
token scan was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Linear Wilson transfer supplies the continuum representative lift (2026-08-20)

The representative graph-norm endpoint now reuses the pre-existing
`WilsonLinearTimeTranslationPin`.  Its `LinearTransferOperator.TCauchy` is the
required representative-level action, and `T_ofCauchy` together with
`operatorPinned` proves that this action represents exactly the already-
selected continuum Wilson time translation.  The new
`BF4WilsonLinearGraphNormLimitApproximation` therefore asks only for that
single established linear-dynamics certificate, finite BF4 approximants,
vacuum-complement preservation, and the two graph-norm convergence laws.

It constructs the representative limit record and then
`WilsonOperatorNormGapPin`.  The AF/Faraut continuum residual has been tightened
to consume this linear version, removing a duplicated transfer-lift field and
descent equation from the open frontier.

This remains conditional: no interacting continuum Wilson linear-time-
translation pin or finite-to-continuum approximation system is constructed.
The result identifies the next analytic frontier more economically; it does
not supply continuum existence or the Clay theorem.  The focused
single-worker build completed 1323 jobs; the forbidden-token scan was empty
and every exported declaration reports only `[propext, Quot.sound]`.  No full
audit, remote push, or GitHub CI run was used.

## Dense finite-stage graph-norm compiler (2026-08-20)

`BF4PhysicalDenseStageGraphNormCompiler` expands the remaining graph-norm
interface into a causal approximation system.  For each continuum
`CauchyGNS` representative it selects an explicit sequence term, maps that
dense observable into the literal finite BF4 carrier, and forms the constant
finite completion representative.  The new
`WilsonPointwiseLinearTimeTranslationPin` records the exact law that the
chosen `TCauchy` lift applies the selected observable shift termwise.  The
finite-stage map separately records exact intertwining of that shift with the
concrete physical macro transfer.

The analytic norm input is now one `CReal.ModCauchyEv` record, not two
independent `ConvergesTo` assumptions.  It exposes a Type-level outer modulus,
inner regularity moduli, and eventual approximation thresholds.  Exact
intertwining makes the transferred finite representative `CauchyNull`-
equivalent to the ordinary dense-stage representative of `TCauchy X`.
Consequently the module proves transferred-norm convergence by applying the
same norm modulus to `TCauchy X`, and then compiles the result to
`BF4WilsonLinearGraphNormLimitApproximation` and `WilsonOperatorNormGapPin`.

`BF4FarautGraphNormContinuumRealization` now has a fully factored
`ContinuumWilsonDenseStageResidualData` endpoint.  On the same selected
continuum object, literal dense-stage maps plus the single modulus construct
the prior graph-norm residual and hence `WilsonMinimalBoundedMassGap`.

No dense stage map, pointwise interacting Wilson transfer lift, vacuum-
complement preservation theorem, or norm modulus is inhabited here.  Those
are the next thermodynamic-limit obligations.  Continuum measure existence,
physical-time/generator identification, the full QFT axioms, and the Clay
theorem remain open.  The focused dense compiler build completed 1263 jobs and
the integrated endpoint build completed 1324 jobs; the forbidden-token scan
was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Summable cross-scale norm variation compiler (2026-08-20)

The dense-stage graph-norm record is now split into reusable exact map data
and its analytic norm control.  The sharper
`BF4WilsonDenseStageEventualVariationApproximation` replaces a freely supplied
global `ModCauchyEv` norm modulus by local cross-scale information: a
nonnegative adjacent-scale variation stream, eventual two-sided step bounds,
explicit inner approximation rates, an antitone cutoff rate, and a summable
tail estimate.

The existing `SummableCRealEventualStepVariation` telescope constructs the
global `ModCauchyEv` record.  The dense-stage compiler then reuses its previous
proof to derive transferred-norm convergence and the continuum Wilson
operator gap.  The AF/Faraut `ContinuumWilsonDenseStageResidualData` endpoint
now consumes this summable-step version directly, so the causal contraction is

`adjacent-scale norm bounds + summable tail + exact transfer intertwining`

`-> graph-norm convergence -> WilsonMinimalBoundedMassGap`.

The remaining norm identification is explicit: the constructive real built
from the telescoped finite norm stream must denote the inner norm of the
selected continuum Wilson representative.  Constructing the continuum GNS
carrier from this same stage system would make that identification structural;
at present it is still an analytic field.  The local step estimates, their
summable BF4 budget, the dense maps, continuum existence, and physical-time
identification are not constructed here.  The focused compiler and integrated
endpoint builds completed 1263 and 1324 jobs respectively; the forbidden-token
scan was empty and exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Cofinal finite-to-continuum dense-norm comparison (2026-08-20)

`BF4PhysicalDenseStageDiagonalComparison` removes the remaining freely pinned
equality between a separately constructed finite-stage norm limit and the
selected continuum norm.  The existing `CauchyGNS` construction already proves
that the raw continuum dense norms converge to `cinnerRep`.  A constructive
cofinal-reindexing theorem preserves that limit along the stage sampler, and a
new Type-level `CRealEventuallyClose` record transports it to the literal
finite BF4 norm stream through explicit outer and inner moduli.

Exact finite/continuum transfer intertwining applies the same argument to the
transferred stream.  The resulting ordinary and transferred convergence laws
compile to the existing graph-norm limit and then to
`WilsonMinimalBoundedMassGap`.  `BF4FarautGraphNormContinuumRealization` now
uses this diagonal comparison endpoint, so neither `normLimitPinned` nor a
separately postulated global finite norm limit remains in the active AF/Faraut
handoff.

The comparison itself is not constructed: the open inputs are the literal
dense-stage observable maps, the interacting pointwise time-translation law,
vacuum-complement preservation, a cofinal sampler, and the vanishing
finite-BF4-versus-continuum-dense norm estimate.  The next reduction should
express that last CReal-level estimate as rational same-observable form bounds,
which are the quantities supplied by lattice measure arguments.  Continuum
measure existence, physical-time/generator identification, the full QFT
axioms, and the Clay theorem remain open.  The focused compiler and integrated
endpoint builds completed 1264 and 1325 jobs respectively; the forbidden-token
scan was empty and exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Rational same-observable norm comparison (2026-08-20)

`BF4PhysicalDenseStageRationalComparison` lowers the active diagonal-limit
hypothesis from completed constructive reals to the rational quadratic forms
that actually occur before completion.  It exposes the finite BF4 form of the
mapped observable and proves definitionally that every approximation of its
constant-completion norm is that rational.  The sampled continuum dense norm
is likewise the constant embedding of the continuum GNS form.

An eventual two-sided rational form bound therefore constructs
`CRealEventuallyClose` with inner approximation rate zero.  Cofinal dense
convergence, exact transfer intertwining, graph-norm limit stability, and the
operator-gap compiler then apply unchanged.  The AF/Faraut dense-stage
residual now consumes this rational comparison record directly.

This is a compiler, not the analytic estimate: the rational finite-versus-
continuum form comparison, dense-stage maps, pointwise time-translation law,
vacuum preservation, continuum construction, physical generator, QFT axioms,
and Clay theorem remain open.  The focused rational compiler and integrated
endpoint builds completed 1265 and 1326 jobs respectively; the forbidden-token
scan was empty and exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Same-object finite/continuum expectation comparison (2026-08-20)

`BF4PhysicalDenseStageExpectationComparison` identifies the two rational forms
from the preceding frontier with their underlying expectation values.  The
finite quantity is the literal BF4 stationary-marginal weighted sum of the
mapped observable squared.  The continuum quantity is the expectation of the
reflected square in the selected OS axiom bundle.  The existing
`WilsonSelectedOSGNSData.expectationPinned` theorem makes this the same
expectation that defines the continuum Wilson GNS form.

An eventual two-sided estimate between those two expectation values now
constructs the rational comparison, cofinal completed-norm convergence,
transferred graph-norm convergence, and selected continuum operator gap.  The
AF/Faraut dense-stage residual has been tightened to consume this measure-level
expectation comparison directly.

The expectation convergence estimate remains an explicit uninhabited field,
as do the dense observable realization, exact time intertwining, vacuum
preservation, continuum construction, physical generator, QFT axioms, and
Clay theorem.  The focused expectation compiler and integrated endpoint builds
completed 1266 and 1327 jobs respectively; the forbidden-token scan was empty
and exported declarations report only `[propext, Quot.sound]`.  No full audit,
remote push, or GitHub CI run was used.

## Projective-functional modulus and diagonal admissibility (2026-08-20)

`BF4PhysicalDenseStageProjectiveComparison` factors same-object expectation
convergence through the projective OS functional already stored in the
selected continuum datum.  `ProjectiveOSRationalModulus` gives the functional
an explicit rational evaluator on the exact `mu.pick` thread, pins its
constructive-real embedding to the existing stage semantics, and retains a
Type-level stage modulus.  The module proves that this rational evaluator
converges to the continuum OS expectation.

The finite BF4 adapter now asks separately for exact identification of its
stationary-marginal expectation with that rational evaluator and for a
diagonal-admissibility law.  The latter is essential: convergence for each
fixed observable does not imply convergence when the sampled dense observable
changes with the cutoff.  These inputs compile through the expectation,
rational, completed-real, and graph-norm layers to the selected continuum
operator gap.  The AF/Faraut residual now consumes this projective-functional
form directly.

The rational projective modulus, finite evaluator pin, admissible diagonal,
dense realization, continuum construction, physical generator, QFT axioms,
and Clay theorem remain open.  The focused projective compiler and integrated
endpoint builds completed 1267 and 1328 jobs respectively; the forbidden-token
scan was empty and exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Vector-adaptive projective diagonal (2026-08-20)

`BF4PhysicalDenseStageAdaptiveProjectiveComparison` removes the unnecessary
requirement that every completed Wilson representative share one global dense
sampling sequence.  Its sampler and cofinality modulus are explicit
Type-level functions of the `CauchyGNS` representative.  The ordinary finite
norm is compared with the continuum dense norm along that representative's
own cofinal diagonal.

The transferred graph-norm leg is now proved directly along the original
representative's sampler.  Exact finite transfer intertwining identifies the
finite transferred square with the stage realization of the translated dense
observable, while the pointwise continuum transfer law identifies the same
term with the selected representative of `T X`.  Therefore no equality or
coherence law between the independently chosen samplers of `X` and `T X` is
assumed.

`BF4FarautGraphNormContinuumRealization` now consumes this adaptive record.
The remaining diagonal input is vectorwise and simultaneous only for the two
observables genuinely needed at each sampled term: its reflected square and
the reflected square of its one-step translate.  Constructing those cofinal
samplers from the pointwise projective rates is the next analytic frontier;
the rational projective modulus, finite evaluator pins, dense realization,
continuum construction, physical generator, QFT axioms, and Clay theorem are
still open.  The focused adaptive compiler and integrated endpoint builds
completed 1268 and 1329 jobs respectively; the forbidden-token scan was empty
and every exported declaration reports only `[propext, Quot.sound]`.  No full
audit, remote push, or GitHub CI run was used.

## Constructed vectorwise slow diagonal (2026-08-20)

`BF4PhysicalDenseStageSlowDiagonalComparison` constructs the sampler that the
adaptive compiler previously accepted as data.  A generic natural-number
threshold ladder accumulates the requirements of successive dense terms, and
an executable bounded search chooses the greatest term whose threshold fits
inside the current finite stage.  The resulting sampler has an explicit
cofinality rate and pays the selected term's requirement by construction.

To cover every positive rational tolerance with one sampler, the module first
regularizes an arbitrary projective modulus along the canonical `invSucc`
precision ladder.  Its running-maximum rate is antitone in tolerance and
retains the original two-sided expectation estimate.  Each vector's threshold
then accumulates both the reflected square of its current dense term and the
reflected square of its one-step translate.  Cofinality plus antitonicity proves
the complete diagonal-admissibility law.

The active AF/Faraut endpoint now consumes
`BF4WilsonDenseStageSlowProjectiveComparison`; sampler choice, sampler
cofinality, and diagonal admissibility are no longer analytic inputs.  The
remaining inputs are the stage observable realization and congruence law,
finite/continuum transfer intertwining, finite evaluator pin, modulus-carrying
projective functional, and vacuum-complement preservation along the constructed
sampler.  Continuum existence, physical generator identification, the QFT
axioms, and the Clay theorem remain open.  The focused slow-diagonal and
integrated endpoint builds completed 1269 and 1330 jobs respectively; the
forbidden-token scan was empty and every exported declaration reports only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Finite rational vacuum certificate (2026-08-20)

`BF4PhysicalDenseStageSlowDiagonalComparison` no longer asks for vacuum
orthogonality as an equality in the completed Type-modulated quotient.  Its
remaining vacuum field is now the exact finite statement
`CentralPhysicalMeanZero` for every stage observable selected by the
constructed slow diagonal.  The new theorem
`centralPhysicalModulatedEmbedV_vacuumOrthogonal_of_meanZero` identifies the
dense observable--vacuum inner product with its stationary weighted mean and
therefore constructs the completed vacuum-orthogonality equality from that
rational certificate.

This lowers the obligation to finite arithmetic but does not yet construct the
certificate.  Automatic centering is not pointwise compatible with the current
transfer field: the finite physical vacuum is transfer-fixed only modulo the
GNS radical on discarded zero-marginal rows.  The next sound interface must
therefore express centered transfer intertwining modulo that radical and prove
that it suffices for the transferred graph-norm comparison.  The finite
evaluator pin, projective modulus, dense realization, same-object continuum
limit, continuum construction, physical generator, QFT axioms, and Clay
theorem remain open.

The focused slow-diagonal target and integrated AF/Faraut endpoint builds
completed 1269 and 1330 jobs respectively; the forbidden-token scan was empty
and exported declarations report only `[propext, Quot.sound]`.  No full audit,
remote push, or GitHub CI run was used.

## Radical-valued centered transfer and vacuum-only graph limit (2026-08-20)

The finite transfer interface has been corrected from pointwise equality to
the physical GNS radical, which is the actual equivalence relation seen by the
quotient and its completion.  `BF4PhysicalCenteredRadicalIntertwining` proves
the exact algebraic bridge: raw transfer intertwining modulo the radical,
stationarity of the finite mean, and transfer-fixity of the finite vacuum
modulo the radical imply transfer intertwining of the automatically centered
observable modulo the radical.  Exact stationary centering simultaneously
constructs `CentralPhysicalMeanZero`, so finite completed vacuum
orthogonality is no longer an independent field.

`BF4PhysicalVacuumGraphNormLimitStability` weakens graph-norm convergence to
the domain on which the operator gap is actually asserted.  Ordinary and
transferred norm convergence are required only when the continuum vector lies
in the selected vacuum complement.  The module proves that this conditional
representative-level data still transports the uniform finite BF4
one-sixteenth estimate to a `WilsonOperatorNormGapPin`.  This avoids the
incorrect demand that exactly centered finite representatives approximate
arbitrary continuum vectors containing a vacuum component.

`BF4PhysicalDenseStageCenteredSlowComparison` combines these two reductions.
Its active conditional record constructs the vector-adaptive slow diagonal,
centers every raw stage observable, proves its radical transfer law and finite
vacuum orthogonality, and derives both graph-norm convergence laws from one
two-sided centered finite/projective comparison on continuum
vacuum-orthogonal vectors.  `BF4FarautGraphNormContinuumRealization` now
consumes this vacuum-complement record and compiles it directly to the
same-object bounded mass-gap endpoint.

The remaining analytic bridge has consequently become narrower but is not
proved: one must construct the raw dense realization and radical-valued
transfer law, the modulus-carrying projective functional, and the conditional
two-sided comparison between the centered finite square and the rational
projective square along the constructed diagonal.  A causal next reduction is
to pin the selected continuum vacuum to the dense unit and split that centered
comparison into an uncentered square comparison plus convergence of the
finite mean to zero for vacuum-complement vectors.  Continuum existence,
thermodynamic and continuum control, physical generator identification, the
full QFT axioms, and the Clay theorem remain open.

The focused centered compiler and integrated AF/Faraut endpoint builds
completed 1272 and 1333 jobs respectively.  Exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Selected dense-unit vacuum and qualitative mean limit (2026-08-20)

`BF4PhysicalSelectedVacuumMeanConvergence` identifies the physical vacuum
structure that was absent from `WilsonSelectedOSGNSData`.  The new
`WilsonDenseUnitVacuumPin` pins the abstract vacuum stored by the selected
transfer operator to the completed dense constant observable and requires the
observable time shift to preserve that unit modulo the Wilson carrier
equivalence.  Dense intertwining then constructs the existing vacuum
stationarity pin, so self-adjointness makes the selected vacuum complement
invariant under one transfer step.

For every explicit cofinal sampler, the module proves that the dense Wilson
pairing with the unit converges to zero when the completed representative is
vacuum orthogonal.  It also proves the corresponding result after one time
step, using the representative-level linear transfer lift and the pointwise
observable translation law.  This is the continuum counterpart of the finite
stationary mean appearing in exact BF4 centering.

The result is deliberately qualitative.  `vacPerp` is a proposition-level
equality in the constructive-real quotient; eliminating its existential
`CReal.Equiv` witness into a `Nat`-valued diagonal rate would use forbidden
choice.  The next interface must therefore carry an explicit Type-level
vacuum-pairing modulus.  It can then combine the finite/projective mean
comparison with the exact identity `centered norm = raw norm - mean^2`.
Continuum existence, the finite/projective estimates, physical generator and
QFT reconstruction, and the Clay theorem remain open.

The focused build completed 1266 jobs.  Exported declarations report only
`[propext, Quot.sound]`.  No full audit, remote push, or GitHub CI run was used.

## Type-level vacuum modulus and raw square/mean compiler (2026-08-20)

`BF4PhysicalVacuumPairingModulus` adds the constructive witness that the
qualitative completed-real statement cannot supply: an explicit `Nat` rate
for the pairing of every selected vacuum-orthogonal representative with the
dense unit.  The modulus is transported through one time step using the
selected vacuum stationarity and pointwise transfer pins.  No witness is
extracted from proposition-level quotient equality.

`BF4PhysicalDenseStageCenteredSlowComparison` now makes its vector-adaptive
slow sampler pay four projective requirements at every selected term: the raw
observable square, the translated square, the vacuum-pairing observable, and
the translated vacuum-pairing observable.  A second outer threshold makes the
selected dense index reach both explicit representative pairing rates.

`BF4PhysicalDenseStageRawMeanComparison` then lowers the remaining centered
finite/projective estimate to two primitive, unconditional rational estimates:
the raw finite square versus the projective reflected-square evaluator, and
the raw finite stationary mean versus the projective vacuum-pairing evaluator.
On the continuum vacuum complement, three quarter-sized mean errors and the
explicit pairing modulus bound the finite mean; an `invSucc` radius makes its
square fit inside half of the requested tolerance.  The exact identity
`centered square = raw square - mean^2` constructs the previous centered
comparison, both graph-norm limits, and the selected completed operator gap.
The AF/Faraut `ContinuumWilsonDenseStageResidualData` endpoint now consumes
this raw square/mean record rather than assuming a centered-square comparison.

This is a strict reduction, not an analytic closure.  The raw dense observable
map and radical transfer law, projective rational modulus, raw-square and
raw-mean finite/continuum estimates, explicit representative vacuum-pairing
modulus, continuum measure, physical generator identification, QFT axioms,
and Clay theorem remain open.  Focused monitored builds completed 1267 jobs
for the pairing modulus, 1275 for the centered sampler integration, 1276 for
the raw compiler, and 1336 for the integrated AF/Faraut endpoint.  The changed
files contain no forbidden proof tokens; every printed load-bearing
declaration reports only `[propext, Quot.sound]`.  No full audit, remote push,
or GitHub CI run was used.

## Fixed-observable raw moments construct the moving diagonal (2026-08-20)

`BF4PhysicalDenseStageRawMomentModulus` replaces a moving-observable
convergence premise by two ordinary pointwise modulus families.  For every
fixed dense observable it carries a `Nat` rate for the raw finite square and a
`Nat` rate for the raw stationary mean, each compared with the corresponding
rational projective evaluator.  Running-maximum regularization makes both
rates antitone in tolerance while retaining their two-sided estimates.

`BF4PhysicalDenseStageCenteredSlowComparison` now makes its executable slow
sampler pay eight rates at each selected term: ordinary and translated
projective square rates, ordinary and translated projective pairing rates,
and the corresponding four raw finite/projective square and mean rates.
Cofinality and antitonicity therefore construct both moving-diagonal raw
comparison laws.  `BF4PhysicalDenseStageRawMeanComparison.ofProjectiveBase`
feeds those theorems into exact centering, graph-norm convergence, and the
completed vacuum-complement operator gap.  The AF/Faraut dense-stage endpoint
now consumes this fixed-observable base directly; moving-diagonal uniformity
is no longer assumed.

This is another strict reduction, not a thermodynamic or continuum proof.
The raw dense realization, its radical-valued transfer intertwining, the
rational projective functional, the fixed-observable raw-square/raw-mean
moduli, the representative vacuum-pairing modulus, and the same-object
continuum measure still require analytic construction.  Physical generator
identification, the complete QFT axioms, and the Clay theorem remain open.
Focused monitored builds completed 1276 jobs for the enriched centered
sampler, 1277 for the raw compiler, and 1337 for the integrated AF/Faraut
endpoint.  Every newly printed load-bearing declaration reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## Exact same-stage semantics construct zero-rate raw moduli (2026-08-20)

`BF4PhysicalDenseStageRawMomentModulus` now exposes an alternative sufficient
route through `BF4RawStageMomentSemanticIdentification`.  It asks for two
same-object identities: the finite raw square and finite raw stationary mean,
embedded in `CReal`, must equal the already selected measure-linked stage
functional on the corresponding continuum square and vacuum-pairing
observables.  The projective stage-functional pin reflects each `CReal`
identity back to exact rational equivalence.  Those equivalences construct
both raw moment modulus families with the identically zero rate.

`BF4WilsonDenseStageCenteredVacuumSemanticBase.toProjectiveBase` packages this
route into the existing fixed-observable projective base.  The raw-mean
compiler and the integrated AF/Faraut endpoint now have direct semantic-base
adapters, so an exact same-stage realization can travel through the already
verified slow diagonal, centering identity, graph-norm limit, and selected
vacuum-complement operator-gap compiler without restating any asymptotic raw
moment estimates.

This route is sufficient but stronger than the general modulus route.  No
semantic identity is inhabited here.  The remaining analytic construction
must still provide either the general fixed-observable raw-square/raw-mean
moduli or these two exact same-stage identities, together with the raw dense
realization, radical transfer intertwining, rational projective functional,
representative vacuum-pairing modulus, and same-object continuum measure.
Physical generator identification, the complete QFT axioms, and the Clay
theorem remain open.  Focused monitored builds completed 1272 jobs for the raw
semantic reduction, 1276 for the centered semantic-base integration, 1277 for
the raw-mean compiler, and 1337 for the AF/Faraut endpoint.  Every newly
printed declaration reports only `[propext, Quot.sound]`; no full audit,
remote push, or GitHub CI run was used.

## Qualitative vacuum convergence bypasses the rate field (2026-08-20)

`BF4PhysicalDenseStageQualitativeVacuumCompiler` proves the graph-norm limits
directly at the proposition-valued convergence layer.  The raw square stream
is connected to the sampled continuum norm through the finite/projective and
projective/continuum comparison legs.  The raw mean stream is connected in the
same way to the sampled dense-unit pairing, whose convergence to zero already
follows qualitatively from vacuum orthogonality and the dense-unit vacuum pin.
Continuity of multiplication and the exact identity
`centered square = raw square - mean^2` then construct both ordinary and
one-step-translated graph-norm limits.

The integrated AF/Faraut endpoint now uses this direct route.  No pairing-rate
field or pairing-rate theorem occurs in the new convergence proofs; only the
underlying `WilsonDenseUnitVacuumPin` is used.  The current input record still
contains the stronger `WilsonDenseUnitVacuumPairingModulus`, so this commit
proves the logical redundancy but does not yet remove the field from the
public residual interface.  That structural weakening is the immediate next
frontier.

This remains conditional finite-to-continuum plumbing, not an analytic
construction of the physical thread.  The raw realization, radical transfer
law, projective rational functional, raw moment moduli or exact stage
semantics, dense-unit vacuum pin, continuum measure, generator identification,
QFT axioms, and Clay theorem remain open.  Focused monitored builds completed
1278 jobs for the qualitative compiler and 1338 for the integrated endpoint;
the printed load-bearing declarations report only `[propext, Quot.sound]`.

## Weak semantic endpoint removes the vacuum-pairing modulus (2026-08-20)

`BF4WilsonDenseStageCenteredVacuumQualitativeSemanticBase` is the strictly
weaker exact-semantic input.  It retains the raw dense-stage realization,
radical-valued transfer intertwining, rational projective functional, exact
same-stage square/mean identities, and `WilsonDenseUnitVacuumPin`, but carries
no representative pairing rate or smallness theorem.  A follow-on dependency
audit also removes `rawStageObservable_congr` from this weak interface: the
qualitative compiler operates on selected representatives and never consumes
that setoid-congruence law.  The legacy quantitative route retains it.

`BF4PhysicalDenseStageQualitativeVacuumCompiler` constructs an executable
cofinal slow diagonal using only the four regularized projective rates for the
ordinary/translated square and vacuum-pairing observables.  Exact stage
semantics give identically-zero raw square and mean comparison rates.  The
result feeds the already checked qualitative convergence argument and hence
the selected completed vacuum-complement operator gap.

`ContinuumWilsonDenseStageQualitativeSemanticResidualData` exposes this weaker
route at the AF/Faraut same-object endpoint.  From that named input it builds
the graph-norm residual and the positive exact-log bounded mass-gap package.
This does not inhabit the residual or construct a continuum theory: the raw
physical realization, transfer law, projective functional, exact stage
identities, dense-unit vacuum pin, continuum measure, generator
identification, full QFT axioms, and Clay theorem remain open.  Focused
monitored builds completed 1276 jobs for the split input structure and 1278
for the qualitative compiler, and 1338 jobs for the integrated endpoint.
Every printed load-bearing declaration reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## General raw-moment endpoint removes the pairing modulus (2026-08-20)

`BF4WilsonDenseStageCenteredVacuumQualitativeProjectiveBase` extends the
interface reduction from the exact-semantic branch to the general
fixed-observable branch.  It carries the raw square and mean modulus families
and `WilsonDenseUnitVacuumPin`, but neither a representative pairing modulus
nor the unused raw-carrier congruence law.

`BF4WilsonDenseStageQualitativeProjectiveCompiler` builds one executable slow
diagonal paying eight pointwise rates: the ordinary/translated projective
square and pairing rates, and the ordinary/translated raw square and mean
rates.  These yield the moving raw comparison laws; qualitative vacuum
convergence then supplies both centered graph-norm limits and the selected
completed operator gap without choosing a vacuum-pairing rate.

`ContinuumWilsonDenseStageQualitativeResidualData` exposes this general weak
route at the AF/Faraut endpoint.  The exact-semantic residual is proved to
specialize it by constructing zero-rate raw moment moduli.  This is still a
conditional compiler, not an inhabitant: the raw physical realization,
radical transfer law, projective functional, fixed-observable raw moment
moduli (or stronger exact identities), qualitative vacuum pin, continuum
measure, generator identification, QFT axioms, and Clay theorem remain open.
Focused monitored builds completed 1276 jobs for the input/refinement layer
and 1278 for the general qualitative compiler, and 1338 jobs for the
integrated endpoint.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Direct raw-to-continuum moment certificate (2026-08-20)

`BF4RawStageContinuumMomentModulus` isolates the fixed-observable statement
actually needed after the finite BF4 carrier is constructed: its raw square
and stationary mean converge, with Type-level rates, directly to the selected
continuum Wilson square and vacuum-pairing expectations.  The certificate no
longer exposes a rational evaluator on every OS observable or a separate
finite/projective and projective/continuum split.

`BF4RawStageMomentModulus.toContinuumMomentModulus` proves that the preceding
two-leg projective input constructs the direct certificate by a half-error
composition.  Antitone regularizations and their retained bounds are proved
for both direct moment rates.  Thus the new interface is a genuine weakening,
not an unrelated alternative; integrating its four-rate slow diagonal is the
next compiler step.

No direct moment certificate is inhabited here.  Constructing the raw stage
observable, its moment convergence on the interacting continuum thread, the
transfer/vacuum pins, continuum measure, QFT axioms, and Clay theorem remains
open.  A focused monitored build completed 1272 jobs, and every newly printed
declaration reports only `[propext, Quot.sound]`.

## Four-rate direct-moment endpoint (2026-08-20)

`BF4PhysicalDenseStageDirectMomentCompiler` now consumes the direct
`BF4RawStageContinuumMomentModulus` certificate at the graph-norm frontier.  It
constructs a cofinal slow diagonal paying exactly four rates: the raw square
and stationary mean for a selected representative and its one-step translate.
Direct raw-moment convergence, qualitative dense-unit vacuum convergence, and
the exact centering identity then give the ordinary and transferred graph-norm
limits required by the completed vacuum-complement operator-gap compiler.

The public general endpoint
`ContinuumWilsonDenseStageQualitativeResidualData` now carries this weaker
direct base.  Its former rational-functional/projective-moment input refines
the direct certificate by the proved half-error composition, and the exact
same-stage semantic route refines it through the existing zero-rate adapter.
Thus neither an all-observable rational projective functional nor an
intermediate projective diagonal is required by the public general endpoint.

This is still a conditional compiler, not a construction of the input data.
The actual continuum measure and selected OS/GNS thread, the raw-stage
observable, radical transfer intertwining, direct fixed-observable moment
moduli, qualitative vacuum pin, generator identification, full QFT axioms,
and Clay theorem remain open.  Focused monitored builds completed 1279 jobs
for the direct compiler and 1339 jobs for the integrated AF/Faraut endpoint.
Every newly printed load-bearing declaration reports only
`[propext, Quot.sound]`; no full audit, remote push, or GitHub CI run was used.

## Representative-only direct-moment endpoint (2026-08-20)

The direct four-rate route no longer assumes a linear continuum transfer.
`WilsonPointwiseRepresentativeTimeTranslationPin` carries only a chosen Cauchy
representative of the actual selected transfer, its quotient-class equation,
and termwise agreement with the observable shift.  The former pointwise
linear pin constructs this smaller record, but the converse is not required.

`BF4PhysicalDenseStageDirectMomentCompiler` now derives a
`BF4WilsonVacuumRepresentativeGraphNormLimitApproximation` directly.  The
AF/Faraut `ContinuumWilsonGraphNormResidualData` is weakened to that same
representative-only endpoint; its previous linear graph-norm input remains a
sufficient refinement through a proved adapter.  Consequently additivity,
scalar homogeneity, and the full `LinearTransferOperator` interface are no
longer premises of the direct bounded operator-gap route.

This does not construct the representative lift or any analytic continuum
input.  The selected continuum measure/OS-GNS object, representative transfer
lift and termwise law, raw-stage realization and radical intertwining, direct
moment moduli, vacuum pin, generator identification, full QFT axioms, and Clay
theorem remain open.  Focused monitored builds completed 1279 jobs for the
direct compiler and 1339 jobs for the integrated endpoint.  Every newly
printed declaration reports only `[propext, Quot.sound]`.

## Stationary dense-unit vacuum reduction (2026-08-20)

`WilsonDenseUnitStationaryVacuumPin` isolates the two vacuum facts actually
used by the direct graph-norm proof: the selected completed vacuum is the
embedded constant unit, and that completed vacuum is stationary under the
actual transfer.  Dense vacuum-pairing convergence is reproved from this
smaller record.  The former `WilsonDenseUnitVacuumPin`, which additionally
requires the carrier-level equation `tau(one) ~ one`, constructs it through a
proved adapter and remains available to the older routes.

The public four-rate direct-moment base now consumes the stationary dense-unit
record.  Hence the observable-level unit-preservation equation is no longer an
analytic premise of the direct bounded operator-gap endpoint.  This is an
interface contraction only: neither the dense-unit identification nor
stationarity is constructed for a physical continuum Wilson theory.

Focused monitored builds completed 1266 jobs for the mean-convergence layer,
1279 jobs for the direct compiler, and 1339 jobs for the integrated endpoint.
Every newly printed declaration reports only `[propext, Quot.sound]`.  The
continuum measure/OS-GNS construction, representative transfer lift, raw-stage
map and radical intertwining, direct moments, generator identification, full
QFT axioms, and Clay theorem remain open.

## Actual-transfer graph-moment endpoint (2026-08-20)

`BF4RawStageContinuumGraphMomentModulus` records the four estimates used by
the direct graph-norm proof: square and stationary mean of the raw finite
observable, and square and stationary mean after applying the literal finite
BF4 macro transfer.  The transferred targets are the corresponding selected
continuum moments of the one-step observable shift.

The public direct base now consumes this graph-moment certificate and no
longer requires an exact radical equation between the finite transferred
observable and a separately realized continuum translate.  The former direct
moment certificate together with radical intertwining constructs the new
record: `B_welldef` transports the square, and radical invariance of the
stationary mean transports the linear moment.  The transferred centered norm
is then obtained internally from the already-proved exact identity that the
finite Markov operator commutes with stationary centering modulo the radical.

This contraction replaces an exact cross-scale structural identity by the two
observable estimates actually needed after transfer; it does not prove those
estimates for the interacting continuum thread.  Focused monitored builds
completed 1279 jobs for the compiler and 1339 jobs for the integrated
endpoint.  Every newly printed declaration reports only
`[propext, Quot.sound]`.  Continuum construction, the representative lift,
raw-stage realization, four graph-moment moduli, stationary dense-unit pin,
generator identification, QFT axioms, and the Clay theorem remain open.

## Representative-targeted graph moments remove the pointwise shift law (2026-08-20)

`WilsonRepresentativeTimeTranslationPin` now isolates only a chosen Cauchy
representative of the actual quotient-level transfer and its class equation.
`BF4RawStageContinuumRepresentativeGraphMomentModulus` targets the transferred
finite square and mean directly at the corresponding terms of that chosen
representative.  Its rates may depend constructively on both the source
Cauchy representative and the sampled index, which the existing slow-diagonal
construction already supports.

The public direct base now uses these two records.  It therefore assumes
neither continuum-transfer linearity nor a termwise identification with the
observable shift `tau`.  The former pointwise representative pin and
observable-shift graph moments construct the new representative-targeted
certificate by the Wilson form-congruence laws; the older projective and
exact-semantic routes consequently continue to refine the public endpoint.

This is the current minimal four-moment compiler interface, not an inhabitant.
The continuum construction must still supply a representative lift of the
actual transfer, a raw finite-stage realization, ordinary and transferred
moment convergence along that lift, and the stationary dense-unit pin.
Focused monitored builds completed 1279 jobs for the compiler and 1339 jobs
for the integrated endpoint.  Every newly printed declaration reports only
`[propext, Quot.sound]`; generator identification, the full QFT axioms, and
the Clay theorem remain open.

## Finite-stage closure and the genuine cross-scale cut (2026-08-20)

A dependency audit of `BF4PhysicalMarkovGNSCompletion` and
`BF4PhysicalCompletedMacroCorrelator` confirms that the finite side of the
current bridge is already concrete.  At every matched cutoff the repository
constructs the physical GNS carrier, the completed Markov transfer, its
normalized stationary vacuum, preservation of the completed vacuum
complement, and the equality between the selected same-object finite
correlation and the completed matrix coefficient.  The producer supplies the
uniform `1/16` contraction on that same finite carrier.

The first missing causal arrow is therefore cross-scale, not operator
theoretic.  One must construct a single selected continuum OS/GNS object and
coherently realize its Cauchy representatives in the varying finite carriers,
with the four ordinary/transferred moment moduli now isolated by the direct
compiler.  The current `ContinuumMeasure` supplies a constructive inverse-limit
thread from an already consistent abstract family; it does not construct the
finite probability-measure carriers, prove Wilson-family consistency, perform
the constructive sigma-additive extension, or prove the required moment
convergence.

This audit adds no theorem and makes no continuum claim.  It identifies the
next mathematical frontier as constructive measure/coarsening and Wilson
moment convergence on the actual BF4 family.  The finite carrier, transfer,
vacuum, and same-object correlator files were inspected here but not rebuilt in
this audit; the newly integrated direct endpoint remains covered by the 1279-
and 1339-job monitored builds above.

## Actual finite BF4 probability functional (2026-08-20)

`BF4PhysicalFiniteProbFunctional` packages the already-constructed physical
row marginal as a genuine `ObservableMeasure.ProbFunctional` at every finite
matched BF4 stage.  Because the repository's raw rational type stores
unreduced fractions while `ProbFunctional.normalized` asks for structural
equality, the observable carrier uses a distinguished tagged unit and literal
rational functions.  The unit has expectation definitionally `1`; literal
functions retain exactly `centralPhysicalStationaryMean`, and the two
constant-one representations are proved equivalent in `Q'.eqv`.

Positivity is the existing physical weighted-square theorem.  The new bridge
also proves that the functional's literal `a* b` moment is definitionally the
same `centralPhysicalWeightedInner` used by the physical GNS completion, and
that expectation is stationary under the exact physical Markov action.
Consequently the probability-functional, GNS, transfer, and vacuum data now
refer to the same concrete finite object rather than parallel abstractions.

This constructs no cross-scale map or limit.  A monitored focused build of the
combined endpoint below rebuilt 1079 jobs; every newly printed declaration is
within `[propext, Quot.sound]`.

## Direct BF4 functional limit from an explicit modulus (2026-08-20)

`BF4PhysicalFunctionalLimit` contracts an explicit cross-scale tail modulus
for the actual matched-stage expectations into a positive normalized
`CRealProbFunctional`.  The modulus contains a Type-level rate and is pinned
at every scale to `matchedPhysicalProbFunctional`; the constructed continuum
functional's rational approximations are therefore exactly the finite BF4
expectations, not an unrelated supplied sequence.  Exact one-step
Kolmogorov equality is not required for this direct pointwise limit.

The public input `MatchedPhysicalFunctionLimitModulus` requests convergence
only for literal edge observables.  Convergence of the tagged unit is
constructed internally as the constant-one, zero-tail modulus.  Thus the
remaining analytic edge is precise: provide uniform two-sided tail estimates
for the stationary BF4 expectation of every intended literal observable.

No inhabitant of that modulus is constructed here.  The resulting object is
only a positive normalized functional on the current rational observable
carrier; Euclidean covariance, reflection positivity on a positive-time
algebra, OS reconstruction, non-triviality, transfer convergence, the uniform
completed gap, the full QFT axioms, and the Clay theorem all remain open.  A
source check and focused monitored build completed successfully, the latter
with 1079 jobs, and every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Fixed-nome BF4 representation-cutoff functional (2026-08-20)

`BF4PhysicalCutoffProbFunctional` applies the already-proved executable
degree-thirteen cutoff modulus to the actual normalized corrected-slab BF4
expectations.  Cutoff-stable `[0,1]` observables are closed constructively
under the constant unit, pointwise multiplication, and identity star, giving
the minimal `ObsAlg` needed by the probability-functional interface.  At each
fixed rational `0 < w < 1` and fixed finite slab extent, their exact cutoff
expectations therefore form a genuine positive normalized
`CRealProbFunctional` after the Peter--Weyl cutoff is removed.

The functional is unconditional beyond the explicit nome inequalities: its
normalization is the exact finite partition divided by itself modulo
`Q'.eqv`, positivity is inherited approximation by approximation from the
nonnegative BF4 weights, and every `CReal` approximation is definitionally the
finite normalized BF4 expectation at that cutoff.  This is the first actual
BF4 limit-functional inhabitant on the current route, rather than a compiler
waiting for a modulus.

Only the representation cutoff is removed.  The nome, finite geometry, and
volume are fixed; the carrier is multiplicative but not additive, and no
linearity is claimed.  Identification with the stationary row-marginal/GNS
functional, uniformity as nome and extent vary, the thermodynamic and spacing
limits, OS reconstruction, the uniform completed gap, and the Clay theorem
remain open.  A source check and focused monitored build completed
successfully, the latter with 784 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Fixed-cutoff slab expectations are the physical stationary GNS moments (2026-08-20)

`BF4PhysicalCutoffStationaryBridge` closes the one-sided finite reindex edge.
The existing ordered bilinear full-slab theorem is specialized with the upper
coefficient equal to one; zero-marginal rows are removed exactly, and the
common partition normalization is carried through the finite sums.  Hence at
every representation cutoff the corrected-slab expectation of a bounded
lower pullback is `Q'.eqv` to `centralPhysicalStationaryMean`.

The transferred cutoff modulus then constructs
`centralPhysicalStationaryCutoffLimit`, whose `K`-th approximation is
definitionally the physical stationary mean at cutoff `K`.  These limits form
the positive normalized
`centralPhysicalStationaryCutoffProbFunctional`.  Its finite `a* b`
approximations are definitionally `centralPhysicalWeightedInner`, the exact
pairing used by the already-constructed physical BF4 GNS completion.  Thus
the cutoff-removed functional, stationary marginal, and finite GNS now refer
to the same moments rather than merely parallel finite descriptions.

The nome and finite half-extent remain fixed, and only globally `[0,1]`-valued
lower observables are carried; the algebra is multiplicative but not additive.
No cutoff limit of the transfer operator, thermodynamic/spacing uniformity,
OS reconstruction, completed limiting gap, or Clay theorem is proved.  A
focused monitored build completed 979 jobs, followed by a clean source check
after adding the explicit weighted-inner identity.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Dense Markov radical descent from pointwise Cauchy data (2026-08-21)

`BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy` proves that the
previously separate dense radical-closeness input follows from any
`CentralPhysicalLinearMarkovDenseCauchyData`.  Markov recoding preserves the
explicit inner rate of the limiting squared distance exactly.  Once a cutoff
pays that rate, the exact finite-cutoff contraction yields a limiting
nonexpansive estimate with an explicit rational slack.

For a null dense input pair, sampling the estimate at half the requested
tolerance gives a concrete output-closeness modulus; the other half absorbs
the null input distance.  Thus
`CentralPhysicalLinearMarkovDenseCauchyData.toDenseRadicalData` constructs the
dense null-quotient transfer without any additional analytic hypothesis.

This does not construct nonconstant pointwise cross-cutoff moduli or the
stronger arbitrary-completion transfer.  The next frontier remains an
adaptive two-index construction for an arbitrary input representative and
proof that it respects close representatives.  The cofinal finite
sixteenth, nome/volume/spacing limits, continuum QFT, and the Clay theorem
remain open.  A source check and focused monitored build completed
successfully, the latter with 1261 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Adaptive two-index Markov completion schedule (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule` replaces the
unjustified same-index requirement on `P_n(X_n)` by an executable slow
diagonal.  At action cutoff `K`, it selects the largest input index `i` whose
cumulative obligations fit inside `K`.  The obligation at `i` is a finite
running maximum over every earlier anchor `j <= i`: it pays both the
cross-cutoff modulus of the fixed observable `X_j` and the inner regularity
of the squared distance from `X_i` to `X_j`.

Both kinds of rate are regularized constructively along the canonical
`invSucc` precision ladder.  The main simultaneous admissibility theorem
proves that one explicit late-stage bound makes the selected index cofinal
past any requested anchor and pays the two rates at independently chosen
positive tolerances.  A regularized version of limiting same-cutoff
nonexpansiveness is also proved for direct use by the completion diagonal.

This constructs the schedule and all of its local witnesses, but does not yet
package `K |-> P_K(X_i(K))` as a Cauchy representative or prove quotient
descent.  Those are the immediate next contraction steps.  Nonconstant
pointwise cross-cutoff data, the cofinal finite sixteenth, thermodynamic/nome/
spacing limits, continuum QFT, and the Clay theorem remain open.  A source
check and focused monitored build completed successfully, the latter with
1301 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Adaptive two-index Markov output is Cauchy (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy` contracts the adaptive
schedule into an actual Cauchy representative for every input completion
representative.  Its sequence is the honest two-index diagonal
`K |-> P_K(X_{i_X(K)})`, with the input selector depending constructively on
the representative and the action cutoff.

For two late action cutoffs, the proof chooses one fixed earlier input anchor.
Input Cauchyness plus regularized same-cutoff nonexpansiveness controls both
outer action legs, while the supplied pointwise cross-cutoff modulus controls
the middle leg.  Two applications of the sqrt-free squared-distance triangle
cost ten copies of a sixteenth tolerance, which are proved rationally to fit
inside the requested tolerance.

This removes the diagonal-Cauchy field of the old
`CentralPhysicalLinearMarkovCompletionModulus`: pointwise dense Cauchy data now
suffice to construct an output Cauchy sequence for every arbitrary input
representative.  Quotient well-definedness for close input representatives is
the remaining immediate transfer-construction edge.  Nonconstant pointwise
data, the cofinal finite sixteenth, thermodynamic/nome/spacing limits,
continuum QFT, and the Clay theorem remain open.  A source check and focused
monitored build completed successfully, the latter with 1302 jobs.  The
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Adaptive completed Markov transfer from pointwise data (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer` proves that close
input representatives have close adaptive output diagonals, even though their
slow input samplers are chosen independently.  A pair-dependent rate selects
one common fixed raw anchor, pays both representatives' selected-to-anchor
rates, and pays the anchor-to-anchor rate induced by the supplied input
closeness.  Three same-cutoff nonexpansive legs and the reusable
ten-sixteenths estimate finish quotient descent.

Therefore any `CentralPhysicalLinearMarkovDenseCauchyData` now constructs the
actual endomap `centralPhysicalAdaptiveCompletedMarkovTransfer` of the whole
cutoff-removed physical completion.  The map is representative-independent,
agrees exactly with the previously proved dense cutoff limit on every embedded
finite-linear observable, and fixes the normalized completed vacuum.

This bypasses both fields of the historical same-index
`CentralPhysicalLinearMarkovCompletionModulus` for existence of a completed
transfer.  The next frontier is to prove rational linearity of the adaptive
map and reconnect its own sampled graph norms to the cofinal finite
sixteenth.  Nonconstant pointwise cross-cutoff data remain uninhabited, and
thermodynamic/nome/spacing limits, continuum QFT, and the Clay theorem remain
open.  Source checks and a focused monitored build completed successfully,
the latter with 1303 jobs.  Every printed load-bearing declaration reports
only `[propext, Quot.sound]`.

## Adaptive completed transfer preserves zero and addition (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd` proves the zero and
addition laws for the new representative-dependent adaptive transfer.  Zero
follows from its exact agreement with the dense transfer.  Addition requires
a new quotient-level comparison because the representatives of a sum and of
its two summands select three independent slow input indices.

The comparison chooses one common fixed raw anchor.  The sum representative
contributes one sixteenth, the two component representatives contribute four
sixteenths through the proved quadratic-Lipschitz addition estimate, and the
final squared-distance triangle contributes ten sixteenths in total.  The
explicit rational budget closes below the requested tolerance.

Thus the adaptive completed transfer is now an additive pointed endomap.
Rational-scalar compatibility is still required before it can be bundled as a
completed `Q'`-linear endomorphism.  Nonconstant pointwise cross-cutoff data,
the cofinal finite sixteenth, thermodynamic/nome/spacing limits, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1304 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Adaptive completed transfer is rational-linear (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear` proves scalar
compatibility for the adaptive transfer and packages all three laws as
`centralPhysicalAdaptiveCompletedMarkovQLinearEndomorphism` on the concrete
completed physical carrier.  This is not pointwise bookkeeping: the scaled
representative and the original representative select independent slow input
indices.

The proof compares both selected terms with one common raw anchor.  It
controls the scaled representative at one quarter of the requested squared-
distance tolerance, asks the unscaled representative for the constructive
`scaleTolerance (scalar * scalar)` needed by scalar continuity, and transports
that bound through scaling.  One sqrt-free triangle then costs exactly four
quarters.

Consequently pointwise dense cross-cutoff data alone now construct a genuine
completed rational-linear transfer operator; the old same-index
`CentralPhysicalLinearMarkovCompletionModulus` is no longer needed for this
operator's existence, quotient descent, or linearity.  Adaptive vacuum
pairing/graph norms and their connection to a cofinal finite sixteenth are the
next contraction frontier.  The nonconstant pointwise data, finite cofinal
sixteenth, thermodynamic/nome/spacing limits, continuum QFT, and the Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1305 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Adaptive transfer pays all graph-diagonal rates (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule` composes the earlier
graph-admissible representative sampler with the new adaptive Markov sampler.
It first constructs the input-side sequence selected by the Markov schedule
and proves that this sequence is Cauchy, close to the original representative,
and therefore denotes the same completed point.

For a graph-normalized representative, cofinality of the second sampler puts
every selected input index beyond the requested graph-diagonal rate.  The
selected index is also bounded by the current action cutoff.  Consequently
the input self-pair and vacuum-pair inner rates are paid at the action cutoff;
exact Markov syntax-rate invariance pays the corresponding two action rates.

This supplies all four rate obligations needed to diagonalize the input and
adaptive-action graph moments using only pointwise dense cross-cutoff data.
The next contraction step is to turn those paid rates and exact finite
stationarity into completed vacuum-pairing invariance and a transfer on the
completed vacuum complement.  Nonconstant pointwise data, the cofinal finite
sixteenth, thermodynamic/nome/spacing limits, continuum QFT, and the Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1306 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Adaptive transfer preserves the completed vacuum complement (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement` contracts the four
paid graph rates with exact finite stationarity.  For each graph-normalized
representative, its input-side adaptive reindexing and its actual adaptive
Markov image have convergent vacuum-pairing diagonals; stationarity identifies
the two diagonal terms at every cutoff, and representative well-definedness
returns the input limit to the original completed point.

This proves a completed vacuum-pairing invariant for the new transfer.
Therefore it preserves the actual completed vacuum complement and restricts
to `centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer`, bundled
as a rational-linear endomorphism of that concrete subtype.

The construction uses only pointwise dense cross-cutoff data and removes the
historical same-index completion modulus from the carrier, transfer,
linearity, vacuum-pairing, and vacuum-complement chain.  The next contraction
frontier is convergence of the two centered graph-norm streams and transport
of a cofinal finite sixteenth to a completed strict contraction.  Nonconstant
pointwise data, the cofinal finite sixteenth, thermodynamic/nome/spacing
limits, continuum QFT, and the Clay theorem remain open.  A source check and
focused monitored build completed successfully, the latter with 1308 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Cutoff-two restricted physical-kernel bridge boundary (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck` and its 65
process-isolated row modules now prove that every stored row weight in the
exact cutoff-two sector table is the sum of its 65 stored kernel entries.
Each individual Boolean row check is axiom-free; the aggregate rational
equality uses only `[propext, Quot.sound]`.

`BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge` isolates the other
representation obligation as
`CutoffTwoSectorPhysicalTableCertificate`: all 65 generated recurrence rows
must agree with the stored exact table.  Conditional on precisely this finite
certificate, every stored entry is proved equal to the production
`centralPhysicalReflectedKernel` restricted to the literal sector states, and
every stored row weight is therefore the exact production restricted row
sum.  The bridge proof itself passed both a direct source check and a focused
dependency-complete build, the latter with 1668 jobs, at exactly
`[propext, Quot.sound]`.

The physical-table certificate is deliberately not inhabited here.  A prior
monolithic attempt to check all physical rows was stopped by the monitored
builder when available memory reached the 12 GiB reserve and is not recorded
as passed.  Thus the existing `49/50` theorem is still a verified exact-table
sector gap plus an explicit conditional production bridge, not yet a fully
discharged production-kernel sector gap.  The next finite frontier is to
inhabit that certificate with crash-safe physical-row shards or replace it by
a more structural recurrence equality.  Compatible sector selection across
cutoffs, completion, thermodynamic/continuum control, QFT axioms, and the Clay
conclusion remain open.

## Adaptive completed graph-norm convergence (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm` diagonalizes the two self-pair
streams paid by the composed schedule.  For the input-side adaptively sampled
representative `Z`, its raw self-pair and vacuum-pair diagonals converge; the
same is true for the actual adaptive Markov output.

A new same-cutoff theorem identifies the literal finite transferred centered
norm directly with the adaptive action diagonal, without mentioning or
inhabiting the historical completion modulus.  Completed vacuum orthogonality
then makes both mean-square corrections converge to zero.  Therefore the
centered finite norm stream converges to the completed squared norm of `Z`,
and the transferred centered stream converges to the completed squared norm
of its adaptive image.

These are precisely the two graph-limit edges needed to transport finite
strictness to the new completed operator.  The next step is to reindex them
along a supplied cofinal family of finite `1/16` cutoffs and construct the
completed strict-contraction datum.  Nonconstant pointwise data, that cofinal
finite certificate, thermodynamic/nome/spacing limits, continuum QFT, and the
Clay theorem remain open.  A source check and focused monitored build
completed successfully, the latter with 1309 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Pointwise-data adaptive cofinal completed gap (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap` reindexes the two new
centered graph streams along a supplied
`FixedNomeCofinalCenteredSixteenth`.  At each selected cutoff, the existing
genuine finite completed operator theorem bounds the transferred squared norm
by `(1/16)^2` times the input squared norm.  Constructive limit order carries
that inequality to the actual cutoff-removed adaptive transfer.

The result is
`centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData`: strict
squared-norm contraction at literal rate `1/16` on the actual completed
vacuum complement.  A companion compiler accepts the more geometric cofinal
local-gluing certificate directly.

This removes `CentralPhysicalLinearMarkovCompletionModulus` from the entire
fixed-nome implication: pointwise dense cross-cutoff Cauchy data plus a
cofinal finite sixteenth now suffice for the completed carrier, linear
transfer, vacuum complement, graph norms, and strict contraction.  Neither
remaining input is inhabited.  Thermodynamic/nome/spacing limits, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1313 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Iterated pointwise-data adaptive contraction (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveContraction` defines natural powers of
the actual pointwise-data adaptive transfer restricted to the actual completed
physical vacuum complement.  Induction on the power proves the same-object
geometric squared-norm estimate
`<T^n v,T^n v> <= (q^2)^n <v,v>` from any adaptive strict-contraction datum.

Specialized corollaries instantiate the rate with the literal `1/16` supplied
by either `FixedNomeCofinalCenteredSixteenth` or the stronger
`FixedNomeCofinalLocalGluing`.  Thus the causal chain from cofinal finite
strictness through the completed adaptive operator to all discrete time powers
is now kernel-checked without the historical same-index completion modulus.

This theorem constructs neither the nonconstant pointwise dense Cauchy data
nor either cofinal finite certificate.  It remains at fixed nome and fixed
finite half-volume; thermodynamic/nome/spacing limits, continuum QFT, and the
Clay theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1314 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Pointwise-data adaptive same-object correlation decay (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay` combines the new
iterated adaptive norm bound with the already proved Cauchy--Schwarz inequality
on the identical cutoff-removed completed physical carrier.  For every
completed vacuum-orthogonal vector `v` and arbitrary completed test vector, it
proves geometric decay of the squared matrix coefficient
`<T^n v,test>^2`.

Concrete cofinal and local-gluing corollaries carry the literal factor
`((1/16)^2)^n`.  This closes the fixed-nome causal implication from pointwise
cross-cutoff control and cofinal finite strictness to same-object completed
correlation decay, without a same-index completion modulus and without
identifying distinct cutoff carriers.

The two analytic inputs remain uninhabited, and the theorem remains at fixed
nome and fixed finite half-volume.  Uniform thermodynamic/nome/spacing limits,
continuum reconstruction and QFT axioms, and the Clay theorem remain open.  A
source check and focused monitored build completed successfully, the latter
with 1315 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Atomic reduction of the pointwise Markov Cauchy residual (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAtomicCauchy` replaces the open demand for an
independent cross-cutoff Cauchy modulus on every finite rational-linear syntax
tree by `CentralPhysicalLinearMarkovAtomicCauchyData`: one modulus for each
atomic physical `[0,1]` observable.

Structural recursion supplies the zero case unconditionally and uses the
already proved completion-continuity of addition and rational scaling to
construct all composite cases.  The resulting
`CentralPhysicalLinearMarkovAtomicCauchyData.toDenseCauchyData` is exactly the
pointwise input consumed by the adaptive completed carrier, transfer, vacuum
complement, strict gap, powers, and correlation-decay chain.

No nonconstant atomic modulus is inhabited here.  The remaining cross-cutoff
analytic residual is now confined to bounded atoms instead of redundantly
including their finite-linear closure.  The independent cofinal finite
sixteenth and all thermodynamic/nome/spacing and continuum obligations remain
open.  A source check and focused monitored build completed successfully, the
latter with 1151 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Uniform pointwise compiler for atomic Markov Cauchy data (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy` proves a general normalized
average theorem: a global pointwise squared bound between two finite-linear
observables bounds their distance in the cutoff-removed physical GNS form by
the same rational.  At every finite approximation, positivity permits
termwise comparison and exact total stationary mass one removes the average.

The sufficient certificate
`CentralPhysicalAtomicMarkovUniformSqCauchyData` therefore compiles finite
rational pointwise convergence of each recoded atomic Markov image into the
atomic and full dense Cauchy data used downstream.  This is an explicit route
from a kernel estimate to the actual completed transfer, rather than a
completed-space assumption.

This uniform certificate is deliberately recorded only as sufficient, not as
necessary or inhabited.  Global sup control may be stronger than the natural
moving-carrier estimate because states entering between two cutoffs form an
asymmetric shell.  Splitting common-carrier convergence from shell mass is the
next sharper frontier.  The cofinal finite sixteenth and all thermodynamic/
nome/spacing and continuum obligations remain open.  A source check and
focused monitored build completed successfully, the latter with 1152 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Moving-carrier core--tail compiler for atomic Markov data (2026-08-21)

`BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy` replaces the overly strong
global pointwise certificate by the finite decomposition naturally seen by a
moving representation carrier.  The stationary finite GNS distance between
two recoded atomic Markov images is bounded by the sum of (i) a pointwise
squared error on a fixed old lower-face carrier and (ii) the stationary row-
marginal mass outside that carrier.  The shell estimate uses only the proved
`[0,1]` range of the two Markov images, while an exact Boolean partition and
row-marginal normalization perform the contraction.

`CentralPhysicalAtomicMarkovCoreTailCauchyData` assigns half of each requested
epsilon to the core and half to the shell and compiles these finite rational
estimates into the atomic and dense Cauchy data used by the adaptive completed
transfer and correlation-decay chain.  Thus the remaining atomic convergence
problem has been causally separated into old-core conditional-kernel
convergence and stationary moving-shell tightness.

Neither analytic estimate is inhabited here.  In particular, the existing
fixed-carrier normalized joint-kernel Cauchy estimate still has to cross the
conditional ratio through a positive row floor, and shell tightness remains a
separate stationary-measure input.  The cofinal finite sixteenth and all
thermodynamic/nome/spacing and continuum obligations also remain open.  A
source check and focused monitored build completed successfully, the latter
with 1153 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Old-row joint-kernel `l1` contraction (2026-08-21)

`BF4PhysicalCutoffConditionalCoreReduction` contracts the already-proved
degree-thirteen normalized joint-kernel entry modulus across one complete old
target row.  For an old carrier with `N` targets, it requests entry tolerance
`epsilon / N`; exact finite summation cancels the dimension and proves

`sum_oldTargets |J_first(source,target) - J_second(source,target)| <= epsilon`

for every supported old source and every two cutoffs beyond the executable
schedule.  This is an inhabited theorem derived from the existing physical
cutoff convergence, not a new residual assumption.  The preceding core--tail
compiler was also sharpened so its core hypothesis includes the exact
zero-outside support condition used by the old enumerated carrier, avoiding an
unnecessary demand on illegal labellings.

This closes the common old-row joint-numerator component only.  Passing to the
conditional Markov row is now backed by the constructive rational theorem
`divPos_conditioning_abs_sub_le`: if two nonnegative numerators lie below their
positive marginals, their conditioned values differ by at most the sum of the
numerator and marginal errors divided by a common positive row floor.  Thus
the division step itself is closed without field tactics or hidden
cancellation.  Instantiating it still requires a positive source-row marginal
floor and joint target-shell bounds; the stationary source-shell tightness
required by the GNS compiler is separate.  The cofinal finite sixteenth and every
thermodynamic/nome/spacing and continuum obligation remain open.  Focused
monitored builds completed successfully with 1153 and 1159 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Positive-row core, constructive floor, and exact target shell (2026-08-21)

The moving-carrier compiler and
`BF4PhysicalCutoffConditionalCoreReduction` now use the exact old **positive**
physical carrier, rather than every old bounded source state.  This removes
zero-marginal states on which the totalized conditional kernel is an arbitrary
extension and therefore should not be required to converge pointwise.  The
stationary source shell is correspondingly the complement of the old bounded,
positive carrier.

For every source in this refined core,
`centralPositivePhysicalMarginalFloor_le_of_core` connects the source to the
already constructed recursive finite minimum
`centralPositivePhysicalMarginalFloorData`.  Thus the anchor-row denominator
floor is inhabited constructively; it is not a new analytic hypothesis.

The later normalized joint row is also split exactly into its old-target mass
and the new-target quantity `centralOldRowJointTargetShellMass`.  Combining
this identity with the proved old-row `l1` estimate gives the two asymmetric
marginal inequalities

`R_first <= R_second + oldL1 + firstShell` and
`R_second <= R_first + oldL1 + secondShell`.

Consequently the remaining conditional-kernel core estimate has been reduced
to target-shell control and transport of a positive denominator floor to the
later cutoffs (or an equivalent direct positivity-persistence theorem).  The
stationary source-shell estimate needed by the GNS contraction is still a
separate residual.  No target-shell bound or cutoff-positivity persistence is
claimed here.  The cofinal finite sixteenth, all thermodynamic/nome/spacing
limits, continuum reconstruction and QFT axioms, and the Clay theorem remain
open.  Focused monitored builds completed successfully with 1153 and 1159
jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Positive physical rows persist under cutoff enlargement (2026-08-21)

`BF4PhysicalCutoffPositiveRowPersistence` proves that every source row with
positive normalized physical mass at cutoff `K` still has positive mass at
every cutoff `L >= K`.  A constructive finite-list search first extracts a
positive target entry.  Multiplication by the positive partition recovers a
positive unnormalized reflected-kernel entry.  Its exact cylinder numerator
at cutoff `L` is the old positive numerator plus the already proved
nonnegative new-label increment, so the later normalized entry and later row
are positive.  Consequently the old positive carrier embeds into every later
positive carrier.

This removes an analytic hypothesis: all later conditional-division guards
on the refined old core are now inhabited.  It is only qualitative
positivity, however, not a cutoff-uniform lower bound.  Quantitative
conditional-kernel Cauchy control still requires target-shell estimates and a
uniform denominator budget derived from them; stationary source-shell
tightness remains separate.  The cofinal finite sixteenth, thermodynamic/
nome/spacing limits, continuum reconstruction and QFT axioms, and the Clay
theorem remain open.  The source check and focused monitored build completed
successfully, the latter with 1160 jobs.  Both printed declarations report
only `[propext, Quot.sound]`.

## Source-uniform physical target-shell modulus (2026-08-21)

`BF4PhysicalCutoffTargetShellTail` identifies the normalized joint mass in
targets beyond an old carrier with one literal corrected-slab Boolean event:
the lower restriction equals the selected source and the reflected upper
restriction lies outside the old carrier.  A finite selector/Fubini proof
shows that the aggregate event numerator is exactly the sum of the relevant
unnormalized reflected-kernel entries, and normalization gives precisely
`centralOldRowJointTargetShellMass`.

The event is empty at the old cutoff.  The existing retained-plus-new
observable decomposition therefore bounds its expectation at every later
cutoff by the complete corrected-slab new-label increment.  Applying the
arbitrary-nome degree-thirteen retained-cutoff schedule constructs
`centralPhysicalTargetShellCutoff` and proves a source-uniform target-shell
bound `<= epsilon` at every later cutoff.

Thus target-shell control is now inhabited rather than assumed.  The next
conditional-kernel residual is quantitative denominator control and the
weighted old-target numerator comparison; stationary source-shell tightness
for the GNS compiler remains separate.  The cofinal finite sixteenth,
thermodynamic/nome/spacing limits, continuum reconstruction and QFT axioms,
and the Clay theorem remain open.  The source check and focused monitored
build completed successfully, the latter with 1163 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Uniform later-cutoff floor on the positive source core (2026-08-21)

`BF4PhysicalCutoffUniformRowFloor` identifies each physical row marginal with
the normalized expectation of one aggregate lower source-cylinder observable.
Its unnormalized numerator is retained exactly under cutoff enlargement and
only gains a nonnegative new-label increment.  At the retained cutoff for
complete new-label tolerance `1`, the partition increment is at most `1` while
the anchor partition is at least `1`; exact rational cross multiplication
therefore proves

`(1/2) * rowMarginal_anchor(source) <= rowMarginal_later(source)`.

Taking one half of the repository's constructive finite minimum over positive
anchor rows defines `centralPhysicalUniformPositiveRowFloor`.  It is proved
strictly positive and below every later row marginal for every source in the
fixed anchor-positive carrier.  Thus the common denominator floor required by
the conditioning-ratio theorem is now inhabited uniformly in the later
representation cutoff.

The same module now closes the moving-core version needed by the actual
Cauchy compiler.  Exact retained-plus-new partition identities prove additive
decomposition of complete slab cutoff increments; nonnegativity then makes
the increment antitone in its retained cutoff.  Hence every source-core cutoff
beyond the unit-tail schedule inherits the same `increment <= 1` estimate.
Half of the constructive positive-row minimum at that moving cutoff defines
`centralPhysicalMovingPositiveRowFloor`, which is strictly positive and below
all later marginals of every positive source in that expanding core.

The remaining pointwise conditional-kernel work is therefore only the
weighted old-target numerator comparison and its combination with the proved
target shells and quotient-stability theorem.  The
stationary source-shell estimate, cofinal finite sixteenth, thermodynamic/
nome/spacing limits, continuum reconstruction and QFT axioms, and the Clay
theorem remain open.  The source check and focused monitored build completed
successfully, the latter with 1164 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Inhabited pointwise conditional-core estimate (2026-08-21)

`BF4PhysicalCutoffConditionalCoreCauchy` now closes the division step for an
arbitrary physical unit observable.  The genuine finite Markov value on a
positive retained source is rewritten as one quotient: its numerator is the
normalized joint row weighted by the observable, and its denominator is the
source-row marginal.  The numerator splits exactly into an old target core
and a new-target shell.  Since observable values lie in `[0,1]`, the weighted
old-core difference is bounded by the already proved unweighted row `l1`
error, and the weighted shell is bounded by the already proved joint shell.

The resulting two-sided numerator and denominator estimates use one common
error: old-row `l1` plus both outgoing target shells.  Positive-row
persistence and `centralPhysicalMovingPositiveRowFloor` supply both positive
division guards and a common lower floor.  The constructive ratio-stability
theorem therefore proves an explicit absolute bound for the difference of
the two genuine Markov values on every positive source in any expanding core
beyond the unit-tail cutoff.  No conditioning or denominator hypothesis
remains uninhabited at this pointwise level.

The next contraction step is quantitative scheduling: allocate the requested
core tolerance among the old-row error and the two target shells, cancel the
moving floor in the quotient bound, square the resulting pointwise estimate,
and instantiate the core field of the atomic Markov Cauchy compiler.  The
stationary source-shell tightness required by that compiler remains separate,
as do the cofinal finite sixteenth, thermodynamic/nome/spacing limits,
continuum reconstruction and QFT axioms, and the Clay theorem.  The source
check and focused monitored build completed successfully, the latter with
1165 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Executable conditional-core modulus and one-residual contraction (2026-08-21)

`BF4PhysicalCutoffConditionalCoreModulus` closes the quantitative scheduling
step without a circular cutoff choice.  It selects the positive source core
first, obtains its constructive moving row floor, then independently enlarges
the target core to pay both target shells.  The old-row schedule is placed
beyond that target core.  One quarter of the quotient budget pays the old-row
error and one eighth pays each shell, so doubling their common sum consumes
exactly the budget `(1/2 * epsilon) * floor`; constructive positive division
then cancels the floor.

This proves an explicit action rate at which genuine conditional Markov values
on the source core differ by at most `1/2 * epsilon`.  Since all recoded values
lie in `[0,1]`, their squared difference is bounded by the same quantity.  The
result directly inhabits the complete conditional-core field of
`CentralPhysicalAtomicMarkovCoreTailCauchyData`.

The remaining analytic input is isolated as
`CentralPhysicalStationaryPositiveSourceTailData`: an expanding positive
source core whose complementary stationary row-marginal mass is eventually
at most `1/2 * epsilon`.  This one record compiles to the existing core-tail,
atomic, and dense Markov cutoff-Cauchy data.  The record is deliberately not
inhabited here; stationary positive-source tail tightness is now the sole
finite-cutoff residual on this route.  The cofinal finite sixteenth,
thermodynamic/nome/spacing limits, continuum reconstruction and QFT axioms,
and the Clay theorem remain open.  The source check and focused monitored
build completed successfully, the latter with 1166 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Unconditional fixed-nome finite-volume Markov cutoff Cauchy data (2026-08-21)

`BF4PhysicalCutoffStationarySourceTail` inhabits the final residual left by
the conditional-core compiler.  The complement of an old positive source
carrier is encoded as a Boolean lower observable: a state is selected exactly
when it is either outside the old representation carrier or has zero old row
marginal.  Its stationary mean is proved exactly equal to the compiler's
literal filtered source-shell mass.

At the base cutoff this event is empty on the positive stationary carrier, so
its expectation is exactly zero.  The finite stationary/slab bridge turns the
later source-shell mass into the expectation of one cutoff-stable corrected-
slab event.  The sharp bounded-observable tail then bounds it by the complete
new-label increment.  Antitonicity in the retained cutoff permits a base that
is simultaneously beyond the moving-row-floor cutoff and the explicit
half-epsilon tail schedule.

The result constructs `centralPhysicalStationaryPositiveSourceTailData` and,
without any remaining input record, compiles it to concrete moving-core,
atomic, and dense physical Markov cutoff-Cauchy data for every fixed
`0 < w < 1` and finite half-extent.  Thus the representation-cutoff Cauchy
frontier for the actual conditional Markov action is closed on this route.
The next contraction frontier is to feed this datum into the adaptive
completed-transfer construction and remove its previously named Cauchy
certificate.  A finite strict-contraction/sixteenth certificate and all
thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom, and Clay
targets remain open.  The source check and focused monitored build completed
successfully, the latter with 1167 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Concrete cutoff-removed completed physical Markov transfer (2026-08-21)

`BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer` specializes the
adaptive completion stack with the now-inhabited dense cross-cutoff Cauchy
datum.  For every fixed `0 < w < 1` and finite half-extent it therefore
constructs an actual endomap of the concrete completed physical carrier,
without a same-index completion hypothesis or any remaining pointwise Cauchy
input.

The concrete map agrees with the finite-linear dense cutoff limit, fixes the
normalized completed vacuum, preserves zero, addition, and rational scaling,
and is bundled as a rational-linear endomorphism.  Its exact completed vacuum
pairing is invariant, so it preserves vacuum orthogonality and restricts to a
rational-linear endomorphism of the actual completed vacuum complement.

This closes the representation-cutoff transfer-existence and
vacuum-complement-construction frontiers at fixed nome and finite volume.  The
next analytic frontier is now the finite strict-contraction certificate: the
existing cofinal compiler needs cutoffs arbitrarily far out with centered
operator norm at most `1/16`.  Such a cofinal certificate is not supplied by
this construction.  Thermodynamic, nome, spacing, continuum-reconstruction,
QFT-axiom, and Clay targets also remain open.  The source check and focused
monitored build completed successfully, the latter with 1326 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Concrete cutoff-removed gap implication with one finite input (2026-08-21)

`BF4PhysicalCutoffLinearMarkovConcreteAdaptiveGap` specializes the entire
adaptive strict-contraction, power, and same-object correlation stack with the
now-constructed dense cutoff-Cauchy datum.  The formerly two-input implication
has therefore contracted to one finite-volume analytic input:
`FixedNomeCofinalCenteredSixteenth`, or its stronger cofinal local-gluing
presentation.

Given that one cofinal finite certificate, the actual cutoff-removed transfer
on the completed physical vacuum complement contracts at literal rate
`1/16`.  Its natural powers satisfy squared-norm decay with factor
`((1/16)^2)^n`, and Cauchy--Schwarz gives the corresponding squared
same-object matrix-coefficient decay against every test vector in the same
completed carrier.  No pointwise cutoff-Cauchy or same-index completion input
remains in these public implications.

The cofinal centered-sixteenth certificate itself is not inhabited.  This is
now the sole fixed-nome finite-volume gap obstruction on the concrete
completed-transfer route.  It requires a genuinely fixed-nome unbounded
family of strict finite estimates; the checked scale-five `s = 2..41` prefix
belongs to a different coefficient/RG frontier and is not such a family.
Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom, and Clay
targets remain open.  The source check and focused monitored build completed
successfully, the latter with 1334 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Two-sided finite rational spectral certificate (2026-08-21)

`FiniteRationalReversibleSpectralCertificate` now exposes the lower spectral
edge that the absolute physical autocorrelation estimate requires.  Alongside
the existing upper-edge quadratic `q D - K + d d^T`, it defines the exact
lower-edge quadratic `q D + K + d d^T` and proves that nonnegativity of both
forms gives `|x^T K x| <= q x^T D x` on the exactly weighted-centered
subspace.

The theorem is available both from the two penalized quadratic inequalities
and from two separately identified finite matrix PSD certificates.  Those
interfaces can be fed directly by the existing exact rational LDL checker, so
the cofinal physical residual is no longer incorrectly presented as a
one-sided PSD problem: each selected cutoff needs an upper and a lower
kernel-checked certificate, plus exact identification with the physical
carrier sums.

No cofinal cutoff family, physical reindexing identification, or new LDL table
is constructed here.  In particular, the existing cutoff-two sector LDL data
certifies one finite matrix only and cannot inhabit the fixed-nome cofinal
sixteenth.  Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom,
and Clay targets remain open.  The source check and focused monitored build
completed successfully, the latter with 216 jobs.  Every printed load-bearing
declaration reports only `[propext]`, within the allowed
`[propext, Quot.sound]` gate.

## Exact physical-carrier finite-index bridge (2026-08-21)

`FiniteListIndexQuadraticBridge` proves generically that totalized `List.getD`
lookup over `0, ..., states.length - 1` preserves literal single and double
`listQSum` expressions.  `BF4PhysicalCutoffFiniteIndexBridge` applies this to
the actual duplicate-free positive-row BF4 carrier at arbitrary nome, cutoff,
and finite half-extent.

The resulting indexed dimension, state lookup, stationary weights, normalized
reflected kernel, and observable coefficients are now proved to reproduce
exactly the physical stationary mean, weighted norm, and joint quadratic.
Physical mean-zero observables therefore become exactly weighted-centered
finite coefficient vectors.  This closes the previously implicit
list-to-matrix identification step; out-of-range fallback values provably do
not enter any checked quadratic.

No upper/lower LDL data or cofinal cutoff family is constructed here.  The
next finite frontier is to specify the canonical two penalized matrices and
compile successful exact LDL checks for both signs into
`FixedNomeCofinalCenteredSixteenth`.  Thermodynamic, nome, spacing,
continuum-reconstruction, QFT-axiom, and Clay targets remain open.  Both source
checks and focused monitored builds completed successfully, with 216 and 983
jobs respectively.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Canonical two-sided finite penalized matrices (2026-08-21)

`FiniteRationalPenalizedMatrix` defines the literal finite matrices
`q D - K + d d^T` and `q D + K + d d^T` whose positive semidefiniteness
controls the upper and lower spectral edges of a reversible finite kernel.
It proves directly that their complete indexed matrix quadratics are the two
penalized scalar quadratics consumed by the two-sided contraction theorem.

The proof expands the diagonal and stationary rank-one entries through exact
finite rational sums, including a constructive local proof that `List.range`
has no duplicates.  This avoids the `Classical.choice` dependency carried by
the corresponding core-library theorem in this Lean toolchain.  External LDL
generation can now target canonical physical entries rather than relying on
an opaque matrix-identification hypothesis.

No LDL factor table or cofinal cutoff family is constructed here.  The next
finite frontier is to compile successful upper and lower Boolean LDL checks
for these matrices, after the exact physical finite-index bridge, into one
cutoffwise absolute centered-correlation certificate and then into
`FixedNomeCofinalCenteredSixteenth`.  Thermodynamic, nome, spacing,
continuum-reconstruction, QFT-axiom, and Clay targets remain open.  The source
check and focused monitored build completed successfully, the latter with 217
jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Cofinal two-sided physical LDL compiler (2026-08-21)

`BF4PhysicalCutoffCofinalLDLGap` connects exact matrix computation to the
actual fixed-nome physical gap interface.  At one genuine physical cutoff,
nonnegativity of the canonical matrices
`(1/16) D - K + d d^T` and `(1/16) D + K + d d^T` now proves the absolute
joint-quadratic bound for every exactly stationary-mean-zero observable.  The
proof uses the exact finite carrier reindexing and transports both sides back
to the physical list sums.

Two executable producers are exposed.  The ordinary interface accepts two
complete `finiteLDLCheck = true` witnesses.  The scalable interface accepts
cleared-denominator row checks, explicit triangularity, and pivot-sign checks
for both signs, allowing large tables to be checked in independent row
shards.  A constructively cofinal family of either kind compiles directly to
`FixedNomeCofinalCenteredSixteenth`, hence into the already proved adaptive
completed-transfer contraction, power decay, and same-object correlation
decay implications.

No per-cutoff LDL record or cofinal family is inhabited here.  Thus the
remaining fixed-nome obstruction has contracted to producing two successful
canonical matrix factorizations at constructively unbounded cutoffs.  Existing
cutoff-two sector data targets a different one-sided mean-zero matrix and is
not silently reused.  Thermodynamic, nome, spacing, continuum-reconstruction,
QFT-axiom, and Clay targets remain open.  The source check and focused
monitored build completed successfully, the latter with 1215 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Constructive centered-coordinate LDL restriction (2026-08-21)

`FiniteRationalCenteredRestrictionCertificate` makes the coordinate reduction
used by finite mean-zero computations explicit.  Its Type-valued restriction
record supplies a lift from a smaller rational coordinate space, proves every
lifted vector is exactly weighted-centered, and constructively recovers
reduced coordinates for every centered full vector.  Separate exact
quadratic identifications connect the reduced upper and lower matrices to the
two canonical full-carrier penalized forms.

Nonnegativity of both reduced matrices now proves the absolute centered
contraction on the full carrier.  Ordinary complete LDL checks and scalable
cleared-denominator row/triangularity/pivot checks are both compiled through
that bridge.  Generic dependent packages bundle a restriction with either
checker, and changing-dimension cofinal packages retain those bundles along an
explicit unbounded finite-model schedule.  Keeping these recursors at the
small finite-arithmetic level also prevents model-specific definitional
expansion during kernel elaboration.  This closes the generic logical gap
between a reduced mean-zero factorization and the canonical physical
two-sided inequality without using a basis choice or an existential coordinate
inverse.

No physical restriction, reduced matrix table, or cofinal certificate family
is constructed here.  In particular, the existing cutoff-two 64-coordinate
table still targets the one-sided `49/50` form and does not establish the
two-sided `1/16` target.  The next frontier is to specialize this restriction
interface to the genuine BF4 physical finite carrier and then construct valid
upper/lower certificate data at constructively unbounded fixed-nome cutoffs.
Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom, and Clay
targets remain open.  The source check and focused monitored build completed
successfully, the latter with 218 jobs.  Every printed load-bearing declaration
reports only `[propext, Quot.sound]`.

## Cofinal reduced-coordinate physical LDL compiler (2026-08-21)

`BF4PhysicalCutoffCofinalRestrictedLDLGap` specializes the generic centered
restriction packages to the genuine finite-index BF4 physical carrier.  At
one cutoff, an ordinary or cleared-denominator reduced LDL package now proves
the exact absolute physical joint-quadratic bound for every stationary-mean-
zero observable.  Exact carrier reindexing transports the reduced finite
matrix conclusion back to the physical list sums.

At fixed nome and half-extent, a constructively cofinal family of either kind
now compiles directly to `FixedNomeCofinalCenteredSixteenth`.  Thus an
external exact-arithmetic producer may eliminate a mean-zero coordinate and
emit smaller upper/lower factor tables without any unrecorded basis or
physical-identification step.

No physical coordinate restriction, LDL table, or cofinal family is inhabited
here.  The historical cutoff-two table remains one-sided at `49/50` and cannot
fill the two-sided `1/16` interface.  The next constructive frontier is a
canonical coordinate-elimination constructor from one proved-positive
stationary weight, followed by production or obstruction analysis of actual
two-sided tables.  Thermodynamic, nome, spacing, continuum-reconstruction,
QFT-axiom, and Clay targets remain open.  Source checks and focused monitored
builds completed successfully; the physical build passed 1217 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Constructive positive-head mean-zero coordinates (2026-08-21)

`FiniteRationalHeadCenteredCoordinates` eliminates the head coordinate of an
`(n+1)`-state weighted carrier whenever its head weight is strictly positive.
The lift retains the `n` literal tail coefficients and defines the head as the
negative tail weighted sum divided by the positive head weight.  A finite-sum
decomposition proves every lifted vector is exactly centered.

Conversely, every centered full vector constructively returns its literal tail
coordinates, and positive-denominator rational algebra proves that its head is
equivalent to the computed lift.  This supplies the lift, centering, and
Type-valued completeness fields of `FiniteCenteredTwoSidedRestriction`
without a basis choice, existential witness extraction, or matrix assumption.
A constructor now leaves only exact identification of the two reduced matrix
quadratics as inputs.

No reduced pullback matrix, physical head-weight proof, LDL table, or cofinal
family is constructed here.  The next finite frontier is to define the
canonical matrix pullback along this lift and prove its quadratic identity;
after that, one physical positive-weight witness will generate the entire
restriction rather than merely parameterize it.  Thermodynamic, nome,
spacing, continuum-reconstruction, QFT-axiom, and Clay targets remain open.
The source check and focused monitored build completed successfully, the
latter with 219 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Exact finite rational matrix pullback (2026-08-21)

`FiniteRationalMatrixPullback` defines the literal reduced matrix `A^T M A`
for arbitrary finite full/reduced dimensions and an explicit rational
coordinate matrix `A`.  A four-index finite Fubini proof, together with exact
rational distributivity and product rearrangement, shows that the complete
reduced quadratic is equivalent to the full matrix quadratic evaluated on the
finite linear lift.

This generates the reduced quadratic-identification theorem rather than
asking an external factor producer to assert it.  Consequently an LDL producer
can target the displayed pullback entries, while Lean verifies both the
entries-to-quadratic semantics and later the factorization itself.

No identification between the positive-head division lift and a finite linear
coordinate matrix is proved here, and no physical pullback or LDL data is
constructed.  The next frontier is to define that head-centering transform and
prove its finite linear application equals the already verified explicit
centered lift.  Thermodynamic, nome, spacing, continuum-reconstruction,
QFT-axiom, and Clay targets remain open.  The source check and focused
monitored build completed successfully, the latter with 219 jobs.  The
load-bearing pullback theorem reports only `[propext]`.

## Canonical positive-head reduced penalized matrices (2026-08-21)

`FiniteRationalHeadCenteredPullback` represents the explicit positive-head
centering formula by a finite rational coordinate matrix.  Its head row is the
negative tail weight divided by the positive head weight; all remaining rows
are the retained-coordinate identity.  Exact finite-sum algebra proves that
matrix application agrees in every full in-range coordinate with the earlier
constructive centered lift.

Pulling the canonical full matrices `qD-K+dd^T` and `qD+K+dd^T` back along
this transform now generates literal reduced upper and lower matrices.  The
generic pullback theorem and coefficient congruence prove both required
quadratic identities, so a positive head weight constructs the entire
`FiniteCenteredTwoSidedRestriction` with no externally supplied matrix-
identification field.

No LDL factorization or physical positive-head witness is constructed here.
The next frontier is to prove positivity of indexed physical weight zero from
the nonempty positive-row carrier, specialize this canonical restriction to
every genuine BF4 cutoff, and pin ordinary/cleared LDL checks to its displayed
matrices.  Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom,
and Clay targets remain open.  The source check and focused monitored build
completed successfully, the latter with 221 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Canonical head-reduced physical LDL target (2026-08-21)

`BF4PhysicalCutoffCanonicalHeadLDLGap` proves that indexed weight zero on the
genuine BF4 positive-row carrier is strictly positive, using nonemptiness of
that carrier and the defining positive-row filter.  It therefore instantiates
the generated positive-head restriction at every physical cutoff.  Its upper
and lower reduced matrices are now literally the pullbacks of
`(1/16)D-K+dd^T` and `(1/16)D+K+dd^T`; no abstract restriction or externally
asserted matrix identity remains.

Ordinary and cleared-denominator LDL certificates are pinned to these exact
generated matrices.  A constructively cofinal family of either kind compiles
directly to `FixedNomeCofinalCenteredSixteenth`, and hence through the existing
adaptive completed-transfer route to the same-object strict contraction and
correlation-decay consequences.

No LDL factor table or cofinal family is inhabited.  The historical cutoff-two
`49/50` table is one-sided and cannot prove the two-sided `1/16` target.  The
next exact finite frontier is therefore a feasibility audit of the displayed
physical matrices, followed either by production of both factor tables on an
unbounded fixed-nome schedule or by a kernel-checked obstruction showing that
this proposed constant/route cannot work.  Thermodynamic, nome, spacing,
continuum-reconstruction, QFT-axiom, and Clay targets remain open.  The source
check and focused monitored build completed successfully, the latter with
1221 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Exact cutoff-two one-sixteenth obstruction (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction` evaluates one
diagonal of the literal canonical head-centered upper matrix for the verified
65-state cutoff-two raw sector.  A new sparse pullback identity reduces that
diagonal to four entries of the full penalized matrix, avoiding evaluation of
the complete 65-by-65 quadratic sum.  Exact rational reduction in Lean proves
that tail coordinate one (full sector index two) has strictly negative
diagonal at `q = 1/16`.  The corresponding coordinate-unit quadratic is
therefore negative, so the upper matrix is not positive semidefinite.

As kernel-checked consequences, neither the ordinary nor the cleared-
denominator `FiniteCenteredRestrictionLDLCertificate` can inhabit this
canonical cutoff-two sector restriction.  The external exact-rational scout
agrees with the local witness: its mean-zero LDL inertia is 64 positive pivots
for `(1/16)D+K` and 43 positive plus 21 negative pivots for `(1/16)D-K`.
Those aggregate inertia counts remain untrusted computational reconnaissance;
the displayed negative diagonal and both no-certificate theorems are the
Lean-checked content.

This closes the proposed all-cutoff `1/16` route and forbids cutoff two as an
anchor for a `1/16` cofinal certificate.  It does not refute `1/16` on some
later unbounded fixed-nome subsequence, and the sector obstruction has not yet
been transported to a full physical-carrier observable.  At this milestone
the next causal frontier was to parameterize the finite/cofinal certificate by
an arbitrary constructive rate `q` with `0 <= q < 1`, then seek a viable
uniform cofinal rate rather than hardcode the disproved cutoff-two constant.
Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom, and Clay
targets remain open.  The narrow source checks completed successfully; the
dependency-complete focused audit was intentionally interrupted while
repairing unrelated generated reflection objects (the most recent run stopped
at 1193/1221 and is not recorded as passed).  The printed obstruction
declarations report only `[propext, Quot.sound]`.

## Arbitrary-rate cofinal and upper-only LDL compiler (2026-08-21)

`BF4PhysicalCutoffCofinalStrictGap` replaces the hardcoded cofinal sixteenth
at the finite-certificate seam by `FixedNomeCofinalCenteredStrictGap`.  The
record carries a supplied rational `q`, constructive proofs `0 <= q` and
`q < 1`, a constructive cofinal anchor, and the exact physical mean-zero form
bound at every anchor.  The historical sixteenth interface embeds as the
special case `q = 1/16`; canonical ordinary and cleared two-sided LDL families
now compile at any supplied strict rate.

The physical route is sharpened further to require only the upper matrix.
Generic ordinary and shardable cleared-denominator upper-only LDL records
prove `K <= qD` on every exactly centered vector.  The finite index bridge
transports this inequality to the genuine physical sums, while the already
proved reflection-positive physical quadratic supplies `0 <= K`; hence
`|K| = K <= qD` without a lower-edge LDL factorization.  Generic cofinal
records plus physical abbreviations avoid pathological dependent unfolding of
the full canonical restriction.

No cofinal upper certificate is inhabited here.  In particular, the existing
cutoff-two `49/50` table is sector-level data and is not yet identified with a
canonical full physical-carrier upper certificate, much less extended along
an unbounded fixed-nome schedule.  At this milestone the next compiler
frontier was to propagate `FixedNomeCofinalCenteredStrictGap q` through the
completed adaptive graph-norm route; the next finite analytic frontier was a
viable full-carrier cofinal upper certificate at one
uniform `q < 1`.  Thermodynamic, nome, spacing, continuum-reconstruction,
QFT-axiom, and Clay targets remain open.  The source check and focused
monitored build completed successfully, the latter with 1222 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Arbitrary-rate completed adaptive cofinal gap (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap` propagates
the exact supplied rate from `FixedNomeCofinalCenteredStrictGap q` through the
actual cutoff-removed completed transfer.  At every selected finite anchor,
exact centering gives the completed form bound with factor `q`; the existing
division-free form-to-operator theorem gives the squared-norm factor `q*q`.
Both adaptive centered graph-norm streams are reindexed along the same
constructively cofinal anchor without changing their limits.

The resulting representative inequality descends through the cutoff-
completion quotient and constructs
`centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionDataAtRate`.
Its stored rate is literally the supplied `q`, with strictness inherited from
the certificate rather than recomputed at `1/16`.  Thus the finite matrix,
cofinal, completed-operator, and quotient layers are no longer tied to the
cutoff-two-obstructed constant.

No cofinal finite certificate or nonconstant Markov completion modulus is
inhabited.  The next finite analytic frontier is a genuine full-carrier upper
certificate on an unbounded fixed-nome schedule at some uniform `q < 1`; the
existing sector-level cutoff-two `49/50` table is only a finite diagnostic
until its matrix identification and physical-carrier scope are proved.
Thermodynamic, nome, spacing, continuum-reconstruction, QFT-axiom, and Clay
targets remain open.  The source check and focused monitored build completed
successfully, the latter with 1318 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Exact cutoff-two invariant-sector upper gap at 49/50 (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorUpperGap` turns the historical cleared LDL
table into a named certificate for the canonical positive-head restriction,
rather than accepting positivity of an unidentified `64 x 64` matrix.  A
local sparse pullback theorem reduces every canonical entry of
`(49/50)D-K+dd^T` to four entries of the full `65 x 65` matrix.  Sixty-four
process-isolated row theorems then kernel-check all 4096 equalities between
that sparse formula and the historical mean-zero table.  The aggregate bridge
pins the old table to the literal canonical upper matrix.

The existing cleared LDL rows and positive pivots therefore inhabit
`FiniteCenteredRestrictionUpperClearedLDLCertificate` at the exact rational
rate `q = 49/50`, with separately checked proofs `0 <= q < 1`.  Its
`upperContraction` theorem proves, for every exactly weighted-centered
coefficient on the verified 65-state cutoff-two cube-subset sector,
`K <= (49/50) D`.  Existing sector-support work proves this 65-state sector is
row-closed in the genuine cutoff-two physical kernel; this is stronger than
the earlier two-state vacuum/cube diagnostic, which is not row-closed.

The result is nevertheless only an invariant-sector upper gap.  It does not
identify the 65 states with the entire cutoff-two physical carrier, does not
control other invariant sectors or their mutual decomposition, and does not
construct a fixed-nome cofinal family at one uniform `q < 1`.  The
nonconstant completion modulus, thermodynamic/nome/spacing limits, continuum
QFT axioms, and Clay conclusion remain open.  The next causal frontier is to
resolve the 65-state sector versus full-carrier decomposition and either
extend this exact upper certificate to every physical component or exhibit a
kernel-checked obstruction/rate requirement on the omitted component.

Verification was deliberately layered.  The bridge-data target completed
successfully with 1610 jobs; the complete 64-row/4096-entry target completed
with 1675 jobs; and the final theorem passed a direct monitored source check,
with both printed load-bearing declarations reporting only
`[propext, Quot.sound]`.  A dependency-complete final target audit was
intentionally interrupted at its then-visible 1785/1788 jobs while replaying
the already-existing 1024 historical LDL chunks after cache invalidation; it
encountered no proof failure and is not recorded as a passed target build.

## Proper nonempty complement of the cutoff-two 65-state sector (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorComplementWitness` resolves the next
carrier-scope question negatively: the row-closed 65-state cube-subset sector
is a proper subset of the literal positive cutoff-two physical carrier.  The
new lower state has fundamental label one only on face `39`; fixed-interface
faces `[40, 41, 49, 59]`, together with the reflected upper face, complete a
transverse closed cube.  Direct kernel reduction proves that complete
production summand strictly positive, hence its diagonal physical reflected
kernel entry is positive and the lower state belongs to the retained carrier.
The exact 65-state membership semantics exclude it: it is neither the
six-face fundamental cube nor a `0/2`-labelled cube subset.

The existing sector row-closure theorem gives zero kernel coupling from every
sector state to this explicit complement state, and exact reflected-kernel
symmetry gives the reverse zero.  Thus the omitted carrier is not merely an
uncertified tail: it contains a positive-norm state in a distinct exact block.
Consequently the sector `49/50` theorem cannot be promoted by identifying its
65 states with the full carrier.  The next causal frontier is the stronger
reducibility consequence: construct the nonconstant centered block indicator,
prove it is fixed by the full physical Markov action, and use its positive norm
to refute every full-carrier strict rate `q < 1` at cutoff two.  Any viable
gap route must then select the physically correct superselection/vacuum sector
before forming the vacuum complement, rather than use the reducible union of
all positive rows.  Cofinal sector selection, the completion modulus,
thermodynamic/nome/spacing limits, continuum QFT axioms, and the Clay target
remain open.

The monitored source check and dependency-complete target build both passed;
the latter completed 1597 jobs.  All four printed declarations report only
`[propext, Quot.sound]`.

## Full-carrier cutoff-two strict-gap no-go (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction` upgrades the
proper-complement witness to the exact obstruction it implies.  Faithful
finite-state codes define the characteristic function of the closed 65-state
sector on the literal positive physical carrier.  Exact cross-block kernel
zeros and row normalization prove that this nonconstant indicator is fixed by
the physical Markov operator.  Subtracting its stationary mean therefore
produces an exactly mean-zero fixed observable.

The centered observable has strictly positive physical weighted norm.  This
is proved constructively from the retained vacuum and retained transverse
states: their centered indicator values differ by one, so at least one value
is nonzero, and its positive row marginal supplies a strictly positive norm
summand.  The weighted Markov/joint identity then shows that the observable's
joint quadratic equals its norm.  Hence `no_cutoffTwo_fullCarrier_strict_upper_gap`
and `no_cutoffTwo_fullCarrier_strict_abs_gap` refute every full-carrier
centered contraction rate `q < 1` at cutoff two.

This is a correction to the previous full-positive-carrier roadmap, not a
failure of the 65-state sector theorem: that invariant sector still has its
proved upper rate `49/50`.  The all-positive carrier contains multiple
stationary blocks and therefore has a degenerate vacuum.  Any viable mass-gap
route must first choose a compatible invariant vacuum/superselection sector
at every cutoff, prove its cofinal compatibility, and only then form the
vacuum complement and pass the sector-restricted gap to completion.  Such a
sector family, its thermodynamic/continuum compatibility, continuum QFT
axioms, and the Clay conclusion remain open.

The monitored source check and dependency-complete target build both passed;
the latter completed 1673 jobs.  All three printed declarations report only
`[propext, Quot.sound]`.

## Cofinal finite-gap compiler for the adaptive completed transfer (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap` proves that the
all-cutoff `FixedNomeCutoffCenteredSixteenth` is stronger than the completed
limit needs.  At each anchor selected by the existing
`FixedNomeCofinalCenteredSixteenth`, exact stationary centering first gives the
finite completed form gap and the division-free form-to-operator theorem gives
the `(1/16)^2` norm bound.

Both adaptive graph-norm streams are then reindexed along the cofinal anchor
map.  Their limits are unchanged, so the anchorwise finite bounds contract to
`centralPhysicalCutoffCompletedMarkovAdaptiveCofinalStrictContractionData`, the
same strict contraction of the actual cutoff-removed transfer at rate `1/16`.
A second compiler accepts the more geometric
`FixedNomeCofinalLocalGluing` directly.

Neither the cofinal finite certificate nor the nonconstant completion modulus
is inhabited.  The finite residual is nevertheless strictly weaker: one now
needs certified cutoffs arbitrarily far out, not a certificate at every
cutoff.  The next completed-transfer frontier is the cross-cutoff completion
modulus.  Thermodynamic/nome/spacing limits, continuum QFT, and the Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1303 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Adaptive completed graph-norm compiler (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm` uses the equal
rate-admissible representative constructed by the adaptive reindexing module
to discharge all four raw graph diagonals.  A generalized diagonal theorem
accepts the regularized inner witness; exact Markov syntax rate invariance then
makes the one input sampler control the input self pair, input vacuum pair,
action self pair, and action vacuum pair.

Those four limits prove completed vacuum-pairing invariance directly from the
completion modulus and prove convergence of both centered graph-norm streams.
Quotient equality transports every arbitrary representative to its adaptive
normal form.  Consequently
`centralPhysicalCutoffCompletedMarkovAdaptiveStrictContractionData` constructs
strict contraction of the actual cutoff-removed completed transfer at literal
rate `1/16` from only `CentralPhysicalLinearMarkovCompletionModulus` and
`FixedNomeCutoffCenteredSixteenth`.  The former separate graph-cofinality input
is no longer present in the final compiler.

Neither of those two remaining analytic inputs is inhabited.  Thus the next
fixed-nome frontiers are the nonconstant completion modulus and the uniform
finite-cutoff centered sixteenth; thermodynamic/nome/spacing limits, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1300 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Fixed-nome cutoff limit of the physical autocorrelation form (2026-08-20)

`BF4PhysicalCutoffAutocorrelationLimit` closes the next same-object moment
edge.  For a lower `[0,1]` observable `a`, the full-slab insertion
`a(lower) * a(reflected-upper)` is again cutoff-stable and `[0,1]`.  The
existing physical Markov-quadratic equality and full-slab reindex identify
its normalized BF4 expectation at every cutoff with the actual weighted
transfer form `centralPhysicalWeightedInner a (P a)`.

The executable cutoff modulus therefore constructs
`centralPhysicalAutocorrelationCutoffLimit`, whose rational approximations
are definitionally those finite physical Markov forms.  The finite OS
positivity and identity-form estimate contract into the limiting interval
`0 <= autocorrelationLimit <= stationaryNormLimit`.  This is a genuine limit
of the same-object one-step transfer moment, not merely an ordinary
expectation limit.

No transfer operator or cutoff-independent Hilbert carrier is constructed;
the nome and finite half-extent remain fixed.  Centering and connected
correlations at the cutoff limit, a strict vacuum-complement bound,
thermodynamic/spacing uniformity, OS reconstruction, and the Clay theorem
remain open.  A source check and focused monitored build completed
successfully, the latter with 1130 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Fixed-nome connected physical BF4 cutoff limits (2026-08-20)

`BF4PhysicalCutoffConnectedLimit` contracts the already-constructed
stationary mean, stationary square, and one-step physical Markov-form limits
into the connected quantities `E(a^2) - E(a)^2` and
`<a, P a> - E(a)^2`.  Bishop-real addition, negation, and multiplication are
pointwise here, so every rational approximation is definitionally the
corresponding finite-cutoff connected expression.

The existing exact finite centering identities then identify those
approximations, modulo `Q'.eqv`, with the stationary norm and one-step Markov
form of the literal marginal-centered observable.  Finite BF4 positivity and
the identity-form estimate therefore survive representation-cutoff removal as

`0 <= connectedAutocorrelationLimit <= connectedNormLimit`.

This is a form-level result at fixed rational nome and fixed finite
half-extent.  It does not construct a cutoff-independent transfer operator or
Hilbert carrier, and it does not prove a strict factor `q < 1`.  In particular,
uniformity in representation cutoff, nome, extent, physical volume, and
spacing must be audited before any completed vacuum-complement gap can be
claimed.  A source check and focused monitored build completed successfully,
the latter with 1205 jobs.  Every printed load-bearing declaration reports
only `[propext, Quot.sound]`.

## Arbitrary-extent pointwise physical BF4 sixteenth (2026-08-20)

`physical_joint_quadratic_abs_le_sixteenth_of_local_gluing` is now proved at
an arbitrary finite half-extent, rather than only at half-extent zero.  The
underlying `PhysicalBF4LocalSliceGluing` record already carried the general
geometry; the contraction proof now retains that parameter through the
positive state carrier, physical and vacuum joint laws, row marginal, and
weighted square.

Consequently, an explicit local slice of centered row rate at most `1/4`,
whose prescribed power is exactly the physical conditional density at a
given nome, cutoff, and finite extent, gives the same pointwise `1/16`
mean-zero quadratic estimate there.  No such slice family is constructed by
this generalization, and no uniformity in representation cutoff or physical
scale follows automatically.  A source check and focused monitored build
completed successfully, the latter with 1117 jobs; the printed declarations
report only `[propext, Quot.sound]`.

## Strict connected BF4 representation-cutoff limit compiler (2026-08-20)

`BF4PhysicalCutoffConnectedGap` isolates the exact uniform input needed for a
strict gap after representation-cutoff removal.  The direct
`FixedNomeCutoffCenteredSixteenth` record is pinned at every cutoff to the
actual mean-zero physical joint quadratic and stationary norm.  The expanded
`FixedNomeCutoffLocalGluing` record instead asks for one explicit local slice
per cutoff, with exact conditional-density gluing and centered row rate at
most `1/4`; a proved adapter constructs the direct sixteenth record.

For either presentation, exact finite centering and pointwise Bishop-real
arithmetic prove the actual limiting bound

`connectedAutocorrelationLimit <= (1/16) * connectedNormLimit`,

with a separately checked proof that `0 <= 1/16 < 1`.  Thus strictness is now
known to survive representation-cutoff removal once it is supplied uniformly
on that same fixed-nome, fixed-finite-extent sequence.

Neither uniform certificate is inhabited.  The existing matched-AF producer
controls a coupled nome/cutoff trajectory at half-extent zero, not the
fixed-nome cutoff sequence used by this limit, so it cannot be substituted
without a new bridge.  No cutoff-independent operator or completed Hilbert
carrier, thermodynamic/spacing uniformity, continuum theory, or Clay theorem
is obtained.  A source check and focused monitored build completed
successfully, the latter with 1206 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Asymptotic connected BF4 cutoff-gap modulus (2026-08-20)

`BF4PhysicalCutoffAsymptoticConnectedGap` weakens the exact cutoff-uniform
frontier to the estimate actually needed by the transitive constructive-real
order.  `FixedNomeCutoffCenteredSixteenthModulus` carries an explicit
tolerance-to-cutoff function and proves, beyond that cutoff, the mean-zero
physical form estimate with additive rational error `epsilon`.

A new exact centering lemma shows that an additive error survives stationary
centering unchanged.  Consequently the modulus proves

`connectedAutocorrelationLimit leEv (1/16) * connectedNormLimit`,

where `leEv` is the transitive eventual Bishop-real order.  An exact
cutoff-uniform sixteenth embeds with threshold zero, so the stronger previous
certificate remains sufficient.

The asymptotic modulus is not inhabited.  Ordinary bounded-observable cutoff
convergence does not itself control the cutoff-dependent centered observable,
and the matched-AF producer still follows a varying-nome trajectory.  Thus the
next analytic task is a centered-form cutoff-tail estimate or a bridge from a
cofinal family of genuinely strict finite cutoffs.  No operator limit,
thermodynamic/spacing control, continuum construction, or Clay result follows.
A source check and focused monitored build completed successfully, the latter
with 1207 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Cofinal strict BF4 representation cutoffs suffice (2026-08-20)

`BF4PhysicalCutoffCofinalConnectedGap` weakens the strict finite input once
more.  `FixedNomeCofinalCenteredSixteenth` carries a constructive anchor
function `anchor` with `base <= anchor base` and the exact mean-zero physical
sixteenth only at those selected representation cutoffs.  The expanded
`FixedNomeCofinalLocalGluing` supplies genuine local-slice witnesses only at
the same anchors.

The connected norm and autocorrelation Bishop reals already carry Cauchy
proofs.  For each target tolerance, the new theorem selects an anchor beyond
both Cauchy thresholds, compares an arbitrary later cutoff to that anchor,
applies its exact `1/16` estimate, and pays the two comparison errors with an
`epsilon/2 + epsilon/2` budget.  Hence either cofinal certificate proves the
same strict connected gap in `CReal.leEv`.

Neither cofinal certificate is inhabited.  This result does not turn the
existing matched-AF producer into a fixed-nome family: that producer varies
the nome together with its cutoff.  The next representation-cutoff analytic
obligation is therefore a genuinely fixed-nome cofinal strict family; the
next structural obligation is an additive cutoff-independent pre-Hilbert
carrier and operator realization.  Thermodynamic/spacing control, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1208 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Fixed-nome finite-linear physical BF4 limiting form (2026-08-20)

`BF4PhysicalCutoffLinearGNSForm` closes the first half of the additive-carrier
frontier.  `CentralPhysicalLinearObservable` is an explicit finite rational
syntax generated by the genuine globally `[0,1]` physical lower observables;
its evaluation is the literal rational function used by every finite BF4
physical GNS.  Unlike the previous unit-observable algebra, this carrier has
zero, addition, negation, subtraction, and rational scalar multiplication up
to pointwise `Q'.eqv`.

The CReal-valued `innerLimit` is assembled only from the already-constructed
fixed-nome cutoff limits of products of unit observables.  Its load-bearing
stage theorem proves that approximation `K` is `Q'.eqv` to the literal
stationary-marginal physical inner product of both evaluated finite-linear
observables at representation cutoff `K`.  Finite GNS symmetry, bilinearity,
semantic congruence, and reflection positivity therefore pass to the limiting
form.  The concrete bundled `centralPhysicalCutoffLinearGNSForm` is an actual
additive positive CReal-valued GNS form datum at every fixed `0 < w < 1` and
finite half-extent.

This does not yet prove CReal radical descent, package the form as the existing
`SquaredSeminorm`, or instantiate its choice-free completion.  It also does not
construct a cutoff-independent transfer action on the syntax.  Those are now
the exact next structural steps; the independent fixed-nome cofinal strictness
certificate is still uninhabited.  Thermodynamic/spacing uniformity, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1133 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## CReal Cauchy--Schwarz and physical limiting radical descent (2026-08-20)

`BF4PhysicalCutoffLinearRadicalDescent` closes the analytic prerequisite for
quotienting the new finite-linear limiting form.  The exact cutoff-stage bridge
feeds the already-proved sharp rational Cauchy--Schwarz inequality of each
finite physical GNS into every approximation of `innerLimit`.  This yields both
the approximation-wise inequality and its invariant form in transitive
`CReal.leEv` order.

If the limiting norm of one finite-linear observable is zero, the proof takes
a constructive local bound for the second norm and selects a positive rational
input tolerance whose product with that bound fits the requested squared
output tolerance.  Stagewise Cauchy--Schwarz then forces the absolute cross
form below the output tolerance.  Hence every limiting null vector pairs to
zero with every other vector.  The resulting
`centralPhysicalCutoffLinearPreHilbert` is a concrete CReal pre-Hilbert datum
with a proved radical law, not an assumed quotient certificate.

The next structural step is now mechanical but still proof-bearing: define the
squared distance from subtraction, prove its triangle and replacement laws,
and instantiate `CRealSeminormCompletion`.  A cutoff-independent transfer
action on the finite syntax remains a separate analytic issue.  The fixed-nome
cofinal strictness certificate, thermodynamic/spacing uniformity, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1134 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Physical BF4 limiting squared-seminorm completion (2026-08-20)

`BF4PhysicalCutoffLinearCompletion` closes the quotient-and-carrier frontier
for the fixed-nome finite-linear physical form.  Squared distance is the
limiting form of the presentation difference.  Its `K`-th approximation is
proved equivalent to the literal squared distance in the finite physical GNS
at representation cutoff `K`; finite reflexivity, symmetry, nonnegativity,
and the sqrt-free quadratic triangle inequality therefore pass directly to
the constructive-real limit.

Endpoint replacement is not inferred from finite stages.  Instead, exact
finite-linear difference algebra and the preceding limiting radical theorem
show that replacing either endpoint by a limiting-null presentation preserves
the squared distance.  This discharges `SquaredSeminorm.null_congr` honestly.
The resulting `centralPhysicalCutoffLinearSquaredSeminorm` instantiates the
existing choice-free framework, yielding a positive-definite null quotient,
an explicit-modulus Cauchy completion
`CentralPhysicalCutoffLinearCompletion`, and constant embeddings of both
presentations and radical classes.

This constructs an actual completed carrier at each fixed rational
`0 < w < 1` and fixed finite half-extent, but it has not yet descended zero,
addition, negation, rational scaling, or a cutoff-independent physical Markov
transfer to that completion.  The cofinal strict `1/16` input is independently
uninhabited, and nome/volume/spacing limits, OS reconstruction, continuum QFT,
and the Clay theorem remain open.  A source check and focused monitored build
completed successfully, the latter with 1135 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Algebraic operations on the completed physical BF4 carrier (2026-08-20)

`BF4PhysicalCutoffLinearCompletedAlgebra` descends the finite-linear
operations to the newly constructed cutoff-removed completion.  Addition is
proved binary quadratic-Lipschitz by comparison at every approximation index
with the finite physical GNS parallelogram bound.  Rational scaling is proved
to multiply squared distance by `s^2`; the computable
`CReal.InnerRegularity.scaleTolerance` therefore supplies the Type-level
continuity modulus needed by the generic completion map.

The module consequently constructs completed addition, rational scaling,
zero, and negation on the exact same fixed-nome, fixed-half-extent carrier.
These are genuine quotient-respecting functions, not selected representative
operations.  Their additive-group and rational-module equations have not yet
been proved on arbitrary completed points, so no bundled linear-space claim is
made here.  A cutoff-independent physical Markov action, strict completed gap,
nome/volume/spacing limits, continuum QFT, and the Clay theorem remain open.
A source check and focused monitored build completed successfully, the latter
with 1137 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Rational module laws on the completed physical BF4 carrier (2026-08-20)

`BF4PhysicalCutoffLinearCompletedModule` proves that the completed operations
form an honest rational module.  Exact semantic laws for zero, inverse,
associativity, commutativity, scalar identity, scalar multiplication,
distributivity in the scalar, and distributivity over vectors are first
checked on the finite-linear syntax.  The finite-stage GNS bridge shows that
semantically equivalent presentations have zero limiting squared distance.

Quotient induction and the explicit pointwise-null closeness witness then
prove every law as literal equality on arbitrary completed Cauchy classes.
The bundled `centralPhysicalCutoffCompletedQModule` therefore carries the
actual fixed-nome completed carrier, its four operations, and all rational
module equations without choosing representatives.

This closes the linear-carrier frontier, not the operator frontier.  The
finite physical Markov action is cutoff-dependent and does not preserve the
finite unit-atom syntax at a fixed cutoff-independent level.  Constructing a
single nonexpansive action on this limiting carrier requires a new transfer
moment/realization bridge.  The strict cofinal `1/16` input, completed inner
product extension, vacuum-complement gap, nome/volume/spacing limits,
continuum QFT, and the Clay theorem remain open.  A source check and focused
monitored build completed successfully, the latter with 1138 jobs.  Every
printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Analytic kernel for the completed physical BF4 inner form (2026-08-21)

`CRealInnerRegularity` now includes `scaleLeftSigned`: an explicit-modulus
regularity combinator for multiplication by an arbitrary rational.  Its proof
uses `abs q` as a constructive Lipschitz constant and a division-free
sign-cased rational product estimate, so signed coefficients in a finite
linear observable no longer hide a proposition-level cutoff.

`BF4PhysicalCutoffLinearCompletedInnerKernel` retains the executable corrected-
slab cutoff modulus as Type-level `InnerRegularity` data and propagates it
through every node of the actual finite-linear physical pairing.  It also
proves a quantitative two-sided Cauchy--Schwarz bound from eventual diagonal
bounds, identifies the dense diagonal with squared distance to zero, and
proves the exact bilinear endpoint telescope.  These are precisely the
analytic inputs required to show that `n |-> B(X_n,Y_n)` is a constructive
outer Cauchy sequence for two explicit-modulus completion representatives.

This closes the inner analytic-kernel frontier, not the completed-form
frontier: the outer pairing limit, representative independence, descent to an
`RC`-valued completed inner form, and its laws are still to be constructed.
The cutoff-independent transfer, strict cofinal `1/16` input, vacuum-complement
gap, nome/volume/spacing limits, continuum QFT, and Clay theorem remain open.
A source check and focused monitored build completed successfully, the latter
with 1139 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Representative-level outer physical BF4 pairing limit (2026-08-21)

`BF4PhysicalCutoffLinearCompletedInnerOuter` constructs the pairing limit for
two explicit-modulus Cauchy representatives of the physical completion.  One
anchor term and its explicit inner approximation rate give a computable
rational bound; the squared-distance triangle then bounds every sufficiently
late diagonal term of each representative.

A division-free product budget combines those diagonal ceilings with the
preceding quantitative Cauchy--Schwarz theorem.  The exact bilinear telescope
therefore supplies a Type-level outer rate for
`B(X_m,Y_m)-B(X_n,Y_n)`.  `CReal.completeLimitFromRate` consumes that rate and
the per-term inner moduli to construct a choice-free Bishop-real limit, with a
proved `ConvergesTo` witness.

This is still a representative-level construction.  Invariance under the
completion `Close` relation, descent to an `RC`-valued form, and completed
bilinear/positive laws remain next.  The cutoff-independent transfer, strict
cofinal `1/16` input, nome/volume/spacing limits, continuum QFT, and Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1140 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Representative independence of the outer physical pairing (2026-08-21)

`BF4PhysicalCutoffLinearCompletedInnerWellDefined` proves that the constructed
outer pairing limit depends only on completion classes.  A general constructive
comparison lemma first shows that two convergent Bishop-real sequences with
same-index two-sided `leRat` differences tending to zero have equivalent
limits.

For physical completion representatives, the two explicit `Close` moduli feed
the exact bilinear telescope.  Uniform diagonal ceilings and quantitative
Cauchy--Schwarz bound both telescope terms, yielding an explicit same-index
comparison rate.  Applying the general limit lemma proves
`physicalCauchyPairingLimit_welldef` simultaneously in both arguments.

The pairing can now descend through the completion quotient; defining that
`RC`-valued form and proving symmetry, positivity, additivity, homogeneity,
and dense compatibility are next.  The cutoff-independent transfer, strict
cofinal `1/16` input, nome/volume/spacing limits, continuum QFT, and Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1141 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## RC-valued completed physical BF4 inner form (2026-08-21)

`BF4PhysicalCutoffLinearCompletedInner` uses representative independence to
descend the constructed pairing limit through both completion quotients.  The
result `centralPhysicalCutoffCompletedInner` is a literal function from the
actual fixed-nome completed physical carrier twice into the genuine-real
quotient `RC`; no representatives are selected from a quotient.

For constant Cauchy representatives, convergence of the outer sequence
reverses directly to equivalence with the original `innerLimit`.  Consequently
the completed form is proved equal to the cutoff-removed physical pairing on
the dense embedded finite-linear image.

Symmetry, diagonal nonnegativity, addition, and rational homogeneity on
arbitrary completed points are not inferred merely from this descent; their
limit-uniqueness proofs are next.  The cutoff-independent transfer, strict
cofinal `1/16` input, nome/volume/spacing limits, continuum QFT, and Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1142 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Positive symmetric rational-bilinear laws for the completed BF4 form (2026-08-21)

`BF4PhysicalCutoffLinearCompletedInnerLaws` proves the intrinsic laws of the
completed `RC`-valued physical form.  Symmetry, diagonal nonnegativity,
additivity in both arguments, and rational homogeneity in both arguments are
first proved for arbitrary explicit-modulus Cauchy representatives by
uniqueness of constructive limits.  Quotient induction then turns them into
literal theorems on arbitrary completed points.

The fixed-nome completed physical BF4 carrier therefore now has an actual
positive symmetric rational-bilinear form extending the dense cutoff-removed
pairing.  This is a structural inner-product milestone, not a transfer or
spectral theorem: separation of points, a normalized vacuum and completed
vacuum complement, a compatible cutoff-independent transfer, its uniform
strict contraction, nome/volume/spacing limits, continuum QFT, and the Clay
theorem remain open.  A source check and focused monitored build completed
successfully, the latter with 1147 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Normalized vacuum and completed physical BF4 vacuum complement (2026-08-21)

`BF4PhysicalCutoffLinearCompletedVacuumComplement` identifies the literal
constant-one finite-linear observable, embeds it into the same fixed-nome
completed carrier, and proves that its completed `RC`-valued self-pairing is
exactly one.  A direct constructive separation at tolerance `1/2` proves that
this normalized vacuum is not orthogonal to itself.

Orthogonality to the vacuum now defines an actual completed subtype.  Every
dense finite-linear orthogonal vector embeds into it; completed zero,
addition, negation, and rational scaling preserve it; and the inherited laws
are bundled as `centralPhysicalCutoffCompletedVacuumComplementQModule`.

This closes the fixed-nome carrier/vacuum-complement frontier, not the
dynamical one.  The finite physical Markov action is still indexed by the
representation cutoff and does not yet define one compatible action on this
cutoff-removed syntax and completion.  Such a transfer, its stationarity and
self-adjointness, its uniform strict complement bound, nome/volume/spacing
limits, continuum QFT, and the Clay theorem remain open.  A source check and
focused monitored build completed successfully, the latter with 1148 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Globally vacuum-fixing recoding of every finite physical BF4 Markov action (2026-08-21)

`BF4PhysicalCutoffLinearMarkovSyntax` constructs a globally unit-interval
atomic image without deciding equality of function-valued edge labellings.
For a unit observable `f`, the recoding is the constructive stochastic
extension `P_K f + (1 - P_K 1) f`.  Every positive conditional row sums to one
on the full finite carrier; filtering to retained targets cannot increase its
mass; and exact rational monotonicity proves that this extension remains in
`[0,1]`.  On every retained physical source, row normalization reduces it to
the genuine finite Markov value.

Recursion over the finite-linear syntax gives a cutoff-indexed endomorphism of
the same carrier used by the cutoff-removed completion.  Its value on retained
states is exactly the genuine finite physical action; the vacuum is fixed as
a global semantic finite-linear object on every edge labelling; and the exact
GNS bridge proves that the limiting squared distance of two recoded images,
evaluated at the same cutoff, is bounded by the original distance evaluated
at that cutoff.

This removes the type mismatch between finite Markov outputs and the limiting
syntax, but does not manufacture an operator limit.  Cross-cutoff Cauchy
control of the recoded outputs, compatibility with Cauchy representatives,
descent to one completed transfer, strict complement contraction,
nome/volume/spacing limits, continuum QFT, and the Clay theorem remain open.
A source check and focused monitored build completed successfully, the latter
with 1149 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Cross-cutoff Markov Cauchy residual and exact vacuum limit (2026-08-21)

`BF4PhysicalCutoffLinearMarkovCauchy` isolates the first genuinely
cross-cutoff operator estimate as the Type-level structure
`CentralPhysicalLinearMarkovCrossCutoffModulus`.  For one finite-linear
observable it supplies an explicit rate after which the limiting squared
distance between its cutoff-`m` and cutoff-`n` recoded Markov images is below
any positive rational tolerance.

Such a witness now constructs an actual Cauchy representative and therefore a
canonical point of the existing physical completion.  The completed point is
independent of the chosen rate witness.  A family of pointwise witnesses
contracts to an actual map from the dense finite-linear syntax into the
completion.  Because the cutoff action is recursive on that common syntax,
this dense map is now proved to preserve zero, addition, and every rational
scalar.  These equalities compare pointwise identical Cauchy sequences and
therefore require no additional analytic hypothesis.

The vacuum channel is closed unconditionally: the global cutoff vacuum
identity gives a zero-rate cross-cutoff modulus, and its completed cutoff
limit is exactly the already normalized vacuum.  Thus the new analytic
residual concerns nonconstant observables rather than stationarity.

No theorem in the current arbitrary-cutoff covariance library inhabits the
nonconstant cross-cutoff modulus.  Moreover, pointwise dense convergence by
itself does not give compatibility with radical-null inputs or with arbitrary
varying Cauchy representatives.  Those descent estimates, a completed
transfer, complement preservation and strict contraction, nome/volume/spacing
limits, continuum QFT, and the Clay theorem remain open.  A source check and
focused monitored build completed successfully, the latter with 1150 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Exact descent interface for one completed physical BF4 transfer (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovTransfer` separates the remaining
operator-limit problem into its actual constructive components.  Dense
radical data consists of pointwise cross-cutoff convergence plus an explicit
close witness for every limiting-radical-null input pair; this descends the
dense map through the positive-definite null quotient.

The stronger `CentralPhysicalLinearMarkovCompletionModulus` has exactly two
quantitative fields.  Its diagonal Cauchy rate controls
`P_m(X_m)` versus `P_n(X_n)` for each arbitrary input Cauchy representative.
Its close-preservation rate controls `P_n(X_n)` versus `P_n(Y_n)` for close
representatives.  These fields now construct a quotient-well-defined map on
the entire completed physical carrier.  The construction agrees with the
dense cutoff limit, fixes the normalized completed vacuum, and automatically
supplies both the earlier pointwise moduli and dense radical data.

This is an exact reduction, not an existence claim: no nonconstant completion
modulus is currently inhabited.  Its two estimates must be derived from new
BF4 cross-cutoff analysis.  Preservation of the completed vacuum complement
also still requires the appropriate pairing/stationarity or self-adjointness
bridge.  Strict complement contraction, nome/volume/spacing limits, continuum
QFT, and the Clay theorem remain open.  A source check and focused monitored
build completed successfully, the latter with 1151 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Rational-linearity of the conditional completed BF4 transfer (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovLaws` proves that every completed
transfer constructed from `CentralPhysicalLinearMarkovCompletionModulus`
preserves completed zero, addition, and rational scaling on arbitrary
completed points.  Quotient induction reduces each equality to the recursive
definition of the same-syntax cutoff action, so no further analytic estimate
is consumed.  The result is bundled as
`centralPhysicalCutoffCompletedMarkovQLinearEndomorphism` on the concrete
completed physical rational module.

The completion modulus remains an uninhabited analytic input for nonconstant
vectors.  Rational-linearity and `T vacuum = vacuum` also do not by themselves
show that `T` preserves vectors orthogonal to the vacuum; that restriction
needs completed vacuum-pairing invariance (or a sufficient self-adjointness
bridge).  Complement preservation, strict contraction, nome/volume/spacing
limits, continuum QFT, and the Clay theorem remain open.  A source check and
focused monitored build completed successfully, the latter with 1152 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Completed BF4 transfer restricted to the vacuum complement (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement` isolates the minimum
remaining form compatibility as the Type-level certificate
`CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant`.  It says exactly
that the already constructed completed transfer preserves pairing with the
already normalized completed vacuum.  A second, stronger certificate records
self-adjointness for the actual completed physical inner form.  Because the
transfer already fixes the vacuum, self-adjointness now proves the minimum
pairing invariant rather than requiring a separate stationarity assumption.

Either certificate, once supplied, restricts the actual transfer to the
actual completed vacuum-complement subtype.  Preservation of zero, addition,
and every rational scalar follows from the ambient completed transfer laws,
and the restricted map is bundled as a rational-linear endomorphism of the
completed vacuum-complement module.

This closes the quotient/subtype mechanics, not the analytic input.  Neither
the nonconstant completion modulus nor completed pairing invariance or
self-adjointness is inhabited here.  The next causal frontier is to transport
finite-cutoff detailed balance through the cutoff limit, with enough explicit
cross-cutoff control to inhabit those certificates.  A strict complement
contraction, nome/volume/spacing limits, continuum QFT, and the Clay theorem
remain open.  A source check and focused monitored build completed
successfully, the latter with 1153 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Finite stationarity to completed BF4 vacuum pairing (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing` proves the literal
finite bridge that was previously only implicit.  At every representation
cutoff `n`, the `n`-th approximation of `<P_n x, vacuum>` is exactly the
`n`-th approximation of `<x, vacuum>`.  The proof uses the recoded action's
agreement with the genuine retained-row action and the already-proved finite
stationary-mean identity.

The iterated-limit obstruction is then isolated as
`CentralPhysicalLinearMarkovVacuumPairingInnerCofinality`.  Its explicit stage
rate says precisely when the diagonal cutoff dominates the already-defined
inner-regularity rates of both pairings.  Exact finite diagonal equality plus
this cofinal rate constructs eventual two-sided approximation closeness,
identifies the two outer pairing limits, supplies the completed
vacuum-pairing invariant, and finally constructs the rational-linear
completed vacuum-complement operator.

This is a strict reduction of the prior abstract pairing/self-adjointness
input, not its analytic discharge.  The cofinal inner-regularity record and
the nonconstant completion modulus remain uninhabited.  A strict complement
contraction, nome/volume/spacing limits, continuum QFT, and the Clay theorem
remain open.  A source check and focused monitored build completed
successfully, the latter with 1154 jobs.  Every printed load-bearing
declaration reports only `[propext, Quot.sound]`.

## Same-object strict contraction and geometric decay contract (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovContraction` isolates the next analytic
statement on the exact cutoff-removed operator as the Type-level certificate
`CentralPhysicalCutoffCompletedMarkovStrictContractionData`.  Its recoverable
rate `q` satisfies `0 <= q < 1`, and its estimate is the literal completed
squared-norm contraction on the actual completed vacuum complement.

The actual restricted transfer is iterated internally, and the one-step
estimate is proved to yield
`<T^n v,T^n v> <= (q^2)^n <v,v>` for every natural power.  This implication
uses no spectral theorem, division by a possibly zero norm, or unbounded
generator.

No strict-contraction certificate is inhabited here.  In particular, the
separate finite or matched-cutoff `1/16` results are not a same-object bridge
to the cutoff-removed operator.  The nonconstant completion modulus, vacuum
cofinality, and strict contraction remain open.  Nome/volume/spacing limits,
continuum QFT, and the Clay theorem also remain open.  A source check and
focused monitored build completed successfully, the latter with 1155 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Same-object completed Cauchy--Schwarz and correlation decay (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay` transports the sharp
finite-linear Cauchy--Schwarz inequality through the explicit outer pairing
limit and the completion quotient.  The actual cutoff-limit physical BF4
inner form therefore satisfies completed-real Cauchy--Schwarz for arbitrary
completed vectors.

Composing this unconditional theorem with the conditional same-object power
norm estimate proves geometric decay of every squared matrix coefficient
`<T^n v,test>^2` when `v` belongs to the actual completed vacuum complement;
`test` may be any vector in the same completed carrier.  Thus the route from
one-step strictness to same-object correlation decay is now kernel-checked.

This does not inhabit the strict-contraction certificate or identify its rate
with the separate finite or matched-cutoff `1/16`.  The nonconstant completion
modulus, vacuum cofinality, and same-object strict contraction remain open, as
do nome/volume/spacing limits, continuum QFT, and the Clay theorem.  A source
check and focused monitored build completed successfully, the latter with
1215 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Fixed-nome finite-cutoff completed operator gap (2026-08-21)

`BF4PhysicalFixedNomeCompletedOperatorNormGap` extends the existing
`FixedNomeCutoffCenteredSixteenth` interface from bounded-observable connected
forms to the genuine physical GNS completion at every representation cutoff.
Exact rational centering now proves the completed vacuum-complement form gap
with rate `1/16` for arbitrary finite half-extent.

The existing constructive form-to-operator argument then upgrades this to the
literal completed squared-norm contraction
`||T v||^2 <= (1/16)^2 ||v||^2`, uniformly in the representation cutoff.  No
division by a vector norm or spectral theorem is used.

No `FixedNomeCutoffCenteredSixteenth` inhabitant is constructed here.  The
result is still a family of finite-cutoff completed GNS spaces, not the single
cutoff-removed completion constructed in the current frontier.  Reaching that
object now requires the fixed-nome finite certificate and centered graph-norm
convergence of both vectors and their transferred images.  Nome/volume/spacing
limits, continuum QFT, and the Clay theorem remain open.  A source check and
focused monitored build completed successfully, the latter with 1237 jobs.
Every printed load-bearing declaration reports only `[propext, Quot.sound]`.

## Centered graph-norm compiler to the same-object gap (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovGraphNorm` constructs, for every
representative of the cutoff-removed completion, its canonical exactly
centered vector in each genuine finite-cutoff physical GNS completion.  Exact
finite stationarity proves unconditionally that every such approximant lies
in its own finite vacuum complement.

The fixed-nome finite completed theorem therefore gives the literal
`(1/16)^2` squared-norm inequality for every member of these two canonical
graph-norm streams.  The only remaining transport data are packaged as
`CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence`: convergence
of the centered finite norms to the cutoff-removed norm and convergence of the
transferred centered norms to the norm of the already constructed
cutoff-removed transfer.  These two laws, together with
`FixedNomeCutoffCenteredSixteenth`, now construct the actual same-object
`CentralPhysicalCutoffCompletedMarkovStrictContractionData` with rate `1/16`.

Neither analytic input record is inhabited.  Thus this closes the finite-gap
to same-object compiler, not the cross-cutoff estimates that feed it.  The
nonconstant completion modulus, vacuum-pairing cofinality, fixed-nome
sixteenth, and centered graph-norm convergence remain open.  Nome/volume/
spacing limits, continuum QFT, and the Clay theorem remain open.  A source
check and focused monitored build completed successfully, the latter with
1257 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Four-rate cofinality compiler for completed graph norms (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality` replaces the two
opaque centered graph-norm convergence laws by four explicit diagonal
inner-regularity rates.  The existing vacuum-pairing cofinality already
supplies the input and Markov-image vacuum rates, so the only genuinely new
fields are cofinality of the input and Markov-image self-pair rates.

A reusable diagonal theorem now proves that when an outer cutoff stage
dominates its own explicit inner-approximation rate, the rational diagonal
converges to the already constructed outer pairing limit.  Exact finite
centering and centered Markov intertwining then prove both centered graph-norm
limits.  Completed vacuum orthogonality kills the input mean-square correction,
and the proved vacuum-pairing invariance kills the transferred correction.
Together with `FixedNomeCutoffCenteredSixteenth`, these explicit rates compile
to strict contraction of the actual cutoff-removed completed transfer at
literal rate `1/16`.

No completion modulus, four-rate cofinality datum, or fixed-nome sixteenth is
inhabited.  The analytic frontier is therefore sharpened to construction of
the nonconstant completion modulus, the two vacuum cofinal rates, the two
self-pair cofinal rates, and the fixed-nome finite certificate.  Nome/volume/
spacing limits, continuum QFT, and the Clay theorem remain open.  A source
check and focused monitored build completed successfully, the latter with
1259 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Markov rate invariance and two-rate graph residual (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance` proves that
the explicit inner-regularity rate is unchanged when both arguments are
recoded by the finite-cutoff Markov syntax, and likewise when a recoded input
is paired with the unchanged vacuum.  The proof is structural: the atomic
slab modulus is independent of the atom value, while Markov recoding preserves
the finite-linear addition and signed-scaling tree exactly.

Consequently the prior four diagonal rate fields contract to
`CentralPhysicalLinearGraphNormInputInnerCofinality`, containing only
input-side self-pair and vacuum-pair cofinality.  Exact rate equalities produce
both action-side fields, the completed vacuum-pairing invariant, both centered
graph-norm limits, and—given the completion modulus and fixed-nome
sixteenth—the actual cutoff-removed strict contraction at rate `1/16`.

The two-rate record is not inhabited.  In particular, arbitrary completion
representatives may carry syntax whose structural modulus grows faster than
its same-index cutoff, so metric Cauchyness alone has not been claimed to
imply this universal same-index property.  The next constructive frontier is
an adaptive representative/reindexing schedule, followed independently by
the nonconstant completion modulus and fixed-nome sixteenth.  Nome/volume/
spacing limits, continuum QFT, and the Clay theorem remain open.  A source
check and focused monitored build completed successfully, the latter with
1260 jobs.  Every printed load-bearing declaration reports only
`[propext, Quot.sound]`.

## Adaptive representative normalization for completed graph norms (2026-08-21)

`BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex` removes the
unjustified demand that an arbitrary completion representative pay its own
syntax-dependent inner rates at the same cutoff index.  It first replaces each
inner regularity witness by an explicitly antitone running-maximum rate and
then applies the existing executable slow-diagonal search to the input
self-pair and input-vacuum-pair requirements.

For every completed representative, the resulting sampler is proved cofinal,
pays both selected regularized rates, and defines a genuine Cauchy
representative.  An explicit closeness modulus proves that this adaptively
sampled representative is equal to the original point in the physical
completion quotient.  Thus representative normalization is now constructive
and no universal same-index cofinality hypothesis is needed.

This module does not yet transport the finite graph-norm inequality through
the sampled representative, and it constructs neither the nonconstant
completion modulus nor `FixedNomeCutoffCenteredSixteenth`.  The next frontier
is the sampled graph-norm convergence compiler, after which those two honest
analytic inputs remain.  Nome/volume/spacing limits, continuum QFT, and the
Clay theorem remain open.  A source check and focused monitored build
completed successfully, the latter with 1299 jobs.  Every printed
load-bearing declaration reports only `[propext, Quot.sound]`.

## Nonzero upper-triangle reduction of the physical table seam (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact` replaces
the historical deeply nested local-zero aggregate with a literal `List.all`
composition of the already process-isolated 65 row theorems.  Every raw-table
zero is therefore again proved to vanish in the production physical kernel,
but the final composition now checks in under one second after its shards are
cached.  Its focused target completed successfully with 1678 jobs.

`BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction` packages the
remaining representation seam as
`CutoffTwoSectorPhysicalNonzeroUpperCertificate`.  At this historical stage it
asked for a cheap exact symmetry law of the stored raw table and physical
equality only on nonzero upper-triangle entries.  Local support discharges
every zero; physical and raw symmetry reflect upper entries into the lower
triangle.  This smaller record
constructs the original `CutoffTwoSectorPhysicalTableCertificate`, so all
existing entry and row-marginal bridges consume it unchanged.  The direct
source check and dependency-complete target passed, the latter with 1747
jobs, and both load-bearing declarations report exactly
`[propext, Quot.sound]`.

The smaller certificate is not inhabited.  The untrusted shared-DAG generator
reports 499 unordered nonzero pairs, but an attempted all-at-once Lean count
was stopped at the 12 GiB memory reserve and no count theorem is retained or
claimed.  More importantly, a direct `by decide` build of even physical
recurrence row zero also reached the reserve, so raw recurrence rows are not a
viable proof route.  The next finite frontier is to check raw-table symmetry
in small shards and scale the already verified shared-DAG bucket method from
its pilot entries to the nonzero upper pairs.  Cofinal sector selection,
completion, thermodynamic/continuum limits, QFT axioms, and the Clay target
remain open.

## Stored cutoff-two raw-kernel symmetry (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck` and the 65 modules under
`BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryRows/` check every transposed
entry equality of the stored exact 65-state table in a separate Lean process.
The compact `BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryRows` aggregate
therefore proves `cutoffTwoSectorRawKernel_symm` unconditionally.

`BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction` now consumes that
theorem directly.  Its residual
`CutoffTwoSectorPhysicalNonzeroUpperCertificate` has exactly one field: the
production physical-kernel equality for upper-triangle entries whose stored
raw value is nonzero.  Raw-table symmetry is no longer an assumed field.

The row-isolated symmetry target completed successfully with 1667 jobs; every
row theorem and the Boolean aggregate are axiom-free.  The exported setoid
symmetry theorem uses only `[propext, Quot.sound]`.  A direct source check and
dependency-complete build of the revised physical reduction also passed, the
latter with 1814 jobs and the same axiom gate.  The external generator reports
499 nonzero upper pairs, but no Lean count theorem is claimed.  Physical trace
equalities, cofinal sector selection, completion, thermodynamic/continuum
limits, QFT axioms, and the Clay target remain open.

## Second adjacent cutoff-two spatial-axis transport (2026-08-21)

`bf4_cutoff_two_axis_swap12_certificate.py` derives the action exchanging the
last two abstract cube axes and emits explicit boundary-coordinate, common
factor, cube-source, lower-link, and 65-sector permutations.  The 64 non-cube
state checks live in separate modules under
`BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates/`; thirteen small
aggregates assemble them without repeating the expensive normalization.

`BF4PhysicalBoundaryCutoffTwoAxisSwap12AllStateTransport` proves the checked
local factor transport for every sector state, and
`BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance` lifts the common
and state transports through the finite coordinate reindex theorem.  Thus the
exact 140-factor interface partition sum is invariant when both sector states
are transformed by this second adjacent swap.  Together with the pre-existing
first adjacent swap, these are the two generators needed for the unsigned
spatial `S3` action.

The all-state target completed successfully with 1680 jobs, the dedicated
axiom audit with 1681 jobs, and the interface target with 1680 jobs.  The
load-bearing declarations report exactly `[propext, Quot.sound]`.  An earlier
five-states-per-module build was intentionally stopped after silent expensive
normalization; it is not counted as passed.  This theorem is only interface
partition invariance: lower-face scalar invariance, physical-kernel
invariance, a kernel-checked `S3` orbit quotient, and the reduced nonzero
physical trace certificate remain open.  Signed coordinate flips also remain
a separate summed-identity problem because the external pointwise factor
transport audit did not validate them.  No cutoff-uniform gap,
thermodynamic/continuum construction, QFT axioms, or Clay conclusion is
claimed.

## Adjacent-swap invariance of the genuine cutoff-two physical kernel (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance` closes the scalar
term left outside the two interface-partition theorems.  Two literal
`List.finRange 65` Boolean certificates verify that the lower-face heat scalar
is invariant under each adjacent sector permutation.  Combining those
certificates with the exact factor-partition equalities and the production
kernel factorization proves simultaneous physical-kernel invariance under
both swaps `(01)` and `(12)` for every pair of sector states.

To make the first generator reproducibly buildable in the current cache,
`bf4_cutoff_two_axis_swap_sector_transport_shards.py` now emits 64
process-isolated state modules and thirteen compact aggregates, matching the
successful second-swap architecture.  All 64 first-swap state checks and the
first-swap interface then rebuilt successfully.  The first-swap interface was
also made explicit about its concrete `EdgeLabelling`/rational-product
dependencies and its boundary involution cases.

The first-swap axiom audit completed with 1681 jobs and the combined
physical-kernel target completed successfully with 1762 jobs.
Both scalar invariance theorems and both genuine kernel invariance theorems
report exactly `[propext, Quot.sound]`.  This closes the two generating
physical equalities but does not yet construct or verify the six-element `S3`
word action, orbit representatives, or a reduced nonzero-pair certificate.
Signed flips, cutoff-uniform contraction, completion, thermodynamic/continuum
limits, QFT axioms, and the Clay theorem remain open.

## Six-element cutoff-two spatial S3 kernel action (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction` packages the two adjacent
swaps into six explicit normal words.  A literal multiplication table is
proved associative with two-sided identity and inverses.  A finite check over
all `6 * 6 * 65` cases proves that table multiplication agrees with function
composition on the exact sector order.  The two generator kernel equalities
then compose to physical-kernel invariance under every normal word.

The focused target completed successfully with 1763 jobs.  Both the checked
action-composition theorem and the six-word physical-kernel invariance theorem
report exactly `[propext, Quot.sound]`.  The next frontier is no longer group
closure: it is a checked canonicalization of unordered state pairs, followed
by raw-table transport and a concrete nonzero orbit-representative list.
Signed flips, residual physical trace evaluations, cutoff-uniform contraction,
completion, thermodynamic/continuum limits, QFT axioms, and the Clay theorem
remain open.

## Canonical unordered-pair transport for the cutoff-two spatial S3 action (2026-08-21)

`BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData` defines a
deterministic least-code representative of an unordered pair of the 65 sector
states.  An abstraction lemma prevents Lean from accidentally reducing the
concrete six-action fold while proving upper-triangularity.
`BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization` then transports the
genuine production reflected kernel to that representative using the proved
six-word action and physical-kernel symmetry.

`BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck`, its 65
process-isolated row modules, and the compact
`BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows` aggregate check
the corresponding equality in the stored raw table for exactly the 2,145
upper-triangle source pairs.  Thus both the physical and stored-raw sides of
the existing nonzero-upper residual now transport to the same canonical pair.
The row target completed successfully with 1,834 jobs and the combined axiom
audit/physical-transport target with 1,836 jobs.  Closed row decisions use only
`[propext]`; both exported transport theorems use exactly
`[propext, Quot.sound]`.

This does not yet inhabit the nonzero-upper physical certificate.  The next
finite obligation is to kernel-check the explicit nonzero representative
carrier and evaluate the production physical/raw trace equality once on each
member.  An external diagnostic reports 127 such representatives, but no
Lean count or completeness theorem is claimed here.  Signed flips,
cutoff-uniform contraction, completion, thermodynamic/continuum limits, QFT
axioms, and the Clay theorem remain open.

## Exact 127-representative contraction of the cutoff-two physical seam (2026-08-21)

`bf4_cutoff_two_spatial_s3_nonzero_representatives.py` emits an explicit
127-pair carrier, a duplicate-free 127-code list, a compact code recognizer,
and 65 process-isolated coverage rows.  Lean proves the pair/code lengths,
uniqueness, upper-triangularity, stored-raw nonzeroness, and that the
recognizer accepts exactly the same in-range codes as the list.  The row
aggregate proves that every nonzero upper-triangle source pair canonicalizes
to an accepted representative code.  The earlier external counts are
therefore replaced by kernel-checked carrier and completeness theorems.

`BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction` packages the
remaining physical work as
`CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate`: production
physical/raw equality only on the 127 checked representatives.  Proved
physical canonical transport, representative coverage, and stored-raw
canonical transport compile that record into the 499-entry nonzero-upper
certificate and then into the original full 65-row physical-table
certificate.  A `Fin 65`/`Nat.getD` accessor theorem closes the representation
seam between the symmetry and raw-table modules.

The dependency-complete axiom-audit target completed successfully with 2,119
jobs.  Recognizer/list equality is axiom-free; the aggregate coverage theorem
and exported compiler declarations use exactly `[propext, Quot.sound]`.
The 127-field representative certificate remains uninhabited.  The next
finite frontier is to extend the existing shared-DAG physical evaluator from
pilot entries to these representatives.  No production-kernel `49/50` gap,
cofinal sector family, completed gap, thermodynamic/continuum construction,
QFT axioms, or Clay theorem is claimed.

## First new shared-DAG representative evaluation (2026-08-21)

`bf4_cutoff_two_shared_dag_certificate.py` now emits the complete shared-DAG
trace for representative `(0,1)`: one trace-data module, six process-isolated
four-step trace shards, the trace root, and the final production-physical/raw
kernel certificate.  The proof reuses the 1,606 globally canonical factor
buckets and transports the actual cutoff-two physical factor list through the
checked 24-step elimination trace.

The dependency-complete physical-certificate target completed successfully
with 1,722 jobs and reports exactly `[propext, Quot.sound]` for
`centralPhysicalReflectedKernel_cutoffTwo_sector_R00C01_eqv_raw_sharedDAG`.
This discharges one previously unevaluated member of the exact 127-element
representative carrier and, importantly, leaves the global bucket cache built
for subsequent traces.  It does not yet inhabit the representative
certificate: the remaining representative equalities must be generated,
kernel-checked, and assembled before the compiler can close the 499 nonzero
upper entries and the full physical table.  No production-kernel `49/50` gap,
uniform limit, continuum QFT, or Clay theorem is claimed.

## Scalable representative aggregation and representative `(0,2)` (2026-08-21)

The shared-DAG generator now supports every canonical source state, rather
than only the specially sharded states `0` and `1`.  Its first use exposed and
repaired a missing `by` in the generated unsharded common-transport module;
that module and state `2` now kernel-check with exactly
`[propext, Quot.sound]`.  The complete trace for representative `(0,2)` then
passes, including a raw-`Nat`-state accessor wrapper suitable for aggregation.

`CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate` now states its
residual equality through the evaluator's raw `Nat/getD` accessor and performs
the proved `Fin`-accessor conversion once, symbolically, in its compiler.
The physical proposition is kept behind
`cutoffTwoSectorRepresentativePhysicalStatement`, so pair equalities can be
transported without reducing the concrete 65-state list.  A four-entry prefix
module checks this assembly architecture for `(0,0)`, `(0,1)`, `(0,2)`, and
`(1,1)`.

The prefix dependency target completed successfully with 2,272 jobs; its
exported aggregate uses exactly `[propext, Quot.sound]` and its final module
built in 0.5 seconds.  Four of the 127 exact representatives are now assembled
by this path.  The remaining 123 trace equalities and the full certificate are
still open, as are the production-kernel `49/50` gap, every uniform limit,
continuum QFT construction, and the Clay theorem.

## Complete cutoff-two physical table from the 127 shared-DAG representatives (2026-08-21)

`bf4_cutoff_two_shared_dag_certificate.py --emit-representatives` now emits
all 127 exact spatial-S3 representative traces from one 1,606-bucket shared
DAG build: 127 trace-data modules, 762 process-isolated trace shards, 127
trace roots, and 127 physical certificates.  The bulk path explicitly
preserves the hand-specialized `(1,1)` bridge used by its kernel certificate.

The representative carrier now has a proved injective pair-code accessor and
a theorem turning its checked code recognizer back into literal list
membership.  `BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate`
assembles the 127 production physical/raw equalities behind opaque statements,
inhabits `CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate`, and
applies the previously checked orbit-reduction compiler to inhabit the exact
full 65-by-65 `CutoffTwoSectorPhysicalTableCertificate`.

The dependency-complete aggregate target completed successfully with 3,413
jobs.  The representative aggregate, residual certificate, and full physical
table certificate each report exactly `[propext, Quot.sound]`.  This closes the
finite cutoff-two physical-table seam.  It does not yet make the stored-table
`49/50` eigenspace estimate an unconditional production-kernel gap theorem,
and it supplies no cofinal cutoff family, cutoff-uniform estimate, Hilbert
completion, thermodynamic/continuum construction, QFT axioms, or Clay theorem.

## Exact constructive canonical-vacuum sector at cutoff two (2026-08-21)

`FiniteBoolGraphRootComponent` now constructs, without choice, the connected
component of a distinguished root in any finite Boolean symmetric graph and
proves root membership, internal connectivity, exact adjacency separation,
and closure under support edges.  `BF4PhysicalFiniteVacuumSector` applies that
construction to the literal indexed positive-row BF4 production kernel.  It
defines the canonical finite vacuum component at every finite cutoff and adds
generic opaque introduction rules for positive kernel edges and two-edge
vacuum connectivity, deliberately keeping concrete cutoff carriers out of
downstream equality normalization.

At cutoff two, `BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive` checks
all 65 stored row-zero entries by kernel `decide`.  The full 127-representative
certificate is sealed behind compact row-zero physical/raw and positivity
theorems, with the generator updated in lockstep.
`BF4PhysicalBoundaryCutoffTwoCubePositiveStar` exposes the genuine production
kernel star, while `BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier` proves
that every state in the exact 65-state cube table belongs to the actual
positive-row Markov carrier and packages proof-local table/carrier index
witnesses.

`BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges`,
`BF4PhysicalBoundaryCutoffTwoCubeVacuumHub`,
`BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge`, and
`BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro` factor the concrete
vacuum-to-hub-to-state path through small proof-only interfaces.
`BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity` consequently proves that
every table state belongs to the canonical physical vacuum component.

For the converse, `BF4PhysicalBoundaryCutoffTwoCubeSectorCode` transports
decidable natural-number code membership to a constructive sector-membership
decision.  `BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape` combines that
decision with exact production-kernel row closure to prove that no support
edge can leave the table sector.  Path induction in
`BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector` then proves exact support
equality between the independently constructed canonical vacuum component and
the literal duplicate-free 65-state table.

Focused source checks and dependency-complete targets pass for the generic
component machinery, the connectivity direction, the no-escape direction,
the exact component equality, and the refactored reducibility obstruction.
Every printed load-bearing declaration reports exactly
`[propext, Quot.sound]`.  This closes the finite cutoff-two sector-selection
seam.  Its `49/50` form-gap contraction is the next finite frontier; all
cutoff/volume compatibility, a uniform completed gap, thermodynamic/continuum
limits, QFT axioms, and the Clay theorem remain open.

## Exact canonical-vacuum production form gap at cutoff two (2026-08-22)

The historical 64-coordinate upper LDL certificate has now been checked
through all rows `0` through `63` and its aggregate theorem.  Together with
the complete 65-by-65 physical/raw table certificate, it proves the exact
centered upper form bound at `q = 49/50`.  On the same literal sector, the
production kernel is independently a finite weighted Gram kernel, so its
quadratic form is nonnegative.  The upper bound therefore becomes the
absolute estimate

```text
|sum_ij x_i K_phys(i,j) x_j| <=
  (49/50) * sum_i d_phys(i) x_i^2
```

for every rational coefficient family satisfying the exact physical
row-sum centering condition `sum_i x_i d_phys(i) = 0` modulo `Q'.eqv`.

The implementation is factored through
`BF4PhysicalBoundaryCutoffTwoSectorPhysicalFormTransport`,
`BF4PhysicalBoundaryCutoffTwoSectorPhysicalGramPositivity`, and
`BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap`.  The transport layer
uses the opaque full-table certificate and explicit wrapper `change`s, so
Lean does not replay the 127-way representative proof during downstream
definitional-equality search.  A separate leaf audit module performs one
recursive axiom report after the contracted theorem has built.

`BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap` combines this form estimate
with the independently proved support equality.  Its theorem
`cutoffTwoCanonicalVacuumSector_exact_and_strict_abs_gap` therefore states in
one place that the 65-state list is exactly the support component of the
vacuum in the genuine finite production carrier and that the production form
on its centered coordinates has strict rate `49/50 < 1`.

Focused source checks and dependency-complete targets pass for form transport,
Gram positivity, the strict absolute form bound, the contracted theorem, and
the leaf axiom audit.  The final audit reports exactly
`[propext, Quot.sound]`.

This closes the finite cutoff-two canonical-vacuum form-gap frontier only.  It
does not construct a compatible family of these canonical components across
cutoffs or volumes, a cutoff/volume-uniform rate, a completed-space operator
gap, thermodynamic or continuum limits, continuum QFT axioms, or the Clay
theorem.  The next causal frontier is to construct explicit cutoff/volume
embeddings that preserve the vacuum root and support edges and intertwine the
restricted physical weights and quadratic forms; only after that can a
uniform strict rate be formulated honestly.

## Physical production-kernel support persists under cutoff enlargement (2026-08-22)

`BF4PhysicalCutoffKernelSupportPersistence` proves that the unnormalized
reflected production kernel is entrywise nonnegative and that every nonzero
entry between states already present at a representation cutoff remains
nonzero at every larger cutoff.  The proof first upgrades nonzero plus
nonnegative to strict positivity, then uses the exact cylinder-numerator
decomposition into the old positive numerator plus a nonnegative new-label
increment.

The source check and dependency-complete target pass, and all three exported
declarations report exactly `[propext, Quot.sound]`.  This closes qualitative
support-edge persistence only.  It does not give equality of kernel entries,
a quantitative lower bound uniform in the cutoff, an explicit index map, or
rooted vacuum-component inclusion.  The next frontier is to use this theorem
with an explicit old-to-new positive-carrier index map and the generic rooted
graph homomorphism to prove canonical vacuum-component compatibility.

## Canonical physical vacuum sector embeds across representation cutoffs (2026-08-22)

`FiniteBoolGraphRootComponentMap` supplies a constructive transport theorem
for root-preserving maps of finite Boolean graphs.  The BF4 specialization in
`BF4PhysicalCutoffVacuumSectorEmbedding` constructs an explicit old-to-new
carrier index map by recursively locating the faithful mixed-radix code of an
old state in the later positive carrier.  A project-local structural locator
is used because the first standard-library `idxOf` proof path introduced
`Classical.choice`; the replacement has no such dependency.

The map is proved in range, represents literally the same edge labelling,
fixes the vacuum index zero, and preserves every true edge of the symmetrized
production support graph.  Root-component transport then proves both indexed
component inclusion and the state-level monotonicity theorem
`centralPhysicalFiniteVacuumSectorStates_mono` for every `base <= later` at
fixed coupling and finite half-volume.

Focused source checks and the dependency-complete target pass.  Every printed
load-bearing theorem reports exactly `[propext, Quot.sound]`.  This closes
qualitative representation-cutoff compatibility of the canonical finite
vacuum sectors.  It does not assert equality of old and later weights or
kernel entries, an exact quadratic-form intertwiner, a cutoff-uniform strict
rate, volume compatibility, Hilbert completion, thermodynamic/continuum
limits, QFT axioms, or the Clay theorem.  The next causal frontier is the
quantitative comparison of the pulled-back later weights and physical forms
with their old-cutoff values.

## Pulled physical carrier entries have constructive cutoff limits (2026-08-22)

`BF4PhysicalCutoffEmbeddedEntryCauchy` pulls each later stationary weight and
normalized reflected-kernel entry back to a fixed old positive carrier using
the explicit state-preserving cutoff index map.  It proves that the resulting
values are exactly the later row marginals and normalized kernel entries of
the same literal old states.  The corrected-slab source and pair cylinder
moduli then give executable two-sided epsilon bounds for any two sufficiently
large cutoffs.

Those bounds are packaged as actual Bishop reals
`centralPhysicalFinitePulledWeightCutoffLimit` and
`centralPhysicalFinitePulledKernelCutoffLimit`.  The source check and
dependency-complete target pass, and every printed declaration reports
exactly `[propext, Quot.sound]`.

This closes entrywise representation-cutoff convergence on every fixed old
finite carrier, and hence on each old canonical vacuum component.  It does
not prove that the cutoff-two entries equal their limits or that its `49/50`
form bound survives.  The next frontier is to pay the finite carrier size and
coefficient envelope to obtain constructive Cauchy limits for the pulled
weighted mean, diagonal form, and matrix quadratic as whole objects.

## Pulled physical finite forms have constructive cutoff limits (2026-08-22)

`BF4PhysicalCutoffEmbeddedFormCauchy` lifts the entrywise pulled cutoff
moduli to the complete weighted mean, diagonal quadratic, and normalized
reflected matrix quadratic on any fixed old positive carrier.  Its finite-sum
estimates explicitly pay the coefficient `l1` envelope for linear forms and
the corresponding quadratic envelope for matrix forms before invoking the
physical source and pair-cylinder moduli.

The three resulting cutoff sequences are packaged as Bishop reals:
`centralPhysicalFinitePulledWeightedMeanCutoffLimit`,
`centralPhysicalFinitePulledDiagonalQuadraticCutoffLimit`, and
`centralPhysicalFinitePulledMatrixQuadraticCutoffLimit`.  The focused source
check and dependency-complete target pass, and every exported declaration
reports exactly `[propext, Quot.sound]`.

This closes cutoff convergence of whole forms only on a fixed finite
coordinate subspace, equivalently after extending its coefficient vector by
zero on all new states.  It does not identify those limits with the
cutoff-two table, preserve exact centering, control the mass of newly entering
vacuum-sector states, or prove that the `49/50` contraction persists.  The
next causal frontier is the canonical vacuum-sector specialization followed
by an exact old/new block decomposition that exposes the leakage and cross
terms requiring uniform estimates.

## Canonical-vacuum-sector pulled forms have cutoff limits (2026-08-22)

`BF4PhysicalCutoffVacuumSectorFormCauchy` restricts the pulled stationary
mean, diagonal quadratic, and normalized reflected matrix quadratic to the
exact root-connected canonical vacuum component at the fixed base cutoff.
The earlier component embedding theorem guarantees that every one of these
old indices represents a state in each later canonical component.  A reusable
list-level linear-form stability theorem makes the construction pay only the
coefficient envelope on this component rather than on the whole positive
carrier.

All three component-restricted sequences are packaged as Bishop reals.  The
focused source check and dependency-complete target pass, and the printed
axiom audit reports exactly `[propext, Quot.sound]` for each exported limit.

These are limits of the embedded old block, equivalently of coefficient
vectors extended by zero beyond it.  They are not limits of the whole growing
canonical component: later cutoffs can add states, stationary mass, and
old/new matrix entries.  The next causal frontier is therefore an exact
finite partition of the later component into the embedded old image and its
new-state complement, followed by algebraic mean/diagonal/matrix block
decompositions.  Only estimates for the resulting leakage and cross terms
could propagate a strict contraction to the growing component.

## Growing physical vacuum sector has an exact old/new block split (2026-08-22)

`BF4PhysicalCutoffVacuumSectorBlockDecomposition` defines the explicit image
of the base canonical component in a later carrier, filters the later
root-connected component into a target-ordered old block and a genuinely new
block, and proves that the old block has exactly the embedded-image members
whenever `base <= later`.  Both filtered lists inherit duplicate-freeness from
the later canonical component.

The full later canonical-sector stationary mean and diagonal quadratic are
then split exactly into old and new terms.  A generic constructive two-by-two
finite quadratic identity splits the reflected matrix form into its old-old,
old-new, new-old, and new-new blocks.  Focused and dependency-complete builds
pass; every printed load-bearing declaration reports exactly
`[propext, Quot.sound]`.

This closes only the algebraic exposure of cutoff leakage.  It supplies no
smallness estimate for the new stationary mass or for either cross block, and
does not yet identify the target-ordered old block sum with the source-indexed
pulled CReal sequences.  The next causal frontier is that exact pushforward
identification, followed by quantitative leakage/cross-term bounds strong
enough to leave a cutoff-uniform strict margin below one.

## Embedded vacuum-sector forms push forward exactly (2026-08-22)

`BF4PhysicalCutoffVacuumSectorFormPushforward` proves that the explicit cutoff
index map is injective on the base canonical component.  The proof uses exact
preservation of literal physical states together with duplicate-freeness of
the base positive carrier.  Hence the target-ordered old block is a literal
permutation of the mapped base component rather than merely a set-theoretic
subset.

For any physical state observable, the module defines an explicit later
coefficient which agrees with the observable on the embedded image and is
zero elsewhere.  Exact finite reindexing then identifies its old-block
weighted mean, diagonal norm, and old-old reflected matrix block with the
source-indexed pulled forms from
`BF4PhysicalCutoffVacuumSectorFormCauchy`.  Focused and dependency-complete
builds pass, and every printed declaration reports exactly
`[propext, Quot.sound]`.

This closes the exact enumeration and coefficient pushforward bridge.  It
does not prove a strict bound for the limiting old block, a rate uniform in
the choice of base component, or a gap on arbitrary vectors in the whole
growing component.  For this particular zero extension the new-coordinate
terms should vanish algebraically; the next frontier is to prove that exact
contraction and isolate the remaining analytic obstruction as the lack of a
base-uniform centered form bound.

## Zero-extended vacuum-sector forms contract exactly to the pulled block (2026-08-22)

`BF4PhysicalCutoffVacuumSectorZeroExtensionContraction` proves that the
observable-based zero extension is literally zero on every genuinely new
later-component coordinate.  Its new-state mean and diagonal contributions
therefore vanish, as do the old-new, new-old, and new-new reflected matrix
blocks.  A generic finite theorem contracts any quadratic whose coefficient
vanishes on one side of a Boolean partition to its true-true block.

Combining those zero identities with the exact pushforward bridge proves that
the full later canonical-component mean, norm, and reflected form of the zero
extension are exactly the pulled base-component forms.  An initial direct
four-block proof repeatedly exceeded the heartbeat limit; factoring the
contraction into the generic theorem reduced the focused check below one
second.  The final focused and dependency-complete builds pass, and all
printed declarations report exactly `[propext, Quot.sound]`.

This removes new-coordinate leakage for every fixed zero-extended vector.
It does not prove a uniform gap on the growing component: every finitely
supported later vector can be based at some cutoff, so the remaining analytic
obligation is a centered strict form bound with one `q < 1` independent of
that base cutoff (and later, of volume and lattice spacing).  The isolated
cutoff-two `49/50` certificate does not supply this uniformity.

## Arbitrary vacuum-sector coefficients extend and contract exactly (2026-08-22)

The pushforward and contraction layers now handle an arbitrary rational
coefficient on the base canonical component, rather than only coefficients
obtained by restricting a global physical observable.  The extension is an
explicit finite sum over the base component.  Injectivity of the cutoff index
map proves that exactly one source contributes on the embedded image, while
no source contributes on a genuinely new target coordinate.

Consequently the full later-component weighted mean, diagonal quadratic, and
reflected matrix quadratic of the arbitrary-coefficient extension equal the
corresponding pulled base-component forms.  This is the required
representation layer for cutoff-dependent head centering: a centered
coefficient may now be constructed directly on the base component and
extended without populating other superselection sectors.  Focused and
dependency-complete monitored builds pass, and all printed declarations use
exactly `[propext, Quot.sound]`.

This is still algebraic compatibility, not a spectral estimate.  The next
frontier is the explicit positive-root head-centering witness at every later
cutoff, followed by cutoff-Cauchy control of its moving correction and a
strict rate uniform in the base cutoff.

## Moving head centering stays inside the canonical vacuum sector (2026-08-22)

`BF4PhysicalCutoffVacuumSectorHeadCentering` constructs the exact
cutoff-dependent centering promised by the arbitrary-coefficient extension.
The cutoff map fixes index zero, and its pulled stationary weight is strictly
positive at every later cutoff.  The coefficient at that one root is changed
by minus the pulled mean divided by the root weight; every other base
coefficient is left unchanged.

A generic finite-list theorem proves the corrected weighted mean is exactly
zero.  After arbitrary-coefficient zero extension, the full later canonical
component is therefore exactly centered, while its diagonal and reflected
forms remain exactly the pulled forms of the moving base coefficient.  This
avoids the mathematically incorrect alternative of subtracting a constant on
the reducible full positive carrier, which would populate other
superselection sectors.  Focused and dependency-complete monitored builds
pass; every printed declaration uses exactly `[propext, Quot.sound]`.

The moving coefficient contains a rational quotient whose numerator and
denominator both vary with the cutoff.  The next frontier is constructive
Cauchy control of that quotient, using the existing pulled-form moduli and a
uniform positive lower bound for the root weight.  Only after that passage
can a base-uniform strict centered rate be meaningfully imposed on the
cutoff-removed dense sector.

## Moving vacuum-sector head correction is cutoff-Cauchy (2026-08-22)

`BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy` packages the positive
head correction (pulled weighted mean divided by pulled root weight) as a
Bishop real.  A reusable signed-quotient estimate controls two rational
quotients from Cauchy bounds on their numerators and denominators, an `l1`
bound on the fixed base coefficient, and one strictly positive lower bound on
both denominators.

For the physical sequence, the numerator and root-weight moduli come from the
already constructed pulled-form and pulled-entry limits.  The root denominator
is bounded below, beyond an explicit cutoff, by the fixed positive-row floor;
all pulled stationary weights are between zero and one.  These data give an
explicit tolerance and cutoff witnessing Cauchy convergence of the moving
correction.  The large modulus proof was factored from the final `CReal`
constructor and checked with a file-local four-million-heartbeat elaboration
budget.  The focused and dependency-complete monitored builds pass, and every
printed declaration reports exactly `[propext, Quot.sound]`.

This proves convergence of the scalar used for exact same-sector centering,
not yet convergence of either centered quadratic form.  The next causal
frontier is finite polynomial stability for the diagonal and reflected forms
when only the root coefficient moves.  Beyond those form limits, the main
analytic obstruction remains a single strict rate `q < 1` uniform in the base
cutoff; no completed, thermodynamic, continuum, or Clay conclusion follows
from this scalar limit alone.

## Root-centered vacuum-sector diagonal is cutoff-Cauchy (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy` proves that changing
only coefficient zero changes a finite weighted square by exactly the
difference of its new and old root contributions.  Applied to the physical
head-centered coefficient, the moving diagonal is therefore the already-
Cauchy fixed-coefficient diagonal plus an explicit polynomial in the moving
head correction and pulled root weight.

Constructive-real addition, negation, and multiplication build a pointwise
Cauchy reference for that polynomial.  A general pointwise-`Q'.eqv` recoding
then packages the literal physical centered diagonal values—not just the
expanded representatives—as a Bishop real.  The focused source check and
dependency-complete monitored build pass; all printed load-bearing
declarations report at most `[propext, Quot.sound]`.

This closes the norm-side limit needed to state a cutoff-removed centered
form inequality.  The reflected matrix quadratic is still open: its root
change produces two fixed-coefficient cross forms and one root-root form,
which must first be given constructive cutoff limits.  After that algebraic
frontier, the substantive obstruction remains a strict contraction rate
`q < 1` uniform in the base cutoff, volume, and spacing.  No completed or
continuum mass-gap conclusion is claimed here.

## Root-centered vacuum-sector reflected form is cutoff-Cauchy (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy` introduces the finite
bilinear form associated to two different coefficient vectors and proves a
cross-`l1` perturbation estimate under uniform entrywise kernel error.  The
existing pulled-entry modulus therefore gives a Bishop-real cutoff limit for
every fixed pair of base-sector coefficients.

Writing the root-centered vector as the original coefficient plus the moving
negative head correction times the root indicator exposes the reflected
quadratic as exactly four terms: the raw quadratic, the coefficient/root and
root/coefficient cross forms, and the root/root form.  Their fixed-coefficient
bilinear limits combine pointwise with the head-correction limit.  A final
pointwise-`Q'.eqv` recoding packages the literal physical centered reflected
values as a Bishop real.  The focused check and 1,469-job dependency build
pass; printed declarations report at most `[propext, Quot.sound]`.

Thus, for every fixed base cutoff and rational base-sector coefficient, the
exactly centered norm and reflected form both possess constructive cutoff
limits.  This removes the moving-centering convergence obstruction but does
not compare the two limits by a strict constant.  The next causal frontier is
an honest certificate interface for one `q < 1` that bounds the centered
reflected form by `q` times the centered diagonal uniformly in the base and
later representation cutoffs.  Constructing such a certificate remains an
open analytic problem; volume and spacing uniformity remain beyond it.

## Cofinal same-object strictness contracts to the centered form limits (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCenteredLimitGap` states the weakest direct
strictness input supported by the new same-object limits.  A single rational
`q` satisfies `0 <= q < 1`; for every base component and rational coefficient,
an explicit anchor function selects arbitrarily late representation cutoffs
where the literal moving centered reflected form is bounded in absolute value
by `q` times its literal moving centered diagonal.

The two Cauchy moduli prove that exact bounds on this constructively cofinal
family suffice.  A half-epsilon argument transports the selected finite bound
to all sufficiently late approximants and yields `CReal.leEv` between the
centered reflected-form limit and `q` times the centered diagonal limit.  The
focused and 1,470-job dependency-complete builds pass, and the theorem uses
exactly `[propext, Quot.sound]`.

No inhabitant of this certificate is asserted.  Its uniformity in the base
cutoff is precisely the analytic content missing from finite-prefix or
single-cutoff LDL computations.  The next implementation frontier is to
connect existing canonical full-carrier LDL/cofinal certificates to this
same-object interface by proving that the zero-extended head-centered sector
coefficient is centered on the full positive carrier.  Even an inhabited
fixed-nome certificate would still leave volume and spacing uniformity,
completion, and continuum QFT open.

## Vacuum-sector forms contract inside the full positive carrier (2026-08-22)

`BF4PhysicalCutoffVacuumSectorFullCarrierContraction` closes the exact carrier
seam between the growing canonical vacuum component and the finite rational
LDL layer.  The explicit arbitrary-coefficient extension is proved zero at
every full-carrier coordinate outside the later vacuum component.  Finite-list
restriction and permutation lemmas then show that its full indexed weighted
mean, diagonal quadratic, and matrix quadratic are exactly the already
constructed pulled sector forms.

Specializing to the moving head-centered coefficient proves exact weighted
mean zero on the whole positive carrier—not merely on the component-local
sum.  This is the centering hypothesis consumed by the canonical full-carrier
LDL certificate.  The monitored focused check and one-job 1,261-job
dependency-complete build pass, and all five printed load-bearing declarations
report exactly `[propext, Quot.sound]`.

This is an equality bridge, not an LDL family or a strict estimate.  The next
causal frontier is to compile an existing cofinal canonical head LDL family at
one supplied `q < 1` into the same-object vacuum-sector certificate and hence
the centered form-limit inequality.  Constructing such a cutoff-uniform LDL
family remains the substantive analytic input; completed-space, volume,
spacing, continuum-QFT, and Clay closure remain open.

## Canonical cofinal LDL families contract to centered sector limits (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge` composes the full-carrier
restriction with the canonical head-reduced LDL machinery.  Given one
ordinary or cleared-denominator canonical LDL family at a supplied rational
`0 <= q < 1`, it reindexes the family by `max base threshold`.  At each
selected cutoff, the zero-extended moving head-centered coefficient is a
valid full-carrier centered vector, so LDL soundness supplies the absolute
quadratic bound.  The exact full-carrier equalities transport it to the
literal pulled same-object forms.

The resulting inhabitant of
`FixedNomeCofinalVacuumSectorCenteredStrictGap` feeds the preceding Cauchy
theorem and proves `CReal.leEv` from the centered reflected-form limit to `q`
times the centered diagonal-form limit for every fixed base coefficient.
Both ordinary and shardable cleared routes are present.  The monitored
focused check and one-job 1,473-job dependency-complete build pass; all four
printed declarations use exactly `[propext, Quot.sound]`.

The implication is now complete, but its antecedent is still open: the
repository contains no inhabited cofinal canonical LDL family at any uniform
strict rate.  The next causal frontier is therefore analytical rather than a
carrier recoding seam: construct such a family, or replace it by a weaker
uniform certificate that proves the same finite bound.  Completed Hilbert
space, volume/spacing uniformity, continuum QFT, and the Clay theorem remain
open.

## Cofinal stationary rank-one row defects contract to the physical gap interfaces (2026-08-22)

`BF4PhysicalCutoffCofinalRankOneDefectGap` replaces the sufficient but strong
canonical-LDL antecedent by a smaller finite analytic target.  At a supplied
rational `0 <= q < 1`, compare the symmetric physical joint kernel with the
stationary rank-one joint `(1-q) d_i d_j` and require the absolute defect in
each row to be at most `q d_i`.  Exact weighted centering annihilates the
rank-one quadratic; the existing weighted Young perturbation estimate then
proves `|x^T K x| <= q x^T D x` without constructing an LDL factorization.

A constructively cofinal family of these row certificates now compiles both
to the global physical centered strict-gap interface and, after exact
zero-extension into the full carrier, to the moving same-object vacuum-sector
certificate.  Consequently it also proves the strict comparison of the two
fixed-nome centered cutoff-limit Bishop reals.  The monitored focused source
check and one-job 1,473-job dependency-complete target build pass; the seven
printed declarations use at most `[propext, Quot.sound]`.

No cofinal row-defect family is constructed here.  The open fixed-nome
analytic problem has been reduced from a growing canonical LDL factorization
to row-relative total variation against one stationary rank-one joint.  The
next causal frontier is to derive this certificate from the repository's
existing common-rank-one, density, core/tail, or minorization estimates.
Uniformity in physical volume and lattice spacing, continuum QFT, and the Clay
mass-gap theorem remain open.

## Literal physical centered rows contract to the same-object limit gap (2026-08-22)

`BF4PhysicalCutoffCofinalCenteredRowGap` aligns the cofinal gap interface with
the analytic quantity already produced throughout the BF4 density, buffer,
and local-gluing layers.  It compares the normalized reflected joint with the
full stationary product joint `d_i d_j`, independently of the requested
contraction rate.  A generic finite-index row transport proves that this
indexed row distance is exactly `physicalCenteredPhysicalRowMass` on the
literal positive carrier.

Exact centering annihilates the stationary-product quadratic, and the
weighted Young estimate turns a row bound at rate `q` into
`|x^T K x| <= q x^T D x`.  Thus one constructively cofinal family of the
repository's literal physical row estimates supplies both the global centered
strict-gap certificate and the moving same-object vacuum-sector cutoff-limit
inequality.  The focused monitored source check and one-job 1,474-job
dependency-complete build pass; all seven printed load-bearing declarations
use exactly `[propext, Quot.sound]`.

No cofinal physical centered-row family is constructed here.  This closes the
indexing and contraction seam from the established analytic target, but not
the target's cutoff-uniform inhabitant.  The next causal frontier is to compile
cofinal genuine local-slice/density/gluing data into this family.  Physical
volume and lattice-spacing uniformity, continuum QFT, and the Clay theorem
remain open.

## Cofinal genuine local slices contract to the same-object sixteenth gap (2026-08-22)

`BF4PhysicalCutoffCofinalLocalSliceGap` packages the geometric producer
immediately upstream of the literal centered-row interface.  At each selected
cutoff, one shared stationary one-step density has exact row and column
normalization, exact all-label density gluing to the physical slab, and a
centered one-step rate at most `1/4`.  Existing tensorization turns that local
quarter into the physical centered-row rate `1/16` for every source.

A constructively cofinal family of these genuine local slices now compiles to
the fixed-nome physical centered-row family, the global centered strict-gap
certificate, the moving same-object vacuum-sector certificate, and its
`CReal.leEv` cutoff-limit inequality.  The focused monitored source check and
one-job 1,475-job dependency-complete build pass.  An exact adapter also shows
that the pre-existing `FixedNomeCofinalLocalGluing` certificate directly
proves this same-object limit inequality; all six printed declarations use
exactly `[propext, Quot.sound]`.

No cofinal genuine local-slice family is constructed.  The remaining analytic
leaf is explicit: produce a stationary one-step density at arbitrarily large
representation cutoffs, prove its exact gluing identity, and bound its
centered row norm by `1/4`.  The next causal frontier is to connect the
repository's conditional-density or buffered-Perron witness packages to this
cofinal local-slice family, or identify the first still-uninhabited field.
Volume/spacing uniformity, continuum QFT, and the Clay theorem remain open.

## Local gluing alone closes the completed physical operator gap (2026-08-22)

`BF4PhysicalLocalGluingCompletedOperatorNormGap` removes an unnecessarily
strong dependency from the completed finite-scale BF4 gap.  A
`PhysicalLocalGluingAFCertificate` alone supplies the finite mean-zero
`1/16` Markov-form estimate.  Exact stagewise centering transports that
estimate through the constructive Cauchy completion to every vector in the
completed vacuum complement.

The existing positive Markov-form Cauchy--Schwarz theorem then upgrades this
completed form gap to the concrete squared-norm contraction
`||T v||^2 <= (1/16)^2 ||v||^2` for the completed physical Markov transfer at
every matched AF scale.  No physical separator, same-object correlation pin,
rate-sharpness witness, or dimensionful physical-length bound is used.

The monitored focused source check and one-job 1,232-job dependency-complete
build pass.  All five printed load-bearing declarations use exactly
`[propext, Quot.sound]`.

No inhabitant of `PhysicalLocalGluingAFCertificate` is constructed.  The
result is a direct finite matched-scale completion theorem, not a
thermodynamic, lattice-spacing, or continuum limit.  The separator data remain
relevant to the distinct dimensionful same-object correlation and mass-floor
interpretation.  The next causal frontier is to iterate this completed
operator estimate into transfer-power and same-object matrix-coefficient
decay, then connect an actually inhabited local-gluing producer to the
certificate and control the cross-scale physical limits.  Continuum QFT and
the Clay theorem remain open.

## The completed local-gluing gap yields geometric same-object decay (2026-08-22)

The direct local-gluing theorem now iterates the concrete completed physical
Markov transfer on its vacuum complement.  After `n` macro steps, the squared
norm is bounded by `((1/16)^2)^n` times the initial squared norm.  Completed
Cauchy--Schwarz then gives the corresponding squared matrix-coefficient bound
against every test vector on the same completed carrier, with same-vector
autocorrelation as an explicit specialization.

The monitored focused source check and one-job 1,232-job dependency-complete
build pass.  The three new printed declarations use exactly
`[propext, Quot.sound]`.

This is a genuine completed finite matched-scale decay theorem conditional on
`PhysicalLocalGluingAFCertificate`.  It does not construct that certificate,
identify transfer power with a dimensionful continuum-time correlation, or
provide volume/lattice-spacing uniformity.  The next causal frontier is to
audit the existing conditional-density, buffered-Perron, and local-gluing
producer packages field by field against `PhysicalLocalGluingAFCertificate`,
then implement the strongest honest inhabitance bridge or isolate its first
missing analytic leaf.  Continuum QFT and the Clay theorem remain open.

## Genuine one-step gluing rows contract directly to completed decay (2026-08-22)

`BF4PhysicalLocalGluingAFAdapter` now forgets the unused endpoint/Faraut
fields of `PhysicalBF4OneStepContractionGluingRow`.  A matched family of those
stronger rows therefore assembles constructively into one shared local slice
per scale and hence an inhabitant of `PhysicalLocalGluingAFCertificate`.
Neither a grouped Harnack profile nor endpoint estimates are required: the
minimal adapter retains only the AF coupling window, the local `q <= 1/4`
cap, the explicit shared kernel, and its genuine gluing rows.  A convenience
adapter also accepts the pre-existing boundary grouped-profile package.

`BF4PhysicalOneStepGluingCompletedGap` kernel-checks the entire causal
composition in named declarations.  The matched one-step rows give the
completed vacuum form gap at rate `1/16`, and therefore geometric decay of
the squared same-vector completed matrix coefficient at rate
`((1/16)^2)^n`.  The adapter's focused check and 1,127-job build pass; the
end-to-end file's focused check and 1,243-job build pass.  All eight newly
printed declarations use exactly `[propext, Quot.sound]`.

No `MatchedBF4OneStepGluingRows` inhabitant is constructed.  The first open
analytic leaf is now exact and finite at each matched scale: exhibit one
stationary slice kernel, prove weighted row and column normalization, prove
that its full power is the physical conditional density on every retained
source/target, and bound every centered row by `1/4` (with depth at least
three).  The direct `PhysicalLocalGluingAFCertificate` does not require the
stronger endpoint/Faraut estimates.  Uniform physical-time interpretation,
volume/lattice-spacing limits, continuum QFT, and the Clay theorem remain
open.

## Literal centered rows bypass local-root gluing and close completed decay (2026-08-22)

`BF4PhysicalLocalGluingAFCertificate` now factors its finite contraction
through the genuinely minimal row theorem: a `1/16` bound on every row of the
literal physical joint minus its stationary product joint directly contracts
all mean-zero physical quadratics.  Separately,
`BF4PhysicalLocalGluingCompletedOperatorNormGap` exposes a reusable finite-
quadratic-gap-to-completed-vacuum-gap interface, and
`BF4PhysicalCompletedOperatorNormGap` now contains the generic completed
power matrix-coefficient decay theorem.

`BF4PhysicalCenteredRowCompletedGap` packages only the AF coupling window and
that literal centered-row `1/16` field.  It discards the Harnack and
diagonal-order fields from the existing
`MatchedCrossZeroPhysicalSixteenthRows` package.  This minimal certificate
then contracts causally through the finite quadratic form, exact centering,
constructive Cauchy completion, concrete transfer norm
`||T v||^2 <= (1/16)^2 ||v||^2`, and squared same-vector power coefficient
decay `((1/16)^2)^n`.

The focused checks pass.  The generic dependency target passes a monitored
one-job 1,232-job build, and the row-to-completion target passes a monitored
one-job 1,233-job build.  All newly printed declarations use exactly
`[propext, Quot.sound]`.

No matched centered-row certificate is inhabited.  The analytic frontier is
now weaker than constructing a stationary local root: prove the literal
physical centered-row `1/16` estimate along the matched AF trajectory.  The
repository already exposes several sufficient producer interfaces—pointwise
conditional-density windows, support-safe core/tail windows, boundary-Gram
majorants, raw projective rows, and buffered/local-gluing rows—but no uniform
inhabitant was found.  Physical-time interpretation, volume/lattice-spacing
limits, continuum QFT, and the Clay theorem remain open.

## Support-safe core/tail windows contract to completed decay (2026-08-22)

`BF4PhysicalCoreTailCompletedGap` isolates the support-safe analytic leaf
upstream of the literal centered-row certificate at physical half-extent
zero.  The retained target core may depend on the AF scale and physical
source.  Its weighted density error is bounded by `1/32`, while both the
discarded stationary mass and discarded conditional row mass are bounded by
`1/64`.  This formulation permits fusion-zero channels and requires neither
strict positivity nor a full-support cross-ratio bound.

The new `PhysicalConditionalDensityCoreTailAFCertificate` retains only those
finite core/tail windows and the matched coupling window.  In particular it
forgets the calibrated Harnack and diagonal-order fields of the older matched
package.  The three budgets add to the literal physical centered-row rate
`1/16`, which then contracts through the previously verified finite quadratic
gap and constructive completion to the completed vacuum form gap, the
concrete transfer estimate `||T v||^2 <= (1/16)^2 ||v||^2`, and geometric
squared same-vector power decay `((1/16)^2)^n`.

Exact adapters accept the pre-existing matched core/tail rows and the deeper
buffered-Faraut rows when their explicit depth schedule is available.  The
focused monitored check and one-job 1,239-job dependency-complete build pass;
all seven printed declarations use exactly `[propext, Quot.sound]`.

No matched core/tail certificate is inhabited.  The first remaining analytic
leaf is now the sourcewise finite estimate itself: construct a retained core
and prove its `1/32` weighted error together with the two `1/64` tail budgets,
uniformly along the matched AF trajectory.  Physical-time interpretation,
volume/lattice-spacing limits, continuum QFT, and the Clay theorem remain
open.

## The support-safe leaf is executable, with an inhabited cutoff-zero base case (2026-08-22)

`BF4PhysicalCoreTailFiniteChecker` turns the remaining finite core/tail leaf
into exact computation.  Its generic row checker scans a finite carrier and
verifies weight and kernel nonnegativity, stationary normalization, the
`1/32` pointwise retained-core window, and the two `1/64` tail sums.  A second
checker scans every physical source at one cutoff.  Kernel-checked soundness
turns `check = true` into the exact `FiniteWeightedDensityCoreTailWindow` and
`PhysicalConditionalDensityCoreTailWindow` structures used downstream.

`PhysicalConditionalDensityCoreTailAFCheckedCertificate` now states the
uniform frontier as one true finite all-source Boolean scan per AF scale.  It
compiles to the minimal support-safe certificate, completed form-gap data,
and geometric completed same-vector decay.  The remaining scale quantifier is
not hidden: no all-scale family of true computations is asserted.

There is also a genuinely inhabited physical base case.  Lean's ordinary
kernel evaluator proves that the canonical cutoff `K = 0`, coupling `w = 1`,
half-extent-zero carrier passes the all-source check when its full carrier is
retained.  That computed fact yields every literal centered row at rate
`1/16`, the concrete finite mean-zero quadratic gap, the completed vacuum
form gap, and geometric squared same-vector completed transfer decay.  This
is a cutoff-zero theorem only, not evidence of cutoff uniformity.

The focused monitored check and one-job 1,240-job dependency-complete build
pass.  Every printed declaration is within the axiom gate: the closed
nonnegativity fact has no axioms and the others use exactly
`[propext, Quot.sound]`.  No `native_decide` or external numerical oracle is
used.

The next causal frontier is to obtain true checked values beyond the trivial
cutoff-zero carrier, preferably for an increasing cutoff prefix with the
source-dependent threshold core, and then replace any finite prefix by an
analytic all-scale proof.  Physical-time, volume/lattice-spacing,
thermodynamic and continuum limits, continuum QFT, and the Clay theorem
remain open.

## Exact carrier recoding removes the `2^24` cutoff-one ambient scan (2026-08-22)

A direct ordinary-kernel attempt to evaluate the full-core `K = 1`
all-source check was interrupted after two healthy minutes and is not counted
as a pass.  The obstruction is architectural: `centralHalfStates 1 0`
enumerates every binary labelling of 24 lower faces before positivity
filtering, and each source check contains further full carrier sums.

`BF4PhysicalCoreTailFiniteCarrierRecode` proves the exact compression seam.
A `PhysicalPositiveCarrierPresentation` supplies a finite code list, a decoder
whose mapped list is definitionally equal to the literal positive carrier,
and an on-carrier encoder/retraction.  A checked core/tail window on the code
list transports every weight, conditional-kernel, retained-core, and tail sum
to the literal physical carrier.  Consequently one compressed all-code scan
covers every physical source without evaluating the ambient `2^24` list.

`PhysicalCoreTailAFRecodeCheckedCertificate` packages one exact presentation
and one true compressed all-source check per matched AF scale, then contracts
them to the minimal support-safe certificate, completed vacuum form gap, and
geometric completed same-vector decay.  The focused check and monitored
one-job 1,241-job dependency-complete build pass; all seven printed
declarations use exactly `[propext, Quot.sound]`.

No nontrivial positive-carrier presentation is constructed.  In particular,
the repository's completed 128-surface forest-gauge calculation evaluates
signed Haar moments; its own closure explicitly does not identify those
moments with the separately normalized positive physical kernel.  The next
cutoff-one frontier is therefore an exact recoding theorem from the literal
positive half-state carrier to a small code list, followed by evaluation or
analytic control of the positive marginal and conditional kernel on that
list.  All-cutoff/AF uniformity, physical-time, volume/lattice-spacing,
continuum QFT, and the Clay theorem remain open.

## Cutoff-two reducibility rules out the full-carrier core/tail frontier (2026-08-22)

`BF4PhysicalCoreTailFullCarrierObstruction` connects the support-safe
core/tail compiler to the repository's exact cutoff-two reducibility mode.
If every retained cutoff-two source admitted the `1/32 + 1/64 + 1/64`
window, the existing row theorem would give an absolute centered form gap at
rate `1/16`.  The centered sector indicator is instead an eigenvalue-one mode
with strictly positive norm, so this conclusion contradicts the already
verified no-gap theorem.

Lean consequently proves, for every source-dependent core predicate, both
that the all-source window family is impossible and that the exact Boolean
all-row checker cannot return `true`.  The focused monitored check and a
combined one-worker 1,779-job dependency-complete build pass; both printed
declarations use exactly `[propext, Quot.sound]`.

This corrects the frontier recorded above: a compressed presentation of the
entire positive carrier cannot produce an all-cutoff strict gap, because the
target itself is false at cutoff two.  Carrier compression remains useful
only after selecting a communicating sector.  The next causal frontier is a
row certificate on the canonical vacuum component, followed by a cofinal
same-object limit estimate.  Thermodynamic/continuum construction and the
Clay theorem remain open.

## Sector-local rows contract to the cofinal same-object limit gap (2026-08-22)

`BF4PhysicalVacuumSectorCofinalRowGap` replaces the obstructed full-carrier
comparison by the canonical vacuum communicating component.  On an arbitrary
finite index list, it proves that exact restricted-weight centering
annihilates the corresponding stationary-product quadratic.  A symmetric
row-distance bound from the physical joint to that product therefore gives
the absolute centered quadratic contraction by the existing weighted Young
estimate.  The restricted physical weights need not be renormalized for this
argument.

`FixedNomeCofinalVacuumSectorRowDistance` asks for that row estimate only on
the canonical vacuum-sector indices at one constructively cofinal cutoff for
each base cutoff and Cauchy threshold.  It compiles directly to
`FixedNomeCofinalVacuumSectorCenteredStrictGap`: exact head centering places
the moving coefficient in the later sector's vacuum complement, and the
verified form-pushforward identities identify its finite matrix and diagonal
forms with the same-object pulled forms.  The existing CReal theorem then
preserves the same strict rate in the two cutoff limits.

The focused monitored check and the combined one-worker 1,779-job
dependency-complete build pass.  All six printed declarations use exactly
`[propext, Quot.sound]`.  No cofinal row-distance family is inhabited;
the new interface is the corrected analytic frontier after the reducibility
obstruction.  Uniform construction of those sector-local rows, followed by
physical-time, thermodynamic, lattice-spacing, and continuum control, remains
open, as does the Clay theorem.

## The cutoff-two canonical vacuum gap is normalized physical data (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap` transports the
exact 65-state cutoff-two calculation from the raw production table to the
normalized reflected physical joint.  Exact row closure makes the filtered
full half-state marginal a permutation of the canonical vacuum-sector row
sum, including zero contributions outside the sector.  Multiplication by the
positive reciprocal of the physical partition function scales the joint
quadratic form, diagonal norm, and mean-zero equation by the same factor.

The resulting theorem identifies the 65 states with the canonical vacuum
support and proves the normalized physical absolute centered contraction at
rate `49/50`.  Thus cutoff two now supplies a genuine nontrivial physical
sector base case rather than only an unnormalized table certificate.

The focused monitored check and one-worker 4,684-job dependency-complete
build pass.  The four printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  This result is only at
cutoff two.  Exact transport to the canonical cofinal finite-index/form
coordinates, a uniform all-cutoff sector estimate, physical-time and
thermodynamic/continuum control, continuum QFT, and the Clay theorem remain
open.

## Cutoff-two gap reaches the canonical finite vacuum-sector forms (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap` removes the table
coordinate seam.  It first proves that finite state lookup is injective on
every canonical vacuum component and hence that the cutoff-two canonical
state list is a literal permutation of the certified 65-state list.  Exact
single- and double-sum transport then identifies the table weighted mean,
diagonal norm, and normalized reflected matrix form with the standard
canonical finite-sector forms.

The bridge initially applies to literal state observables.  A constructive
finite code observable then encodes any arbitrary coefficient on the
canonical index list; code faithfulness and duplicate-freeness prove exact
recovery at every sector index.  Therefore every exactly centered canonical
cutoff-two coefficient satisfies the normalized physical absolute form gap
at rate `49/50` in precisely the form language consumed by the cutoff-limit
modules.

The focused monitored check and one-worker 4,717-job dependency-complete
build pass.  All seven printed declarations use exactly
`[propext, Quot.sound]`; there is one benign unused-`simp`-argument linter
warning.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This closes the finite cutoff-two
coordinate bridge only.  The causal frontier is now to propagate a strict
sector estimate uniformly to later/cofinal cutoffs; physical-time,
thermodynamic and continuum control, continuum QFT, and the Clay theorem
remain open.

## Cutoff two inhabits the moving pulled centered-gap expression (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledVacuumGap` connects the canonical finite
theorem to the exact expression used by the cofinal same-object certificate.
At `base = later = 2`, the explicit cutoff index map represents the same
literal state, so pulled weights and normalized reflected-kernel entries are
exactly the canonical cutoff-two entries.  The corresponding weighted mean,
diagonal, and matrix forms agree term by term.

Applying the previously verified arbitrary-coefficient theorem to the
root-centered coefficient therefore proves the `49/50` absolute gap for the
moving pulled forms at this first nontrivial anchor.  This is an inhabited
finite point of the eventual `centeredGap` field, not an inhabitant of the
cofinal structure itself.

The focused monitored check and one-worker 4,721-job dependency-complete
build pass.  All four printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The next causal
frontier is a uniform persistence estimate from this anchor to arbitrarily
late/cofinal cutoffs.  Physical-time, thermodynamic and continuum control,
continuum QFT, and the Clay theorem remain open.

## Cutoff-two gap persistence is reduced to two explicit comparisons (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledGapPersistence` isolates a sufficient
non-tautological bridge from the exact cutoff-two anchor to later pulled
forms.  For every later moving-centered coefficient, the certificate supplies
a coefficient exactly centered at cutoff two, bounds the later absolute
matrix form by the cutoff-two matrix form plus `epsilon` times the later
diagonal, and bounds the cutoff-two diagonal by the later diagonal.  The
verified cutoff-two theorem then contracts these data to the later rate
`49/50 + epsilon`.

One uniform `epsilon` and a constructively cofinal family of those comparison
certificates, with `49/50 + epsilon < 1`, now imply a strict comparison of the
existing moving centered matrix and diagonal Bishop-real limits on the fixed
cutoff-two 65-dimensional vacuum sector.  Compact aliases for those `CReal`
sequences keep the physical content exact while avoiding repeated elaboration
of the full finite forms.

The focused monitored check and one-worker 4,729-job dependency-complete
build pass.  All three printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  No cofinal comparison
family is constructed here.  The next causal frontier is to derive its two
comparison fields from quantitative cutoff stability (including the
recentring correction and diagonal control).  Extension beyond the fixed
cutoff-two sector, physical-time, thermodynamic/continuum control, continuum
QFT, and the Clay theorem remain open.

The same module now also records the weaker robust interface that the limit
argument actually needs.  Exact diagonal domination is replaced by a
nonnegative inflation factor `cD`, matrix perturbation by `eM`, and the
resulting rate is exactly `(49/50) * cD + eM`.  The cofinal stage may depend on
the fixed coefficient while both error budgets and the final rate remain
uniform.  This is sufficient because `CReal.leEv` fixes the coefficient
before requesting a Cauchy stage.  The refined focused check and one-worker
4,729-job build pass; both additional printed declarations again use exactly
`[propext, Quot.sound]`.

This refinement removes two unnecessary analytic obligations, but does not
construct the remaining comparison estimates.  Moreover, cutoff-Cauchy
convergence alone controls pairs of sufficiently late cutoffs; it does not
bound the total change from cutoff two.  The next estimate must therefore
control that total perturbation (or propagate the gap incrementally) tightly
enough that `(49/50) * cD + eM < 1`.

## Pulled entrywise errors now coerce to the physical diagonal norm (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl` proves a finite-list
Cauchy--Schwarz inequality in the repository's exact rational `coefficientL1`
normalization.  Any nonnegative pointwise weight floor then yields the cleared
coercivity estimate

`floor * ||x||_1^2 <= |states| * diagonal(x)`.

For the physical specialization, the anchor is chosen as the maximum of
cutoff two and the already verified uniform row-floor cutoff.  Positivity of
the moving finite minimum and positive-row persistence put one explicit
strictly positive rational floor below every pulled weight in the canonical
cutoff-two vacuum component at every later cutoff.  The generic inequality
therefore gives the required physical `l1`-square-to-diagonal conversion for
arbitrary coefficients on that fixed component.

The focused monitored check and one-worker 4,730-job dependency-complete
build pass.  All four printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  This is an actual norm
coercivity theorem, but it supplies neither the needed total cutoff-two-to-
limit entry error nor the moving recentering comparison.  Those estimates,
followed by the robust rate budget, remain the next frontier; completed-space,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## The BF4 root-sector cylinder union has a concrete injective completion (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletion` forms the union of all
finite canonical root-sector cylinder presentations at fixed nome and finite
half-extent, equips it with the squared seminorm inherited from the existing
cutoff-removed physical GNS form, and applies the explicit-modulus constructive
Cauchy completion.  Termwise cylinder realization sends every sector Cauchy
representative to a global physical Cauchy representative.

The descended map into the existing global physical completion is proved
injective: global closeness of two mapped representatives reflects verbatim
to sector closeness.  On every dense sector constant, the actual global
completed inner product is the quotient class of the already constructed
pulled-sector diagonal Bishop real.  The focused monitored check and
exact-target one-worker 1,263-job build pass.  All four audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  This does not
prove that the image is all of the global vacuum complement, that the global
transfer preserves it, or that one strict rate works over all carriers.
Those completion-invariance and uniform-analytic steps, followed by the
thermodynamic/continuum construction, remain open.

## BF4 completed root-sector invariance is isolated as an exact lift (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderTransferLift` pulls the global completed
inner product and global-vacuum-orthogonality predicate back along the new
injective sector embedding.  It then states the exact remaining invariance
datum: a map on the sector completion whose image under the embedding equals
the already constructed concrete adaptive global Markov transfer.

Any such lift is proved unique by injectivity.  It automatically preserves
the global-vacuum-orthogonal part of the sector, and its completed transfer
pairing is exactly the global concrete transfer pairing restricted to the
sector image.  The focused monitored check and exact-target one-worker
1,357-job build pass.  All three audited theorems use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The lift record is
deliberately uninhabited: constructing it requires a cofinal schedule on which
the adaptive cutoff action preserves finite root-sector support.  The common
all-carrier strict rate and thermodynamic/continuum construction also remain
open.

## Every fixed pulled BF4 carrier has normalized mass (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledMass` proves for arbitrary nome, base
cutoff, half-extent, and later cutoff that the stationary mass retained on the
fixed base vacuum component is strictly positive.  The persistent vacuum root
supplies the positive summand.  Whenever the base embeds into the later
carrier, the same mass is at most one: the index embedding is injective and
the complete later positive-row stationary law has exact total mass one.

The focused monitored check and exact-target one-worker 4,752-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`.  These bounds remove
mass as a separate base-dependent hypothesis in the pending Poincare
contraction.  The edge-floor/path-ceiling ratio may still deteriorate as the
base expands; no cofinal uniform rate, completed gap, thermodynamic/continuum
QFT, or Clay theorem is asserted.

## Every fixed pulled BF4 energy reaches the moving deficit (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding` maps the Cartesian
square of an arbitrary fixed base vacuum component injectively into the
Cartesian square of every later component.  Exact coefficient-extension and
kernel recodings identify all old-old summands, while nonnegativity permits
the remaining later summands to be discarded.  The pulled old-block
Dirichlet energy is therefore bounded by the full later zero-extension
energy.

The finite stationary/symmetric Dirichlet identity and the exact moving
head-centering form recodings then bound this energy by twice the actual
pulled diagonal-minus-matrix deficit.  The focused monitored check and
exact-target one-worker 4,751-job build pass.  Both audited declarations use
exactly `[propext, Quot.sound]`.  This construction is uniform in the later
cutoff for each fixed base, but it does not compare constants across bases;
the cofinal uniform rate, completion, thermodynamic/continuum QFT, and Clay
theorem remain open.

## Entrywise pulled errors compile to relative physical form errors (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation` consumes the positive
floor coercivity instead of postulating form comparisons.  A uniform
entrywise error `eta` between two pulled normalized kernels gives the cleared
bound

`floor * |M_first(x) - M_later(x)| <= |states| * eta * D_later(x)`.

Likewise, a uniform entrywise pulled-weight error gives

`floor * |D_first(x) - D_later(x)| <= eta * D_later(x)`.

Exact rational budget inequalities against the positive floor cancel that
floor constructively.  The first estimate becomes the robust `matrixError`
term; the second becomes both a relative diagonal error and the multiplicative
inflation `D_first(x) <= (1 + diagonalError) D_later(x)`.

The focused monitored check and one-worker 4,731-job dependency-complete
build pass.  All four printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  These theorems compare
the same coefficient at two cutoffs.  The moving root-centered coefficients
differ, so their recentering perturbation and a strict total entry-error
budget from the finite anchor remain open.  The completed-space and physical
thermodynamic/continuum frontiers, continuum QFT, and the Clay theorem remain
open.

## Moving cutoff-two recentering is exactly root-supported (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation` now subtracts the
two exact root-shift descriptions of a fixed raw coefficient centered at two
different representation cutoffs.  The difference is precisely the change
of the scalar head correction times the distinguished root indicator.  On
the fixed cutoff-two carrier its coefficient `l1` norm is therefore exactly
the absolute scalar correction change, with no carrier-cardinality loss.

The existing constructive Cauchy modulus for the head-correction sequence
then gives a cofinal `l1` Cauchy modulus for the moving centered coefficient.
The focused monitored check and the exact-target one-worker 4,732-job build
pass, and all three printed declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  A broader default
workspace build was separately stopped by the safety monitor at job
2,116/3,696 when memory reached its 12 GiB reserve; that interrupted audit is
not counted as a pass and reported no Lean error before termination.

This closes the root-support and coefficient-norm seam only.  The next causal
step is to turn that `l1` perturbation into matrix and diagonal perturbations
under one fixed later pulled law, and then combine it with entrywise law
errors.  A strict total cutoff-two-to-limit budget, a cofinal robust
persistence family, the completed spectral gap, thermodynamic/continuum QFT,
and the Clay theorem remain open.

## Same-law moving recentering has explicit matrix and diagonal errors (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering` puts the matrix and
diagonal forms onto one common finite quadratic interface.  A generic
bilinear estimate proves that a law with entries of absolute value at most
one sends a scalar basis-vector perturbation to the exact three-term `l1`
bound (two cross terms and one quadratic term).  The normalized physical
pulled kernel has that entry cap because every nonnegative entry lies below
its row marginal, and the row marginal is at most one.  The pulled diagonal
law has the same cap because every retained pulled weight lies in `[0,1]`.

The exact root-only coefficient identity therefore yields explicit absolute
same-law perturbation bounds for both the later pulled matrix and later pulled
diagonal.  Their small parameter is precisely the absolute head-correction
change; no factor 65 is introduced into that parameter.  The focused
monitored check and exact-target one-worker 4,733-job build pass.  All six
printed load-bearing declarations use only `[propext]` or
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.

These estimates are absolute and retain finite coefficient-`l1` factors.
They are not yet a relative uniform error against the later diagonal.  The
next causal step is a coefficientwise dichotomy: the root-only raw mode
centers to zero identically, while any non-root coefficient supplies a
positive later-diagonal witness against which the head-correction Cauchy
modulus can be chosen.  That relative recentering estimate must then be
combined with entrywise law errors.  A strict total cutoff-two-to-limit
budget, robust cofinal persistence, the completed spectral gap,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## Moving recentering is relatively stable in the cutoff tail (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering` closes the
coefficientwise relative version of the same-law recentering estimate.  A
constructive finite dichotomy says that every raw cutoff-two coefficient is
either supported only at the distinguished root or has a non-root coordinate
of positive absolute value.  Root-supported coefficients are annihilated
exactly by moving root centering.  In the other branch, the unchanged
non-root coordinate gives a cutoff-independent positive lower bound for the
later centered `l1` norm.  The head-correction Cauchy modulus can therefore
make the moving root shift an arbitrarily small multiple of that norm.

Combining this coefficient estimate with the verified same-law quadratic
bounds and positive physical diagonal floor gives, for every coefficient and
every positive requested relative error, one cutoff after which both the
matrix and diagonal recentering errors are bounded by that error times the
later diagonal.  The rational amplification budget and its positive error
fraction are explicit constructions rather than hypotheses.

The focused monitored check and exact-target one-worker 4,734-job build pass.
All printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is a late-pair theorem: it does
not bound the change from cutoff two to the tail.  The next causal step is to
combine it with entrywise cutoff-law Cauchy estimates into full moving-form
tail stability.  The finite cutoff-two-to-tail or summable-increment bridge,
robust persistence from the cutoff-two gap anchor, completed spectral gap,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## The complete moving physical forms are relatively stable in the tail (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability` combines the two
independent moving pieces that had remained separate.  The corrected-slab
modulus is first packaged into coefficient-independent entry certificates
for both the pulled normalized kernel and pulled weights.  Explicit positive
rational tolerances make those entries fit arbitrary relative matrix and
diagonal law-error budgets through the verified physical row floor.

At a late pair, the uniform law certificate is instantiated at the
coefficient centered at the first cutoff.  The relative same-law recentering
theorem then compares that coefficient with the coefficient centered at the
later cutoff.  Its diagonal estimate gives exactly the norm-inflation factor
`1 + recenteringError`, so the composed matrix error is

`matrixLawError * (1 + recenteringError) + recenteringError`,

and the diagonal error has the analogous formula.  An explicit component
choice `relativeError / (relativeError + 2)` proves constructively that every
positive requested total relative error is attained for both actual moving
forms on all sufficiently late cutoff pairs.

The focused monitored check and exact-target one-worker 4,735-job build pass.
All eight printed load-bearing declarations use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  This completes the
different-law-plus-recentering tail stability seam.  It remains a tail
Cauchy theorem, not a bound on the finite change from the verified cutoff-two
`49/50` anchor to the tail.  A finite-prefix certificate or a summable
increment estimate with a strict remaining rate budget is now the next
frontier.  Robust anchor-to-limit persistence, the completed spectral gap,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## One aligned finite tail seed now suffices for the cutoff-two CReal gap (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge` isolates the exact
finite datum still missing after full tail stability.  The fixed tail error
is `1/200`.  A `CutoffTwoPulledTailSeedGapAt coefficient` records one cutoff
which is both a start for that verified moving-form stability estimate and a
finite strict-gap seed at the cutoff-two anchor rate `49/50`.

From this one aligned seed, the diagonal error gives the inflation
`1 + 1/200`, the matrix error contributes the remaining `1/200`, and every
later cutoff satisfies the explicit rate

`(49/50) * (1 + 1/200) + 1/200 = 9899/10000 < 1`.

The theorem then contracts this cofinal finite bound through the existing
moving matrix and diagonal Cauchy moduli to a same-object Bishop-real form
gap at `9899/10000`.  A coefficientwise family of such seeds supplies that
same uniform CReal rate for the entire fixed cutoff-two physical vacuum
carrier.  Separately, the stability half of the certificate is proved to
exist for every coefficient; the uninhabited analytic field is the finite
`49/50` seed gap aligned with one such tail start.

The focused monitored check and exact-target one-worker 4,736-job build pass.
All four printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Two initially slow narrow checks were
stopped without being counted as passes; compact aliases removed the costly
Bishop-real unfolding and the final checks pass.  The coefficientwise seed
family is not yet inhabited.  Extending from the cutoff-two component to all
finite base carriers, the completed Hilbert gap, thermodynamic/continuum QFT,
and the Clay theorem remain open.

## The cutoff-two-to-tail obstruction is now an explicit finite recurrence (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge` expands the last
fixed-carrier obstruction into consecutive physical moving-form increments.
Starting at the verified cutoff-two rate `q(0) = 49/50`, a step with common
relative matrix/diagonal error `eta(n)` forces exactly

`q(n+1) = q(n) * (1 + eta(n)) + eta(n)`.

`CutoffTwoPulledFinitePrefixIncrementControl.abs_gap_at_stage` proves by
finite induction that certified steps propagate the gap to every prefix
stage.  `CutoffTwoPulledFinitePrefixToTailGap` then requires the prefix
endpoint to be a `1/200` moving-form stability start and checks the explicit
final rate is still below one.  From those fields, every later cutoff and the
literal same-object matrix/diagonal Bishop reals satisfy that computed strict
rate.

While the propagated rate remains at most one, the nonlinear recurrence has
the closed additive envelope

`q(n) <= 49/50 + 2 * sum_{j<n} eta(j)`.

A uniform rational partial-sum estimate therefore discharges the strict
final-rate field without normalizing a potentially enormous recurrence.  An
attempted executable evaluation of the existing uniform-row-floor cutoff
exhausted the interpreter recursion stack after more than eighty thousand
nested cutoff-power calls.  That failed diagnostic is not a proof result, but
it shows why a summable or telescoping increment theorem, rather than a small
manual table, is the viable route.

The certificate keeps the cutoff-two alias-form anchor as an explicit field
to prevent Lean from repeatedly unfolding the very large Bishop-real
recoding.  Its mathematical content is already the proved cutoff-two
physical gap; the genuinely open fields are the finitely many consecutive
increment bounds, their alignment with a tail start, and the remaining-slack
inequality.  One slow narrow check that attempted the giant definitional
unfolding was stopped and is not counted as a pass.

The optimized focused check and exact-target one-worker 4,737-job build pass.
The six printed declarations use only `[propext]` or
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The finite-prefix
certificate is not inhabited.  All-base carrier control, the completed
Hilbert gap, thermodynamic/continuum QFT, and the Clay theorem remain open.

## Every finite BF4 prefix increment now has a constructive control (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence` proves
that the individual consecutive relative errors are not an additional
qualitative analytic hypothesis.  A data-bearing finite scan returns either
a proof that the coefficient is root-supported or an explicit non-root
coordinate of positive magnitude; unlike the earlier propositional
dichotomy, this witness is retained in `Type` and can construct downstream
certificate data without choice.

In the root-supported branch, moving head centering annihilates both forms
exactly and every prefix error is zero.  In the non-root branch, the selected
coordinate is unchanged by moving centering.  Its cutoff-two physical row is
positive and positive-row persistence keeps its pulled weight strictly
positive at every later cutoff.  Its square-weight summand therefore makes
the moving diagonal strictly positive.  The explicit error

`eta(n) = (|M_n-M_(n+1)| + |D_n-D_(n+1)|) / D_(n+1)`

simultaneously bounds the matrix and diagonal increments.  Consequently,
`finitePrefixIncrementControlForEveryCoefficient` constructs every field of
the finite prefix increment certificate for every coefficient and length,
apart from a named exact `CutoffTwoActualMovingFormRecode`.  That structure
records only the definitional identification of the compact Bishop-real
approximant aliases with the displayed physical forms.  Direct unfolding of
that recoding exceeded a 500,000-heartbeat diagnostic, so the equality is
kept explicit rather than hidden or claimed checked.

The focused monitored check and exact-target one-worker 4,738-job build pass.
All seven printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Two earlier monitored checks were
interrupted while diagnosing unresolved namespaces and are not counted as
passes; the later short checks exposed and fixed those names.  The remaining
analytic obstruction is quantitative: align a finite endpoint with the
proved tail and show that the finite sum of the constructed errors retains
strict rate slack.  No unconditional fixed-carrier limit gap, completed
spectral gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## A `1/200` total BF4 prefix error is sufficient (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure` eliminates the
remaining recursive rate arithmetic.  If every partial sum of the
constructed relative prefix errors is at most `1/200`, then the prefix
envelope is at most

`49/50 + 2 * (1/200) = 99/100`.

Composing that envelope with the independent `1/200` moving-form tail error
gives the exact strict upper rate

`(99/100) * (1 + 1/200) + 1/200 = 19999/20000 < 1`.

The new `CutoffTwoPulledFinitePrefixSumClosure` carries precisely the exact
compact-form recode, a tail-aligned finite endpoint, the proved tail
stability at that endpoint, and the one partial-sum budget.  It constructs
the complete prefix-to-tail certificate and contracts to the literal
same-object moving matrix/diagonal Bishop-real gap.  Individual step controls
and recursive-rate inequalities are no longer open fields.

The focused monitored check and exact-target one-worker 4,739-job build pass.
The two exact rational slack theorems are axiom-free; the other three printed
declarations use exactly `[propext, Quot.sound]`.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The closure structure is not inhabited: the exact recode, tail
alignment as data, and especially the `1/200` finite total-variation estimate
remain open.  No unconditional fixed-carrier CReal gap, completed spectral
gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## Every finite prefix of BF4 carriers has one constructed common gap (2026-08-22)

`BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap` takes the located
`Q'.runningMax` of the constructed rates for bases `0, ..., bound`.  Induction
on the finite bound proves that this maximum remains strictly below one, while
located-max monotonicity bounds every earlier base rate.  The resulting
`fixedCarrierPrefixConstructedUniformGapData` supplies one common rate for all
later moving forms and all same-object Bishop-real cutoff limits in that finite
carrier prefix.

The first focused check was deliberately interrupted after a recursively
referenced package caused prolonged elaboration; it was not counted as
validation.  Factoring the moving and cutoff-limit estimates into named
theorems removed that path.  The subsequent focused monitored check and
exact-target one-worker 4,758-job build pass, and all four audited exports use
exactly `[propext, Quot.sound]`.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.

This is finite compactness only.  It does not show that the prefix maxima stay
below one by a common margin as `bound` grows.  That uniform-tail estimate,
vacuum-sector density/completion, thermodynamic/continuum QFT, and the Clay
theorem remain open.

## The BF4 uniform-rate frontier is denominator-cleared (2026-08-22)

`BF4PhysicalCutoffVacuumSectorUniformFloorPathRate` rewrites the remaining
cross-carrier problem entirely in terms of the constructed finite constants.
For a supplied common `q < 1`, it asks at every base for the rational inequality

`pathCeiling <= q * (pathCeiling + edgeFloor)`.

Positive-denominator division proves this is exactly an upper bound on the
constructed rate `pathCeiling / (pathCeiling + edgeFloor)`.  The module then
compiles those inequalities through the cross-carrier certificate, the cofinal
moving-centered vacuum-sector gap, and the same-object Bishop-real limit.
`FixedBaseConstructedUniformGapData` now also records the exact equality between
its sealed rate and that displayed quotient, allowing the compilers to compose
without unfolding the finite minimum.

The focused monitored checks and exact-target one-worker 4,757-job build pass.
All four new audited exports and the updated constructed package use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The all-base rational
inequality remains unproved; this is now the concrete quantitative frontier.
A distinct vacuum-sector density/completion bridge, thermodynamic/continuum
QFT, and the Clay theorem remain open.

## The BF4 cross-carrier rate bottleneck is an exact certificate (2026-08-22)

`BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge` isolates the
strictly stronger datum not supplied by the fixed-carrier theorems: one
rational `q` with `0 <= q < 1` that bounds every constructed base rate.  From
that single field it selects, for each base and Cauchy threshold, a cutoff
beyond the constructed tail start, enlarges the base-rate estimate using
nonnegativity of the diagonal form, and constructs the existing
`FixedNomeCofinalVacuumSectorCenteredStrictGap` certificate.  The same common
rate then controls every corresponding Bishop-real cutoff limit.

The focused monitored check and exact-target one-worker 4,756-job build pass.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No inhabitant of the cross-carrier rate
bound is claimed.  The next analytic task is to derive it from a uniform
floor-to-path-ceiling estimate (or a sharper sector comparison), after which a
separate vacuum-sector density/completion bridge is still required.  No
completed-space gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## Any strict late finite BF4 gap now preserves its own slack (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge` removes the
artificial requirement that the moving cutoff sequence remain within a fixed
`1/200` total error of the cutoff-two `49/50` anchor.  Given any rational
finite-seed rate `0 <= q < 1`, it chooses the explicit moving-form tail error

`epsilon(q) = (1/4) * (1 - q)`

and proves constructively that the propagated rate

`qAdaptive = q * (1 + epsilon(q)) + epsilon(q)`

is still strictly below one.  The proof uses `q * epsilon <= epsilon`, hence
`qAdaptive <= q + 2*epsilon = q + (1/2)*(1-q) < 1`.  The existing full
moving-form tail theorem constructs a stability start for this exact positive
error.  If that same finite cutoff carries a gap at rate `q`, every later
cutoff and the literal same-object moving matrix/diagonal Bishop-real limits
inherit the strict rate `qAdaptive`.  A coefficientwise family with one common
`q` gives a uniform fixed-carrier CReal form gap.

This changes the causal frontier.  The `1/200` finite-prefix sum closure
remains a valid sufficient route, but it is no longer necessary.  The direct
route now asks only for one common strict finite gap on the canonical vacuum
sector at coefficient-dependent cutoffs already lying in their certified
tails.  Constructing that finite-sector gap is the genuine next analytic
problem; no small comparison with cutoff two is assumed.

The focused monitored check and exact-target one-worker 4,737-job build pass.
All eight printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  One initial full-module check hit a
stack overflow while elaborating compact aliases in the displayed existence
statement; spelling that theorem with the underlying physical forms removed
the reduction and the subsequent check passed.  The adaptive seed family is
not inhabited.  No unconditional fixed-carrier gap, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## The finite BF4 Markov action closes on the canonical vacuum sector (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderFiniteAction` proves the finite support
ingredient required by the completed-sector transfer lift.  Raw reflected-
kernel row closure, together with exact kernel symmetry, first shows that the
physical conditional kernel cannot carry a source outside the canonical root
component into that component.  Hence a sector-cylinder presentation whose
base is at most the action cutoff has a genuine Markov image which vanishes at
every retained state outside the current root component.

The image values on the current component define an explicit sampled
coefficient and a new presentation at the action cutoff.  Equal-cutoff index
maps are proved to be identities on the component; zero extension of the
sampled coefficient therefore agrees with the Markov image on the entire
positive carrier.  The resulting finite-linear cylinder realization has
exactly those values.  This is an actual support-preserving finite action, not
an assumed invariant-subspace certificate.

The focused monitored check and exact-target one-worker 1,264-job build pass.
The three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Earlier focused attempts exposed a
missing namespace and an elaboration-heavy projection route and are not
counted as validation.  The next frontier is to choose action cutoffs
cofinally along every sector Cauchy representative and prove the recoded
outputs are Cauchy and completion-close, thereby inhabiting the existing
completed transfer-lift interface.  One all-carrier strict rate, completed
uniform gap, thermodynamic/continuum QFT, and the Clay theorem remain open.

## Every BF4 sector Cauchy class has a base-controlled representative (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy` removes the
remaining finite-support scheduling mismatch.  A slow diagonal pays the base
cutoff of each selected presentation.  It uses the literal zero presentation
before the zeroth requirement is affordable and thereafter follows a cofinal
subsequence of the original sector Cauchy representative.  The resulting
representative is constructively Cauchy, explicitly close to the original,
and satisfies `presentation.base <= stage` at every sequence stage.

The existing global adaptive Markov selector is also proved never to exceed
its action stage.  Applying it to the base-controlled representative therefore
gives

`base(selected presentation) <= selected index <= action cutoff`.

Thus the finite root-sector support and recoding theorem applies at every
adaptive stage, and the sampled action has an exact current-carrier cylinder
realization.  No new cofinality certificate is assumed.

The focused monitored check and exact-target one-worker 1,348-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The remaining completed-lift frontier
is now specifically a tail estimate: prove that the sequence of these finite
sector recodings is Cauchy in the inherited limiting seminorm and is
completion-close to the already constructed global adaptive output.  One
all-carrier strict rate, completed uniform gap, thermodynamic/continuum QFT,
and the Clay theorem remain open.

## Finite BF4 vacuum-sector vectors are realized in the dense GNS carrier (2026-08-22)

`BF4PhysicalCutoffVacuumSectorLinearRealization` constructs a globally bounded
state-cylinder indicator for every state of an arbitrary fixed canonical
vacuum component.  Finite rational linear combinations of those indicators
are literal `CentralPhysicalLinearObservable` terms, rather than external
coefficient tables.  On every later positive carrier, finite coordinate
agreement is proved equivalent to the explicit old-to-new cutoff index map.
Therefore evaluation of the one fixed cylinder combination is exactly the
previously constructed vacuum-sector coefficient extension by zero.

The pointwise identity contracts further to exact equalities between the
observable's physical weighted norm and pulled sector diagonal quadratic, and
between its physical transfer quadratic and pulled sector matrix quadratic,
at every later cutoff.  An initial focused check was interrupted after an
overly generous heartbeat bound concealed ordinary namespace errors and is
not validation.  With a bounded heartbeat budget, the corrected focused check
and exact-target one-worker 1,262-job build pass.  All four audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  This proves
dense-carrier realization, not density of these cylinders in a completed
vacuum sector.  A uniform all-carrier rate, sector-completion closure,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## Every actual cutoff-two moving approximant has a strict finite gap (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledPoincareGap` transports the new finite
Poincare theorem to the literal approximants of the cutoff-two same-object
moving Bishop reals.  At every representation cutoff at least two, the moving
head-centered coefficient extends by zero to the full finite vacuum sector;
that extension has exactly zero weighted mean, and its full matrix and
diagonal forms are exactly the pulled cutoff-two forms.  Consequently, for
every coefficient,

`abs(actualMovingMatrix cutoff) <= q(cutoff) * actualMovingDiagonal cutoff`,

where `q(cutoff)` is coefficient-independent and satisfies
`0 <= q(cutoff) < 1`.

Two definitional projection lemmas were added to the centered matrix and
diagonal CReal constructions so this exact physical recoding seam can be used
without forcing Lean to unfold the full Cauchy and BF4 kernel expressions at
once.  The initial giant-reduction proof exhausted the elaboration stack; the
named seams independently check and the revised bridge checks cleanly.

The focused monitored checks pass, and the dependency-complete exact-target
one-worker 4,747-job build passes.  All three audited bridge declarations use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  This removes
finite strict-gap existence from the same-object frontier, but the displayed
rate still depends on cutoff.  No common tail rate, completed-space gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## Every fixed finite BF4 vacuum sector has an explicit strict form gap (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPoincareGap` eliminates the pairwise variance
between its exact centered identity and path bound, cancelling only the
explicitly positive doubled sector mass.  It proves the finite Poincare
inequality
`edgeFloor * diagonal <= sectorMass * pathCeiling * (diagonal - matrix)`.

With `A = sectorMass * pathCeiling`, the module defines the concrete rational
rate `q = A / (A + edgeFloor)`, proves `0 <= q < 1`, and derives
`abs(matrix) <= q * diagonal` for every exactly centered coefficient on every
fixed finite canonical sector.  Gram positivity supplies the absolute-value
step.  The rate is uniform over all coefficients at that fixed cutoff; it may
depend on the cutoff and is not asserted uniform along the continuum route.

The focused monitored check and exact-target one-worker 1,188-job build pass.
All five audited exports use only `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  No cutoff-uniform rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## BF4 pairwise variance is exactly centered mass times diagonal (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPairwiseVariance` defines the ordered weighted
pairwise variance and proves the generic exact identity
`PV = 2 * (mass * diagonal - mean^2)`.  It does so by viewing
`weight_i * weight_j` as a stationary product joint kernel and reusing the
already-audited Dirichlet identity; the selected communicating component need
not have unit total mass.

For exactly centered BF4 sector coefficients this contracts to
`PV = 2 * sectorMass * diagonal`.  Independently, summing the common endpoint
estimate with the nonnegative stationary product weights proves
`edgeFloor * PV <= sectorMass^2 * pathCeiling * Dirichlet`.  These are now two
kernel-checked faces of the same quantity, so the next module can eliminate
`PV` and derive an explicit finite Poincare inequality.

The focused monitored check and exact-target one-worker 1,187-job build pass.
All five audited exports use only `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  No Poincare inequality, strict finite rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted yet.

## Every finite BF4 vacuum sector has one path-amplification ceiling (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPathCeiling` packages each sector index together
with its membership proof, enumerates the finite Cartesian square of attached
indices, and sums the nonnegative scales of all canonical paths.  Adding `1`
produces a strictly positive, coefficient-independent rational ceiling above
every endpoint-specific scale.

Combining this ceiling with the common positive edge floor and the local and
global path-energy estimates yields a single all-endpoint theorem:
`floor * (f_i-f_j)^2 <= ceiling * Dirichlet(f)` for every pair of indices in
the fixed finite sector.  This is the exact input needed to sum pairwise
variance and derive a finite Poincare inequality.

The focused monitored check and exact-target one-worker 1,186-job build pass.
The four audited exports use only `[propext]` or `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No pairwise-variance identity, Poincare
inequality, strict finite rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted yet.

## Canonical BF4 path energy is bounded by global Dirichlet energy (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPathGlobalEnergy` assigns each Type-level
positive-kernel chain an explicit recursive amplification scale.  A generic
summand lemma first proves that every nonnegative kernel-weighted edge square
is below the full directed finite Dirichlet double sum.  Induction on the
actual chain then bounds its recursively amplified energy by its scale times
that global energy.

The theorem is specialized to every canonical path in every finite BF4
vacuum sector using the already-proved nonnegativity of the genuine normalized
physical kernel.  The remaining ceiling step is purely finite: sum (or
maximize) the explicit path scales over the attached sector-pair carrier, so
one coefficient-independent constant controls every endpoint estimate.

The focused monitored check and exact-target one-worker 1,185-job build pass.
The four audited exports use only `[propext]` or `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No common path ceiling, Poincare
inequality, strict finite rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted yet.

## Every finite BF4 vacuum sector has a common positive edge floor (2026-08-22)

`BF4PhysicalFiniteVacuumSectorEdgeFloor` constructs a single explicit positive
rational below every positive physical-kernel entry between canonical sector
indices.  It forms the finite ordered-pair list, replaces each nonpositive
entry by `1`, and folds the located rational minimum with a positive `1`
fallback.  Hence the minimum is strictly positive without a proposition-level
selection, while on every actual positive path edge its candidate reduces to
the kernel entry itself.

The resulting floor discharges the lower-edge premise of the canonical
path-energy theorem for every pair of sector indices.  The next remaining
finite step is no longer positivity: it is to compare each recursively
amplified path energy with the global Dirichlet energy and combine the finite
path factors into one common ceiling.

The focused monitored check and exact-target one-worker 1,184-job build pass.
The five audited exports use no axioms or only `[propext]` or
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  No amplification
ceiling, Poincare inequality, strict finite rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted yet.

## Positive BF4 paths quantitatively control endpoint differences (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPathEnergy` equips every Type-level positive-
kernel chain with an explicit recursively amplified physical edge energy.  If
a nonnegative rational floor lies below every positive entry used by the
chain, the floor times the squared endpoint difference is bounded by that
amplified energy.  The proof is an induction on the actual chain data and uses
only the two-term square inequality; it takes no reciprocal and extracts no
propositional witness.

The theorem is specialized to the canonical path returned between every pair
of BF4 vacuum-sector indices.  Thus the remaining finite work is now cleanly
combinatorial: construct a positive minimum of the finitely many positive
sector entries and bound the finitely many path amplifications by one common
factor, then sum the endpoint bounds into a Poincare inequality.

The focused monitored check and exact-target one-worker 1,183-job build pass.
All four printed declarations use only `[propext]` or
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  No common edge floor,
finite `q < 1`, cutoff uniformity, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted yet.

## Every finite BF4 vacuum component is a positive Gram sector (2026-08-22)

`BF4PhysicalFiniteVacuumSectorGramPositivity` removes a cutoff-two-only
restriction from the lower spectral edge.  At arbitrary nonnegative coupling,
representation cutoff, and half-depth, the common positive partition
reciprocal is absorbed into the physical boundary-channel weights.  Every
normalized kernel entry between indices in the canonical vacuum component is
then identified with the corresponding entry of this scaled weighted Gram.
The complete sector quadratic is exactly the resulting finite weighted-Gram
quadratic and is nonnegative for every coefficient.

This establishes reflection positivity directly on every finite canonical
vacuum sector.  Consequently the remaining finite strict-gap problem is
one-sided: connected support must provide a quantitative Poincare upper bound
strictly below the diagonal.  Once proved, nonnegativity will turn that upper
bound into the absolute form bound needed by the adaptive tail-seed bridge.

The focused monitored check and exact-target one-worker 1,179-job build pass.
All four printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is positivity, not strictness: no
finite `q < 1`, uniform cutoff rate, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## The finite BF4 vacuum component is physically irreducible (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPositiveConnectivity` closes the semantic gap
between the Boolean graph used to select the canonical component and the
actual normalized physical kernel.  On sector indices, a true symmetrized
support edge is equivalent to strict positivity of the normalized reflected
kernel in the requested orientation.  The reverse-orientation case uses
exact Gram symmetry and nonnegativity, so no directed edge is silently lost.

The new `PositiveKernelChainIn` is Type-level path data carrying a strict
kernel-positivity witness at every step.  The generic `ofChainIn` compiler
turns the already constructed Boolean `ChainIn` data into these physical
paths.  Therefore every pair of indices in every finite canonical vacuum
sector is connected by an explicit positive-kernel chain.  Every sector
stationary weight is also proved strictly positive.

This proves finite physical irreducibility constructively.  The next step is
quantitative rather than qualitative: turn the finite positive paths into a
positive bottleneck/path constant and a Poincare upper estimate.  Combined
with the all-cutoff Gram nonnegativity, that estimate will produce a strict
absolute finite form rate for the adaptive tail-seed bridge.

The focused monitored check and exact-target one-worker 1,180-job build pass.
All five printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No quantitative rate, cutoff
uniformity, completed Hilbert gap, thermodynamic/continuum QFT, or Clay theorem
is asserted.

## Every fixed BF4 carrier gap contracts to its Bishop-real limit (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap` gives a reusable
eventual-gap compiler for two Bishop reals and applies it to every arbitrary
fixed BF4 vacuum carrier.  The existing Cauchy moduli select an anchor beyond
both approximation moduli and the finite Poincare start; the finite
absolute-value estimate then passes to `CReal.leEv` with the exact same rational
rate, without relaxation.

The focused monitored check and exact-target one-worker 4,754-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  This contracts the later-cutoff estimate for one chosen fixed
carrier and certificate.  Instantiating it with the constructed arbitrary-base
floor removes that input; proving a single rate below one across an
unbounded/cofinal carrier family remains open.  No completed-space gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## The finite BF4 vacuum component has its exact stationary row law (2026-08-22)

`BF4PhysicalFiniteVacuumSectorStationaryLaws` proves that restricting the
normalized reflected joint kernel to the canonical root component preserves
the exact physical row marginal.  For every sector source, the sum of the
actual normalized physical entries over sector targets is exactly the stored
stationary weight.  The proof recodes the full positive carrier by indices,
uses component row closure to erase every complementary entry, and identifies
the component enumeration with the corresponding carrier filter by a
constructive nonnegative-sum reordering argument.

The component's total stationary mass is also strictly positive: the vacuum
index lies in the component and its retained physical weight is positive.
Together with all-cutoff Gram nonnegativity and positive-kernel connectivity,
these laws provide the exact hypotheses for the next finite Dirichlet and
path-Poincare calculations.

The focused monitored check and exact-target one-worker 1,181-job build pass.
All three printed declarations use exactly `[propext, Quot.sound]`.  The
standard `List.nodup_range` in this toolchain introduced `Classical.choice`, so
it was deliberately replaced by an explicit list-inductive range proof.  No
choice, `Classical.*`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration remains.  No quantitative rate, cutoff uniformity, completed
Hilbert gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## The finite BF4 vacuum-sector deficit is an exact edge energy (2026-08-22)

`BF4PhysicalFiniteVacuumSectorDirichlet` proves a generic finite identity for
every symmetric joint kernel whose row sums equal its stationary weights: the
directed edge energy `sum K_ij (f_i-f_j)^2` is exactly twice the diagonal-minus-
transfer deficit.  Its half-energy form is also proved without division or
square roots.

Specializing the generic theorem with the newly proved restricted BF4 row law
and exact physical symmetry gives both identities on every canonical finite
vacuum component and at every representation cutoff.  This turns the pending
upper-gap problem into a literal path-energy estimate: it is now enough to
bound the centered stationary square by the displayed sum of positive edge
squares.

The focused monitored check and exact-target one-worker 1,182-job build pass.
All four printed declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration was added.  The first proof shape caused expensive definitional
reduction; named diagonal and matrix bridges reduced the final check to under
one second.  No finite strict rate, cutoff uniformity, completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## A uniform tail Poincare rate is now the sole same-object input (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap` removes the apparent
coefficientwise seed-alignment hypothesis from the fixed cutoff-two
same-object frontier.  Its only new certificate supplies a rational `q` with
`0 <= q < 1`, one global start, and the bound
`poincareRate(cutoff) <= q` at every later cutoff.

For each requested coefficient, the proof obtains the already verified
pairwise moving-form stability start and takes its maximum with the global
rate start.  Stability is still valid at the maximum, while the all-cutoff
finite Poincare theorem supplies the strict seed gap there.  Named exact
matrix and diagonal recoding seams transfer the physical tail inequalities to
the literal Bishop-real approximants.  The existing adaptive compiler then
gives, at one common propagated rate strictly below one, the same-object CReal
matrix-versus-diagonal inequality for every coefficient.

The coefficientwise starts are eliminated only inside the Prop-valued CReal
comparison, so no choice function is formed.  The focused monitored check and
exact-target one-worker 4,749-job build pass.  All five audited exports use
only `[propext]` or `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The uniform tail bound itself is not constructed here.  No completed
Hilbert gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## Fixed cutoff-two paths retain one cutoff-independent ceiling (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy` replaces the growing
full-sector path construction by the fixed cutoff-two vacuum carrier.  It
proves from the existing rooted support-graph embedding that every positive
edge of every canonical cutoff-two path remains positive in every later
pulled kernel.  A generic `rekernel` operation transports the Type-level path
and proves that its recursive amplification scale is exactly unchanged.

The new `CutoffTwoPulledUniformPositiveEdgeFloor` certificate asks only for a
common positive lower bound on positive entries of the fixed 65-state pulled
kernel after one cutoff.  Given that datum, every fixed-carrier endpoint
difference is bounded by the certificate floor and the original cutoff-two
path ceiling times the later pulled Dirichlet energy.  Thus no cardinality,
minimum-edge, or path-ceiling constant from the growing full sector appears in
the uniform estimate.

The focused monitored check and exact-target one-worker 4,748-job build pass.
All five audited exports use only `[]`, `[propext]`, or
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The quantitative
positive-edge floor is not constructed here.  No uniform form gap, completed
Hilbert gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## The fixed pulled energy is a sub-energy of the moving deficit (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding` maps the Cartesian
square of the fixed cutoff-two vacuum carrier injectively into the Cartesian
square of every later full vacuum sector.  Exact coefficient-extension and
pulled-kernel recodings identify each source term with its old-old image,
while positivity of every target summand makes the pulled Dirichlet energy a
constructive sub-sum of the full zero-extension energy.

The exact finite Dirichlet identity and the already proved head-centering form
recodings then contract the full energy to twice the actual moving
diagonal-minus-matrix deficit.  Consequently, the fixed-carrier energy needed
by the uniform path estimate is now connected directly to the same moving
forms used by the Bishop-real limit compiler, with no quantitative assumption.

The focused monitored check and exact-target one-worker 4,749-job build pass.
Both audited declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  A common positive pulled-edge floor is
still an open analytic input, and no uniform strict rate, completed Hilbert
gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## The fixed pulled carrier has normalized positive mass (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledMass` proves that the stationary mass of
the fixed cutoff-two vacuum component is strictly positive at every later
cutoff and is at most one whenever the cutoff is at least two.  Positivity is
witnessed by the retained vacuum root.  For the upper bound, the cutoff index
map injects the fixed component into the complete later positive-row carrier,
and the latter's finite weight sum is identified with the exactly normalized
physical stationary mean.

Thus the mass factor arising when the endpoint estimate is summed can be
cancelled constructively and then bounded by one.  It does not require a new
uniform analytic hypothesis: the only unresolved quantitative datum on this
fixed-carrier branch remains the common positive pulled-edge floor.

The focused monitored check and exact-target one-worker 4,750-job build pass.
Both audited declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No common edge floor, uniform strict
rate, completed Hilbert gap, thermodynamic/continuum QFT, or Clay theorem is
asserted.

## One pulled edge floor now gives a uniform finite BF4 gap (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap` completes the
fixed-carrier finite Poincare contraction.  It sums the common endpoint
estimate against the later pulled weights, uses exact moving centering to
identify pairwise variance with twice mass times the diagonal, and uses the
old-old energy embedding to bound the pulled energy by twice the moving
diagonal-minus-matrix deficit.  Strict positivity cancels the pulled mass and
its proved upper bound by one removes it from the final constant.

For a `CutoffTwoPulledUniformPositiveEdgeFloor` certificate, the resulting
rate is the explicit cutoff-independent rational
`ceiling / (ceiling + floor)`.  The fixed path ceiling is positive and the
certificate floor is positive, so the rate is nonnegative and strictly below
one.  Full-sector Gram positivity and exact form recodings then give the
absolute moving-matrix bound at this one rate for every later cutoff and every
coefficient.

The focused monitored check and exact-target one-worker 4,751-job build pass.
The four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The common positive-edge-floor
certificate is not inhabited, and no unconditional same-object CReal gap,
completed Hilbert gap, thermodynamic/continuum QFT, or Clay theorem is
asserted.

## The uniform finite rate reaches the same-object Bishop-real limit unchanged (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap` recodes the uniform pulled
finite inequality to the literal moving matrix and diagonal approximants and
passes it to their same-object Bishop-real limits.  Because the finite gap
already holds after one common certificate start, the eventual-order proof
uses only the two Cauchy moduli and preserves the exact rational rate
`ceiling / (ceiling + floor)`; no adaptive tail relaxation is needed.

Thus a `CutoffTwoPulledUniformPositiveEdgeFloor` now contracts all the way to
one uniform strict CReal form inequality for every coefficient on the fixed
cutoff-two vacuum carrier.  This is still a conditional finite-carrier
statement: neither the edge-floor certificate nor a density/completion bridge
to the full physical vacuum complement is constructed here.

The focused monitored check and exact-target one-worker 4,752-job build pass.
Both audited declarations use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No unconditional completed Hilbert gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## The transported cutoff-two path-edge floor is now constructed (2026-08-22)

The earlier `CutoffTwoPulledUniformPositiveEdgeFloor` was stronger than the
canonical-path argument actually needs: it requested a lower bound on every
entry which is positive at a later cutoff, including entries which may first
become positive only after new representation labels are admitted.  The path
proof uses only edges already positive at cutoff two.  The new
`CutoffTwoPulledUniformBasePositiveEdgeFloor` records exactly that weaker and
sufficient premise.

`BF4PhysicalFiniteVacuumSectorPathEnergy` now contains a generic quantitative
`rekernel` compiler which retains each base-edge positivity proof while
measuring energy with the replacement kernel.  Consequently the fixed
cutoff-two path endpoint theorem applies under the weaker base-positive floor
without any converse support-persistence claim.

`BF4PhysicalCutoffUniformRowFloor` exposes the underlying observable-level
half-retention theorem: every nonnegative cutoff-stable unit observable keeps
at least half of its anchor expectation whenever the complete new-label
partition increment is at most one.  Applying this to ordered pair cylinders,
`BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor` chooses the explicit anchor
`max 2 centralPhysicalUniformRowFloorCutoff`, takes a finite positive minimum
over the fixed cutoff-two Cartesian carrier there, and proves that half this
minimum is below every later pulled kernel entry whose cutoff-two ancestor is
positive.  This constructs
`cutoffTwoPulledUniformBasePositiveEdgeFloor` with no analytic certificate.

The focused monitored checks and exact-target one-worker 4,749-job build pass.
All newly audited declarations use only `[propext, Quot.sound]` (with the
shape-preservation equality itself axiom-free); no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  This removes the edge-floor input on the fixed-carrier branch, but the
existing finite Poincare and same-object CReal contraction files still need
to be recoded from the obsolete stronger certificate to the newly inhabited
exact certificate.  A density/cofinal bridge to the full vacuum complement,
completed-space gap, thermodynamic/continuum QFT, and Clay theorem remain
open.

## The fixed-carrier same-object BF4 gap is now unconditional (2026-08-22)

`BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap` and
`BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap` now consume the exact
`CutoffTwoPulledUniformBasePositiveEdgeFloor` required by the canonical paths,
rather than the obsolete stronger all-later-positive condition.  Their
finite Poincare and Bishop-real limit arguments are unchanged: the constructed
floor and fixed path ceiling give one rational rate
`ceiling / (ceiling + floor)`, this rate is nonnegative and strictly below
one, and it controls every coefficient on the fixed cutoff-two pulled carrier.

`BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap` specializes
those compilers to the constructed pair-cylinder floor.  Its sealed
`cutoffTwoConstructedUniformGapData` contains the rational rate, proofs
`0 <= rate < 1`, the uniform finite moving-form estimate after the certificate
start, and the same-object Bishop-real matrix-versus-diagonal inequality for
every fixed-carrier coefficient.  No certificate argument remains on this
branch.  The opaque presentation boundary is kernel checked and prevents
downstream elaboration from normalizing the explicit 65 by 65 finite minimum.

The focused monitored checks and exact-target one-worker 4,754-job build pass.
The final package uses exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  This is an unconditional gap only for one fixed finite carrier at
the representation-cutoff limit.  No density or cofinality theorem identifies
that carrier with the full cutoff-removed vacuum complement, so no completed
Hilbert-space gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## Every fixed BF4 vacuum carrier has a persistent path-edge floor (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor` generalizes the constructed
cutoff-two edge floor to arbitrary fixed nome, base representation cutoff, and
finite half-extent.  A positive normalized edge in the base vacuum component
remains positive after every canonical cutoff embedding.  The ordered-pair
cylinder for two old literal states obeys the common half-retention theorem
beyond the anchor
`max base (centralPhysicalUniformRowFloorCutoff w half)`.

At that anchor, a finite positive minimum over the Cartesian square of the
base component gives an explicit rational floor.  Half of this minimum is
below every later pulled-kernel entry whose base edge was positive.  The
sealed `fixedBasePulledPositiveEdgeFloor` therefore constructs this persistent
floor for every fixed carrier without a new analytic certificate.

The focused monitored check and exact-target one-worker 4,749-job build pass.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This expands the quantitative geometry
from one 65-state carrier to every member of the finite vacuum-sector family,
but the floor and anchor still depend on the base.  A common strict rate
uniform over an unbounded/cofinal family, the corresponding completed-space
gap, thermodynamic/continuum QFT, and the Clay theorem remain open.

## Every fixed BF4 carrier has later-uniform path control (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledPathEnergy` transports each arbitrary
base component's canonical positive paths to every later pulled kernel.  The
transport retains the base-edge witnesses and preserves the recursive path
amplification scale exactly, so the original finite base path ceiling remains
valid at all later cutoffs.

Combining that shape preservation with the constructed base edge floor gives
a coefficient-independent endpoint estimate: the base floor times every
endpoint square is bounded by the base path ceiling times the later pulled
Dirichlet energy.  The focused monitored check and exact-target one-worker
4,750-job build pass; both audited exports use exactly
`[propext, Quot.sound]`.  The floor and ceiling are still allowed to vary with
the base component.  The ensuing base-indexed strict form rate is the next
finite contraction; a common rate below one on a cofinal family, completion,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## Every fixed BF4 carrier has a later-uniform strict Poincare rate (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap` contracts the arbitrary-
base edge floor, transported path ceiling, pulled Dirichlet embedding, exact
pairwise-variance identity, and normalized positive pulled mass into an explicit
rational rate
`basePathCeiling / (basePathCeiling + floor)`.  The rate is nonnegative and
strictly below one, and its absolute-value form controls every moving centered
matrix quadratic by the corresponding diagonal quadratic at every cutoff after
the floor certificate's start.

The focused monitored check and exact-target one-worker 4,753-job build pass.
The four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This proves a cutoff-uniform gap for each
fixed carrier, but its rate may depend on that carrier.  Passing the estimate to
the same-object Bishop-real cutoff limit is the next contraction; proving one
strict rate uniform over an unbounded/cofinal carrier family remains the next
expansion.  No completed-space gap, thermodynamic/continuum QFT, or Clay theorem
is asserted.

## Same-object BF4 gap data is constructed on every fixed carrier (2026-08-22)

`BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap` instantiates the
arbitrary-carrier Poincare and Bishop-real compilers with the constructed
persistent edge floor.  For every fixed nome, base cutoff, and half-extent, the
sealed `fixedBaseConstructedUniformGapData` now contains a rational rate, proofs
`0 <= rate < 1`, a later-cutoff start above the base, the uniform moving-form
estimate, and the same-object Bishop-real matrix-versus-diagonal inequality.

The focused monitored check and exact-target one-worker 4,755-job build pass.
The audited package uses exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  No analytic certificate remains for any individually fixed finite
carrier.  The rates and starts remain base-indexed, so the next genuine
frontier is a common strict rate on an unbounded/cofinal carrier family,
followed by the vacuum-sector density/completion bridge.  No completed-space
gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## Cofinal finite-prefix ceilings exactly characterize all-carrier BF4 rate uniformity (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge` isolates the infinitary
step left after finite-prefix compactness.  A certificate now supplies one
rational `q < 1`, a cofinal schedule `anchor B >= B`, and a proof that the
running maximum of all constructed carrier rates through `anchor B` is at most
`q`.  This data compiles to the existing all-carrier rate certificate, the
cofinal moving-centered strict gap, and the same-object Bishop-real inequality.

Conversely, every all-carrier rate certificate constructs such a cofinal
finite-prefix ceiling using the identity schedule.  Thus merely choosing
larger finite prefixes cannot hide deterioration of the carrier-dependent
rates: the scheduled-prefix statement is constructively equivalent to a
single bound on every carrier.  The focused monitored check and exact-target
one-worker 4,759-job build pass.  All four audited exports use exactly
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  The certificate is
deliberately uninhabited: a uniform analytic estimate (or sharper replacement
for the canonical-path constants) and the separate vacuum-sector
density/completion bridge remain open.  No completed-space gap,
thermodynamic/continuum QFT, or Clay theorem is asserted.

## One adaptive recoding tail now compiles to the completed BF4 sector transfer lift (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderFiniteAction` now strengthens exact
finite recoding from pointwise carrier equality to zero finite GNS squared
distance: whenever a presentation base is below the current action cutoff,
the realized sector recoding and the genuine global finite-linear Markov
action represent the same finite GNS vector.

`BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail` applies that
identity to every support-safe adaptive sample.  The limiting squared-distance
approximation is exactly zero at its own action cutoff.  The remaining
infinitary input is isolated as one explicit-modulus tail record requiring the
limiting distance from the sector recoding to the global adaptive output to
tend to zero.  A sufficient diagonal-regularity record states exactly when
the current cutoff pays the moving inner-regularity rate and compiles to that
tail.

Given the tail, a three-leg squared-distance estimate constructs the recoded
sector Cauchy sequence.  Completion closeness identifies its global image
with the already constructed concrete adaptive transfer; injectivity of the
sector embedding then supplies quotient descent.  The resulting sector
transfer inhabits the previously stated
`CentralPhysicalVacuumSectorCylinderTransferLiftData` and therefore has the
proved vacuum-orthogonality and completed-pairing consequences.

The focused monitored check and exact-target one-worker 1,360-job build pass.
The four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Several earlier focused checks timed
out during elaboration and are not counted as validation.  Neither the tail
record nor its diagonal-regularity sufficient condition is inhabited here:
the completed lift remains conditional on that one analytic estimate.  A
common strict rate over all carriers is independently open.  No completed
uniform gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

## The BF4 sector slow diagonal now pays an amplitude-scaled source-shell schedule (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy` now attaches two
requirements to every original sector presentation.  It still pays the
literal representation base.  In addition it computes the presentation's
finite coefficient `l1` envelope, squares the doubled envelope, rescales
`1/(i+1)` by that nonnegative factor, and pays the existing stationary
target-shell cutoff at the resulting tolerance.

The slow diagonal remains Cauchy and completion-equal to the original
representative because its proof works for any pointwise natural-number
requirement.  Its selected presentation still has `base <= stage`, and a new
theorem proves that the corresponding amplitude-scaled shell cutoff is also
at most the sequence stage once the zeroth requirement is admitted.  The
downstream adaptive recoding-tail compiler continues to pass unchanged.

The focused monitored checks for the strengthened schedule and downstream
compiler pass, and the exact-target one-worker 1,351-job build passes.  The
three newly audited scheduling exports use exactly `[propext, Quot.sound]`;
no `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This does not yet inhabit the recoding
tail: the next layer must prove global and recoded pointwise amplitude bounds,
the finite core-zero plus shell-mass inequality, and the nested cofinality
estimate.  The all-carrier strict rate and all continuum/Clay conclusions
remain open.

## The BF4 global action and sector recoding share a pointwise `l1` envelope (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude` proves that the
finite-linear cutoff Markov action is pointwise bounded by the input
presentation's coefficient `l1`.  For the sector recoding, it proves that at
most one finite lower-face state cylinder can match an arbitrary labelling;
the recoded value is therefore one coefficient rather than a sum carrying a
growing state-count factor.  Consequently both sides of the future recoding
error have the same cutoff-independent pointwise envelope.

The focused monitored check and exact-target one-worker 1,352-job build pass.
Both audited exported amplitude bounds use exactly `[propext, Quot.sound]`;
no `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This proves the amplitude input to the
planned core/shell argument, not yet its finite GNS inequality or the adaptive
tail.  The completed transfer lift therefore remains conditional, and the
uniform completed gap, thermodynamic/continuum QFT, and Clay theorem remain
open.

## The BF4 sector recoding has a uniform limiting core--shell estimate (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell` generalizes the
finite unit-observable core--shell inequality to arbitrary observables with a
nonnegative pointwise square envelope.  For the sector recoding, exact finite
action identifies the discrepancy with zero on the action-cutoff positive
carrier, while the pointwise amplitude theorem bounds the complementary
square by `(2 l1)^2`.

The stationary source-shell theorem and the amplitude-scaled cutoff already
paid by the base-controlled representative then give, uniformly in every
later finite GNS approximation,
`distSq(recoding, global action) <= 1/(i+1)`.  This replaces the previously
open moving-inner-regularity condition by a concrete shell estimate.

The focused monitored check and exact-target one-worker 1,353-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The estimate has not yet been threaded
through the nested adaptive and slow-diagonal cofinality schedules, so the
tail record and completed lift remain conditional at this checkpoint.  The
all-carrier strict rate and all thermodynamic/continuum/Clay conclusions
remain open.

## The BF4 adaptive recoding tail and completed sector transfer lift are inhabited (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited` composes
the two slow schedules explicitly.  At tolerance `epsilon`, the outer
adaptive sampler is forced beyond both the inner zeroth threshold and the
inner threshold at `CReal.lv epsilon`.  The selected original presentation
index `i` is therefore at least `CReal.lv epsilon`; its amplitude-scaled shell
cutoff is below the sampled controlled stage and hence below the action stage.

Applying the proved core--shell estimate gives limiting squared distance at
most `1/(i+1)`, and antitonicity plus `CReal.invSucc_lv_le` contracts this to
`epsilon`.  This supplies an unconditional
`CentralPhysicalVacuumSectorAdaptiveRecodingTailData`.  The existing
three-leg, completion-closeness, injectivity, and quotient-descent compiler
then constructs an unconditional
`CentralPhysicalVacuumSectorCylinderTransferLiftData`, including its proved
intertwining with the concrete global adaptive transfer and the inherited
vacuum-orthogonality consequences.

The focused monitored check and exact-target one-worker 1,363-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  This closes completed root-sector transfer invariance at fixed
nome and finite half-extent.  It does not supply the independently open
strict rate uniform over all carriers, nor thermodynamic/continuum control or
the Clay theorem.

## The completed BF4 root sector now has powers and same-object moments (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments` packages the
unconditionally inhabited root-sector transfer as an endomorphism of the
completed sector and of its actual global-vacuum-orthogonal subtype.  That
vacuum complement embeds injectively into the global cutoff-removed BF4
vacuum complement, and the restricted transfer intertwines the concrete
global adaptive transfer.

Natural powers of the sector and global transfers are defined explicitly.
Induction upgrades the one-step intertwining theorem to every power and shows
that every sector power remains vacuum orthogonal.  The resulting same-object
sector autocorrelation is proved equal to the global completed adaptive
matrix coefficient of the embedded vector.  Thus future rate estimates now
refer to one actual completed vector and one actual transfer at every time,
instead of unrelated finite presentations.

The focused monitored check and exact-target one-worker 1,364-job build pass.
All thirteen audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This constructs the completed
same-object moment interface but proves no carrier-independent strict rate.
The common-rate analytic estimate, thermodynamic/continuum QFT, and Clay
theorem remain open.

## Any cofinal strict rate now reaches the actual adaptive completion (2026-08-22)

`BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap` removes the obsolete
same-index completion-modulus assumption from the arbitrary-rate gap route.
It combines the modern pointwise-adaptive input and transferred graph limits
with the existing finite anchor theorem for
`FixedNomeCofinalCenteredStrictGap q`.

For every supplied rational `q` with `0 <= q < 1`, cofinal reindexing carries
the finite squared-norm estimate through the two actual adaptive graph limits.
Quotient descent gives
`CentralPhysicalAdaptiveCompletedMarkovStrictContractionData` at rate `q` on
the whole cutoff-removed global vacuum complement.  Specializing to the
already-constructed stationary source-shell Cauchy data makes the cofinal
strict-rate certificate the sole remaining input.

The focused monitored check and exact-target one-worker 1,346-job build pass.
All five audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No cofinal common-rate certificate is
inhabited here, so no unconditional completed gap, thermodynamic/continuum
QFT, or Clay theorem is claimed.

## One cofinal common rate now closes the completed BF4 sector gap (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedGap` pulls the modern
arbitrary-rate global adaptive contraction through the now-inhabited
injective invariant root-sector embedding.  A
`FixedNomeCofinalCenteredStrictGap` at any rational `q` with
`0 <= q < 1` constructs strict squared-norm contraction data on the actual
completed sector vacuum complement at rate `q*q`.

Induction gives
`||T^n v||^2 <= (q*q)^n ||v||^2`.  Pulling completed Cauchy--Schwarz back
along the sector embedding then gives
`|<T^n v,v>|^2 <= (q*q)^n ||v||^4` for the exact same-object
autocorrelation constructed in the previous milestone.

The focused monitored check and exact-target one-worker 1,372-job build pass.
All seven audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is a proved conditional
implication: the sole fixed-nome finite-half-volume rate input is the still
uninhabited cofinal common-rate certificate.  No unconditional completed
gap, thermodynamic/continuum QFT, or Clay theorem is claimed.

## The actual completed sector transfer form is the pulled sector cutoff limit (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm` proves that on every
dense root-sector cylinder presentation, the matrix coefficient of the actual
completed lifted sector transfer is exactly the `CReal.RC` represented by the
already-constructed pulled finite-sector matrix cutoff limit.

The proof first shows that one-sided Markov recoding preserves the explicit
structural inner rate.  Hence the same-cutoff diagonal converges to the
completed dense transfer pairing.  At every cutoff beyond the presentation
base, finite semantic recoding, weighted self-adjointness, and the linear
realization theorem identify that diagonal with the pulled sector matrix
quadratic.  Cofinal reindexing and constructive uniqueness of limits then give
the completed equality.

The focused monitored check and exact-target one-worker 1,365-job build pass.
All five audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This removes the transfer-form
identification half of the direct sector completion bridge.  Still open are
the density/representation theorem for moving head-centered sector
presentations, one common sector-local `q < 1`, and all
thermodynamic/continuum/Clay conclusions.

## Dense completed sector vacuum pairing is the pulled mean limit (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing` identifies the
actual completed global-vacuum pairing of every dense root-sector cylinder
with its existing pulled weighted-mean cutoff limit.  At each sufficiently
large cutoff, the finite weighted pairing with the constant vacuum is reduced
to the indexed stationary mean; exact coefficient extension then identifies
that mean with the pulled root-sector mean.  Eventual stage equality and
quotient descent carry the identity to the completion.

Consequently, if the dense completed sector vector lies in the actual global
vacuum complement, its pulled weighted-mean cutoff limit is constructively
equivalent to zero.  This supplies the numerator-zero statement required to
show that moving rational head corrections disappear for an orthogonal dense
vector.

The focused monitored check and exact-target one-worker 1,366-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Still open are head-correction
vanishing in completed norm, moving head-centered density for arbitrary
completed sector vectors, one common sector-local `q < 1`, and all
thermodynamic/continuum/Clay conclusions.

## Dense orthogonal sector cylinders have vanishing moving head correction (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing` combines
the completed dense vacuum-pairing identity with the already-proved uniform
positive rational floor for the pulled vacuum-root weight.  For any dense
root-sector cylinder whose completed image is globally vacuum orthogonal, the
pulled mean numerator is eventually bounded by `epsilon * floor`, while the
root denominator remains at least `floor`.  Constructive signed-division
estimates therefore prove that the head-correction cutoff limit is equivalent
to zero in `CReal`.

The focused monitored check and exact-target one-worker 1,368-job build pass.
The audited export uses exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  This closes the scalar vanishing part of moving head-centering.
Still open are the completed-norm comparison between the moving centered
presentations and their dense source, the extension to arbitrary completed
sector vacuum vectors, one common sector-local `q < 1`, and all
thermodynamic/continuum/Clay conclusions.

## Moving centered limits are the actual dense completed sector forms (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification`
contracts the vanishing head correction through the exact polynomial
expansions of the moving centered diagonal and reflected quadratics.  Whenever
the head-correction limit is zero, both centered Bishop-real form limits are
constructively equivalent to their uncentered pulled limits.

For every dense root-sector cylinder already orthogonal to the normalized
global vacuum, the preceding norm and transfer-form bridges therefore become
exact completed identities: its actual completed squared norm is represented
by the moving head-centered diagonal limit, and its actual completed transfer
form is represented by the moving head-centered matrix limit.  These are the
same two objects controlled by the sector-local cofinal Poincare certificate.

The focused monitored check and exact-target one-worker 1,577-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The direct sector form-identification
edge is now closed on dense orthogonal vectors.  Still open are a common
sector-local `q < 1`, extension of the resulting estimate from the dense
orthogonal domain to arbitrary completed sector vacuum vectors, and all
thermodynamic/continuum/Clay conclusions.

## The sector-local cofinal certificate controls the actual dense completed form (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap` combines the dense
centered endpoint identifications with
`FixedNomeCofinalVacuumSectorCenteredStrictGap`.  Any supplied rational
certificate at `0 <= q < 1` now yields, on every dense completed root-sector
cylinder orthogonal to the global vacuum, the actual quotient-level form
bound

`<T v,v> <= q <v,v>`.

The rate is unchanged: no squaring, extra prefactor, or full-carrier
certificate enters this direct sector route.  This is important because the
full positive carrier is reducible; the sector-local certificate is the
mathematically appropriate remaining analytic input.

The focused monitored check and exact-target one-worker 1,579-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  No common-rate certificate is inhabited here.  Still open are
one sector-local rate uniform over all bases, extension from the dense
orthogonal domain to the full completed sector vacuum complement, and all
thermodynamic/continuum/Clay conclusions.

## The remaining completed-sector centering bridge is one exact cofinality datum (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality`
packages the precise completion datum still needed by the direct sector
route.  For each vector in the actual completed sector vacuum complement it
asks for a sequence of finite sector presentations whose moving centered
diagonal and matrix limits converge, respectively, to Bishop-real
representatives of that vector's actual completed norm and transfer form.

The datum is unconditionally inhabited for every already-dense orthogonal
sector vector by a constant outer presentation sequence.  A global inhabitant
for all completed vectors, together with any one
`FixedNomeCofinalVacuumSectorCenteredStrictGap q`, now compiles to the actual
all-vector completed form inequality `<T v,v> <= q <v,v>` at the unchanged
strict rate `0 <= q < 1`.

The focused monitored check and exact-target one-worker 1,580-job build pass.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The completion frontier and analytic
rate frontier are now separate and explicit.  Neither the all-vector
cofinality datum nor the common strict rate is inhabited here; all
thermodynamic/continuum/Clay conclusions remain open.

## Arbitrary completed orthogonal sector representatives have vanishing outer head corrections (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing`
starts the genuinely non-dense construction of the all-vector centered-form
cofinality datum.  For every Cauchy representative of a completed root-sector
vector, the outer sequence of pulled weighted-mean cutoff limits converges to
the representative's actual completed pairing with the global vacuum.
Completed vacuum orthogonality makes that target constructively zero.

The fixed positive pulled-root floor then controls division uniformly over
the outer representative index: a sufficiently small pulled mean numerator
forces the corresponding full Bishop-real head correction to be small.
Thus the outer head-correction sequence converges to zero for every completed
orthogonal sector representative, rather than only for constant dense
representatives.

The focused monitored check and exact-target one-worker 1,581-job build pass.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is the first arbitrary-completion
ingredient of the global cofinality datum.  Outer centered diagonal and
matrix convergence, a global cofinality inhabitant, one common sector-local
`q < 1`, and all thermodynamic/continuum/Clay conclusions remain open.

## Outer raw diagonals converge to the actual completed sector norm (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal` takes an
arbitrary sector Cauchy representative and, at each outer stage, forms the
already-constructed pulled diagonal cutoff-limit Bishop real of that dense
term.  Termwise dense form identification transports the global completed
pairing convergence theorem to this pulled sequence.

The resulting limit is definitionally the representative-level pairing limit
whose real-quotient class is the actual completed squared norm of the sector
quotient vector.  Thus the uncentered diagonal side of the arbitrary-vector
cofinality bridge now has both outer convergence and exact endpoint
identification.

The focused monitored check and exact-target one-worker 1,582-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  Still open are control of the centered-minus-raw outer diagonal,
the analogous outer matrix convergence, a global centered-form cofinality
inhabitant, one common sector-local `q < 1`, and all
thermodynamic/continuum/Clay conclusions.

## Arbitrary completed sector representatives have a controlled root-coordinate limit (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate` proves
that the distinguished root coefficient is a continuous coordinate on the
completed sector carrier.  At every sufficiently large finite cutoff, the
uniform positive vacuum-row floor times the squared root-coordinate
difference is bounded by the literal finite physical GNS distance.  Passing
through the exact cutoff-stage bridge gives the corresponding eventual
`CReal` inequality for the cutoff-removed sector distance.

Reindexing an arbitrary sector representative's supplied squared-distance
modulus at `floor * epsilon^2`, cancelling the positive floor, and reflecting
the square bound constructs an explicit `CReal.QCauchy` datum for its rational
root coefficients.  Hence every arbitrary completed-sector representative
now has a canonical Bishop-real root-coordinate limit, with a proved
convergence theorem.

The focused monitored check and exact-target one-worker 1,583-job build pass.
Both audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  This supplies the missing bounded/convergent root factor for the
centered-minus-raw diagonal comparison.  Outer centered diagonal and matrix
convergence, the global centered-form cofinality inhabitant, one common
sector-local `q < 1`, and all thermodynamic/continuum/Clay conclusions remain
open.

## The pulled sector matrix cutoff now exports its constructive inner modulus (2026-08-22)

`BF4PhysicalCutoffVacuumSectorFormCauchy` now exposes the exact finite-sector
matrix cutoff rate which was previously local to the legacy `CReal.cauchy`
proof.  The new
`centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular`
theorem proves the two-sided estimate at that rate, and
`centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity`
packages it as recoverable `CReal.InnerRegularity` data.

The existing pulled-matrix Bishop real is unchanged extensionally and now
uses the same exported rate theorem for its `CReal.cauchy` field.  This avoids
any extraction from a propositional existential when a later moving
presentation must pay its own inner cutoff, which is the next constructive
step toward arbitrary-representative outer matrix convergence.

The focused monitored check and exact-target one-worker 1,177-job build pass.
Both newly audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  No moving-matrix convergence, global
centered-form cofinality, common sector-local `q < 1`, thermodynamic or
continuum limit, or Clay theorem is claimed here.

## Outer head-centered diagonals converge to the actual completed sector norm (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal`
combines the arbitrary-representative raw diagonal, head-correction, and root
coordinate limits.  The pulled vacuum-root weight is proved termwise
equivalent to one canonical base-zero Bishop real because every cutoff
embedding fixes index zero.

Constructive continuity of addition, negation, and multiplication then shows
that the exact root-replacement polynomial

`((root - correction)^2 - root^2) * rootWeight`

converges to zero.  The existing exact dense expansion transports raw
diagonal convergence across this vanishing term, so the outer moving
head-centered diagonal sequence of every completed vacuum-orthogonal sector
representative converges to the representative pairing limit whose quotient
class is its actual completed squared norm.

The focused monitored check and exact-target one-worker 1,584-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The diagonal half of the arbitrary-
vector centered-form cofinality datum is now closed.  Outer centered matrix
convergence, the resulting global cofinality inhabitant, one common
sector-local `q < 1`, and all thermodynamic/continuum/Clay conclusions remain
open.

## Outer raw transfer matrices converge to the actual completed sector form (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix` constructs a
base-controlled slow diagonal for every arbitrary sector Cauchy
representative.  Its selected presentations pay both the same-object
physical-inner cutoff and the independently exported pulled-matrix cutoff
modulus.  The construction remains cofinal, is Cauchy, and represents the
same completed sector vector.

A generic regularized-diagonal lifting theorem upgrades convergence of the
rational same-cutoff diagonal to convergence of the moving pulled-matrix
Bishop reals.  The exact finite Markov-action identity identifies that
diagonal with the pulled sector matrix, while the adaptive completed transfer
construction identifies its limit with the actual completed transfer pairing
of the original quotient class.

The focused monitored check and exact-target one-worker 1,366-job build pass.
The generic lifting theorem uses `[propext]`; the three sector exports use
exactly `[propext, Quot.sound]`.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  This closes
the raw matrix half of the arbitrary-vector bridge.  Outer head-centered
matrix convergence, the resulting global centered-form cofinality inhabitant,
one common sector-local `q < 1`, and all thermodynamic/continuum/Clay
conclusions remain open.

## Outer centered matrices close the completed sector inequality without representative choice (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix` packages
every fixed-base pulled finite kernel as a constructive rational GNS form and
derives sharp bilinear Cauchy--Schwarz.  Along the previously constructed
outer matrix presentation, this bounds each head-centering cross square by a
null correction square times convergent raw/root quadratics.  Both cross
terms and the root correction therefore converge to zero, so the exact
four-term centered expansion converges to the actual completed transfer
pairing.

For one arbitrary Cauchy representative, the same recoded presentation now
simultaneously supplies centered diagonal and centered matrix limit data with
the actual completed norm and transfer endpoints.  A global Type-valued
selector of such data cannot be obtained merely by quotient induction and is
not asserted.  Instead, the completed strict-form proposition itself is
proved by choice-free quotient induction: any explicit
`FixedNomeCofinalVacuumSectorCenteredStrictGap q` now yields
`<T v,v> <= q <v,v>` for every vector in the actual completed root-sector
vacuum complement.

The focused monitored check and exact-target one-worker 1,596-job build pass.
All eleven audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The completed-vector extension is no
longer an independent hypothesis for the strict-form inequality.  Still open
are construction of a common sector-local `q < 1` with the required
cutoff/volume scope, the resulting unconditional completed spectral gap, and
all thermodynamic/continuum/Clay conclusions.

## The actual completed BF4 sector transfer form is positive and strictly bounded at every supplied certified rate (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap` passes finite
pulled-kernel positivity through the arbitrary-representative outer matrix
limit.  Each moving pulled matrix is nonnegative by its constructive finite
GNS form; closedness of Bishop-real order under convergence then proves that
the actual cutoff-removed transfer form is nonnegative on every completed
root-sector vector, with quotient induction used only into `Prop`.

The resulting `CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData`
packages the literal completed interval

`0 <= <T v,v> <= q <v,v>` with `0 <= q < 1`

for every completed vacuum-complement vector from any supplied
`FixedNomeCofinalVacuumSectorCenteredStrictGap q`.  Thus positivity and the
upper form estimate now live in one actual completed-sector datum rather than
as separate endpoint facts.

The focused monitored check and exact-target one-worker 1,597-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is still conditional on an
explicit cofinal rate certificate.  It does not construct one rate uniform
over the required cutoff/volume scope, does not upgrade the quadratic-form
bound to an operator-norm gap without an additional square-form or positive-
form Cauchy--Schwarz bridge, and does not assert a thermodynamic, continuum,
or Clay conclusion.

## The completed BF4 sector form gap compiles to an operator gap from one positive-form law (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap` isolates the
remaining functional-analytic input as sharp Cauchy--Schwarz for the actual
cutoff-removed Markov form `(left,right) |-> <T left,right>`.  Given that one
law, the now-constructed completed form interval yields the square-form bound

`||T v||^2 <= q <T v,v>`

by constructive cancellation, without dividing by the possibly zero value
`||T v||^2`.  A second application of the form gap gives the genuine
completed squared-norm contraction

`||T v||^2 <= q^2 ||v||^2`.

The result is packaged directly as the existing
`CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`, so all
previously proved power and same-object correlation decay consumers apply
without another carrier bridge.

The focused monitored check and exact-target one-worker 1,606-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The positive Markov-form
Cauchy--Schwarz datum itself is not yet inhabited, and no common cofinal rate
is constructed.  Therefore no unconditional operator gap, thermodynamic or
continuum limit, or Clay result is asserted.

## Sharp Markov-form Cauchy--Schwarz now holds on the dense completed BF4 root sector (2026-08-22)

`BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz`
generalizes the same-object dense transfer diagonal to two independent
finite-linear observables.  At every cutoff, the regular same-cutoff
approximation is identified with the rational positive Markov form
`(left,right) |-> <P_K left,right>_K`.  Structural inner regularity is
unchanged by recoding the left syntax, so each cross form converges to the
literal completed pairing of the dense cutoff-removed transfer with its test
observable.

Finite sharp Markov-form Cauchy--Schwarz then passes through the three
constructive product limits.  Pulling the result through the inhabited sector
transfer lift proves the exact `CReal.RC` inequality on any two dense
canonical root-sector cylinders, including presentations with different
bases.

The focused monitored check and exact-target one-worker 1,366-job build pass.
All four audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The positive-form law is now proved on
the dense sector, but its joint continuity extension to arbitrary completed
sector representatives and one common cofinal rate `q < 1` remain open.  No
unconditional operator gap, thermodynamic/continuum limit, or Clay theorem is
asserted.

## The adaptive BF4 transfer is norm-nonexpansive on the whole completed carrier (2026-08-22)

`BF4PhysicalCutoffLinearMarkovAdaptiveNonexpansive` aligns the graph-normalized
input representative with its literal same-cutoff adaptive Markov image.  At
each stage, the two regular inner diagonals are identified with the finite
physical input and output squared norms, so exact rational Markov `L2`
contraction gives the required pointwise inequality.

The already-proved input-square and action-square convergence laws then pass
that inequality through the two explicit constructive-real limits.  Graph
reindexing and adaptive input sampling preserve the completion class, so the
representative result descends to the actual adaptive completed endomorphism:

`<T x,T x> <= <x,x>`

for every vector in the whole fixed-nome, fixed-volume cutoff completion.

The focused monitored check and exact-target one-worker 1,310-job build pass.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  This is nonexpansiveness at rate one,
not a strict gap.  Joint continuity of the positive Markov cross form, one
common strict rate below one, the thermodynamic/continuum limit, and the Clay
conclusion remain open.

## Sharp Markov-form Cauchy--Schwarz now holds on the entire completed BF4 root sector (2026-08-22)

`BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule` constructs one explicit
two-vector slow diagonal which simultaneously pays both original adaptive
sampling requirements and the left-self, right-self, and cross-inner cutoff
rates.  Its aligned input and action sequences are Cauchy, remain cofinal, and
represent the same completed vectors and actual adaptive transfer images as
the original one-vector construction.

`BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz` identifies all three
aligned finite positive Markov forms with their literal completed pairings.
Finite sharp positive-form Cauchy--Schwarz therefore passes through the three
constructive-real limits.  Pullback along the inhabited root-sector transfer
lift proves the law for any two arbitrary completed vacuum-sector vectors and
inhabits the previously isolated
`CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`.

Consequently one supplied sector-local
`FixedNomeCofinalVacuumSectorCenteredStrictGap q` now compiles directly to the
existing completed strict-contraction datum; no independent functional-
analytic certificate remains.  The focused monitored checks pass, the joint
schedule exact-target one-worker build passes 1,303 jobs, and the final
Cauchy--Schwarz target passes 1,609 jobs.  All eight audited final exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  The sole local
analytic obstruction to an unconditional completed sector gap is now the
construction of a common cofinal rate `q < 1`.  Thermodynamic/continuum control
and the Clay theorem remain open.

## The BF4 fixed-carrier path rate now uses a finite maximum instead of a sum (2026-08-22)

`BF4PhysicalFiniteVacuumSectorPathMaximum` replaces the earlier positive path
ceiling `1 + sum(all endpoint path scales)` by the located finite quantity
`1 + max(all endpoint path scales)`.  It proves constructively that every
canonical endpoint path is controlled by this maximum and that the maximum
ceiling is no larger than the previous sum ceiling.  The corresponding
endpoint inequality is transported unchanged to every sufficiently late
pulled physical kernel.

`BF4PhysicalCutoffVacuumSectorPulledPoincareScale` factors the rational
Poincare algebra through a reusable positive-scale datum.  The maximum path
estimate inhabits this datum in
`BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap`, giving the explicit
fixed-base rate

`q_max = pathMaximum / (pathMaximum + edgeFloor) < 1`.

Monotonicity of `scale / (scale + edgeFloor)` is proved division-free and
shows `q_max <= q_sum`, so this is a genuine quantitative strengthening of
the constructed rate, not a parallel certificate.  Focused monitored checks
pass and the exact-target one-worker dependency-complete build passes 4,757
jobs.  All audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The maximum and edge floor may still
vary with the base carrier.  A common cofinal `q < 1`, the unconditional
completed spectral gap, thermodynamic/continuum control, and the Clay theorem
remain open.

## The all-base BF4 frontier now uses maximum path scale and reaches the completed operator directly (2026-08-22)

`BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge` replaces the former
all-base sum-ceiling frontier by the strictly weaker maximum-scale condition.
Its denominator-cleared analytic input is exactly

`pathMaximum <= q * (pathMaximum + edgeFloor)`

for every base carrier, with one rational `0 <= q < 1`.  This condition bounds
the already-constructed maximum Poincare rate.  Conversely, any witness for
the old sum-ceiling frontier supplies a witness for the new maximum-rate
frontier at the same `q`, because the maximum rate is no larger than the sum
rate.

The new bridge contracts either form of maximum-rate witness first to the
cofinal same-object centered finite gap and then, using the now-proved
completed Markov-form Cauchy--Schwarz law, directly to the actual completed
vacuum-sector strict-contraction datum.  Thus no functional-analytic residue
remains after the uniform rate is supplied.

The focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 4,890 jobs.  All five audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  The all-base
maximum/floor inequality is deliberately not inhabited.  Constructing one
such common rate, the unconditional completed gap, thermodynamic/continuum
control, and the Clay theorem remain open.

## The BF4 path compiler now has a polynomial length-square rate frontier (2026-08-23)

The former canonical-path energy proof accumulated the recursively defined
scale `s(refl) = 0` and `s(step rest) = 2 + 2 * s(rest)`, which is exponential
in the number of path edges.  `BF4PhysicalFiniteVacuumSectorPathLengthEnergy`
instead proves the finite rational Cauchy inequality

`(sum values)^2 <= values.length * sum(value^2)`.

Applied to the literal list of edge differences, this telescopes to the
endpoint difference and gives the polynomial estimate

`edgeFloor * endpointDifference^2 <= pathLength^2 * DirichletEnergy`.

The proof survives re-kerneling because its floor hypothesis is needed only
on the positive base edges actually traversed by the path.  The resulting
quadratic length scale is also proved no larger than the former recursive
amplification scale.

`BF4PhysicalFiniteVacuumSectorPathLengthMaximum` takes a located maximum over
all endpoint pairs and defines the positive scale

`pathLengthMaximum = 1 + max(pathLength^2)`.

It controls every endpoint difference and is no larger than the preceding
`pathMaximum`.  The pulled-kernel and Poincare modules transport this estimate
to every later cutoff and construct the sharper fixed-base rate

`q_len = pathLengthMaximum / (pathLengthMaximum + edgeFloor) < 1`.

Constructively, `q_len <= q_max <= q_sum`.  Finally,
`BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge` makes the new
all-base frontier exactly the denominator-cleared condition

`pathLengthMaximum <= q * (pathLengthMaximum + edgeFloor)`

for every base carrier and one rational `0 <= q < 1`.  Such a witness compiles
directly to the cofinal centered strict gap and the actual completed
vacuum-sector strict contraction.  A witness for the previous maximum-rate
frontier maps to this strictly weaker frontier at the same `q`.

Focused monitored checks pass for all five new modules, and the final
exact-target one-worker dependency-complete build passes 4,895 jobs.  All 20
audited exports remain within the axiom gate: each uses at most
`[propext, Quot.sound]`, with `edgeLength_rekernel` using no axioms.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  The common all-base `q` is deliberately
not inhabited: a uniform comparison between path length and persistent edge
floor, the unconditional completed gap, thermodynamic/continuum control, and
the Clay theorem remain open.

## Uniform path-scale and edge-floor controls now compile to an explicit completed rate (2026-08-23)

`BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler` splits a concrete
sufficient form of the remaining dimensionless path/floor comparison into two
independently named inputs.  A
`FixedNomeUniformPathLengthScaleUpperBound ... scale` supplies

`pathLengthMaximum(base) <= scale`

for every base carrier, while a
`FixedNomeUniformPulledEdgeFloorLowerBound ... floor` supplies one positive
rational `floor` with

`floor <= persistentEdgeFloor(base)`

for every base.  The compiler defines the explicit common rate

`q = scale / (scale + floor)`.

It proves `0 <= q < 1` and, by constructive cross multiplication,

`pathLengthPoincareRate(base) <= q`

for every base.  The cross term is exactly

`pathLengthMaximum(base) * floor <= scale * persistentEdgeFloor(base)`.

The resulting rate witness contracts through the existing same-object
cofinal bridge and completed Markov Cauchy--Schwarz theorem to the actual
completed vacuum-sector strict-contraction datum.

The focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 4,896 jobs.  All four audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  Neither
uniform input is inhabited.  Moreover, separate absolute scale and floor
bounds are only a sufficient decomposition of the sharper relative-ratio
frontier.  Constructing adequate uniform estimates, an unconditional
completed gap, thermodynamic/continuum control, and the Clay theorem remain
open.

## BF4 canonical paths are now loop-free and bounded by the explicit carrier size (2026-08-23)

`FiniteBoolGraphSimplePaths` gives a constructive graph engine that normalizes
a Boolean `ChainIn` witness to a cons-form walk, augments each edge with a
target-in-support certificate, and chronologically erases loops using
decidable membership. The resulting walk has no repeated vertices, remains
inside the supplied finite support, and satisfies the finite-pigeonhole bound

`edgeLength <= support.length`.

No shortest-path choice or classical selection is used.

`BF4PhysicalFiniteVacuumSectorSimplePathScale` specializes that engine to the
finite BF4 physical vacuum sector. It turns the loop-erased supported walk
back into a positive physical-kernel chain and bounds every endpoint path by
the number of enumerated vacuum-sector indices. The resulting explicit
positive scale is

`simpleCarrierSquareScale(base) = 1 + (#vacuumSectorIndices(base))^2`.

Finite Cauchy--Schwarz and telescoping then give the endpoint-energy estimate

`edgeFloor * (f(left) - f(right))^2 <= simpleCarrierSquareScale * DirichletEnergy`.

The pulled-scale and endpoint-scale compiler modules transport this estimate
to every sufficiently late physical kernel and convert it, using weighted
pairwise variance and mass cancellation, to the fixed-base Poincare rate

`q_simple(base) = simpleCarrierSquareScale(base) /
  (simpleCarrierSquareScale(base) + persistentEdgeFloor(base)) < 1`.

Finally, `BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge` exposes two
equivalent all-base interfaces: a uniform upper bound on these fixed-base
rates, or the denominator-cleared inequality

`simpleCarrierSquareScale(base) <=
  q * (simpleCarrierSquareScale(base) + edgeFloor(base))`

for one rational `0 <= q < 1` and every base. Either witness compiles through
the already-proved same-object centered bridge and completed Markov
Cauchy--Schwarz theorem to the actual completed vacuum-sector strict
contraction.

Focused monitored checks pass for all six new modules, and the final exact-
target one-worker dependency-complete build passes 4,901 jobs. All 19 audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added. This is a structurally explicit alternate rate, not a claimed
pointwise sharpening of the preceding path-maximum rate: no ordering between
the new carrier-square scale and the old canonical maximum has been proved.
The common all-base `q` is deliberately not inhabited. Carrier cardinality
may grow and the persistent edge floor may shrink with the cutoff, so an
unconditional completed gap, thermodynamic/continuum control, and the Clay
theorem remain open.

## The BF4 path frontier is now expressed by an ambient power count and a finite physical minimum (2026-08-23)

`BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound` removes the remaining
combinatorial opacity from the loop-erased carrier scale. It proves the nested
cardinality bounds

`#vacuumSector <= #positivePhysicalCarrier <=
  (cutoff + 1)^(#lowerFaceCoordinates)`

and therefore bounds the simple-path scale by

`A(cutoff, half) =
  1 + ((cutoff + 1)^(#lowerFaceCoordinates(half)))^2`.

At the smallest central slab the lower carrier has exactly 24 coordinates, so
the ambient state count is `(cutoff + 1)^24`. This is an upper bound on the
actual vacuum-sector size, not a proof that the sector itself grows at that
rate.

`BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula` constructs a second
fixed-base floor certificate from the already-proved finite-minimum and
half-retention estimates. A formula-carrying opaque bundle makes its
quantitative projections explicit without forcing downstream elaboration to
normalize the proof payload:

`F(base, half) = (1/2) * fixedBasePulledEdgeAnchorMinimum(base, half)`.

The minimum is taken over the finite base vacuum-sector pair carrier at the
common row-tail anchor. Its positivity is constructed at each base, but no
all-base positive lower bound is proved.

`BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap` enlarges the sharper
simple-sector Poincare scale to `A` and constructs the explicit fixed-base rate

`q_ambient(base) = A(base) / (A(base) + F(base)) < 1`.

It proves that the sharper simple-carrier rate is no larger than this ambient
rate. `BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge` then
isolates the fully expanded denominator-cleared all-base condition

`A(base) <= q * (A(base) + F(base))`

for one rational `0 <= q < 1` and every base. Any witness contracts through
the same-object centered limit and completed Markov Cauchy--Schwarz machinery
to the actual completed vacuum-sector strict contraction.

Focused monitored checks pass for all four new modules. The final exact-target
one-worker dependency-complete build passes 4,905 jobs. All 22 audited exports
use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added. Two earlier diagnostic attempts with a fully transparent proof payload
were manually interrupted and are not counted as successful checks; the
formula-carrying opaque refactor is the version that passed.

The ambient condition is sufficient but deliberately stronger than the
sharper sector-size/floor condition. It is not inhabited. The explicit power
count and finite minimum show exactly why global canonical paths may lose
uniformity, but they do not prove that loss. A uniform relative estimate or a
stronger local mixing/tensorization argument, the unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## Vacuum-sector row mixing now uses the correct component mass (2026-08-23)

The local-mixing audit exposed a normalization issue that is invisible after
exact centering but decisive for rowwise estimates.  If the canonical vacuum
component `S` has stationary mass `pi(S)`, its conditioned equilibrium joint
is

`pi(x) * pi(y) / pi(S)`,

not the unnormalized restricted product `pi(x) * pi(y)`.  The earlier
`BF4PhysicalVacuumSectorCofinalRowGap` interface remains a valid sufficient
condition, because its rank-one quadratic vanishes on sector-centered
coefficients, but it is unnecessarily strong whenever `pi(S) < 1`.

`BF4PhysicalVacuumSectorMassNormalizedRowGap` constructs the corrected
component-conditioned rank-one joint, proves that its quadratic is the
ordinary stationary-product quadratic divided by the positive component
mass, and hence proves that exact sector centering kills it.  A symmetric
row-relative estimate

`sum_y |J(x,y) - pi(x)pi(y)/pi(S)| <= q * pi(x)`

therefore gives the same centered finite quadratic contraction.  A
constructively cofinal family of these corrected estimates compiles directly
to the existing moving same-object cutoff-limit gap.

`BF4PhysicalVacuumSectorMassNormalizedFiniteChecker` makes the corrected
condition executable with exact rational arithmetic.  Its all-row Boolean
scan ranges only over the graph-defined canonical vacuum component, avoiding
the already-proved cutoff-two reducibility obstruction on the full positive
carrier.  A true scan packages the finite symmetric certificate, and one
true scan at every constructively selected cofinal cutoff compiles to the
same centered strict-gap certificate.

Focused monitored checks pass for both modules, and the final exact-target
one-worker dependency-complete build passes 1,482 jobs.  All 11 audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was added.  Two
performance diagnostics were manually interrupted: direct evaluation of a
graph-defined cutoff-zero smoke theorem, and a redundant convenience theorem
whose elaboration unfolded the checked family.  Neither is reported as
verified; both were removed from the passing module without removing the
checker or its compiler.

No nontrivial cofinal scan is inhabited.  The next local frontier is to
construct a sector-normalized conditional density/core-tail or local-slice
witness that proves these checked rows uniformly.  The unconditional
completed gap, thermodynamic/continuum control, and the Clay theorem remain
open.

## Conditioned density compiles exact sector core/tail windows to the gap (2026-08-23)

`BF4PhysicalVacuumSectorMassNormalizedDensity` constructs the conditional
probability weight and density on the canonical positive-mass vacuum
component.  It proves exact recovery of the physical joint from the
component-conditioned stationary product and density, normalization of the
conditioned weight, and the row identity

`sum_y |J(x,y) - pi(x)pi(y)/pi(S)|
  = pi(x) sum_y pi_S(y)|k_S(x,y)-1|`.

Thus the generic checked core/tail budget `1/32 + 1/64 + 1/64` gives the
correct mass-normalized row estimate at rate `1/16` with no spurious factor
of `pi(S)`.

`BF4PhysicalVacuumSectorCoreTailFiniteChecker` specializes the exact rational
core/tail checker to this conditioned component.  It scans only canonical
vacuum-sector rows, permits a source-dependent Boolean core, packages a true
all-row scan as the corrected finite row-distance certificate, and compiles
a constructively cofinal family of true scans through the same-object
centered cutoff limit to the completed vacuum-sector strict gap at `1/16`.

Focused monitored checks pass for both modules.  Exact-target one-worker
dependency-complete builds pass 1,484 jobs for the density module and 1,523
jobs for the final checker target.  All 11 audited exports use at most
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.  A diagnostic physical
wrapper whose transparent proof payload caused CPU-bound elaboration was
manually interrupted and removed; it is not counted as a successful check.

No cofinal checked family is inhabited.  The next analytic frontier is to
construct uniform sector-conditioned core/tail or local-slice estimates.
Full-carrier density convergence cannot be silently reused: on the component
the conditioned density rescales by its mass, so a component-mass defect must
either be budgeted explicitly or avoided by a genuinely sector-local mixing
argument.  The unconditional completed gap, thermodynamic/continuum control,
and the Clay theorem remain open.

## The full-density reuse branch now exposes and compiles its exact mass defect (2026-08-23)

`BF4PhysicalVacuumSectorDensityMassDefect` proves the exact conditioning law

`k_S(x,y) = pi(S) * k_full(x,y)`

on the canonical vacuum component and therefore the centered decomposition

`k_S - 1 = pi(S) * (k_full - 1) + (pi(S) - 1)`.

The pointwise triangle estimate is lifted through the conditioned stationary
weight.  Exact cancellation of `pi(S)` against that weight gives the useful
row bound

`conditioned sector row error <=
  restricted full-density row error + |pi(S) - 1|`.

Thus the mass defect is neither silently lost nor multiplied by the size of
the component: normalization contributes exactly one copy.

`BF4PhysicalVacuumSectorFullDensityMassDefectGap` packages a constructively
cofinal two-budget route.  A restricted full-density row bound `<= 1/32` for
every selected vacuum-sector source and a scalar vacuum-sector mass defect
`<= 1/32` at the same cutoff imply the conditioned density row bound `1/16`.
That estimate compiles to the corrected mass-normalized joint-row certificate
and then to the completed same-object vacuum-sector strict gap at `1/16`.

Focused monitored checks pass for both modules.  Exact-target one-worker
dependency-complete builds pass 1,485 jobs for the density-defect module and
1,486 jobs for the final two-budget gap target.  All 12 audited exports use at
most `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.

Neither `1/32` budget is inhabited.  The causal analytic frontier is now an
explicit fork: prove both full-density mixing on the restricted rows and
vacuum-sector mass concentration, or construct sector-normalized local
mixing directly and avoid the mass-concentration obligation.  No current
theorem proves that the canonical component mass approaches one.  The
unconditional completed gap, thermodynamic/continuum control, and the Clay
theorem remain open.

## Sector-local density-power gluing avoids the component-mass defect (2026-08-23)

`BF4PhysicalVacuumSectorLocalContractionGluing` extracts a generic finite
signed-`L1` tensorization theorem for a stationary density presented as two
endpoint steps and a middle power of one common local density.  Exact row and
column laws, exact density-power gluing at depth at least three, and a
centered one-step row rate `qS` give the explicit carrier-free estimate

`conditioned density row error <= qS * qS * qS^(depth - 2)`.

Consequently `qS <= 1/4` implies a uniform conditioned row bound `<= 1/16`.
The theorem is then specialized directly to the canonical vacuum-component
probability weight and conditioned physical density.  This route never
passes through the full-carrier stationary law and therefore introduces no
`|pi(S)-1|` component-mass defect.

`FixedNomeCofinalVacuumSectorLocalSliceGluing` packages one shared
sector-local step, its exact gluing depth, and its uniform quarter contraction
at every constructively selected cofinal cutoff.  Such a family compiles to
the corrected mass-normalized row certificate and then to the existing
completed same-object vacuum-sector strict gap at rate `1/16`.

The focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,485 jobs.  All eight audited exports use at
most `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.

No sector-local slice family is inhabited.  The next producer obligation is
to construct a shared sector-preserving one-step density with exact row and
column normalization, an exact finite density-power identity for the
conditioned physical density, and a cutoff-uniform centered rate `qS <= 1/4`.
The unconditional completed gap, thermodynamic/continuum control, and the
Clay theorem remain open.

## The sector-local compiler now consumes the exact depth-amplified rate (2026-08-23)

`BF4PhysicalVacuumSectorLocalPowerBudgetGap` removes the unnecessarily rigid
local condition `qS <= 1/4`.  It proves that the coefficient already produced
by signed-`L1` tensorization is exactly

`(qS * qS) * qS^(depth - 2) = qS^depth`

whenever the gluing depth is at least three.  Hence the local rate may depend
on the cutoff and may approach one: the actual uniform obligation is that its
complete depth-amplified power stay below one fixed rational `rate < 1`.

`FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing` records that exact
cofinal power budget.  It compiles the conditioned density-row estimate to
the corrected mass-normalized joint-row certificate and then to the existing
completed same-object vacuum-sector strict gap at the supplied uniform rate.
The earlier quarter-rate theorem remains a convenient sufficient special
case, but is no longer the only local-slice route.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,486 jobs.  All four audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  An initial check failed because one finite-density namespace had not
been opened; the namespace was added and the passing check and exact build
were rerun.

No local slice or depth-amplified budget is inhabited.  The next producer
frontier is now sharper: construct exact sector-local density-power gluing
and prove `qS(cutoff)^depth(cutoff) <= rate < 1`, rather than prove the
stronger cutoff-independent cap `qS <= 1/4`.  The unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## Cutoff-two reducibility rules out every strict full-carrier local slice (2026-08-23)

`BF4PhysicalFullCarrierLocalSliceObstruction` first generalizes the physical
row-to-form perturbation theorem from the hard-coded rate `1/16` to an
arbitrary rational rate.  A row estimate

`physical centered row <= rate * stationary source weight`

therefore gives the absolute centered quadratic estimate at exactly the same
rate.

Combining that theorem with the explicit nonzero centered eigenvalue-one mode
on the reducible cutoff-two positive carrier proves that no full-carrier
`PhysicalBF4LocalSliceGluing` can exist when

`(qS * qS) * qS^(depth - 2) < 1`.

This is stronger than ruling out the earlier `qS <= 1/4` sufficient case:
every strictly contracting depth-amplified full-carrier slice is impossible
at cutoff two, regardless of its proposed depth or one-step density.  Thus a
uniform campaign covering this cutoff cannot obtain its analytic witness by
inhabiting the old full-carrier interface and later restricting it.  The
slice itself must be constructed on the selected vacuum component (or an
equivalent sector-native carrier) from the outset.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,675 jobs.  All three audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Initial focused checks exposed missing namespace opens; those were
added before the passing check and exact build.

This theorem prunes a false producer route but does not construct the
sector-local slice or its power budget.  The unconditional completed gap,
thermodynamic/continuum control, and the Clay theorem remain open.

## Closed-sector conditioning commutes with every positive density power (2026-08-23)

`BF4PhysicalVacuumSectorConditionedDensityPower` proves a constructive finite
kernel theorem for an outgoing-closed sector: if the conditioned kernel is
the full kernel divided by the sector mass, then every positive-length
conditioned density power is exactly the corresponding full density power
multiplied by that mass.  At each intermediate convolution the density
rescaling cancels the restricted stationary weight, so there is one overall
component-mass factor rather than one accumulating mass defect per step.

The generic theorem is instantiated by the actual BF4 physical density.  Its
canonical root component is outgoing-closed by construction from graph
reachability, and the full indexed density vanishes from that component to
its complement.  Consequently the canonical vacuum-sector conditioned
density power is exactly the component mass times the full indexed physical
density power for every positive length and every pair of sector states.

This result supplies the exact restriction algebra needed by a future full
physical time-factorization: such a factorization can be transported to the
closed vacuum sector without paying a new component-mass defect at each
convolution.  It does not construct that factorization or a strict
sector-local contraction rate.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,486 jobs.  All four audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Initial focused checks exposed an unavailable local tactic, missing
namespace opens, a list-sum theorem used in the wrong direction, and a
missing graph-adjacency argument; all were corrected before the passing
focused check and exact build.

No exact physical time-factorization or strict sector-local power budget is
inhabited.  The unconditional completed gap, thermodynamic/continuum
control, and the Clay theorem remain open.

## Full time-factorization now restricts exactly to the BF4 vacuum sector (2026-08-23)

`BF4PhysicalVacuumSectorTimeFactorizationAdapter` isolates the next causal
producer into two mathematically distinct obligations.  First, a non-strict
full-carrier one-step density must have exact row and column normalization,
preserve the canonical vacuum component in both directions, and factor the
actual full physical density as a depth-`d` weighted density power.  Second,
only its conditioned restriction must satisfy a strict centered one-step
bound.  This formulation respects the cutoff-two theorem ruling out every
strict full-carrier slice.

The new total conditioned-kernel extension equals `mass * fullOneStep` on
sector endpoints and equals the stationary density one off the sector.  The
file proves constructively that outgoing and incoming closure make all its
conditioned rows and columns exactly normalized.  The earlier conditioning-
power theorem then transports a compatible full factorization to the actual
component-conditioned physical density at the same depth.

`PhysicalBF4VacuumSectorDensityPowerGluing` uses the natural power syntax:
power index `depth - 1` means exactly `depth` one-step factors.  Its direct
tensorization theorem gives the conditioned centered-row estimate
`qS^depth`, without routing through the older endpoint/middle/endpoint
association.  Thus the remaining strict estimate is explicitly sector-
native and the complete amplified rate is exposed with no mass defect.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,489 jobs.  All five audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Initial focused checks exposed missing namespace opens and one
off-sector column branch; those proof-engineering issues were corrected
before the passing focused check and exact build.

Neither the compatible full time-factorization nor the sector strict bound
is inhabited.  A cofinal direct-power compiler, the unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## Cofinal direct density powers now compile to the completed BF4 sector gap (2026-08-23)

`BF4PhysicalVacuumSectorDirectPowerBudgetGap` closes the compiler edge left
by the time-factorization adapter.  A constructively cofinal family of exact
conditioned density powers, together with one fixed strict budget
`localRate(base,threshold)^depth(base,threshold) <= rate < 1`, now compiles to
the corrected mass-normalized row-distance certificate and then to the
existing completed same-object vacuum-sector strict gap.

The module also exposes the full-factorization producer as one precise
certificate.  At every selected cutoff it asks for a normalized non-strict
full one-step density, exact component preservation and physical density-
power factorization, a centered bound only after conditioning on the vacuum
component, and the uniform depth-amplified power budget.  Its compiler first
uses the exact restriction adapter and then reaches the completed gap.  No
full-carrier strict estimate is requested.

The focused monitored check passes on its first run, and the exact-target
one-worker dependency-complete build passes 1,490 jobs.  All five audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.

No cofinal direct-power or compatible full-factorization family is inhabited.
The remaining finite analytic frontier is now exactly the construction of
that producer (or a sector-native equivalent).  The unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## The actual BF4 vacuum-sector centered boundary Gram is exact (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGram` replaces the artificial same-carrier
matrix-root search by the genuine heterogeneous physical time cut already
present in the BF4 model: lower-half states couple through complete
fixed-time boundary channels.  On the canonical vacuum component, the
module centers every physical half-amplitude against the component-
conditioned stationary weight.

Exact sector closure gives the two component first-moment identities and
the channel-total square identity.  These prove, without a spectral square
root, that the weighted Gram of the centered physical half-amplitudes is
exactly

`physicalJoint(left,right) - weight(left) * weight(right) / sectorMass`

for sector endpoints.  Consequently the corrected mass-normalized row
distance is bounded by a literal boundary-channel Tonelli majorant.
`FixedNomeCofinalVacuumSectorCenteredGramMajorant` packages only the
remaining analytic producer: a constructively cofinal uniform bound on this
explicit actual majorant by `rate * weight(source)`, for one `rate < 1`.  Its
compiler reaches the existing completed same-object vacuum-sector strict
gap directly, with no component-mass defect.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,487 jobs.  All five audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The initial focused run naturally reached the heartbeat limit after
namespace and reciprocal-normal-form errors; it was not manually
interrupted.  Those proof-engineering issues were corrected before the
passing focused check and exact build.

No cofinal majorant bound is inhabited.  The next finite analytic frontier
is to factor the explicit sector-centered Gram majorant into target and
source boundary-posterior deviations and isolate the corresponding uniform
mixing estimates.  The unconditional completed gap, thermodynamic/continuum
control, and the Clay theorem remain open.

## The BF4 sector Gram majorant factors into two physical profiles (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramProfiles` splits the literal actual
boundary-Gram Tonelli majorant into two independently meaningful quantities:
the total absolute centered target profile at one fixed-time boundary
channel, and the channel-weighted centered boundary profile visible from one
vacuum-sector source state.

The module proves the exact causal estimate

`rowMajorant <= targetRate * sourceDeviation`

and then, from `sourceDeviation <= sourceRate * weight(source)`, obtains

`rowMajorant <= (targetRate * sourceRate) * weight(source)`.

Thus strictness belongs to the product of the two physical mixing rates;
neither factor is arbitrarily fixed to a quarter.  The cofinal two-profile
certificate compiles this product directly through the actual centered-Gram
majorant to the completed same-object vacuum-sector strict gap.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,488 jobs.  All four audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused check exposed missing namespace opens and one
associativity direction; both were corrected before the passing focused
check and exact build.

No profile bounds are inhabited.  The next frontier is to normalize the two
sector profiles as target-given-boundary and boundary-given-source posterior
`L1` distances, including zero-channel handling, so the remaining estimates
are stated as explicit conditional mixing.  The unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## The BF4 vacuum-sector profiles are exact posterior distances (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramPosterior` constructs the two genuine
conditional laws on the actual finite physical carriers.  The target law is
the sector state conditioned on a positive fixed-time boundary channel.  The
source law is the boundary channel conditioned on a sector source, and its
reference law is the sector square-amplitude boundary prior.

The module first proves generic weighted-Gram normalization and Bayes
identities.  In the BF4 sector specialization, the target conditional,
boundary prior, and source conditional are pointwise nonnegative on their
literal carriers and each has total mass one.  It then proves the exact
unnormalizations

`targetProfile(boundary) = channelTotal(boundary) * targetPosteriorL1`

and

`sourceProfile(source) = physicalWeight(source) * sourcePosteriorL1`.

Channels of zero total are discharged constructively from nonnegativity; no
positivity decision or classical branch is hidden.  Therefore cofinal bounds
on the two posterior `L1` distances, with product strictly below one, compile
through the actual centered boundary Gram to the completed same-object
vacuum-sector strict gap.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,490 jobs.  All twelve audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused run naturally reached the deterministic heartbeat
limit after missing namespace opens left downstream types unresolved; it was
not manually interrupted.  After those opens were corrected, one function-
arity mismatch was exposed and fixed before the passing focused check and
exact build.

No cofinal posterior-mixing family is inhabited.  The next finite analytic
frontier is now an explicit uniform estimate on the two actual conditional
laws (or a projective/coupling criterion that implies it), with product rate
strictly below one.  The unconditional completed gap,
thermodynamic/continuum control, and the Clay theorem remain open.

## One sector half-amplitude diameter controls both posteriors (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramProjective` reduces the two posterior
mixing estimates to one division-free four-index inequality for the actual
vacuum-sector half-amplitude matrix.  It first proves constructively that
projective spread is unchanged when either or both rays are divided by
positive common normalizations.

The existing positive-summation closure is then specialized to the canonical
sector.  A single half-amplitude cross-ratio field survives the weighted
column sum and becomes projective control of
`target | boundary` versus the sector stationary law.  The same field
survives the row sum and becomes projective control of
`boundary | source` versus the sector square-amplitude prior.  Exact sector
moments supply all normalization factors.

At squared spread at most `65/64`, the normalized-projective theorem bounds
each posterior `L1` distance by `1/4`.  Their product is the semantic rate
`1/16`, and the cofinal half-amplitude projective certificate compiles all
the way to the completed same-object vacuum-sector strict gap.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,494 jobs.  All seven audited
exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused run naturally reached the deterministic heartbeat
limit after missing namespace opens left dependent types unresolved; it was
not manually interrupted.  Adding the required stationary-law and quarter-
constant namespaces resolved all reported errors before the passing focused
check and exact build.

No cofinal half-amplitude projective family is inhabited.  The next causal
frontier is to inspect the actual sector amplitude support: either prove the
uniform `65/64` cross-ratio estimate, or exhibit a support obstruction and
replace this sufficient criterion by a support-compatible coupling or
multi-step estimate.  The unconditional completed gap,
thermodynamic/continuum control, and the Clay theorem remain open.

## The cutoff-two vacuum sector obstructs every finite projective spread (2026-08-23)

`BF4PhysicalVacuumSectorProjectiveObstruction` resolves the first branch of
that frontier negatively.  The exact cutoff-two vacuum half-amplitude row is
zero at the explicit non-vacuum single-face boundary, while the fundamental-
cube row is strictly positive there and the vacuum-to-vacuum corner is
strictly positive.  The canonical-vacuum-sector theorem places the cube in
the literal 65-state vacuum component.

These four entries form a support rectangle whose projective inequality has
a strictly positive left side and a zero right side.  Hence no rational
spread of any size can satisfy the proposed half-amplitude cross-ratio field
on the cutoff-two canonical sector and full physical boundary carrier.  This
is an obstruction to that sufficient criterion, not an obstruction to
posterior mixing itself.

The focused monitored check passes after adding one missing namespace open,
and the exact-target one-worker dependency-complete build passes 3,583 jobs.
All three audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.

This finite result does not rule out a cofinal family that skips cutoff two.
The next causal frontier is therefore a support-compatible overlap,
minorization, coupling, or multi-step estimate for the two exact posterior
laws.  No such cofinal bound is yet inhabited.  The unconditional completed
gap, thermodynamic/continuum control, and the Clay theorem remain open.

## Posterior overlap replaces the obstructed projective criterion (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramOverlap` introduces the canonical common
submass `sum_x min(p(x),q(x))` for finite rational laws.  It proves first, at
the generic finite level, that removing any common submass leaves two
nonnegative residuals whose total controls `L1`.  For normalized laws this
gives the support-compatible estimate

`L1(p,q) <= 2 * (1 - overlap(p,q))`.

Unlike a projective ratio, this bound permits zeros and therefore remains
applicable to the actual cutoff-two support pattern.  The module specializes
the overlap to both exact sector laws: `target | boundary` versus the sector
stationary law, and `boundary | source` versus the square-amplitude boundary
prior.  Cofinal overlap floors `alpha` and `beta` now compile to the completed
same-object vacuum-sector strict gap whenever

`[2(1-alpha)] * [2(1-beta)] < 1`.

The corrected focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,491 jobs.  All seven audited exports use at
most `[propext, Quot.sound]`; the four generic finite exports use only
`[propext]`.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration was added.  The first focused run naturally
reached the deterministic heartbeat limit after two raw-denominator
normalizations and missing namespace opens caused cascading elaboration
errors.  It was not manually interrupted.  Structural exact-rational
identities and the correct physical namespaces resolved every error before
the passing focused check and exact build.

No cofinal overlap floors are inhabited.  The next analytic frontier is to
derive positive uniform common mass for the two physical posterior pairs,
potentially after a fixed number of support-compatible steps.  The
unconditional completed gap, thermodynamic/continuum control, and the Clay
theorem remain open.

## Both physical posterior overlaps are positive at every finite cutoff (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramOverlapPositivity` proves that the new
overlap quantities are genuinely inhabited rather than formal placeholders.
A generic finite argument extracts a positive atom from a normalized
nonnegative law and shows its overlap is positive whenever the reference law
is positive on that atom.

For `target | boundary`, the reference is the sector stationary law, already
strictly positive at every canonical vacuum-sector index.  For
`boundary | source`, the module proves the missing physical support inclusion
directly: positivity of the exact conditioned Bayes numerator forces positive
boundary weight and positive channel total, hence positive square-amplitude
prior mass at the same channel.  No global full-support hypothesis is used.

Therefore, for every fixed finite cutoff, each positive target boundary
channel and each canonical sector source has posterior overlap strictly
between zero and one inclusive.  The focused monitored check passes after two
missing namespace opens were added, and the exact-target one-worker
dependency-complete build passes 1,492 jobs.  All seven audited exports use at
most `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.

The result supplies no cutoff-uniform quantitative floor: the positive
rationals may tend to zero along a cofinal sequence, and positivity alone does
not make either residual `L1` rate smaller than one.  The next frontier is to
construct the exact minimum overlap over each finite carrier and isolate the
single persistence estimate needed to keep those minima uniformly above the
threshold required by the product-rate gap.  Thermodynamic/continuum control
and the Clay theorem remain open.

## Every finite carrier contracts to two exact positive overlap floors (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramOverlapFloor` defines a constructive
capped minimum by folding `Q'.min'` from one.  Target channels of zero total
and natural indices outside the canonical sector are assigned the neutral
value one, so the total functions remain positive while agreeing with the
actual posteriors on every relevant carrier member.

Folding over the literal fixed-time boundary list and canonical vacuum-sector
index list produces exact target and source overlap floors.  Both floors are
strictly positive and at most one at every fixed cutoff, and each is proved to
bound every corresponding physical posterior overlap.  Thus all pointwise
finite mixing obligations are reduced to two exact rational scalars.

A cofinal persistence structure records uniform lower bounds on only those
two scalars and compiles them through the overlap and posterior layers to the
completed same-object vacuum-sector strict gap whenever the residual-rate
product is below one.

The corrected focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,493 jobs.  All seven audited exports use at
most `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  The first
focused check exposed three elementary positive-one goals that `decide` could
not close while their expected types retained free variables; explicit type
annotations resolved them before both passing checks.

No uniform floor persistence is inhabited.  The next causal contraction is
to combine the two exact floors into the one finite residual-rate scalar
consumed by the centered Gram and make a uniform cofinal upper bound below one
the sole analytic obligation.  Thermodynamic/continuum control and the Clay
theorem remain open.

## Posterior mixing is reduced to one exact finite residual-rate sequence (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate` defines the target
and source support-compatible rates `2(1-alpha_K)` and `2(1-beta_K)` from the
two exact finite overlap floors, then defines their product `r_K` as the sole
finite scalar consumed downstream.

The module proves successively that `r_K` is nonnegative; each actual target
and source posterior `L1` distance is bounded by its corresponding floor rate;
the two physical profile deviations inherit those rates; and the literal
actual centered-Gram row majorant is bounded by

`r_K * physicalWeight(source)`.

A constructively cofinal certificate now asks only for anchors at which
`r_K <= q` for one fixed rational `q < 1`.  That one scalar estimate compiles
directly through the centered Gram to the completed same-object vacuum-sector
strict gap.  Separate uniform target/source floors are no longer necessary.

The corrected focused monitored check passes after adding one missing
positive-connectivity namespace, and the exact-target one-worker dependency-
complete build passes 1,494 jobs.  All seven audited exports use at most
`[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration was added.

No cofinal upper bound `r_K <= q < 1` is inhabited.  The next finite diagnostic
frontier is to evaluate or characterize this exact scalar on the already
solved cutoff-one model and then isolate which cutoff-growth estimate must
prevent it from approaching one.  Thermodynamic/continuum control and the
Clay theorem remain open.

## The exact posterior-overlap residual rate is uniformly below four (2026-08-23)

`BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling` uses the already
proved strict positivity of both exact finite overlap floors to prove that
each residual factor `2(1-alpha_K)` and `2(1-beta_K)` is strictly below two.
Nonnegativity and monotonic multiplication then give the unconditional
all-cutoff estimate

`0 <= r_K < 4`.

This is the first cutoff-uniform bound on the single exact scalar controlling
the literal centered-Gram row majorant.  It is intentionally not presented as
a contraction or gap result: the completed compiler needs `r_K <= q` for one
fixed `q < 1`, whereas the proved ceiling is four.  The remaining analytic
improvement is therefore quantitatively pinned to crossing the exact scalar
threshold from `< 4` to a cofinal uniform `< 1`.

The focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,495 jobs in 269 seconds.  All three audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.

No cofinal upper bound below one is inhabited.  The next causal frontier is
to determine whether the solved cutoff-one physical block identifies the
canonical-sector scalar exactly, and then to isolate a support-stable
all-cutoff overlap mechanism strong enough to improve the ceiling below one.
Thermodynamic/continuum control and the Clay theorem remain open.

## The cutoff-one vacuum/cube block is exactly the canonical vacuum sector (2026-08-23)

`BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape` first transports the already
proved zero of every normalized two-row target outside `{vacuum,cube}` back
to the raw reflected kernel by multiplying through the strictly positive row
mass.  Decidable natural-number state codes, rather than equality branching
on function-valued labellings, then prove that one support-graph edge cannot
leave the block without introducing `Classical.choice`.

`BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector` propagates that one-step
closure along every chain in the rooted support component.  In the converse
direction, the exact vacuum-to-cube reflected-kernel entry is strictly
positive, so the cube index is in the component.  The resulting support
theorem is exact for every rational `w > 0`:

`state in canonicalVacuumSectorStates(w, K=1, half=0)`
`  iff state in [vacuum, centralLowerCubeState]`.

Focused monitored checks pass for both modules.  Exact-target one-worker
dependency-complete builds pass 1,398 and 1,399 jobs; all six audited exports
use exactly `[propext, Quot.sound]`.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Direct branching on labelling equality was rejected after its audit
exposed `Classical.choice`; the final proof branches on the faithful finite
state code.  Earlier long exploratory checks and the broad `YMGapGuard` run
were interrupted and are not counted as passing audits.

This finite support equality is not a cutoff-uniform sector theorem.  It
provides the prerequisite for evaluating the exact canonical posterior-
overlap residual scalar at cutoff one.  A cofinal bound `r_K <= q < 1`,
thermodynamic/continuum control, and the Clay theorem remain open.

## The cutoff-one canonical vacuum sector is an exact posterior-refresh block (2026-08-23)

`BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh` joins the exact
rooted-component support theorem to the previously verified genuine
vacuum/cube Gram rows.  Every source state in the actual canonical vacuum
sector therefore has the same posterior-refresh Markov row on the complete
positive target carrier.  Restriction to the exact two-state support remains
normalized, constants are fixed, and the explicit nonconstant
posterior-centered cube mode is annihilated in one step.

This is the first theorem that places the solved rank-one physical transfer
block on the graph-defined canonical vacuum sector rather than on a displayed
two-state surrogate.  The focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,402 jobs.  All four audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused check failed only because `EdgeLabelling` resolved
to a generic namespace; opening the concrete SU(2) labelling namespace fixed
the type and the corrected check passed.

The result is finite at `K = 1` and does not yet identify the indexed
sector-conditioned stationary law with the refresh posterior.  That
normalization bridge is the next prerequisite for evaluating the exact
target/source overlap floors and their residual scalar `r_1`.  A cofinal
bound `r_K <= q < 1`, thermodynamic/continuum control, and the Clay theorem
remain open.

## The cutoff-one canonical index presentation is exactly two-state and multiplicity-free (2026-08-23)

`BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation` strengthens
the cutoff-one state-support equivalence to a multiplicity-preserving list
equivalence.  It proves that totalized carrier lookup is injective on the
canonical component, the mapped canonical state list is nodup, and that list
is a permutation of `[vacuum, central cube]`.  A reusable theorem therefore
transports every rational `listQSum` from the canonical index presentation to
the explicit two-state presentation without selecting inverse
representatives.

The corrected focused monitored check passes, and the exact-target
one-worker dependency-complete build passes 1,403 jobs.  All four audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Two failed focused checks exposed only a reversed associativity step
in the local permutation-sum proof and a missing namespace for the totalized
vacuum fallback; both were corrected before the passing audit.

This is still finite at `K = 1`.  It removes the normalization multiplicity
ambiguity but does not yet prove that the indexed sector-conditioned
stationary law equals the refresh posterior.  That equality, the exact
overlap floors and `r_1`, a cofinal `r_K <= q < 1`, thermodynamic/continuum
control, and the Clay theorem remain open.

## The cutoff-one component-conditioned stationary law is exactly the refresh posterior (2026-08-23)

`BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior`
computes the normalization inherited from the genuine finite physical joint
law.  It first proves that every physical row marginal is the raw positive-row
mass times the common finite partition reciprocal.  The solved cutoff-one
vacuum/cube rows then give the exact relative marginal identity

`marginal(cube) = coeffW(w,1)^6 * marginal(vacuum)`.

Transport across the multiplicity-free two-state presentation proves that the
canonical component mass is the vacuum-column denominator times the vacuum
marginal.  Positive-mass cancellation consequently identifies, pointwise on
every actual canonical index, the component-conditioned stationary weight
with the genuine vacuum-column refresh posterior.

The corrected focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,548 jobs.  All four audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  During proof
development one long exploratory check was intentionally interrupted, and
three bounded failed checks exposed an expensive rational ring step, a missing
list-sum namespace, and global reduction caused by substituting a let-bound
state.  Explicit rational equality chains, the correct namespace, and two
state-specific posterior-times-mass lemmas resolved those issues; only the
final passing checks are counted as verification.

This remains an exact `K = 1`, half-extent-zero result.  The next finite
contraction is to use the common refresh row and this stationary-law identity
to prove both target/source posterior overlap floors equal one and hence the
exact residual mixing scalar `r_1` is zero.  A fixed cofinal bound
`r_K <= q < 1`, thermodynamic/continuum control, and the Clay theorem remain
open.

## The cutoff-one physical amplitude is rank one and its overlap residual vanishes (2026-08-23)

`BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual` proves
directly on every literal fixed-time boundary channel that the central-cube
half-amplitude is `coeffW(w,1)^6` times the vacuum half-amplitude.  Exact
two-state recoding then gives the genuine indexed factorization

`amplitude(index,boundary)`
`  = stationaryWeight(index) * channelTotal(boundary)`.

This is stronger than merely observing equal transfer rows: it exposes the
rank-one state/boundary factorization before the Gram contraction.  As exact
Bayes consequences, every positive-channel target posterior equals the
component-conditioned stationary law, and every canonical source posterior
on boundary channels equals the common boundary prior.  Therefore both actual
posterior overlaps and both capped finite overlap floors equal one.  The
single exact scalar consumed by the centered-Gram compiler consequently
satisfies

`r_1 = 0`.

The corrected focused monitored check passes in 1.2 seconds, and the exact-
target one-worker dependency-complete build passes 1,556 jobs.  All seven
audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first exploratory check was intentionally interrupted after ten
minutes.  Two subsequent low-heartbeat diagnostics exposed missing namespaces
and an expensive generic rational distributivity step; explicit namespace
opens and the exact chain `v + A*v = 1*v + A*v = (1+A)*v` resolved them.
Only the final passing checks are counted as verification.

The equality `r_1 = 0` is a solved finite base case, not a cofinal estimate.
The next causal frontier is to isolate an all-cutoff support-stable defect from
this rank-one factorization and prove that its contribution keeps the exact
sequence `r_K` below one on a constructively cofinal family.  The completed
uniform gap, thermodynamic/continuum QFT, and Clay theorem remain open.

## The physical posterior frontier is sharpened to exact finite L1 maxima (2026-08-23)

`BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate` removes the slack caused
by passing first through overlap lower bounds.  It totalizes each actual
target- and source-posterior `L1` defect by zero off its relevant carrier,
takes a located finite maximum of each family, and defines their product

`s_K = maxBoundaryL1_K * maxSourceL1_K`.

Both maxima and `s_K` are nonnegative.  Every actual target/source posterior
defect is bounded by its corresponding exact maximum, so the existing Bayes
profile factorization proves the literal centered physical Gram row bound

`rowMajorant_K(source) <= s_K * physicalWeight_K(source)`.

A constructively cofinal fixed upper bound `s_K <= q < 1` now compiles
directly to the completed same-object vacuum-sector strict gap.  This is a
strictly weaker analytic interface than the previous overlap-residual one:
the module proves `s_K <= r_K` at every finite cutoff.  The cutoff-one
rank-one theorem also evaluates both exact maxima and their product to zero.

The corrected focused monitored check passes in 0.83 seconds, and the exact-
target one-worker dependency-complete build passes 1,557 jobs.  All eight
audited exports use at most `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused check failed only on an ambiguity between two
definitionally identical names for `finiteL1Distance`; qualifying the genuine
physical boundary-posterior definition resolved it before both passing
checks.

No cofinal bound on `s_K` is inhabited.  The next exact contraction is to
take the located maximum of the physical centered-Gram row majorant divided by
its strictly positive stationary source weight.  That scalar is no larger
than `s_K` and removes the remaining product-of-maxima slack.  A uniform
below-one estimate, thermodynamic/continuum control, and the Clay theorem
remain open.

## The physical centered-Gram frontier is contracted to its exact row rate (2026-08-23)

`BF4PhysicalVacuumSectorExactCenteredGramRowRate` totalizes, on every actual
finite source index, the centered physical Gram row majorant divided by its
strictly positive component-conditioned stationary weight.  Its located
finite maximum is the exact common row coefficient

`g_K = max_source rowMajorant_K(source) / physicalWeight_K(source)`.

Every centered row is bounded by `g_K` times its source weight.  Conversely,
any nonnegative rational coefficient that bounds all of those rows also bounds
`g_K`; thus this is the least coefficient available from the literal finite
row inequalities, rather than another sufficient upper estimate.  A
constructively cofinal fixed estimate `g_K <= q < 1` compiles directly to the
completed same-object vacuum-sector strict gap.  The comparison ladder

`g_K <= s_K <= r_K`

is proved at every finite cutoff, and the rank-one cutoff-one calculation
evaluates the sharp scalar exactly as `g_1 = 0`.

The focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,558 jobs.  All seven audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.

No cofinal bound on `g_K` is inhabited.  The remaining finite analytic
frontier is now irreducible within the current row-majorant architecture:
prove a single constructively cofinal `g_K <= q < 1`, or introduce additional
finite geometry that strictly improves the literal centered-row estimate.
The unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
remain open.

## The physical row frontier retains cancellations through the actual kernel (2026-08-23)

`BF4PhysicalVacuumSectorExactMassNormalizedRowRate` removes the remaining
Tonelli slack from the sufficient finite scalar.  It takes the literal row
distance between the physical joint and the stationary product conditioned on
the canonical vacuum component, divides each canonical source row by its
strictly positive stationary weight, and forms the located finite maximum

`h_K = max_source actualRowDistance_K(source) / physicalWeight_K(source)`.

Every actual mass-normalized row is bounded by `h_K` times its source weight.
Conversely, every nonnegative rational coefficient satisfying all literal row
inequalities bounds `h_K`, so `h_K` is the least coefficient at the exact
row-distance interface.  A constructively cofinal fixed bound
`h_K <= q < 1` compiles directly to the completed same-object vacuum-sector
strict gap.  The comparison theorem establishes the sharpened ladder

`h_K <= g_K <= s_K <= r_K`,

and the cutoff-one rank-one calculation gives `h_1 = 0`.

The corrected focused monitored check passes, and the exact-target one-worker
dependency-complete build passes 1,559 jobs.  All seven audited exports use
exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration was added.  Three earlier
focused checks failed on missing sector-law namespace opens and one redundant
unfold after the goal had already reduced; none is counted as a pass.

No cofinal bound on `h_K` is inhabited.  The remaining row-distance frontier
is the actual finite analytic statement: prove one fixed constructively
cofinal `h_K <= q < 1`.  Further algebraic progress must either estimate this
literal scalar from BF4 geometry or pass below rowwise total variation to a
sharper signed-form/operator coefficient.  The unconditional completed gap,
thermodynamic/continuum QFT, and Clay theorem remain open.

## The exact row scalar and executable finite checker are equivalent (2026-08-23)

`BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker` identifies the new
sharp scalar with the existing exact Boolean scan.  For every nonnegative
rational `q`, it proves the biconditional

`allRowsCheck_K(q) = true  <->  h_K <= q`.

The proof first identifies one Boolean row check with its literal
mass-conditioned row inequality, then lifts that equivalence through the
canonical vacuum-sector list, and finally uses the defining least-coefficient
property of `h_K`.  The Type-level constructively cofinal exact-rate family
and the constructively cofinal checked-row family convert in both directions,
so the executable and analytic frontiers now contain exactly the same
quantifiers and no comparison slack.  At cutoff one, the rank-one result
produces the actual certificate `allRowsCheck_1(0) = true`.

The focused monitored check passes on the first attempt, and the exact-target
one-worker dependency-complete build passes 1,560 jobs.  All six audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.

No nontrivial cofinal scan is asserted.  The next finite diagnostic is the
cutoff-two row criterion: the already-proved `49/50` cutoff-two signed-form
gap does not logically imply a row-total-variation bound at the same rate, so
that stronger Boolean statement must be evaluated or proved separately.  A
uniform cofinal strict rate, thermodynamic/continuum QFT, and the Clay theorem
remain open.

## Cutoff two obstructs the stronger physical row-TV route (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction` proves that the exact
mass-normalized row-total-variation criterion is already superunit on one
actual production-kernel row at cutoff two.  An untrusted Python diagnostic
first located rows `10`, `19`, and `37` and computed the table maximum as

`12557268462086759048710571458930572244006473246401451415552`
`/ 6280167100747004266260229105393860824732559645509611405537`

(approximately `1.9995118379243628`).  Lean then checked, independently of
that diagnostic, the exact raw component mass and the denominator-cleared
row-ten distance and proved the strict inequality

`physicalMass * physicalRowSum(10)`
`  < physicalClearedMassNormalizedRowDistance(physicalMass, 10)`.

The proof transports the literal arithmetic result through the previously
sealed shared-DAG certificate to the genuine production reflected kernel.
Thus the stronger rowwise sufficient condition cannot supply any rate
`q < 1` at cutoff two.  This does not contradict the existing cutoff-two
signed centered-form contraction at `49/50`: the form theorem retains
cancellations that row total variation discards.  It also does not rule out a
subunit row criterion on some later cofinal cutoff family.

The corrected focused monitored check passes in 6.2 seconds, and the exact-
target one-worker dependency-complete build passes 3,419 jobs.  The three raw
arithmetic exports use no axioms; the three production-kernel transport
exports use exactly `[propext, Quot.sound]`.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  A first aggregate raw-kernel prerequisite build was stopped by the
safety wrapper at its 12 GiB memory reserve, and the first narrowed focused
check exposed a missing namespace open; neither interrupted/failed run is
counted as verification.

The immediate coordinate frontier is to identify this row-ten witness with
the named canonical exact scalar `h_2`.  Analytically, however, the viable
cofinal route now has to preserve signed form/operator cancellations rather
than demand row-TV contraction at every cutoff.  A cofinal signed-form
certificate, completed uniform gap, thermodynamic/continuum QFT, and the Clay
theorem remain open.

## The cutoff-two row-TV obstruction survives physical normalization (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction` proves
that the row-ten obstruction is invariant under the common positive physical
partition normalization.  A sealed dependent certificate now packages the
normalization scale, its positivity, and the exact kernel and row-mass
transport laws.  This prevents the checker from expanding the enormous
partition expression while preserving the kernel-checked provenance of every
downstream equality.

The module proves that the normalized component mass is the raw physical
component mass times the common scale, while the normalized cleared centered
row distance is the physical cleared distance times the square of that scale.
The left side of the unit row bound acquires the same positive square.
Consequently Lean proves the exact strict inequality

`normalizedMass * normalizedRowSum(10)`
`  < normalizedClearedMassNormalizedRowDistance(normalizedMass, 10)`.

The corrected focused monitored checks pass in about 1.3 seconds.  The exact
normalization module target passes 4,684 jobs, and the new exact-target
one-worker dependency-complete build passes 4,686 jobs.  All three audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Development checks that timed out while comparing opaque and
transparent partition representatives, failed on record syntax or namespace
opens, terminated with a Lean expression-equality stack exception, or were
intentionally interrupted after diagnostic `#exit` probes are not counted as
verification.  Factoring the algebra into generic scale-transport lemmas made
the final check small and stable.

This is still a finite cutoff-two theorem.  The next coordinate frontier is
the canonical state-list permutation and the resulting statement for the
named exact scalar `h_2`.  The viable analytic frontier remains a
cancellation-preserving cofinal signed-form or spectral certificate; the
completed uniform gap, thermodynamic/continuum QFT, and Clay theorem remain
open.

## The named cutoff-two canonical row rate is superunit (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction` closes the
coordinate bridge from the normalized 65-state table to the named production
scalar `h_2`.  It extracts the canonical vacuum-sector index whose state is
table row ten, transports the normalized component mass through the exact
state-list permutation, and identifies the canonical denominator-cleared row
distance with the already-certified normalized row-ten value.  The resulting
strict product inequality contradicts the defining row bound for any
hypothesis `h_2 <= 1`; hence Lean proves both `not (h_2 <= 1)` and `1 < h_2`.

This eliminates the exact mass-normalized row-total-variation coefficient as
a subunit mechanism already at cutoff two.  It does not contradict the
cutoff-two `49/50` signed centered-form theorem, which retains cancellations
discarded by row absolute values, and it does not prove any cofinal or
continuum statement.

The final focused monitored check passes in about 2.8 seconds, and the exact-
target one-worker dependency-complete build passes 4,790 jobs.  All five
audited exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Several direct concrete wrappers and a source-indexed Type-valued
seal were intentionally interrupted after exceeding 30--180 seconds; one
probe exposed a missing namespace qualification.  None is counted as a
pass.  Replacing the expensive canonical mass-positivity wrapper by transport
from the proved normalized positive mass restored a small stable proof.

The next honest frontier is therefore cancellation-preserving: construct or
factor a cofinal signed-form/upper-LDL certificate that controls the actual
vacuum-sector quadratic form uniformly.  A uniform completed gap,
thermodynamic/continuum QFT, and the Clay theorem remain open.

## Upper-only canonical LDL families now reach same-object form limits (2026-08-23)

`BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge` now compiles both ordinary
and shardable cleared-denominator *upper-only* canonical LDL families into
the exact two-parameter same-object certificate
`FixedNomeCofinalVacuumSectorCenteredStrictGap`.  At each reindexed anchor,
the upper LDL check proves `K <= qD` for the zero-extended centered
coefficient.  Exact carrier recoding transports that inequality to the pulled
vacuum-sector form, while the existing finite Gram/reflection-positivity
theorem proves `0 <= K`; therefore `|K| <= qD` without a lower LDL check or a
row-total-variation majorant.

Both new routes then feed the existing Cauchy theorem and prove the literal
`CReal.leEv` comparison between the centered reflected-form cutoff limit and
`q` times the centered diagonal-form cutoff limit.  Thus the
cancellation-preserving upper-LDL interface now reaches the same object whose
limit is used by the vacuum-sector program.

The focused monitored check passes in about 1.3 seconds, and the exact-target
one-worker dependency-complete build passes 4,755 jobs.  All four new audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  A direct local reproving of pulled reflection positivity was
intentionally interrupted after prolonged elaboration and is not a pass; the
final proof reuses the already kernel-checked positivity theorem.

No cofinal upper-LDL family is constructed.  The next analytic frontier is
an honest inhabitant at one rate `0 <= q < 1`, ideally via a checkable
cutoff-dependent upper matrix certificate plus a uniform tail argument.
Completion, volume/spacing uniformity, continuum QFT, and the Clay theorem
remain open.

## Canonical LDL checks are reduced to the vacuum component itself (2026-08-23)

`BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge` removes a remaining
certificate-scope mismatch.  It totalizes the duplicate-free canonical
vacuum-sector list into coordinates `0, ..., n-1` and proves exact reindexing
of the physical sector weighted mean, diagonal quadratic, and reflected
matrix quadratic.  Nonemptiness and positivity of every retained sector
weight give a positive coordinate-zero head, so the generic canonical
head-centered restriction is constructed directly on this sector-local
matrix.

Ordinary and shardable cleared upper-only LDL certificates for the generated
sector restriction prove the fixed-cutoff absolute centered gap by reflection
positivity.  Cofinal families of those smaller certificates then compile to
`FixedNomeCofinalVacuumSectorCenteredStrictGap` and to the same literal
`CReal.leEv` cutoff-limit inequality as the prior full-carrier route.  This is
a genuine weakening of the open input: disconnected positive-carrier
components no longer appear in the required matrices.

The focused monitored check passes in about 1.3 seconds, and the exact-target
one-worker dependency-complete build passes 4,756 jobs.  All ten audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Two initial focused checks failed on omitted namespace opens and one
unfold ordering; neither is counted as a pass.

No cofinal sector-local certificate is inhabited.  The next concrete
frontier is to identify the already-proved cutoff-two `49/50` signed-form/LDL
data with this generated sector-local restriction, establishing the first
nontrivial finite inhabitant before seeking an unbounded uniform schedule.
The completed gap, volume/spacing control, continuum QFT, and Clay theorem
remain open.

## The generated sector-local upper certificate is inhabited at cutoff two (2026-08-23)

`BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge` now separates the
order-invariant content of an upper matrix certificate from any particular
triangular LDL presentation.  A structurally recursive ambient coordinate
lift has an exact right-inverse theorem on the duplicate-free sector list.
Consequently any physical mean-zero absolute sector estimate transports to
the generated coordinate order, and it packages constructively as upper PSD
of the canonical head-centered restriction.  The generic PSD interface then
proves the same centered upper contraction as an LDL certificate.

`BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate` applies
that compiler to the already verified cutoff-two canonical gap at `49/50`.
It constructs an actual witness for the exact generated sector-local upper
restriction, proves its reduced matrix is nonnegative on every vector, and
derives the coordinate mean-zero upper gap.  This avoids the invalid move of
permuting the historical triangular LDL factors while preserving their
proved signed-form consequence.

The bridge focused check passes in about 1.5 seconds, the cutoff-two focused
check in about 1.8 seconds, and the exact one-worker target passes 4,757 jobs.
All newly audited exports use exactly `[propext, Quot.sound]`; no
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration was added.  Two monitored checks were deliberately
interrupted while an unresolved `cutoffTwoHalfCoupling` name caused massive
elaboration; a diagnostic version then exposed `Classical.choice` in a
multi-pattern `idxOf` inverse proof.  Neither run is counted as a pass.  The
final structurally recursive lookup removes that dependency and restores the
axiom gate.

This is a genuine finite inhabitant at cutoff two only.  No cofinal family at
one uniform strict rate has been constructed.  That all-cutoff analytic
input, the completed vacuum-complement gap, volume/spacing control,
continuum QFT, and the Clay theorem remain open.

## Cofinal sector-local upper PSD now reaches the completed transfer (2026-08-23)

`BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge` now defines a
constructively cofinal family of order-invariant upper-PSD witnesses for the
generated canonical sector restriction.  At any supplied `0 <= q < 1`, that
family compiles to the same-object moving centered strict-gap interface and
its literal `CReal.leEv` matrix-versus-diagonal cutoff-limit inequality.

`BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge` isolates an even
more direct analytic input: exact physical mean-zero absolute sector gaps at
one strict rate along an unbounded cofinal cutoff schedule.  It converts each
such gap to the generated upper-PSD restriction, then contracts the family
through the existing same-object interface and the independently proved
completed positive-form Cauchy--Schwarz law.  The endpoint is the actual
`CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`, not only
a finite matrix statement.

The local bridge focused check passes in about 1.6 seconds.  The new cofinal
compiler focused check passes in about 1.1 seconds, and its exact one-worker
dependency-complete target passes 4,884 jobs.  All six newly audited cofinal
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Three abnormal elaboration runs around a redundant CReal wrapper were
interrupted and are not passes; diagnostic `#exit` boundaries located that
wrapper, which was removed because the underlying PSD bridge already exports
the same CReal theorem.

No cofinal finite strict-gap or upper-PSD family is inhabited.  The cutoff-two
`49/50` witness proves only the first finite anchor.  The next genuine
analytic frontier is uniform strict persistence on an unbounded cutoff
schedule; after that, volume/spacing-uniform completion and the continuum QFT
and Clay targets remain open.

## Cutoff-two signed control is expanded to the full growing sector (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence` addresses the precise
scope deficit left by zero extension.  For an arbitrary centered vector on a
later full vacuum sector, a persistence certificate supplies a recentered
cutoff-two core, a relative matrix-tail error `epsilon`, and a diagonal
inflation factor `lambda`.  The verified cutoff-two theorem then proves the
later full-sector bound at the exact composed rate

`(49/50) * lambda + epsilon`.

The finite anchor is genuinely inhabited: at cutoff two, identity
recentering, zero matrix error, and unit diagonal inflation satisfy every
field and recover the original strict gap.  A constructively cofinal family
of these full-sector comparisons compiles to the cofinal finite strict-gap
interface and hence to the actual completed vacuum-sector transfer
contraction.

The focused monitored check passes in about 2.3 seconds, and the exact
one-worker dependency-complete target passes 4,885 jobs.  All five audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.

No later-cutoff or cofinal comparison is inhabited.  The next expansion is
to derive its two comparison fields from the existing exact old/new
four-block identity: old-old drift, the two cross blocks, the new-new block,
and the new-sector diagonal contribution.  Uniform control of those residuals
is the genuine analytic frontier; completion beyond the fixed nome/volume,
continuum QFT, and the Clay theorem remain open.

## Full-sector persistence is factored into four old/new block budgets (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual` specializes the exact
old/new decomposition to the cutoff-two base and turns four separately
checkable estimates into the aggregate matrix comparison required by the
full-sector persistence theorem.  The old-old budget measures drift from the
recentered cutoff-two core; the two cross budgets and the new-new budget
measure the genuinely added sector.  Their exact total is

`(eOO + eON) + (eNO + eNN)`,

so the completed contraction rate supplied by a cofinal family is

`(49/50) * lambda + (eOO + eON) + (eNO + eNN)`.

The compiler uses the kernel-checked four-block equality and three triangle
inequalities, then feeds the resulting persistence family through the
existing cofinal finite-gap and completion bridges.  It therefore exposes
the next analytic work without hiding it inside one undifferentiated matrix
error.

The focused monitored check passes in about 1.3 seconds, and the exact
one-worker dependency-complete target passes 4,886 jobs.  All four audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Five diagnostic checks were deliberately interrupted while a missing
namespace for `centralPhysicalFiniteKernel` made Lean's error pretty-printer
expand enormous unresolved terms; none is counted as a pass.

No later-cutoff block residual or cofinal family is inhabited.  The next
frontier is to construct the cutoff-two recentering from the old coefficient
block and prove exact mean/diagonal identities, leaving only kernel drift,
cross-block, and new-tail analytic estimates.  Uniform full-sector control,
the completed gap inhabitant, volume/spacing control, continuum QFT, and the
Clay theorem remain open.

## The cutoff-two core is now a canonical pullback and recentering (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual` removes the
arbitrary recentering map from the full-sector residual input.  Any later
coefficient is restricted constructively along the explicit cutoff-two index
embedding.  Its old weighted mean, old diagonal, and old-old matrix block are
proved exactly equal to the corresponding moving pulled forms.

For a centered later vector the pulled-old mean plus the new-sector mean is
therefore exactly zero.  The full diagonal likewise splits exactly into the
pulled-old diagonal plus the new diagonal.  The old pullback is then centered
at the fixed cutoff-two root and explicitly extended on the cutoff-two sector;
the resulting core is unconditionally centered, and its diagonal and matrix
forms are exactly the fixed pulled forms.

The specialized residual certificate now asks only for five analytic
estimates: moving-versus-fixed old-old control, both cross blocks, the
new-new block, and centered-core diagonal inflation.  Its cofinal compiler
inserts all structural witnesses and reaches the actual completed
vacuum-sector transfer contraction through the previously verified bridges.

The final focused monitored check passes in about 1.6 seconds, and the exact
one-worker dependency-complete target passes 4,887 jobs.  All eleven audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Three early checks were interrupted while missing namespaces for
`listQSum` and its private local reindexing lemmas caused unresolved-term
expansion; subsequent diagnostic failures are not passes.

No later-cutoff analytic estimate or cofinal family is inhabited.  The next
frontier is to expand the fixed-root recentering correction quantitatively in
terms of (i) old pulled-weight drift and (ii) the exactly cancelling new mean,
then reduce the diagonal inflation and old-old comparison to explicit
relative tail budgets.  The uniform completed gap inhabitant, volume/spacing
control, continuum QFT, and the Clay theorem remain open.

## Old/new contraction now preserves the exact diagonal partition (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap` corrects an
important rate-accounting weakness in the additive residual route.  An
arbitrary later-sector vector may be supported entirely on newly appearing
states, so its new diagonal is not a uniformly small fraction of the full
norm.  A valid recursive gap argument must contract the old and new diagonal
blocks separately rather than pay both against the full diagonal.

The module proves both diagonal pieces nonnegative and each bounded by the
full diagonal.  More importantly, it combines

`|M_old,old| <= q D_old`,

`|M_new,new| <= q D_new`, and

`|M_old,new| + |M_new,old| <= c D_full`

into the exact full-sector rate `q + c`, using
`D_full = D_old + D_new`.  The two diagonal rates are not added.  A
constructively cofinal family of these block certificates compiles directly
to the existing finite strict-gap interface and then to the actual completed
vacuum-sector transfer contraction.

The focused monitored check passes in about 1.1 seconds, and the exact
one-worker dependency-complete target passes 4,888 jobs.  All seven audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Two initial namespace/syntax checks failed and are not passes.

No cofinal diagonal-block family is inhabited.  The next frontier is now
causal and recursive: prove one common subunit diagonal-block rate on both
the embedded old sector and its new complement, plus a cross budget smaller
than the remaining margin.  This replaces the untenable demand that every
new-sector norm be small.  The completed gap inhabitant, volume/spacing
control, continuum QFT, and the Clay theorem remain open.

## Full-sector Dirichlet energy splits into positive old/new blocks (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks` replaces the lossy
absolute-value treatment of old/new cross terms by the equivalent Dirichlet
form.  It proves a generic exact four-block partition of directed finite
Dirichlet energy and specializes it to the cutoff-two old/new decomposition.
Each old-old, old-new, new-old, and new-new block is nonnegative.  Consequently
the within-block and cross-block energies are separately nonnegative and each
is bounded by the full energy.

The full block energy is also proved exactly equal to twice the physical
diagonal-minus-transfer deficit.  Thus cross edges are now exposed as
coercivity that can help a gap estimate, rather than an absolute matrix error
that consumes the strict-rate margin.

The final focused monitored check passes in about 1.0 seconds, and the exact
one-worker dependency-complete target passes 4,889 jobs.  All nine audited
exports use exactly `[propext]` or `[propext, Quot.sound]`; no `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
was added.  One earlier check failed because two imported namespaces had not
yet been opened; it is not counted as a pass.

No recursive Poincare constant or cofinal family is inhabited.  The next
frontier is a constructive two-block gluing estimate: control old and new
within-block variances by their internal energies and control the difference
of the two block means by cross energy, with constants that remain uniformly
bounded on an unbounded cutoff schedule.  A completed gap inhabitant,
volume/spacing control, continuum QFT, and the Clay theorem remain open.

## Two-block coercivity now compiles causally to the completed gap (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing` partitions the
stationary-product pairwise variance along exactly the same cutoff-two old/new
cut as the physical Dirichlet energy.  Its within-block and cross-block pieces
are separately nonnegative, and their sum is exactly the full pairwise
variance.  The cross piece retains the block-separation mode that is invisible
to the two internal energies.

At one later cutoff, `CutoffTwoFullSectorDirichletGluingAt` asks for a common
floor `kappa` satisfying

`kappa * V_within <= E_within` and
`kappa * V_cross <= E_cross`,

together with a lower bound `m0` on the total sector mass.  The module proves
that these estimates glue without an additive loss, and exact centering gives

`(kappa * m0) * D <= D - M`.

The resulting explicit transfer rate is

`q = 1 / (1 + kappa * m0) < 1`.

A constructively cofinal family with fixed positive `kappa` and `m0` compiles
through the existing finite strict-gap interface to the actual completed
vacuum-sector contraction.

The focused monitored check passes in about 1.3 seconds, and the exact
one-worker dependency-complete target passes 4,890 jobs.  All ten audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Two preliminary checks failed on namespace exposure and explicit
setoid doubling/cancellation algebra; neither is counted as a pass.

No positive common coercivity floor, mass floor, or cofinal family is
inhabited.  The next frontier is to expose the cross pairwise term explicitly
in block masses, block means, and block diagonal fluctuations, then reduce
`V_cross <= kappa^-1 E_cross` to a quantitative old/new bridge conductance
estimate.  Uniform volume/spacing control, continuum QFT, and the Clay theorem
remain open.

## Cross variance exposes the block-mean mode and a local kernel test (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity` proves the generic exact
rectangular identity

`V(L,R) = square(L) * mass(R) + mass(L) * square(R)
          - 2 * mean(L) * mean(R)`.

It specializes both directed orientations to the cutoff-two old/new split.
For a globally centered coefficient, the old and new means cancel exactly,
so the negative mean product becomes a positive old-mean square.  Consequently
the full directed cross pairwise variance is two copies of

`newMass * oldSquare + oldMass * newSquare + 2 * oldMean^2`.

This identifies the precise mode that internal old-old and new-new gaps cannot
control: the relative constant shift between the two blocks.

The module also proves a local-to-global cross coercivity theorem.  If, on
both directed old/new rectangles,

`kappa * weight(old) * weight(new) <= physicalKernel(old,new)`,

then summing against every squared coefficient difference gives

`kappa * V_cross <= E_cross`.

Thus an explicit `CutoffTwoCrossKernelMinorizationAt` supplies the cross field
of the previously proved gluing certificate.

The focused monitored check passes in about 2.3 seconds, and the exact
one-worker dependency-complete target passes 4,891 jobs.  All eight audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  Two preliminary checks failed on namespace exposure and local
setoid-expression elaboration; neither is counted as a pass.

No positive cutoff-uniform minorization is inhabited.  Entrywise
minorization may be stronger than necessary; the next honest frontier is to
test it against the exact BF4 kernel and, if it degenerates, replace it by a
path/aggregate old-new conductance certificate while preserving the proved
cross-mean coercivity.  The within-block uniform recursion and sector-mass
floor also remain open, as do volume/spacing control, continuum QFT, and the
Clay theorem.

## Sparse old/new paths can now allocate within energy honestly (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing` removes the unnecessary
requirement that cross energy alone dominate the entire cross pairwise
variance.  This matters for a sparse support graph: a path between arbitrary
old and new states may use internal edges before it reaches a genuine bridge.

The new certificate chooses nonnegative shares `a` and `b` with `a + b = 1`
and asks for

`kappa * V_within <= a * E_within`,

`kappa * V_cross <= b * E_within + E_cross`.

The module proves these combine exactly into

`kappa * V_full <= E_full`.

A minimal global coercivity interface then uses the sector-mass floor to
recover `(kappa * m0) * D <= D - M`, the same explicit rate
`1 / (1 + kappa * m0) < 1`, the cofinal finite strict gap, and the completed
vacuum-sector transfer contraction.

The focused monitored check passes in about 1.2 seconds, and the exact
one-worker dependency-complete target passes 4,892 jobs.  All five audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  One preliminary check failed on a namespace and right-additive
congruence orientation; it is not a pass.  A separate cutoff-three direct
support probe was stopped by the 12 GiB safe-build memory reserve before
returning a value and is not treated as evidence either way.

No allocated certificate is inhabited.  The next analytic frontier is now a
sparse path gluing theorem that converts: internal old/new path estimates, a
positive old/new bridge edge (or bridge family), and explicit path-congestion
budgets into the two allocated inequalities above.  Uniform path constants,
the sector-mass floor, volume/spacing control, continuum QFT, and the Clay
theorem remain open.

## Canonical sparse old/new path costs are now aggregated exactly (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoSparsePathAggregation` replaces the abstract
cross-budget premise by a concrete sum over the actual canonical positive
paths in the later full vacuum sector.  It first proves a generic rectangular
summation theorem: pointwise endpoint estimates can be multiplied by their
exact stationary pair weights and summed without replacing the result by a
pair-count times one global energy.

For the physical cutoff-two split, the module totalizes the canonical
full-sector path energy and defines the directed old-to-new and new-to-old
weighted path budgets.  The explicit finite-sector positive-edge minimum then
gives

`edgeFloor(later) * V_cross(later,f) <= canonicalCrossPathBudget(later,f)`.

Thus a supplied lower floor below the finite edge minimum and a congestion
bound

`canonicalCrossPathBudget <= b * E_within + E_cross`

produce the cross field of the allocated gluing certificate.  Together with
the supplied within budget, complementary energy shares, and mass floor, the
new sparse-path certificate compiles all the way to the completed strict
contraction interface.  The paths and the finite edge floor in this statement
are inhabited canonical objects; only their uniform aggregate congestion is
left as analytic input.

The focused monitored check passes in about 1.2 seconds, and the exact
one-worker dependency-complete target passes 4,893 jobs.  All six audited
exports use exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration was
added.  The first focused check failed on two missing namespace openings; it
is not a pass.

The next frontier is to decompose the canonical aggregate path budget by edge
occurrences and prove an explicit congestion comparison with the within and
cross Dirichlet blocks.  Uniform positive floors, congestion constants,
sector mass, cutoff persistence, continuum QFT, and the Clay theorem remain
open.

## Cross-path aggregation now uses polynomial literal-edge energy (2026-08-23)

The sparse path aggregation module now also instantiates the existing finite
Cauchy--Schwarz path theorem.  For each canonical old/new path it replaces the
recursively doubled energy by

`pathLength * sum_{edge in path} kernel(edge) * (delta f(edge))^2`.

Summing these exact length-weighted linear path costs gives

`edgeFloor(later) * V_cross <= canonicalCrossLengthLinearPathBudget`.

The corresponding sparse certificate compiles a congestion bound on this
polynomial literal-edge budget through allocated gluing and the completed
strict-contraction interface.  This is the appropriate form for the next
edge-load calculation: path occurrences are additive, and the only path
amplification is the explicit length factor rather than recursive doubling.

The focused monitored check passes in about 1.5 seconds, and the exact
one-worker dependency-complete target passes 4,895 jobs.  All nine audited
exports use exactly `[propext, Quot.sound]`; no forbidden construct was added.
No uniform path-length, edge-load, positive-floor, or mass-floor certificate
is inhabited, so no uniform completed gap or continuum/Clay conclusion is
claimed.

## Linear path energy is now a literal edge-occurrence sum (2026-08-23)

`BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences` extracts the ordered list
of directed edges traversed by any positive-kernel path, retaining both
orientation and repetitions.  It proves that this list has the existing path
length, that both endpoints of every occurrence lie in the declared support,
and that the recursive `linearEnergy` is exactly

`sum_{edge occurrence} kernel(edge) * (delta f(edge))^2`.

The length-weighted linear path cost is therefore also exactly path length
times this literal occurrence sum.  This closes the combinatorial exposure
needed before defining stationary-weighted per-edge loads.  The focused check
passes in about 0.4 seconds and the exact one-worker target passes 1,189 jobs.
All four audits use at most `[propext]`; no forbidden construct was added.

The next frontier is a finite reindexing theorem that groups the endpoint-pair
path occurrences by physical directed edge.  Its resulting per-edge load can
then be compared pointwise with the within/cross energy capacities.  No such
load bound, uniform gap, continuum QFT, or Clay theorem is claimed here.

## Weighted path occurrences can now be regrouped by physical edge (2026-08-23)

`BF4PhysicalFiniteVacuumSectorPathEdgeLoad` introduces a weighted directed
edge occurrence and defines the total rational load carried by each directed
edge.  For any duplicate-free finite support it proves the exact reindexing

`sum_{occurrence} load(occurrence) * edgeEnergy(occurrence.edge)`

`  = Dirichlet(states, edgeLoad * physicalKernel)`.

The proof keeps repeated path uses as additive load and uses only finite-list
selectors and Cartesian reindexing.  This is the contraction dual to the
previous expansion into literal occurrences: an arbitrarily long occurrence
list is now represented by one load value per directed physical edge.

The focused monitored check passes in about 0.8 seconds and the exact
one-worker dependency-complete target passes 4,897 jobs.  The two audited
exports use at most `[propext, Quot.sound]`; no forbidden construct was added.
The first two focused checks failed during selector/Fubini proof development
and are not passes.

The next frontier is the physical specialization: flatten the actual
stationary-weighted old/new canonical paths into weighted occurrences, prove
their polynomial cross-path budget equals the loaded physical Dirichlet form,
then reduce congestion to pointwise load bounds on the four old/new edge
blocks.  Those bounds and all continuum/Clay conclusions remain open.

## Canonical cross-path congestion is now pointwise on physical edges (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad` instantiates the generic
occurrence reindexing with every actual old-to-new and new-to-old canonical
path.  Each path edge is charged its stationary endpoint-pair weight times the
path length.  Equal directed physical edges are then grouped into the
coefficient-independent rational
`cutoffTwoCanonicalCrossEdgeLoad later source target`.

The module proves the exact identity

`canonicalCrossLengthLinearPathBudget(f)`

`  = Dirichlet(full, canonicalCrossEdgeLoad * physicalKernel, f)`.

It partitions this loaded Dirichlet form into the same four old/new blocks as
the physical energy and proves that the following coefficient-free bounds are
sufficient:

`old-old load <= crossShare`, `new-new load <= crossShare`,

`old-new load <= 1`, and `new-old load <= 1`.

They imply

`canonicalCrossLengthLinearPathBudget`

`  <= crossShare * E_within + E_cross`,

which compiles with the existing within budget, positive floor, mass floor,
and complementary shares through allocated coercivity to the completed
strict-contraction interface.  This is a genuine causal reduction: the open
cross estimate no longer quantifies over coefficients, only over finite
directed edges and their explicitly defined canonical loads.

The focused monitored check passes in about 1.3 seconds, and the exact
one-worker dependency-complete target passes 4,898 jobs.  All ten audited
exports use at most `[propext, Quot.sound]`; no forbidden construct was added.
Several preliminary focused checks failed on stale `.olean` state, missing
namespace openings, overly eager unfolding, and one heartbeat-heavy monolithic
proof; they are not passes.  The final proof is split into small loaded-within,
loaded-cross, and recombination lemmas.

No pointwise load certificate is inhabited.  The next analytic frontier is to
bound the explicit rational edge load itself, preferably by a canonical-path
counting/injection argument that is uniform along a cofinal cutoff schedule.
The within-block coercivity, positive edge and sector-mass floors, continuum
QFT, and the Clay theorem remain open.

## Finite edge capacities and denominator-free scaling are now explicit (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling` removes the prior unit
bridge-capacity normalization.  It introduces independent internal and bridge
capacities and proves that their four pointwise bounds imply

`canonicalCrossLengthLinearPathBudget`

`  <= internalCapacity * E_within + bridgeCapacity * E_cross`.

Both capacities are inhabited at every finite cutoff by `1 +` the located
maximum of the explicit canonical edge load on the corresponding finite pair
list.  Thus finite congestion existence is no longer an open hypothesis.

After adjoining a declared within-block cost, the module contracts the two
variance budgets to the denominator-free inequality

`baseFloor * V_full <= totalCost * E_full`,

where `totalCost = withinCost + internalCapacity + bridgeCapacity`.  A fixed
effective floor is required only through the transparent cofinal comparison

`effectiveFloor * totalCost <= baseFloor`.

Positive rational cancellation then produces the existing full-sector
coercivity certificate and compiles to the completed strict-contraction data.
This is the precise uniform quantitative frontier: prove a cofinal lower
bound on the capacity-scaled floor, a within-block budget, and a fixed
positive sector-mass floor.

The focused monitored check passes in about 1.8 seconds, and the exact
one-worker dependency-complete target passes 4,899 jobs.  All eight audited
exports use at most `[propext, Quot.sound]`; no forbidden construct was added.
The first focused check failed on missing namespace openings and is not a
pass.  No uniform ratio or mass-floor family, continuum QFT, or Clay theorem
is claimed.

## Full-sector edge loading removes the finite within-block hypothesis (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad` aggregates the canonical
positive path over every ordered pair in the finite vacuum sector, rather
than only over old/new cross pairs.  Stationary endpoint weight times path
length is attached to every literal directed-edge occurrence, and finite
regrouping proves the exact identity

`fullCanonicalLengthLinearAggregateBudget`

`  = Dirichlet(fullCanonicalEdgeLoad * physicalKernel)`.

The coefficient-independent capacity `1 + max(fullCanonicalEdgeLoad)` is
constructively located on the finite full edge-pair list.  The module proves

`edgeFloor(later) * V_full`

`  <= fullEdgeLoadCapacity(later) * E_full`

and therefore inhabits the finite cleared coercivity certificate without any
separate within-block cost or induced-subgraph connectivity assumption.  A
cofinal family now requires only the transparent quantitative inputs

`effectiveFloor * fullEdgeLoadCapacity(anchor(request))`

`  <= edgeFloor(anchor(request))`

and a fixed positive lower bound on sector mass.  Those inputs compile to the
completed strict-contraction interface.

The focused monitored check passes in about 1.4 seconds, and the exact
one-worker dependency-complete target passes 4,900 jobs.  All eight audited
exports use exactly `[propext, Quot.sound]`; no forbidden construct was added.
One preliminary focused check failed on missing namespace openings and an
over-eager unfolding step and is not a pass.  The two reused one-path atoms
were made public and separately audited in the sparse aggregation and cross
edge-load modules.

The next frontier is no longer finite coercivity existence.  It is to replace
or compare the arbitrary canonical paths with loop-free carrier-bounded paths
and obtain a usable cutoff dependence for the full edge-load capacity, then
prove a cofinal positive ratio and mass floor.  Continuum QFT and the Clay
theorem remain open.

## Loop erasure exposes an explicit polynomial full-sector cost (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost` proves that the stationary
mass of the canonical finite vacuum sector is at most one by injecting its
index list into the completely normalized positive-row carrier.  It then
aggregates the existing loop-erased endpoint estimate to obtain

`edgeFloor(later) * V_full`

`  <= (1 + |vacuumSector(later)|^2) * E_full`.

The known ambient enumeration bound contracts this further to

`edgeFloor(later) * V_full`

`  <= (1 + ((later + 1)^24)^2) * E_full`

at half extent zero.  Both the sector-size and ambient-size coefficients are
positive, inhabited cleared coercivity costs.  A cofinal lower bound on the
edge floor divided by the explicit ambient cost, together with a positive
mass floor, compiles to completed strict contraction.

The focused monitored check passes in about 1.5 seconds, and the exact
one-worker dependency-complete target passes 4,904 jobs.  All seven audited
exports use exactly `[propext, Quot.sound]`; no forbidden construct was added.
The first focused check failed on two missing namespace openings and is not a
pass.

This is an honest diagnostic contraction as well as a theorem: the ambient
fallback grows like degree 48 in the cutoff and is therefore too coarse to
establish a uniform gap without a compensating edge-floor estimate.  The next
frontier is a sharper simple-path edge-load/congestion bound exploiting which
endpoint paths actually use each edge, or a stronger analytic BF4 kernel
minorization.  A uniform completed gap, continuum QFT, and the Clay theorem
remain open.

## Simple-path congestion lowers the explicit cost to degree 24 (2026-08-23)

`FiniteBoolGraphSimplePaths` now records the literal directed edges of a
cons-form walk and proves that a vertex-simple walk has a duplicate-free edge
list.  `BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad` transports that fact
to the actual loop-erased BF4 positive paths, assigns each occurrence its
stationary endpoint-pair weight times path length, and regroups all ordered
endpoint paths by physical directed edge.

For every directed edge, duplicate-freeness gives one charge per endpoint
path.  Summing over all endpoint pairs and using stationary sector mass at
most one proves

`simpleFullEdgeLoad(later, source, target) <= |vacuumSector(later)|`.

The exact occurrence-energy identity therefore contracts to the inhabited
finite coercivity estimate

`edgeFloor(later) * V_full`

`  <= (1 + |vacuumSector(later)|) * E_full`.

At half extent zero the ambient enumeration gives the exact presentation

`1 + ambientSize(later, 0) = 1 + (later + 1)^24`,

halving the previous fallback's polynomial degree from 48 to 24.  A supplied
cofinal positive lower bound for `edgeFloor / (1 + (later + 1)^24)` and a
positive sector-mass floor compile through the existing capacity-cleared
pipeline to completed strict contraction.

The final focused monitored check passes in about 72 seconds, and the exact
one-worker dependency-complete target passes 4,905 jobs with the new module
itself taking about 78 seconds.  Nine audited exports use exactly
`[propext, Quot.sound]`; the exact ambient-power presentation uses only
`[propext]`.  The two supporting public lemmas and the generic no-repeated-edge
lemma remain inside the same axiom gate.  Earlier missing-olean, proof-rewrite,
syntax, and deterministic-heartbeat failures are not passes.

The structural congestion frontier is closed at the linear-carrier level.
The next analytic frontier is to compare the canonical positive BF4 edge
floor against this degree-24 cost (or replace the global minimum by a stronger
weighted flow/minorization estimate), and separately establish a uniform
positive vacuum-sector mass floor.  A uniform completed gap, continuum QFT,
and the Clay theorem remain open.

## The cutoff-two vacuum sector has a uniform positive mass floor (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor` observes that finite
index zero is literally the all-zero lower boundary state and belongs to the
root-selected vacuum sector at every cutoff.  The existing uniform positive
row-floor theorem applies to that same state beyond its explicit unit-tail
anchor.  Since all sector weights are nonnegative, the weight of index zero
is bounded above by the full sector mass.  Therefore

`centralPhysicalUniformPositiveRowFloor(cutoffTwoHalfCoupling, 0)`

is an explicit rational constant which is strictly positive and lies below
the canonical vacuum-sector mass at every sufficiently large cutoff.

The module then refactors the degree-24 cofinal compiler: a cofinal lower
bound for

`edgeFloor(later) / (1 + (later + 1)^24)`

alone now supplies the completed strict-contraction datum.  The mass-floor
field and its positivity/persistence proofs are inhabited internally.

The focused monitored check passes in about 1.1 seconds, and the exact
one-worker dependency-complete target passes 4,906 jobs with the new module
taking about one second.  All three audited exports use exactly
`[propext, Quot.sound]`; no forbidden construct was added.  The first focused
check failed on two missing names and is not a pass.

The positive sector-mass frontier is closed.  The sole remaining finite-gap
input in this route is the degree-24 cost-scaled edge-floor bound.  The next
frontier is to reuse the constructed uniform persistence of cutoff-two pulled
positive edges and isolate precisely which newly appearing states/edges still
prevent that bound.  A uniform completed gap, continuum QFT, and the Clay
theorem remain open.

## The embedded cutoff-two block has a uniform positive coercivity floor (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity` reuses the constructed
uniform floor on transported cutoff-two canonical-path edges and sums the
endpoint estimate against arbitrary pulled stationary endpoint pairs.  The
pulled component has stationary mass at most one, so division by the fixed
positive path ceiling constructs the explicit rational constant

`delta_old = pulledBasePositiveEdgeFloor / pulledCanonicalPathCeiling > 0`

and proves, without any centering hypothesis,

`delta_old * V_pulled(later, coefficient)`

`  <= E_pulled(later, coefficient)`.

Exact permutation and cutoff-index-map identities then transport both forms
to the embedded old block of every sufficiently late full sector:

`delta_old * V_old-old(later, coefficient)`

`  <= E_old-old(later, coefficient)`.

The old-old and total-mass inputs of the two-block gluing compiler are now
inhabited.  `CutoffTwoCofinalNewAndCrossCoercivity` exposes the strictly
smaller residual: at cofinally many later cutoffs one must prove only
new-new coercivity and old/new cross coercivity at the already constructed
constant `delta_old`; such a family compiles to the completed strict
contraction datum.

The focused monitored check passes in about 1.6 seconds, and the exact
one-worker dependency-complete target passes 4,910 jobs with the new module
itself taking about 1.5 seconds.  All eight audited exports use exactly
`[propext, Quot.sound]`; no forbidden construct was added.  The first focused
check failed on missing namespace openings and premature unfolding of local
abbreviations and is not a pass.

This closes the entire fixed embedded old-block contribution.  The next
finite analytic frontier is genuinely about states absent at cutoff two:
prove uniform new-new and cross-block coercivity, preferably by a recursive
shell gluing or a weighted minorization argument.  A completed uniform gap,
thermodynamic/continuum construction, and the Clay theorem remain open.

## Novel weighted flow removes the shrinking global edge floor (2026-08-23)

`BF4PhysicalFiniteVacuumSectorPathLengthEnergy` now exposes the floor-free
endpoint Cauchy estimate

`(c(left) - c(right))^2 <= pathLength * sum_path_edges (Delta c)^2`,

and `BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences` identifies the latter
square sum exactly with the literal directed-edge list.  Building on those
atoms, `BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow` enumerates precisely the
ordered endpoint pairs with at least one state absent at cutoff two, routes
their stationary-product weights along the existing loop-erased positive
paths, and assigns each traversed edge the load

`weight(left) * weight(right) * pathLength`.

Finite Cauchy--Schwarz sums and exact occurrence regrouping prove

`V_novel(later, coefficient)`

`  <= DirichletBlock(novelEdgeLoad(later), coefficient)`

without inserting the cutoff-dependent minimum positive physical edge.
Moreover `V_novel` is proved exactly equivalent to the new-new variance plus
both directed old/new cross variances.

`BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity` then defines

`delta_flow = (1/2) * delta_old > 0`.

The first half of old-old physical energy pays for the already proved old
variance.  The other half is reserved for novel paths traversing old-old
edges, while new-new and cross edges retain full physical capacity.  Four
coefficient-independent pointwise inequalities of the form

`delta_flow * novelEdgeLoad(source,target)`

`  <= allocatedPhysicalKernel(source,target)`

compile to full-sector Dirichlet coercivity at `delta_flow`, using the
constructed uniform sector-mass floor.  A constructively cofinal family of
these local capacity certificates therefore compiles directly to the
completed vacuum-sector strict-contraction datum.

The focused checks pass after replacing one oversized rational normalization
by explicit distributivity steps.  The exact one-worker dependency-complete
target passes 4,912 jobs, with the final capacity module taking about 1.3
seconds.  All eleven audited exports across the two new frontier modules use
exactly `[propext, Quot.sound]`, except the generic pointwise finite-block
domination theorem, which uses only `[propext]`; the two new generic path
atoms stay inside the same gate.  Preliminary stale-olean, missing-namespace,
placeholder, timeout, and intentionally interrupted diagnostic checks are
not passes.

This replaces the former separate coefficient-dependent new-new and cross
coercivity hypotheses by one explicit local weighted-flow capacity family
and removes the known shrinking global edge-floor obstruction from this
route.  The new finite analytic frontier is to inhabit that cofinal pointwise
capacity family from the concrete BF4 kernel and stationary-weight formulas,
or to identify a genuine obstruction.  The uniform completed gap remains
conditional on that family; thermodynamic/continuum construction and the
Clay theorem remain open.

## Exact finite novel-flow capacity ratio (2026-08-23)

`BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences` now proves that every
literal directed edge of a positive-kernel chain retains strict positivity
of the corresponding kernel entry.  The generic support lemma added to
`BF4PhysicalFiniteVacuumSectorPathEdgeLoad` proves constructively that every
strictly positive regrouped load has a literal occurrence on that directed
edge.  Together these facts show that a positive novel-flow load can occur
only where the concrete normalized BF4 physical kernel is strictly positive.

`BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio` allocates half of the
physical kernel on the embedded old-old block and the full kernel on the
other three blocks.  It then defines the exact edge ratio

`allocatedPhysicalKernel(source,target) / novelEdgeLoad(source,target)`

on positive-load edges, uses the harmless value one on zero-load edges, and
takes a located finite minimum over every ordered pair in the full sector.
This explicit cutoff-dependent minimum is positive and its product with the
load is bounded by the allocated kernel on every full-sector edge.

Consequently a single scalar comparison

`delta_flow <= finiteFlowCapacityFloor(later)`

inhabits all four old-old, old-new, new-old, and new-new capacity fields.
`CutoffTwoCofinalNovelFlowCapacityRatio` states only the remaining uniform
content: the fixed constructed `delta_flow` must lie below that explicit
finite minimum on a constructively cofinal cutoff schedule.  Such a scalar
certificate compiles through the existing flow theorem to the completed
vacuum-sector strict-contraction datum.

The focused monitored checks pass, and the exact one-worker
dependency-complete target passes 4,913 jobs, with the final module taking
about 2.4 seconds.  The five audited exports of the new ratio module use
exactly `[propext, Quot.sound]`; the generic directed-edge positivity theorem
uses only `[propext]`, and the other supporting audited exports stay within
`[propext, Quot.sound]`.  Preliminary stale-olean, parser, missing-tactic, and
dependent-rewrite checks failed and are not passes.

The four local capacity hypotheses have therefore contracted to a lower-bound
problem for one completely explicit rational sequence.  The next finite
analytic frontier is to derive a cutoff-uniform cofinal lower bound from the
concrete BF4 kernel/load formulas, or prove that the chosen simple flow has a
vanishing ratio.  The completed uniform gap is still conditional; the
thermodynamic/continuum construction and Clay theorem remain open.

## Exact finite novel-flow capacity decision (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision` reflects the explicit
finite capacity minimum into a Boolean scan.  Generic constructive lemmas
prove that a candidate lies below `listPositiveMinOne` exactly when it lies
below the unit fallback and every listed candidate.  Therefore
`cutoffTwoNovelFlowCapacityCheck later = true` is a sound and complete finite
test for

`delta_flow <= cutoffTwoNovelFiniteFlowCapacityFloor(later)`.

A Type-level recursive failure locator avoids eliminating propositional
existence into data.  `inspectCutoffTwoNovelFlowCapacity later` consequently
returns one of three exact outcomes: a certified scalar floor comparison, a
proof that the requested strength is not below the unit fallback, or a
literal full-sector directed edge with positive flow load on which

`delta_flow * load <= allocatedPhysicalKernel`

fails.  Thus a negative fixed-cutoff computation now produces a local
overloaded-edge obstruction to the chosen path family rather than an opaque
failed minimum.

`CutoffTwoCofinalNovelFlowCapacityCheck` packages a constructively cofinal
schedule of successful Boolean scans and compiles it through the ratio and
flow layers to the completed vacuum-sector strict-contraction datum.  This is
equivalent in analytic strength to the preceding cofinal scalar lower bound,
but each finite member is executable and kernel-auditable.

The focused monitored check passes.  The exact one-worker
dependency-complete target passes 4,914 jobs, with the new module taking about
1.1 seconds.  All four audited exports use exactly
`[propext, Quot.sound]`.  The first focused check failed on Boolean theorem
application syntax and forbidden proposition-to-Type elimination; both were
replaced by explicit theorem arguments and a Type-level recursive witness,
and that failed check is not a pass.

The finite capacity question is now an exact certificate-or-local-obstruction
calculation.  The next frontier is to rule out the unit-fallback branch and
then analyze the returned loaded edges using concrete BF4 weight and kernel
factorizations, seeking a cofinal uniform comparison or a genuine asymptotic
counterexample.  The uniform completed gap, continuum QFT, and Clay theorem
remain open.

## Unit fallback removed from the novel-flow decision (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound` proves that the fixed
novel-flow strength is at most one.  The proof does not unfold the opaque
transported edge-floor certificate: it applies the certificate's own
pointwise lower-bound field to the cutoff-two vacuum-root diagonal, bounds
that normalized BF4 entry by one using the established Markov row law, proves
the fixed canonical-path ceiling is at least one, and observes that the novel
flow spends only half of the resulting old-block coercivity constant.

The Boolean frontier therefore simplifies to
`cutoffTwoNovelEdgeCapacityCheck`, which scans only the actual ordered
full-sector edge ratios.  Soundness and completeness identify its success
exactly with the finite capacity-floor comparison.  The Type-level
`inspectCutoffTwoNovelFlowCapacityDecisively` has only two outcomes:

1. the cutoff capacity is certified; or
2. a literal full-sector directed edge has positive novel-flow load and fails
   `delta_flow * load <= allocatedPhysicalKernel`.

The earlier unit-fallback branch is now kernel-checked impossible.
`CutoffTwoCofinalNovelEdgeCapacityCheck` compiles any cofinally successful
family of these edge-only scans to completed strict contraction.

The focused monitored check passes after adding one missing namespace opening.
The exact one-worker dependency-complete target passes 4,915 jobs, with the
new module taking about 1.1 seconds.  All five audited exports use exactly
`[propext, Quot.sound]`; the initial missing-name check failed and is not a
pass.

Every negative finite diagnostic is now a genuine local overloaded-edge
witness.  The next analytic frontier is to expand such an edge's grouped load
into the contributing stationary endpoint pairs and compare those terms with
the concrete normalized BF4 kernel formula, uniformly in the representation
cutoff.  The completed uniform gap, continuum QFT, and Clay theorem remain
open.

## Endpoint-pair expansion of each novel-flow edge load (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad` now exposes the generic
flat-map load identity and proves the exact load of one loop-erased endpoint
path on a selected edge.  That contribution is zero when the edge is absent
from the path and otherwise equals

`weight(left) * weight(right) * pathLength(left,right)`.

`BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion` defines this term as
`cutoffTwoNovelPathPairEdgeContribution` and proves the exact regrouping

`novelEdgeLoad(source,target)`

`  = sum_{novel endpoint pairs} pathPairEdgeContribution(source,target,pair)`.

This reverses the earlier occurrence aggregation at precisely the local edge
returned by the decisive failure diagnostic.  The new
`CutoffTwoNovelEdgePairAllocation` interface also proves a finite payment
compiler: if every endpoint-pair contribution is assigned a payment and the
sum of those payments fits inside the edge's allocated physical kernel, then
the grouped edge-capacity inequality follows.  This exposes the stationary
endpoint weights and path incidence needed for a weighted congestion argument
without reverting to the shrinking global positive-edge floor.

The focused supporting check passes in about 70 seconds; rebuilding its exact
target takes about 77 seconds.  The new expansion module's focused check
passes in about one second, and the exact one-worker dependency-complete
target passes 4,916 jobs with the new module taking about 0.94 seconds.  All
four newly audited exports use exactly `[propext, Quot.sound]`.  The first
expansion checks failed on missing namespace openings and an under-applied
finite-sum monotonicity theorem and are not passes.

The local obstruction is now a finite sum of explicit stationary-product
path terms.  The next frontier is to normalize those terms by their common
allocated BF4 kernel, producing the standard edge-congestion quantity and a
uniform weighted-Harnack target.  The uniform completed gap, continuum QFT,
and Clay theorem remain open.

## Exact normalized novel-flow edge congestion (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion` divides each
positive novel-flow edge load by precisely the physical BF4 kernel allocated
to that flow.  It proves that the resulting congestion is the exact finite
sum of the endpoint-pair contributions from the preceding milestone divided
by their common edge capacity.  Zero-load edges are handled separately, so
no artificial positive denominator or global edge floor is introduced.

The original edge payment comparison is now proved equivalent to the
dimensionless unit bound

`delta_flow * normalizedCongestion(source,target) <= 1`.

Consequently, an all-full-edge congestion bound implies
`delta_flow <= cutoffTwoNovelFiniteFlowCapacityFloor(later)`.  The cofinal
structure `CutoffTwoCofinalNovelNormalizedCongestionBound` compiles such
bounds through the exact capacity ratio and flow theorem to the completed
vacuum-sector strict-contraction datum.

The focused monitored check passes in about 1.3 seconds.  The exact
one-worker dependency-complete target passes 4,917 jobs, with the new module
taking about 1.1 seconds.  All four audited exports use exactly
`[propext, Quot.sound]`.  Two earlier focused checks hit deterministic
elaboration timeouts, and one also exposed a nonexistent convenience lemma;
explicit setoid congruences and primitive nonnegativity algebra replaced
those proof attempts.  The failed checks are not passes.

The next analytic frontier is now sharply local: uniformly bound the exact
finite sum of normalized stationary endpoint-product/path-length indicators
on every loaded BF4 edge, using concrete stationary-weight and allocated
kernel factorizations, or produce a cofinal overload family proving that the
chosen canonical paths require redesign.  No such uniform bound is claimed;
the completed gap inhabitant, continuum QFT, and Clay theorem remain open.

## Stationary source mass cancels from novel-flow congestion (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion` exposes the
Markov factorization hidden inside the preceding joint-kernel ratio.  On every
actual vacuum-sector source, the indexed physical joint kernel is exactly

`weight(source) * conditionalKernel(source,target)`.

The old-old half allocation is recorded by an explicit fraction taking only
the values `1/2` and `1`, so the allocated joint capacity is exactly

`weight(source) * allocatedConditionalKernel(source,target)`.

Every routed pair contribution is divided by the same strictly positive
source weight and the resulting terms are summed into
`cutoffTwoNovelRelativeSourceEdgeLoad`.  Finite-sum distributivity proves the
exact reverse factorization

`weight(source) * relativeSourceEdgeLoad = novelEdgeLoad`.

Positive rational cancellation therefore gives an equivalence, not merely a
sufficient implication:

`delta_flow * novelEdgeLoad <= allocatedJointKernel`

if and only if

`delta_flow * relativeSourceEdgeLoad <= allocatedConditionalKernel`.

Every literal novel-flow occurrence is also proved to traverse a strictly
positive conditional transition.  A constructively cofinal family of the
relative conditional comparisons compiles through the exact capacity ratio
to the completed vacuum-sector strict-contraction datum.

The focused monitored check passes in about 1.2 seconds.  The exact
one-worker dependency-complete target passes 4,918 jobs, with the new module
taking about 1.1 seconds.  All five audited exports use exactly
`[propext, Quot.sound]`; no forbidden construct was added.

The common stationary source factor is no longer part of the analytic
obstruction.  The next frontier is to expand the relative load into the exact
path-incidence sum of endpoint stationary-weight ratios and compare that sum
uniformly with the allocated conditional transition probability.  Such a
uniform Markov/Harnack bound is not yet proved; the completed gap inhabitant,
continuum QFT, and Clay theorem remain open.

## Conditional Harnack load is now an exact path-incidence sum (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget` defines the
stationary endpoint/source ratio and proves that multiplication by the
strictly positive source weight recovers the endpoint weight exactly.  For
each literal novel endpoint pair, it then exposes the source-cancelled routed
demand as

`weight(pair.left) / weight(edge.source)`

`  * weight(pair.right) * pathLength(pair.left,pair.right)`

when the selected directed edge lies on the actual loop-erased positive path,
and as zero otherwise.  Summing these terms proves an exact equality with the
relative source edge load from the preceding milestone.

Consequently, the original physical joint-edge capacity comparison is proved
equivalent to bounding this explicit conditional-Harnack load by the allocated
conditional transition probability.  An all-edge proof of that comparison
gives the finite flow-capacity floor, and the cofinal structure
`CutoffTwoCofinalNovelConditionalHarnackBound` compiles it to completed
vacuum-sector strict contraction.

The first focused check exposed an incorrectly qualified private theorem name
and is not a pass.  After replacing it by the underlying constructive row-
marginal nonnegativity proof, the focused monitored check passes in about 1.3
seconds.  The exact one-worker dependency-complete target passes 4,919 jobs,
with the new module taking about 1.2 seconds.  All five audited exports use
exactly `[propext, Quot.sound]`.

The analytic obstruction is now the explicit finite path-incidence sum rather
than an opaque flow ratio.  The next frontier is to transport each stationary
endpoint/source ratio along its positive path using detailed balance and then
obtain a uniform projective/Harnack comparison with the selected conditional
transition, or prove that these paths overload cofinally and must be
redesigned.  The uniform completed gap inhabitant, continuum QFT, and Clay
theorem remain open.

## Stationary ratios telescope by pathwise detailed balance (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance` proves detailed
balance for the exact indexed conditional kernel used by the novel-flow load.
It also proves that a positive directed joint edge is positive in reverse and
hence has strictly positive conditional probabilities in both orientations.

On one positive directed edge, exact rational cross multiplication gives

`weight(left) / weight(right)`

`  = conditional(right,left) / conditional(left,right)`.

A recursive product over the existing Type-level positive-kernel chain then
telescopes these one-edge identities.  For any supported positive path from
`first` to `last`, the projective stationary ratio
`weight(first) / weight(last)` is exactly the product of its reverse/forward
conditional transition ratios.  The construction carries the initial and
successive carrier-membership proofs explicitly; it introduces no reachability
proposition or choice.

The first focused check found that support symmetry is exposed as an equality
and that the rational library provides separate left/right multiplication
congruences; a second check exposed the need to unfold the recursive endpoint
ratio before congruence.  Those failed checks are not passes.  The corrected
focused monitored check passes in about 1.4 seconds.  The exact one-worker
dependency-complete target passes 4,920 jobs, with the new module taking about
1.3 seconds.  All four audited exports use exactly
`[propext, Quot.sound]`.

The next frontier is to extract, from each actual directed-edge occurrence,
the positive prefix ending at that edge source.  Applying the telescoping
identity to that prefix will rewrite the exact conditional-Harnack summand in
local transition-ratio form.  A cutoff-uniform bound for the resulting sums,
the completed gap inhabitant, continuum QFT, and Clay theorem remain open.

## Conditional Harnack load is an exact transition-product sum (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget`
constructs, from literal membership of a directed edge in a positive path,
the positive prefix ending at that edge's source.  The extractor returns the
source and target carrier witnesses, the prefix as Type-level chain data, and
the selected edge's strict kernel positivity.  Its only generic computational
input is explicit `DecidableEq`; on the actual `Nat` carrier no classical
decision procedure is used.

Applying pathwise detailed balance to this prefix rewrites every nonzero
conditional-Harnack summand as

`product_{prefix edges u->v} conditional(v,u)/conditional(u,v)`

`  * weight(pair.right) * fullPathLength(pair)`.

The module proves exact equality of the finite summed load with the preceding
conditional-Harnack load.  It then proves that physical edge capacity is
equivalent to bounding this transition-product sum by the allocated
conditional transition probability.  The cofinal structure
`CutoffTwoCofinalNovelConditionalTransitionProductBound` compiles such bounds
to the completed vacuum-sector strict-contraction datum.

The first focused check found a reserved identifier and an explicit empty-path
contradiction; the second showed that eliminating propositional membership
directly into Type is forbidden; the third caught an implicit use of
`Classical.propDecidable`.  Those failed checks are not passes.  Supplying
constructive decidable equality and branching on the computed head-edge test
removes choice.  The corrected focused check passes in about 1.3 seconds.  The
exact one-worker dependency-complete target passes 4,921 jobs, with the new
module taking about 1.1 seconds.  Prefix extraction audits to `[propext]`; the
four downstream audited exports use exactly `[propext, Quot.sound]`.

The next analytic frontier is now local and multiplicative: obtain uniform
control of the reverse/forward conditional ratios along canonical prefixes,
then combine it with path length and endpoint-weight counting to bound the
explicit edge sum.  No such uniform estimate, completed gap inhabitant,
continuum QFT, or Clay theorem is claimed.

## Local projective distortion is separated from path counting (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling` introduces an
explicit nonnegative one-edge ceiling `rho` for the reverse/forward
conditional ratio on every positive directed edge of a fixed cutoff carrier.
It proves recursively that every exact prefix transition product is strictly
positive and satisfies

`prefixProduct <= rho ^ prefixLength`.

Substituting this inequality into each literal path-pair term and using
nonnegativity of the endpoint weight and path length yields a termwise bound.
Finite-list monotonicity then proves that the exact transition-product load is
bounded by the explicit ratio-ceiling load

`sum_{pairs crossing edge}`

`  rho^prefixLength * weight(pair.right) * fullPathLength(pair)`.

The cofinal structure `CutoffTwoCofinalNovelConditionalRatioCeilingBound`
keeps two obligations separate: a local one-edge ratio ceiling and a global
comparison of the resulting ceiling-weighted path count with the allocated
conditional transition.  Supplying both compiles to the already constructed
completed vacuum-sector strict-contraction datum.

The first focused check exposed unnamed carrier witnesses, a zero-length
unfolding issue, missing namespace openings, and a downstream timeout; the
second exposed one missing qualified natural-number nonnegativity theorem.
Those failed checks are not passes.  The corrected focused check passes in
about 1.3 seconds.  The exact one-worker dependency-complete target passes
4,922 jobs, with the new module taking about 1.2 seconds.  All five audited
exports use exactly `[propext, Quot.sound]`.

The remaining finite-volume analytic work is now visibly bifurcated: construct
and control the cutoff dependence of a concrete one-edge projective ceiling,
and prove that the corresponding weighted path count is uniformly payable by
the selected conditional transition.  Neither uniform estimate, the completed
gap inhabitant, continuum QFT, nor the Clay theorem is claimed.

## The fixed-cutoff projective ceiling is now constructed (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling` totalizes
the reverse/forward conditional ratio by zero away from positive directed
carrier edges and takes the located `Q'` maximum over the literal finite
Cartesian square of the cutoff-two vacuum-sector carrier.  The totalized ratio
and its maximum are proved nonnegative.

Every actual positive physical edge belongs to that finite Cartesian square,
so its reverse/forward conditional ratio is bounded by the constructed maximum
`cutoffTwoConditionalReverseForwardFiniteCeiling`.  This supplies an explicit
`CutoffTwoConditionalReverseForwardCeilingAt` datum at every fixed cutoff; the
local projective bound is no longer an assumed field there.

The resulting concrete ceiling load bounds the exact transition-product load.
The remaining cofinal certificate now asks only that, at chosen arbitrarily
late cutoffs, this fully constructed ceiling-weighted path load be payable by
the allocated conditional transition on every carrier edge.  Such a family
still compiles to completed vacuum-sector strict contraction.

The first focused check hit a deterministic elaboration timeout while
accidentally unfolding the large carrier, retained an unreduced pair lambda,
and missed two namespaces; it is not a pass.  After pinning the abstract
maximum argument and normalizing only the selected pair, the focused check
passes in about 1.1 seconds.  The exact one-worker dependency-complete target
passes 4,923 jobs, with the new module taking about 1.0 seconds.  All four
audited exports use exactly `[propext, Quot.sound]`.

The projective ceiling is therefore constructive at each finite cutoff, but no
uniform upper bound on its cutoff dependence is proved.  The decisive open
finite-volume frontier is the cofinal payment of its explicit weighted path
load; the completed gap inhabitant, continuum QFT, and Clay theorem remain
open.

## Concrete ratio-ceiling payment is now a finite reflected check (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision`
scans the literal Cartesian square of the cutoff-two vacuum-sector carrier.
For each ordered edge it decides the exact rational comparison

`coercivityFloor * concreteFiniteRatioCeilingLoad(source,target)`

`  <= allocatedConditionalKernel(source,target)`.

The Boolean checker is proved sound and complete for precisely this finite
payment predicate.  Successful evaluation therefore supplies every edgewise
ceiling-payment inequality and compiles through the concrete ceiling theorem
to the exact finite flow-capacity floor.

A separate recursive Type-level inspector avoids eliminating a propositional
existential into data.  It returns either the compiled finite floor bound or a
literal ordered carrier edge, its two membership witnesses, and the failed
rational payment inequality.  This distinguishes failure of the conservative
ceiling/path choice from an unavailable analytic proof; it does not turn such
a failure into a no-go theorem for the underlying exact flow.

The cofinal checked-schedule structure
`CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck` compiles successful
checks at arbitrarily late cutoffs to completed vacuum-sector strict
contraction.  No inhabitant of that cofinal structure is constructed here.

The focused monitored check passes in about 1.1 seconds.  The exact one-worker
dependency-complete target passes 4,924 jobs, with the new module taking about
1.1 seconds.  All five audited exports use exactly
`[propext, Quot.sound]`.

The next frontier is analytic and asymptotic: determine the cutoff behavior of
the constructed reverse/forward ceiling and the resulting weighted path load,
then either prove cofinal checker success or extract a systematic overload
family that forces a redesigned flow.  The uniform completed gap inhabitant,
thermodynamic/continuum construction, and Clay theorem remain open.

## The conditional ceiling is exactly a stationary-weight edge ratio (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope`
uses detailed balance to identify the totalized reverse/forward conditional
ratio on every positive physical edge with the stationary-weight ratio across
that edge.  Pointwise rational equivalence is lifted through the located
finite maximum, proving that the constructed conditional ceiling is exactly
the maximum positive-edge stationary-weight ratio.

The module then constructs a simpler all-pairs envelope: the located maximum
of `weight(left) / weight(right)` over the full finite Cartesian carrier.  The
positive-edge ceiling lies below this envelope, so the local projective datum
can now be supplied using stationary weights alone, without inspecting the
conditional-kernel support.

A constructive power induction proves monotonicity of every ceiling-weighted
path term in its ceiling.  Finite summation gives monotonicity of the whole
edge load and therefore bounds the concrete finite-ratio-ceiling load by the
stationary-envelope load.  A cofinal payment family for this explicit
stationary envelope still compiles to completed vacuum-sector strict
contraction.

The first focused check exposed missing namespace imports and is not a pass;
the second exposed dependent proof-witness normalization after unfolding and
is not a pass.  The corrected focused monitored check passes in about 1.3
seconds.  The exact one-worker dependency-complete target passes 4,925 jobs,
with the new module taking about 1.3 seconds.  All seven audited exports use
exactly `[propext, Quot.sound]`.

This clarifies the asymptotic issue but does not solve it: the sufficient
all-pairs envelope can grow when the smallest carrier weight shrinks, and no
uniform ceiling or payment theorem is claimed.  The next frontier is to
factor that envelope into an explicit numerator ceiling and positive
stationary-weight minimum, compare those quantities with the known normalized
mass bounds, and determine whether the resulting estimate can be uniform or
is necessarily too coarse.  The completed gap inhabitant, continuum QFT, and
Clay theorem remain open.

## Stationary oscillation factors into a finite maximum and minimum (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation`
constructs the located maximum and positive minimum of the stationary weights
on every finite cutoff-two vacuum-sector carrier.  Literal membership gives
the expected pointwise upper and lower bounds, while finite maximum-to-sum
comparison proves that the maximum lies below the sector mass.

The previously proved normalized-sector estimate then gives

`maximumWeight <= sectorMass <= 1`.

Cross-multiplication with positive denominators proves the explicit chain

`positiveEdgeConditionalCeiling`

`  <= allPairsStationaryRatioEnvelope`

`  <= maximumWeight / minimumWeight`

`  <= 1 / minimumWeight`.

The reciprocal-minimum envelope supplies a valid local ratio-ceiling datum.
Monotonicity of the ceiling-weighted load carries it into a sufficient
edge-payment theorem and a cofinal compiler to completed vacuum-sector strict
contraction.

The focused monitored check passes on its first attempt in about 1.1 seconds.
The exact one-worker dependency-complete target passes 4,926 jobs, with the
new module taking about 1.1 seconds.  All eight audited exports use exactly
`[propext, Quot.sound]`.

This is a diagnostic contraction, not a uniform estimate.  The reciprocal of
the global minimum is deliberately coarse and can diverge solely because the
carrier expands; it must not be mistaken for the sharper adjacent-edge
oscillation.  The next frontier is therefore to preserve adjacency and seek a
local BF4 weight-ratio estimate from the explicit action/support geometry, or
to certify that the chosen canonical paths encounter growing adjacent
oscillation.  The uniform completed gap inhabitant, continuum QFT, and Clay
theorem remain open.

## The global partition cancels from every positive-edge ratio (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio` defines the
unnormalized reflected BF4 row mass of every indexed vacuum-sector state as
the finite sum of `centralPhysicalReflectedKernel` over the literal positive
carrier.  The pre-existing general marginal factorization is specialized to
prove, on every retained state,

`stationaryWeight = rawRowMass * commonPartitionReciprocal`

in the rational setoid.  Retained stationary-weight positivity and positivity
of the common reciprocal then constructively imply strict positivity of the
raw row mass, so all following divisions have explicit positive-denominator
witnesses.

Cross multiplication cancels the common reciprocal exactly from each ordered
carrier ratio.  After restricting to positive physical edges and lifting the
pointwise identity through the located finite maximum, the already constructed
reverse/forward conditional ceiling is proved exactly equal to the maximum of
unnormalized BF4 row-mass ratios on positive edges.  A raw-row ceiling datum,
edge-load payment theorem, and cofinal compiler carry any eventual raw-row
capacity estimate through to completed vacuum-sector strict contraction.

The first two focused checks exposed missing namespace openings and are not
passes.  The corrected focused monitored check passes in about 1.4 seconds.
The exact one-worker dependency-complete target passes 4,966 jobs, with the new
module taking about 1.3 seconds.  All seven audited exports use exactly
`[propext, Quot.sound]`.

This removes a global normalization obstruction but does not provide a
cutoff-uniform local estimate.  The next frontier is to expand each raw row
mass into its finite boundary-channel weighted-Gram sum and isolate what
comparison of neighboring BF4 amplitudes or local action terms would bound
the positive-edge row ratio uniformly.  The uniform payment theorem,
completed gap inhabitant, thermodynamic/continuum theory, and Clay theorem
remain open.

## Raw rows are boundary moments; amplitude Harnack bounds their ratios (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment` expands
the unnormalized reflected row sum through the genuine weighted-Gram
factorization and finite Fubini reordering.  For every retained indexed state,
the raw row mass is exactly

`sum_boundary boundaryWeight * sourceHalfAmplitude * totalTargetAmplitude`.

All three factors are the literal BF4 boundary data, and their required
nonnegativity is proved on the finite boundary carrier.  The module introduces
the Type-level datum `CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt`: on each
positive physical edge it compares the two source half-amplitudes pointwise
on every boundary channel by one nonnegative factor `rho`.

Multiplication by the common nonnegative boundary weight and target-amplitude
total preserves that comparison.  Finite summation bounds the raw row masses,
positive-denominator division bounds their ratio, and the preceding exact
normalization cancellation plus detailed balance bounds the reverse/forward
conditional ratio.  Thus this local amplitude datum constructs the existing
conditional-ceiling datum.  A cofinal fixed-`rho` Harnack-and-payment family
then compiles to completed vacuum-sector strict contraction.

The first focused check exposed two missing namespace openings and is not a
pass.  The corrected focused monitored check passes in about 1.3 seconds.  The
exact one-worker dependency-complete target passes 4,967 jobs, with the new
module taking about 1.2 seconds.  All seven audited exports use exactly
`[propext, Quot.sound]`.

This is a sufficient reduction, not an inhabitant of the local Harnack datum.
Pointwise domination can be too strong when adjacent Gram rows have overlapping
but non-nested boundary support.  The next frontier is therefore to inspect the
explicit positive-edge support geometry and existing projective/Harnack
machinery, then either construct the amplitude comparison on the relevant
weighted support or replace it by a support-aware moment comparison.  Uniform
payment, the completed gap inhabitant, thermodynamic/continuum theory, and the
Clay theorem remain open.

## Structural zeros force a support-aware defect (2026-08-23)

`BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect` tests the
preceding pointwise Harnack interface against the literal cutoff-two carrier.
The cube state and vacuum state form a positive physical edge, while on the
explicit single-face boundary the cube half-amplitude is strictly positive and
the vacuum half-amplitude is exactly zero.  Consequently no finite rational
factor can satisfy the proposed all-boundary positive-edge Harnack condition at
cutoff two.  This is a kernel-checked no-go theorem for that sufficient route,
not an assertion about every possible local comparison.

The module replaces pointwise domination by the exact nonnegative relative
defect

`abs (sourceHalfAmplitude(left) - rho * sourceHalfAmplitude(right))`.

After weighting by the same boundary weight and total target amplitude as the
raw row moment, the elementary inequality `left <= rho * right + defect`
propagates through the finite boundary sum.  Dividing by the positive right raw
row mass gives

`rawRatio <= rho + weightedDefectMoment / rightRawMass`.

A totalized positive-edge defect fraction and its literal finite carrier
maximum therefore construct a support-aware conditional reverse/forward
ceiling.  The corresponding load comparison, capacity-floor theorem, and
cofinal payment compiler carry any eventual uniform estimate on this new
quantity to completed vacuum-sector strict contraction.

The first focused check exposed missing namespace openings and an incorrect
setoid addition congruence; the second exposed an implicit-argument inference
site.  Neither failed check counts as a pass.  The corrected focused monitored
check passes in about 1.5 seconds.  The exact one-worker dependency-complete
target passes 4,973 jobs, with the new module taking about 1.6 seconds.  All
eight audited exports use exactly `[propext, Quot.sound]`.

No uniform defect estimate or payment is supplied.  The next frontier is to
identify the weighted defect moment with an existing boundary-posterior `L1`
quantity (or prove the precise comparison), so the already developed posterior
mixing machinery can address structural-zero leakage without restoring the
false pointwise hypothesis.  The uniform completed gap inhabitant,
thermodynamic/continuum theory, and Clay theorem remain open.
