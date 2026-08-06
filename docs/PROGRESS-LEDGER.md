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
