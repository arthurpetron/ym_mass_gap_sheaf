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
