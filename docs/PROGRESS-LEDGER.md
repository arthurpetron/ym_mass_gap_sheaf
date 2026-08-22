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
