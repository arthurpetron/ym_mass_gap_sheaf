# 2D Yang–Mills END-TO-END ADEQUACY TEST

**File:** `lean/YMGap/Continuum/TwoDYangMillsAdequacy.lean` (new; imported in `lean/YMGap.lean` after `YMGap.Rubric.ClayScorecard`).
**Build:** `lake build` exit 0 (130 jobs). **Frontier guard:** `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` — UNCHANGED (still 5).
**Axioms:** every declaration `⊆ {propext, Quot.sound}`; no `sorryAx`, no `native_decide`, no new axiom. Lean-core only (Q'/CReal/Nat).

---

## What was built (the genuine 2D YM object)

In d=2, after gauge fixing the heat-kernel lattice measure factorizes; the single-plaquette weight IS the heat kernel `K_t(g)=Σ_R dim(R)χ_R(g)e^{−t·C₂(R)}`. This is *exactly* what the repo already carries as `WilsonFunctional.wilsonCharExp` / `ReflectionPositivity.reflWeight` — so the repo's SU(2) heat-kernel layer IS 2D Yang–Mills (in d=2 it is the *complete* theory, not a per-plaquette fragment).

Operating point: `t = 4/3`, fundamental `s=1`, `C₂(fund)=3/4`, so `t·C₂(fund)=1` and `λ_fund = e^{−1} ≤ 5/12 < 1`. Gap margin `1 − 5/12 = 7/12 > 0`.

| Lean object | Content | Status |
|---|---|---|
| `twoDCoupling = 4/3`, `twoDSep = 5/12` | explicit operating point | def |
| `twoD_arg_eqv_one` | `t·C₂(fund) = 1` exactly | proved |
| `twoD_fund_le` | true CReal eigenvalue `reflWeight = e^{−1} ≤ 5/12` (genuineness link) | proved `[propext]` |
| `twoDModel : SpectralModel` | 2D Källén–Lehmann transfer model (fundamental mode, `w=1>0`, `λ=5/12`) | def |
| `twoDLocatedGap : LocatedSpectralGap twoDModel` | `sep=5/12<1`, `∀i λᵢ≤sep` | def (non-vacuous) |
| `twoD_gapMargin_pos` | `1 − sep = 7/12 > 0` — the mass gap | proved `[propext,Quot.sound]` |
| `twoD_clustering` | `G(n) ≤ G(0)·(5/12)ⁿ` (Källén–Lehmann decay) | proved `[propext]` |
| `twoD_os2` | OS2 reflection positivity, ALL orders, ALL real c (exact in 2D) | proved `[propext,Quot.sound]` |
| `twoDClayTarget : TwoDClayTarget` | **d=2 analogue of ClayTargetPinned — GENUINELY INHABITED** | proved `[propext,Quot.sound]` |

`twoD_fund_le` is the honesty anchor: the located *rational* separator `5/12` provably dominates the *true irrational* heat-kernel eigenvalue `e^{−1}` (via `ExpNeg.expNeg_one_leRat` transported across `t·C₂=1`), so `twoDLocatedGap` is a rigorous bound on the exact 2D theory, not a surrogate. True 2D gap `1 − e^{−1} ≥ 7/12 > 0`.

`TwoDClayTarget` is a **separate, non-frontier type** mirroring the four Clay clauses at d=2, and it is genuinely inhabited (`twoDClayTarget`) — the joint-inhabitability certificate. It is NOT any guarded d=4 type; inhabiting it does not inhabit any of them (guard stayed 5).

---

## Per-interface adequacy table (the core deliverable)

| Pipeline interface (d=4 pipeline uses) | Composes with real 2D YM? | Witness / finding |
|---|---|---|
| `SpectralModel` (finite transfer op) | **YES** | `twoDModel` — real 2D character-expansion model |
| `LocatedSpectralGap` (`sep<1`, compact 2nd eigenvalue) | **YES** | `twoDLocatedGap` — explicit `sep=5/12`, margin `7/12` |
| `SpectralGapBound ⇒ clustering` (`decay_of_spectralGap`) | **YES** | `twoD_clustering` — real geometric decay |
| `ReflectionPositiveSchwinger` (OS2) | **YES (exact)** | `twoD_os2` — heat kernel is the *complete* 2D weight; all orders, all real c |
| `RubricNontrivial` (genuine excited mode) | **YES** | `twoDModel.w 0 = 1 > 0` |
| `ClayScorecard.ClayContinuumExistence` | **NO — d=4-hardwired** | fields `defectRecursion : DefectGapRecursion`, `loopyResidual : LoopyCorrelatorResidual gw` are tied to the 4D block-spin recursion + 4D data `gw`. 2D supplies its OWN clause (`TwoDContinuumExistence`, inhabited) — honest, since 2D is a genuinely different (finite) theory. |
| `ClayScorecard.RubricO4Restoration` (OS0) | **INTERFACE DEBT** | `rubricO4_trivially_satisfiable` — PROVABLE unconditionally (defect ≡ 0) |
| `ClayScorecard.RubricUniformInCoupling` (OS4) | **INTERFACE DEBT** | `rubricUniform_trivially_satisfiable` — PROVABLE unconditionally (constant schedule, defect ≡ 0) |

The analytic core (located gap, OS2, clustering, nontriviality) **jointly composes** with real 2D YM → adequacy PASS for the load-bearing chain.

---

## HIGH-VALUE FINDINGS (latent interface debt — the SixJPentagon failure mode, live)

Two of the four Clay clauses in the d=4 `ClayScorecard.ClayTarget` are **dimension-blind and trivially satisfiable** — machine-proved here with NO axioms beyond `propext`:

1. **`RubricO4Restoration` (OS0 / O(4) restoration) is trivially satisfiable.**
   Its "rotational-anisotropy defect" is existentially chosen *after* the scale `k`, with no pin to a real lattice anisotropy, so `defect ≡ 0` discharges the whole Prop. The in-code comment claims a "non-vacuity guard … pinned to a genuine positive baseline so the predicate is not free" — but the baseline is only an *upper* bound on a *freely chosen* defect, so it pins nothing. The Prop carries no content that could fail in d=4.

2. **`RubricUniformInCoupling` (OS4 / uniform-in-coupling gap) is trivially satisfiable.**
   A constant positive gap schedule with zero degradation (`defect ≡ 0`) discharges it, so it does not encode the running-coupling degradation it names.

Consequence for the guard/architecture: with `ClayFixedSpacingMet` already proved and these two Props now shown trivially provable, the *only* substantive obstruction inside `ClayTarget` is `ClayContinuumExistence` (the genuinely d=4-hardwired `DefectGapRecursion` + `LoopyCorrelatorResidual gw`). The two OS0/OS4 rubric Props are the WRONG TYPE to carry the frontier — exactly the interface-debt (SixJPentagon) pattern this test defends against. **Neither proof inhabits `ClayTarget`** (that still needs `ClayContinuumExistence`), so the frontier guard is unaffected and correctly stays at 5 — but the finding is that two of its four clauses would not, on their own, stop a vacuous closure.

Recommended remediation (not done — would edit guarded/rubric files owned elsewhere): re-type `RubricO4Restoration` / `RubricUniformInCoupling` so the defect/schedule is a *fixed universally-quantified family pinned to a real anisotropy / real running gap*, not an inner existential chosen per scale. As stated they are `∀ε ∃…` with the physics existentially escaping.

---

## Honest verdict

**ADEQUACY PASS for the analytic chain.** The load-bearing mass-gap interfaces — `SpectralModel`, `LocatedSpectralGap`, `ReflectionPositiveSchwinger` (OS2), `decay_of_spectralGap` (clustering), `RubricNontrivial` — are JOINTLY inhabitable by exactly-solvable 2D Yang–Mills, machine-checked and axiom-clean, assembled into a genuinely-inhabited `TwoDClayTarget`. These interfaces are real: 2D field theory satisfies the SAME types the d=4 pipeline routes the gap through.

**One interface is honestly d=4-specific:** `ClayContinuumExistence` (2D gets its own trivial-limit clause — correct, 2D is finite).

**Two interfaces are interface debt:** `RubricO4Restoration` and `RubricUniformInCoupling` are dimension-blind and trivially satisfiable — they cannot carry the d=4 OS0/OS4 frontier content as currently typed. This is the sharpest structural finding.

Guard: **5** (unchanged). Clay YM mass gap: **OPEN**. No d=4 frontier type inhabited.
