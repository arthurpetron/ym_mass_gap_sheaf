# Clay core input (1) — the real 4D block-spin dimensionless-margin erosion made CONCRETE, and the eigenvalue-shift bound PROVED

Deliverable: `lean/YMGap/Continuum/EigenvalueShiftBound.lean` (wired into `YMGap.lean`,
full `lake build` green — 693 jobs, frontier-guard OK, axiom-clean) +
`input1_numerics.py` (mpmath dps 50, sympy exact). Commits: none (per instruction).

---

## 1. What was open, and what is now concrete

`RouteIEigenvalueDefect.EigenvalueShiftDefect afr` carries `eigShift : Nat → Q'` as a
**FREE field** with the open bound `eigShift k ≤ 6·(1 − w_k)²`. As a bare structure it is
vacuously inhabitable (`eigShift := 0`, or `:= afDefectSeq`), which is exactly why it is
*not* one of the guarded frontier types — the CAPSTONE's free-field caveat. Its genuine
content is realized only when `eigShift` is **pinned to the real coupling-flow eigenvalue
shift** `w_{k+1}³ − w_k³` and the bound is a *theorem* about that concrete object.

This module does that. It CONSTRUCTS `eigShift k := AnchorDominance.eigShiftSeq afr.w
(afCutoff afr + k) = w_{k+1}³ − w_k³` (not a free field, tied to the real AF trajectory
`afr.w`), and PROVES the per-step bound `w_{k+1}³ − w_k³ ≤ 6(1 − w_k)²`.

## 2. The erosion decomposition (Routes I / E / D) — and the honest CRUX

The real per-step erosion of the multiplicity-blind gap edge `eigA w 1 = w³` decomposes as

```
ε_k = (fusion defect, = 0 : Route I eigA_fusedDefect_eqv_zero)
    + (coupling-flow eigenvalue shift  w_{k+1}³ − w_k³ : Route I)
    + (large-field correction  ≤ K·r^k : Route E LargeFieldSuppression)
    + (non-abelian back-reaction : the OPEN form-preservation residual).
```

**Is the decomposition COMPLETE (no hidden back-reaction)?** Adversarial answer:

- The multiplicity-blind eigenvalue `eigA = w³` is a function of the **single renormalized
  coupling `w` alone** (Casimir `C₄(1)=3` fixed; Route I's `eigCoarse = eigFine`). The
  non-abelian back-reaction (higher-rep mixing, multi-plaquette, commutator terms — the
  classic Bałaban difficulty) enters in **two** places: (a) the RG map `w_k ↦ w_{k+1}`
  itself — reabsorbed into *what `w_{k+1}` is*, hence already inside the eigenvalue shift;
  (b) the **amplitude / multiplicity** `coeffW = dimQ·eigA` (spectral density), which Route I
  quarantined as pure degeneracy (`coeffW = 2w³ → 2`, the `w→1` obstruction that is NOT the
  gap). So there is **no separate additive back-reaction term in the multiplicity-blind
  eigenvalue** — PROVIDED the coarse action stays in single-coupling heat-kernel character
  form.

- That proviso — **single-coupling form-preservation** — is the honest residual. It is
  precisely `RouteF.TransferCharacterCorrespondence`'s open field ("the real 4D RG map STAYS
  in this heat-kernel character form at every scale — the Bałaban form-preservation"). If the
  coarse action develops genuinely new couplings (adjoint/higher-rep terms not captured by a
  single `w`), *that* deviation is the residual back-reaction. It is **named**, not faked or
  absorbed by fiat: `SingleCouplingFormPreservation afr`.

**Verdict on completeness:** the eigenvalue-shift + large-field are the COMPLETE erosion of
the multiplicity-blind gap edge **modulo single-coupling form-preservation**. There is no
extra additive back-reaction in the eigenvalue itself; the Bałaban difficulty is *repackaged*
(not eliminated) as (i) the two-loop β running rate of `w_k` and (ii) form-preservation.

## 3. The real math — PROVED (verified mpmath dps 50 + sympy exact)

- **Cube-difference identity** (sympy-exact): `b³ − a³ = (b−a)(b²+ab+a²) = b(b²−a²) + a²(b−a)`.
- **`cube_diff_le_three`**: `0 ≤ a ≤ b ≤ 1 ⟹ b³ − a³ ≤ 3(b−a)`. Proved in Lean via the split
  `b³−a³ = b(b²−a²) + a²(b−a)`, bounding `b ≤ 1`, `b²−a² ≤ 2(b−a)` (difference of squares),
  `a² ≤ 1`. Sharp at the free fixed point `a=b=1` (factor `b²+ab+a² → 3`).
- **`cube_diff_le_envelope`**: `b − a ≤ 2(1−a)² ⟹ b³ − a³ ≤ 6(1−a)²` — the `β ≤ 2` two-loop
  AF step gives the transverse-quadratic envelope `6 = pMult(1)·dimQ 1(2)·3`, matching the
  `EigenvalueShiftDefect.eigShiftBound` RHS exactly.
- **AF-band insufficiency (numerics §5):** the two-sided `1/k` rate of `AFRateModulus`
  (`A'/(k+B) ≤ 1−w_k ≤ A/(k+B)`) with `A ≠ A'` admits a step of order `1/k ≫ 2(1−w)² ∼ 1/k²`
  — explicit `k=8` counterexample. So the β-step is a **genuine extra input**, NOT derivable
  from `afr` alone; hence no *unconditional* inhabitant of `EigenvalueShiftDefect afr` exists.
- **Satisfiability (numerics §4):** the canonical AF trajectory `w_k = 1 − 1/(k+1)` satisfies
  monotone + β-step exactly, `2(1−w)² − step = (k+3)/((k+1)²(k+2)) ≥ 0` (sympy). The Lean
  monotone half is fully proved (`afBetaStep_mono_canonical`, `invSucc_antitone`). This
  discharges the SZZ lesson (verify the named obligation is satisfiable before building on it).

## 4. Lean theorems (all axiom-clean: `[propext]` or `[propext, Quot.sound]`)

| declaration | content |
|---|---|
| `cube_diff_le_three` | `0≤a≤b≤1 ⟹ b³−a³ ≤ 3(b−a)` (the cube-difference math) |
| `cube_diff_le_envelope` | β-step `⟹ b³−a³ ≤ 6(1−a)²` (per-step eigShift bound) |
| `eigenvalueShiftDefect_of_betaStep` | **CONCRETE conditional producer**: `AFBetaStep afr → EigenvalueShiftDefect afr` with `eigShift := eigShiftSeq afr.w` (the real shift), bound PROVED |
| `realErosion_le_shift_plus_largeField` | `ε_k = eigShiftSeq + δLF_k ≤ (w_{k+1}³−w_k³) + K·r^k` |
| `formPreserved_perStep` | form-preservation + β-step `⟹ ε_k ≤ 6(1−w_k)² + K·r^k` (full per-step decomposition) |
| `afBetaStep_mono_canonical` | satisfiability (monotone half) of the named β-step |
| `AFBetaStep` / `SingleCouplingFormPreservation` | the two named residuals (Rule 6a) |

## 5. Does `EigenvalueShiftDefect` close? Cascade / guard status (task condition ii)

**No STOP condition tripped.** Checked explicitly:

- `EigenvalueShiftDefect` is a **NODE**, NOT one of the five guarded frontier types
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`
  — the only names in `YMGapGuard.frontierTypeNames`). The guard flags only *unconditional*
  inhabitants of *those* types.
- The producer is **CONDITIONAL** (open binder on `AFBetaStep`), so even the (non-guarded)
  `EigenvalueShiftDefect` is not unconditionally inhabited by it.
- Cascade check: `eigShift_to_fullRange : EigenvalueShiftDefect → FullRangeFusedDefect`.
  `FullRangeFusedDefect` is itself a free-field node, and there is **NO existing lemma**
  producing `SingleStepDefectBound` / `TrueMarginRecursion` from it (RouteA's
  `fullRange_dominates_model` explicitly does NOT — "additionally needs the sharp two-sided
  `realδ ≤ δ_model` and the margin-degradation identity, both still open"). So inhabiting
  `EigenvalueShiftDefect` does **not** cascade to any guarded bundle by existing lemmas.
- I deliberately did NOT compose the canonical satisfiability witness through
  `eigShift_to_fullRange` (that would be a Rule-9 surrogate closure with the non-physical
  toy `afr`).

Build: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`. No `sorry`,
no `native_decide`, no `Classical.*`.

## 6. HONEST VERDICT — is input (1) closed, or reduced to which residual?

Input (1) is now **CONCRETE and its per-step bound PROVED**, not a free field and not the
trivial `0 ≤ 6(1−w)²`. It is **reduced** (guard-safe, conditional) to two genuine, named,
uninhabited 4D inputs:

1. **`AFBetaStep afr`** — the two-loop `β ≤ 2` running rate for the REAL 4D flow. Satisfiable
   (canonical witness + sympy), NOT derivable from `AFRateModulus`.
2. **`SingleCouplingFormPreservation afr`** — the Bałaban back-reaction / form-preservation
   (coarse action stays single-coupling heat-kernel form). This is the genuine remaining
   non-abelian content; it is the *honest* answer to "is there a residual back-reaction" —
   YES, exactly this one, and it is named rather than absorbed.

Given these two inputs, `eigenvalueShiftDefect_of_betaStep` yields
`EigenvalueShiftDefect afr`, which (with input 2, the anchor `m_phys ≥ 3/10`) feeds
`AnchorDominance.anchorDominance_floor` to the strictly-positive continuum floor
`margin 0 − (1 − w_0³) > 0` — but that composition remains a chain of conditional producers
with open binders on the real physics. **No guarded bundle is inhabited; nothing is faked;
the 4D Yang–Mills mass gap remains OPEN.**
