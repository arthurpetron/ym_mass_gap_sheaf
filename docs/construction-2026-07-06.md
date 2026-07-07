# Constructing the real 4D SU(2) block-spin margin — and the machine-refutation of the naive identification

**Target.** Dissolve the free-field vacuity of
`SingleStepDefectReduction.SingleStepDefectBound.trueMargin` (a FREE `Nat→Q'`, so
`singleStep` is vacuously fakeable) by CONSTRUCTING the real per-scale block-spin margin
from the PROVED objects (`reconTransfer_located_gap`, the AF flow, Routes F/H/I), and make
the identification `realLeak = δ_ren` a genuine theorem — or report honestly what it
reduces to.

**Deliverables.**
`lean/YMGap/Continuum/BlockSpinMarginConstruction.lean` (full `lake build` green, frontier
guard OK at 5, axiom-clean), this report. Committed: nothing (per instructions).

---

## 1. The construction (CONCRETE, non-free)

Following Route F (the real `reconTransfer_located_gap.sep` **is** the character
eigenvalue `coeffW gw 1`) and Route I (the physical gap edge is the multiplicity-BLIND
transfer EIGENVALUE `eigA w 1 = w^{C₄(1)} = w³`, not the amplitude `coeffW`), the real
fixed-spacing eigenvalue margin at RG scale `k` is the CONCRETE sequence

```
eigMarginSeq afr k  :=  1 − w_k³ ,     w_k = afr.w (afCutoff afr + k)   (the AF-flowed coupling)
```

`def eigMarginSeq (afr : AFRateModulus) (k : Nat) : Q' := 1 - qpow (afr.w (afCutoff afr + k)) (c4 1)`.
This is a genuine `Nat → Q'`, NOT a free field — every value is the real transfer
eigenvalue margin at the AF-flowed coupling.

Its per-step degradation is the eigenvalue shift (Route I `bulk_shift`):
`eigShiftSeq afr k := w_{k+1}³ − w_k³`.

---

## 2. The exact additive degradation identity (PROVED)

`eigMargin_degradation_eq_shift` (axioms `[propext, Quot.sound]`):

```
eigMarginSeq afr k − eigMarginSeq afr (k+1)  ≃  eigShiftSeq afr k  =  w_{k+1}³ − w_k³
```

for EVERY AF rate — the exact `Q'` identity `(1−a)−(1−b) ≃ b−a`
(`oneSub_sub_oneSub_eqv`, pure additive algebra, `[propext]`). So the CONSTRUCTED margin's
degradation is EXACTLY the multiplicity-blind coupling-flow eigenvalue shift — precisely
Route I's `EigenvalueShiftDefect.eigShift`.

---

## 3. THE CRUX — the constructed margin PROVABLY FAILS the multiplicative `singleStep`

`SingleStepDefectBound.singleStep` is the MULTIPLICATIVE recursion
`(1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)`. Since
`afDefectSeq afr k = renDefect afr 1 (afCutoff+k) = bondMovingDeltaRen 1 1 (w_k)` exactly,
the model defect at coupling `w` is `bondMovingDeltaRen 1 1 w`. Instantiating `singleStep`
with `trueMargin := eigMarginSeq` at the genuine consecutive canonical AF-trajectory
couplings `w = 10/11 = w₁₀`, `w' = 11/12 = w₁₁` (`afRateModulus_canonical.w k = 1−1/(k+1)`):

| quantity | exact value | decimal |
|---|---|---|
| `δ = bondMovingDeltaRen 1 1 (10/11)` | `64/1331` | 0.04808 |
| `1 − w³` | `331/1331` | 0.24869 |
| **LHS** `(1−δ)·(1−w³)` | `419377/1771561` | **0.23673** |
| **RHS** `1 − w'³` | `397/1728` | **0.22975** |

**LHS > RHS**, so `singleStep` is **FALSE**. Machine-proved by kernel `decide`
(**zero axioms**): `eigMargin_fails_singleStep`. mpmath (dps 50) + exact `fractions`
confirm; the multiplicative step fails for ALL large `k` on every AF rate tested
(A = 1/2, 1, 2), the slack `→ −3A/k²` — systemic, not a boundary artifact — so it
certainly fails on the deep-UV tail `[afCutoff, ∞)` where `SingleStepDefectBound` lives.

**Contrast — the ADDITIVE Route-I bound HOLDS at the same pair**
(`eigShift_le_delta_at_pair`, zero axioms):

```
w'³ − w³ = 43561/2299968 ≈ 0.01894   ≤   δ = 64/1331 ≈ 0.04808 .
```

`additive_holds_multiplicative_fails` bundles both. So the constructed margin's
degradation obeys the ADDITIVE eigenvalue-shift bound (`EigenvalueShiftDefect`) but
VIOLATES the MULTIPLICATIVE `singleStep`. The two inequalities are genuinely different:
`singleStep` demands `w'³ − w³ ≤ δ·(1 − w³)`, which carries an extra factor `(1 − w³) → 0`
and fails; Route I only asserts `w'³ − w³ ≤ δ`.

---

## 4. WHY it fails — the honest structural diagnosis

The multiplicative recursion `(1−δ_k)·m_k ≤ m_{k+1}` with SUMMABLE `δ_k` FORCES a positive
floor `m_k ≥ m_0·∏(1−δ_k) > 0` (this is exactly what `defectRecursion_of_singleStep` +
`afFloorEps` deliver — the whole point of `SingleStepDefectBound`). But the fixed-spacing
eigenvalue margin `1 − w_k³ → 0` as `w_k → 1` (the deep-UV/continuum end of the AF flow).
A sequence tending to `0` CANNOT satisfy that recursion with a positive floor — hence the
refutation is not an accident, it is structural.

The category error is precise: **`1 − w_k³` is the fixed-spacing lattice gap (in lattice
units), which SHRINKS as the continuum is approached; it is NOT the dimensionless
RG-invariant margin `m_lat(a_k)/a_k`, which converges to `m_phys > 0`.** The physical mass
in physical units is `m_phys = lim m_lat(a_k)/a_k`, and `m_lat(a_k) ∼ m_phys·a_k → 0` in
lattice units — exactly mirroring `1 − w_k³ → 0`. What is missing from the naive
identification is the **dimensionful spacing rescaling** (the accumulated block factor
`b^k`, `a_{k+1} = b·a_k`) that divides the shrinking numerator by `a_k` to produce the
constant dimensionless margin.

---

## 5. Adversarial verdict — is the construction the REAL block-spin margin, or a relabeling?

**It is a genuine object but NOT the real dimensionless margin — and the module proves
this, rather than papering over it.** The construction:

- **dissolves the *free-field* vacuity** — `eigMarginSeq` is a concrete `Nat→Q'` tied to
  the real transfer eigenvalue (`reconTransfer_located_gap`, Route F/I), not a free field;
- **has an exact, proved degradation** = the multiplicity-blind eigenvalue shift (Route I);
- but **is machine-refuted as an inhabitant of `SingleStepDefectBound`** — so the
  identification `realLeak = δ_ren` does NOT close the multiplicative margin recursion.

So the answer to the task's crux ("is the degradation EXACTLY δ_ren, or is there a gap?")
is: **there is a genuine gap, and it is dimensionful.** The eigenvalue-shift numerator
`w_{k+1}³ − w_k³` is correctly bounded by `δ` additively (Route I), but the MULTIPLICATIVE
margin recursion that the product floor needs is a statement about `m_lat/a`, whose
`a_k`-denominator the eigenvalue margin omits. The real block-spin flow does have content
beyond the fixed-`w` eigenvalue shift: the accumulated scale factor. This is the concrete,
non-free RG obligation the identification reduces to.

**Reduction achieved (honest):** free-field vacuity of `SingleStepDefectBound.trueMargin`
→ a concrete eigenvalue margin whose degradation is the proved eigenvalue shift → the SOLE
remaining obligation is the **dimensionful spacing rescaling** turning `1 − w_k³` (eroding)
into `m_lat(a_k)/a_k` (RG-invariant), i.e. supplying the `a_k`-denominator that makes the
additive eigenvalue-shift bound into the multiplicative margin recursion. Equivalently:
the residual is `EigenvalueShiftDefect` (additive, proved satisfiable at every tested
point) **plus** the rescaling bridge; the multiplicative `singleStep` for the bare
eigenvalue margin is FALSE.

---

## 6. Build / guard / axioms — nothing guarded inhabited

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
      uninhabited across YMGap.*
Build completed successfully (690 jobs).
```

`#print axioms` for all load-bearing declarations:

| declaration | axioms |
|---|---|
| `oneSub_sub_oneSub_eqv` | `[propext]` |
| `eigMargin_degradation_eq_shift` | `[propext, Quot.sound]` |
| `eigMargin_fails_singleStep` | **none** (kernel `decide`) |
| `eigShift_le_delta_at_pair` | **none** (kernel `decide`) |
| `additive_holds_multiplicative_fails` | **none** |

No `Classical.*`, no `native_decide`, no `sorry`/`admit`. **No `SingleStepDefectBound`,
`TrueMarginRecursion`, `GapChannelDomination`, `FullRangeFusedDefect`,
`EigenvalueShiftDefect`, or any guarded bundle (`Tier0Scorecard`,
`UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) is inhabited.**
The guard is UNCHANGED at 5.

**MANDATORY STOP CHECK (task condition (ii)):** the constructed margin does **NOT** inhabit
`SingleStepDefectBound` — the required `singleStep` is machine-REFUTED for it
(`eigMargin_fails_singleStep`). Therefore there is no cascade to `TrueMarginRecursion` /
`FrontierDAG.trueMargin`, no guard trip, and no guarded inhabitant is left. This is the
safe (honest-negative) outcome, reported rather than hidden.

## 7. Honest verdict (one line)

`eigMarginSeq` makes the free-field `trueMargin` CONCRETE and gives its degradation an
exact identity = the eigenvalue shift, but PROVES (kernel `decide`, zero axioms) that the
fixed-spacing eigenvalue margin `1 − w_k³` (which erodes to `0`) does NOT satisfy the
multiplicative `singleStep` — so the identification `realLeak = δ_ren` does NOT close
`SingleStepDefectBound`; it reduces the vacuity to the genuine dimensionful obligation of
rescaling the eroding fixed-spacing margin into the RG-invariant dimensionless margin
`m_lat/a`. The 4D Yang–Mills mass gap remains **OPEN**; nothing is faked; no free field is
left; no guarded bundle is inhabited.
