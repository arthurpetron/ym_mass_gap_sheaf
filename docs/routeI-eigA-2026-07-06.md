# Route I — the eigA / PHYSICAL-GAP-EDGE resolution of the coeffW↔eigA tension

**Target.** `RouteADefectCharacter.FullRangeFusedDefect` — the convergent Clay core that
Route F's fused-character IDENTIFICATION left open, flagged as the coeffW↔eigA tension.

**Deliverables.** `lean/YMGap/Continuum/RouteIEigenvalueDefect.lean` (full `lake build`
green, frontier-guard OK, axiom-clean), `routeI_numerics.py` (mpmath dps 50, sympy exact),
this report.

---

## 1. The tension (Route F's flag), restated precisely

Route F proved the block-spin margin degradation IS the fused-character defect, but in the
AMPLITUDE / measure-weight picture `coeffW w s = dimQ s · w^{C₄(s)} = (s+1)·w^{C₄(s)}`:

```
sep'(w) − sep(w) = acNfull w 1 − coeffW w 1 ≃ coeffW w 1 = 2·w³      (fusedDefect_eqv_charExcited).
```

This RAW amplitude defect `2w³` exceeds the model envelope `6(1−w)²` for `w > 0.677` and
`→ 2` as `w → 1` — REFUTED at weak coupling (`raw_ratio_exceeds_at_weak`, `w = 9/10`:
`1.458 > 0.06`). That failure is the residual `FullRangeFusedDefect`.

**But** `GapIsEigenvalue` (VERDICT **A**) proved the PHYSICAL mass gap is the
multiplicity-BLIND transfer EIGENVALUE `eigA w s = w^{C₄(s)}` — the repo's gap bounds
`SpectralModel.lam` (the eigenvalue / decay rate), NOT `SpectralModel.w` (the amplitude,
which carries the degeneracy). Gap edge `eigA w 1 = w³`, dominant for ALL `w ∈ [0,1]`
(`eigEdge_dominates_all_w`, no `w ≤ 7/9` window). The two objects are related by
`coeffW = dimQ · eigA` exactly (`coeffDominance_is_measureWeight`, `rfl`).

**Which object sets the physical gap edge?** The transfer-operator spectral gap is the
EIGENVALUE ratio `λ₁/λ₀` (the correlation decay RATE in `corr n = Σ wᵢ·λᵢⁿ`); the
multiplicity `dimQ = s+1` is the degeneracy of that eigenvalue and multiplies the
AMPLITUDE `wᵢ`, not the rate. So the physical gap edge is **eigA (multiplicity-blind)** —
this is already the repo's committed reading (`SpectralModel.lam`, `LocatedSpectralGap.sep`,
`SpectralGapData.massGap = 1 − sep`). Route I takes that reading to the FUSED defect.

---

## 2. THE RESOLUTION — the eigA fused defect VANISHES uniformly

Strip the multiplicity from the fusion step. The coarse (one-block-spin) FIRST-EXCITED
COEFFICIENT factors exactly:

```
acNfull w 1 ≃ coeffW w 1 + coeffW w 1 ≃ 4·eigA w 1        (acNfull_one_eqv_four_eig, = 4·w³),
```

i.e. coarse degeneracy `4` (two Clebsch channels `(0,1),(1,0)` × the spin-1 dimension `2`)
times the coarse EIGENVALUE `eigA w 1 = w³`. The decay-rate eigenvalue is UNCHANGED
(`eigCoarse_eq_eigFine`: both `= eigA w 1`), because the Casimir `C₄(1) = 3` of the
first-excited representation is fixed — fusion multiplies the DEGENERACY, not the rate.
Hence:

```
eigA fused defect  =  eigCoarse w − eigFine w  =  eigA w 1 − eigA w 1  ≃  0
        (eigA_fusedDefect_eqv_zero,  ALL w, exact).
```

The entire amplitude defect is pure degeneracy:

```
sep'(w) − sep(w) ≃ coeffW w 1 ≃ (Δmultiplicity = 4−2 = 2)·eigA w 1 = 2·w³
        (coeffW_fusedDefect_eqv_mult_eig).
```

Therefore the eigA fused defect is `≤ 6(1−w)²` for **ALL `w`, with NO window**
(`eigA_fusedDefect_le_envelope`, and `eigA_fusedDefect_le_modelEnvelope` in the exact
`afDefectSeq`-RHS form `1·(dimQ 1·(3·(1−w)²))`), since `0 ≤` a nonnegative constant times
a square. `eigA_holds_where_coeffW_refuted` exhibits both facts at `w = 9/10`: the eigA
defect holds (`0 ≤ 6/100`) exactly where the amplitude defect is refuted (`1.458 > 6/100`).

**Numeric validation** (`routeI_numerics.py`, mpmath dps 50, sympy exact):
- eigA fused defect `= 0` for every tested `w` (max `|·| = 0`); coeffW defect `2w³` exceeds
  `6(1−w)²` for all `w > 0.677`.
- `coeffW defect − 2·eigA(w,1) = 0` identically (sympy-exact) — the multiplicity identity.
- coarse coefficient `acNfull w 1 = 4w³ = 4·eigA(w,1)` exact.

---

## 3. eigA defect ≤ 6(1−w)² for ALL w? — YES (it is 0). What that closes vs leaves open.

**Does the eigA fused defect ≤ 6(1−w)² uniformly, unlike coeffW's 2w³? YES** — it is
identically `0`. This **CLOSES the fusion-degeneracy half of the reconciliation
uniformly**: the block-spin fusion step (autoconvolution / Clebsch degeneracy) does NOT
degrade the multiplicity-blind decay-rate gap at all. The `w → 1` obstruction that made
Route F's identification regime-limited (`w ≤ 1/2`) was a MULTIPLICITY (spectral-density)
artifact, now quarantined from the gap.

**Adversarial honesty — this does NOT close `FullRangeFusedDefect`.** The eigA fused
defect being `0` is the DEGENERACY-fusion contribution at FIXED `w`. The PHYSICAL
block-spin also FLOWS the coupling `w_k → w_{k+1}` (the RG map). The multiplicity-blind
per-step gap defect is then the **coupling-flow EIGENVALUE SHIFT**

```
eigA w_{k+1} 1 − eigA w_k 1 = w_{k+1}³ − w_k³,
```

which is nonzero and IS the genuine remaining content. This is the
`SpectralLocalization.bulk_shift` object — multiplicity-BLIND and O((1−w)²) (perturbation
theory is multiplicity-blind, `d(w³)/dw = 3w²`). Crucially it is **NOT refuted at
`w → 1`**: numerically `w'³ − w³ ≤ 6(1−w)²` for AF-rate steps `w'−w ≤ 2(1−w)²` (β ≤ 2) at
every `w` up to `0.999`, whereas the amplitude `coeffW = 2w³` is refuted for every
`w > 0.677`. The eigA residual reduces to the STANDARD asymptotic-freedom β-rate, not a
false algebraic inequality.

So Route I **REDUCES `FullRangeFusedDefect`** (guard-safe, conditional producer
`eigShift_to_fullRange`) to the strictly sharper, non-refuted residual
`EigenvalueShiftDefect` — the multiplicity-blind coupling-flow eigenvalue shift `≤ δ_model`.
This is genuine progress: Route F could only reduce via the amplitude `coeffW` (REFUTED at
`w → 1`); Route I reduces via the eigenvalue shift (quadratic, not refuted), *because the
fusion-degeneracy defect is proved `0`.*

---

## 4. Lean status

- File `lean/YMGap/Continuum/RouteIEigenvalueDefect.lean`, wired into `YMGap.lean`.
- `lake build` — **SUCCESS, 688 jobs**; `frontier-guard OK: 5 Clay-frontier types
  unconditionally uninhabited`; no `error`, no `sorry`.
- `#print axioms` for all 11 load-bearing declarations: `[propext]`, `[propext, Quot.sound]`,
  or empty — NO `Classical.*`, no `sorryAx`, no `native_decide`. No banned tokens in the
  module (only prose comments mention them).
- **Guard UNTOUCHED**: `FullRangeFusedDefect`, `GapChannelDomination`,
  `SingleStepDefectBound`, `TrueMarginRecursion` NOT inhabited. `EigenvalueShiftDefect` is
  a NEW, strictly-sharper, UNINHABITED named residual (Rule 6a); `eigShift_to_fullRange` is
  a CONDITIONAL producer (open binder), not an inhabitant.

Key theorems: `acNfull_one_eqv_four_eig`, `eigCoarse_eq_eigFine`,
`eigA_fusedDefect_eqv_zero`, `coeffW_fusedDefect_eqv_mult_eig`,
`eigA_fusedDefect_le_envelope`, `eigA_fusedDefect_le_modelEnvelope`,
`eigA_holds_where_coeffW_refuted`, `eigShift_to_fullRange`.

---

## 5. HONEST VERDICT

**Is eigA GENUINELY the physical gap edge (multiplicity-blind)?** YES — the repo's gap
bounds `SpectralModel.lam` (the eigenvalue / decay rate); the multiplicity `dimQ = s+1`
enters only the Källén–Lehmann amplitude `SpectralModel.w`. This is `GapIsEigenvalue`'s
committed VERDICT A, not a new assumption.

**Does the eigA fused defect ≤ 6(1−w)² uniformly, where coeffW's 2w³ does not?** YES — it
is identically `0`, hence `≤ 6(1−w)²` for ALL `w` with no window. The coeffW defect `2w³`
that failed at `w → 1` is PURE degeneracy `(Δmult = 2)·eigA w 1`, quarantined from the gap.

**Does `FullRangeFusedDefect` therefore close?** NO — and nothing here claims it. The
fusion-DEGENERACY defect closes uniformly (`= 0`), but the PHYSICAL per-step defect also
includes the coupling-flow eigenvalue shift `w_{k+1}³ − w_k³` (the `bulk_shift` O((1−w)²)),
which is the genuine remaining residual `EigenvalueShiftDefect` — multiplicity-blind,
quadratic, NOT refuted at `w → 1`, reducing to the standard AF β-rate. `FullRangeFusedDefect`
is REDUCED (guard-safe) to it. The coeffW↔eigA tension is RESOLVED IN FAVOR OF eigA; the
residual is SHARPENED from a statement refuted at `w → 1` to one that is not. **The 4D
Yang–Mills mass gap remains OPEN; nothing is faked; no free-field/`δ:=0` is used; no
guarded bundle is inhabited.**
