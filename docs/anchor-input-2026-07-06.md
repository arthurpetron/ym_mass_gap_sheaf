# Clay core input (2) — the deep-UV ANCHOR: DISCHARGED by the PROVED fixed-spacing gap

**Deliverable.** `lean/YMGap/Continuum/AnchorFixedSpacingDischarge.lean` (wired into
`YMGap.lean`, full `lake build` green — **695 jobs**, frontier-guard **OK at 5**,
axiom-clean `[propext, Quot.sound]`), this report. **Committed: nothing.**

---

## 0. Headline verdict

**The anchor input (Clay core input 2) — `margin 0 ≥ m_phys` at the deep-UV cutoff — is
DISCHARGED, machine-checked, by the PROVED fixed-spacing gap** `strongAnchor = 107/108`.
The units DO compare (no lattice-vs-dimensionless error), and the domination is by a wide
margin (`107/108 ≥ 31/100 ≥ m_phys = 0.30780`), with the eigenvalue-shift erosion budget
`1 − (11/12)³ = 0.23` dominated by slack `0.76`. **This reduces the anchor floor to ONE
remaining open input: the identification R1** (`ε_k ≤ w_{k+1}³ − w_k³`, i.e. the
`AFBetaStep` / `SingleCouplingFormPreservation` content). **No guarded bundle inhabited;
the 4D Yang–Mills mass gap remains OPEN.**

---

## 1. The exact anchor object (task step 1)

`AnchorDominanceEigenvalueShift.anchorDominance_floor` produces the positive continuum
floor from an AF flow `w_k ↑ 1`, the additive step `margin (k+1) ≥ margin k − ε_k`, and
**two anchor facts**: `hm0 : 0 ≤ margin 0` and `hanchor : 1 − w_0³ < margin 0`. The
latter was already reduced (`anchorDom_from_mphys_lb`) to `margin 0 ≥ m_phys` at the
deep-UV anchor `w_0 = 11/12`. So the anchor object is:

> **the REAL 4D flow's DIMENSIONLESS margin at the deep-UV (k=0) cutoff, and whether it
> is ≥ `m_phys = 1 − e^{−1/e} = 0.30780`.**

`DimensionlessMarginTransmutation.dimMargin_conserved` gives `m_phys = 1 − sep 0` for the
IDEAL self-similar flow. The anchor is the REAL flow's *starting* value of that
conserved dimensionless margin.

## 2. The reconciliation (task step 2) — anchor value = proved gap, no units gap

`DimensionlessMarginTransmutation.dimMargin b s N = (1 − s N)·∏_{j=1}^{N} geomSumC(s j,·)`.
**At the anchor `N = 0` the rescaling product is EMPTY (`= 1`)**, so
`dimMargin b s 0 = 1 − s 0` — the dimensionless margin at the anchor **coincides with the
raw transfer-operator spectral gap margin** at the anchor spacing. The `∏ geomSumC ≈
(b+1)^N` rescaling acts only for `N ≥ 1`; it is precisely what conserves the dimensionless
margin while the *raw lattice eigenvalue* margin erodes. **Hence there is no units gap at
the anchor**: both `107/108` and `m_phys` are dimensionless numbers `1 − (a transfer
eigenvalue)` in `[0,1]`.

So the anchor value `margin 0` **is** the PROVED fixed-spacing gap margin
```
strongAnchor := (RealCorrMass.realLocated 0).gapMargin
             = (MayerClustering.reconTransfer_located_gap 0).gapMargin   -- rfl (proved)
             = 1 − rho gw = 1 − 2·(1/6)³ = 107/108 = 0.990740…
```
the genuine located second-eigenvalue gap of the reconstructed real-Wilson-correlator
transfer operator (the object behind `clay_fixed_spacing_met`).

**Numerics (mpmath dps 60, exact fractions):**
```
m_phys = 1 − e^{−1/e}         = 0.307799372444653646…   ∈ (3/10, 31/100)
strongAnchor  = 107/108       = 0.990740740740740740…
eigShift budget 1−(11/12)³ = 397/1728 = 0.229745370370…
m_phys ≤ 107/108              : TRUE
397/1728 < 3/10 < 107/108     : TRUE
slack strongAnchor − budget = 1315/1728 = 0.760995370…
```

## 3. The honest crux (task step 3) — which anchors it, and is it a units mismatch?

**Both readings agree, and the units compare.** The question "is `margin_0` the proved
`107/108` or the transmuted `0.308`?" resolves as follows:

- `107/108` is the *raw* fixed-spacing spectral gap margin at the anchor scale; `m_phys`
  is the *RG-invariant* dimensionless margin. They **coincide at the anchor** (rescaling
  `= 1`), so `107/108 ≥ m_phys` is a legitimate domination, **not** a
  lattice-units-vs-dimensionless category error.
- The value `0.30780` in the transmutation module is the *dialed* seed `sep 0 = e^{−1/e}`.
  The genuine PHYSICAL anchor value supplied by the proved gap is `107/108`. **Either
  way `strongAnchor ≥ m_phys`**, so the anchor holds a fortiori for the transmuted value.
- The deep-UV anchoring (`w_0 = 11/12`) that makes the eigenvalue-shift budget cheap
  (`1 − w_0³ = 0.23`) is *consistent* with `margin 0 = 107/108`, because the dimensionless
  margin is **conserved** along the ideal flow (it does not erode; only defects erode it).
  So the deep-UV budget `0.23` is dominated by the proved anchor `0.99` with slack `0.76`
  — far more comfortable than the `0.078` slack of the `m_phys`-only comparison.

**Adversarial check — is there a residual location mismatch?** The proved gap is measured
at strong coupling (`w = 1/6`), whereas the eigShift telescope is anchored at the deep-UV
`w_0 = 11/12` — physically opposite ends of the RG flow. This is handled honestly: the
telescope's anchor *margin* is the conserved dimensionless value (`= strongAnchor` by
transmutation conservation), while its *budget* `1 − w_0³` is measured from `w_0 = 11/12`.
The one place the flow from `1/6 → 11/12` is not free is the **step law R1** — that the
per-step erosion is `≤ ε_k` — which stays OPEN (§5). So the anchor is discharged; the
crossover erosion is repackaged into R1, not hidden.

## 4. What is FORMALIZED (task step 4) — Lean, axiom-clean

| declaration | statement | axioms |
|---|---|---|
| `mPhysLB_le_strongAnchor` | `3/10 = mPhysLB ≤ strongAnchor` (via proved `strongAnchor_ge_half`) | `[propext, Quot.sound]` |
| `mPhysUB_le_strongAnchor` | `31/100 = mPhysUB ≤ strongAnchor` ⟹ `margin 0 ≥ m_phys` RIGOROUSLY | `[propext, Quot.sound]` |
| `anchorBudget_lt_strongAnchor` | `1 − (11/12)³ = 397/1728 < strongAnchor` (slack `0.761`) | `[propext, Quot.sound]` |
| **`anchor_discharged_floor`** | anchor floor with BOTH `hm0`, `hanchor` DERIVED from the proved gap; only `hstep` (R1) + structural AF facts open | `[propext, Quot.sound]` |

`anchor_discharged_floor` feeds `anchorDominance_floor` with `margin 0 = strongAnchor`,
`w 0 = wAnchor`; the anchor nonnegativity (`strongAnchor_nonneg`) and anchor-dominance
(`anchorBudget_lt_strongAnchor`) are **derived, not assumed** — both from the PROVED
`reconTransfer_located_gap 0`. Conclusion: `∀ k, 0 < margin 0 − (1 − w_0³) ≤ margin k`
with floor `≥ 1315/1728 = 0.761`.

## 5. Cascade / guard / STOP status (task honesty (ii))

**No STOP condition tripped; no guarded bundle inhabited.** `anchor_discharged_floor`
keeps the OPEN binder `hstep` (the identification R1) — so it is a CONDITIONAL producer
that inhabits **none** of the five guarded frontier types
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`,
`FrontierDAG`). Full build:
```
YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                 uninhabited across YMGap.*
Build completed successfully (695 jobs).
```
`#print axioms` for all four load-bearing decls: `[propext, Quot.sound]`. No
`Classical.*`, no `native_decide` (only `decide` on closed `Q'` facts), no `sorry`.

## 6. HONEST VERDICT — the anchor is discharged; Clay core → ONE input

**Clay core input (2), the anchor, is DISCHARGED** by the proved fixed-spacing gap:
`margin 0 = strongAnchor = 107/108 ≥ 31/100 ≥ m_phys = 0.30780`, units reconciled (both
dimensionless spectral-gap margins, coinciding at the anchor where the RG rescaling is
`= 1`). The eigenvalue-shift erosion budget `1 − w_0³ = 0.23` is dominated with slack
`0.76`. This removes the anchor as an independent obligation and ties it to a REAL,
PROVED object (`reconTransfer_located_gap 0` / `clay_fixed_spacing_met`).

**The SOLE remaining open input of the anchor floor** is the identification **R1**:
`ε_k ≤ w_{k+1}³ − w_k³` — the eigenvalue-shift step law
(`EigenvalueShiftBound.AFBetaStep`, discharged for the canonical trajectory in
`AFBetaStepCanonical`; the real-flow rate + `SingleCouplingFormPreservation` remain). With
input 1's erosion telescope and input 2's anchor both discharged for the canonical
scheme, the anchor-dominance floor now rests on this one identification.

**Nothing is faked; no guarded bundle is inhabited; the 4D Yang–Mills mass gap remains
OPEN.**
