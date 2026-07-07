# Peter–Weyl eigenvalue vs. character: the SU(2) heat-kernel transfer rate, settled

**Deliverable Lean file:**
`lean/YMGap/Continuum/PeterWeylEigenvalueResummation.lean` (imported in `YMGap.lean`;
full `lake build` green, 756 jobs; frontier guard OK = 5 types uninhabited).

## DEFINITIVE VERDICT: (A) — a provable Peter–Weyl spectral fact.

The single-plaquette SU(2) heat-kernel transfer operator's fundamental-sector transfer
**EIGENVALUE** (the exponential correlator-decay RATE, hence the mass gap `−log`) is

```
    w³ = heatKernelSep w      with multiplicity dim(fundamental) = 2,
```

**NOT** `2w³`. The `2w³ = coeffW w 1 = rho w` is the **CHARACTER** (= dim × eigenvalue =
trace over the isotypic block). `reconTransfer`'s per-step "rate" `2w³` is exactly the
**character-vs-eigenvalue misidentification**, and its mechanism is now pinned precisely:
it uses the **bare Kronecker orthogonality** `vacSubKernel = δ` at each internal chain
link, which **drops the Peter–Weyl normalization `1/dim`**, over-counting by `dim` at
every step.

The fork is settled as **(A), not (B)**. The rate is not genuinely `2w³`.

## The Peter–Weyl / Schur-convolution structure (the math)

`L²(SU(2)) = ⊕_r V_r ⊗ V_r*`. Convolution by the heat kernel
`K_w(g) = Σ_r dim(r)·w^{C₄(r)}·χ_r(g)` acts as `w^{C₄(r)}·Id` on the isotypic block
(Schur): the **eigenvalue** of rep `r` is `w^{C₄(r)}`, with multiplicity `dim(r)²`
(or `dim(r)` in the character/correlator sector). For the fundamental `r = 1`:
`C₄(1) = 3`, so eigenvalue `= w³`, and `dim(1) = 2` is multiplicity.

The cancellation is concrete and already lived in the codebase
(`PeterWeylRealWeight.restored_link_amplitude`): integrating out a shared link between
two plaquettes carrying rep `r` gives the **real** orthogonality
`∫ D^r D^{r*} = δ/dim_r` (`haarSubKernel`), and

```
    coeffW w r · (δ/dim_r)  =  (dim_r · w^{C₄(r)}) · (1/dim_r)  =  w^{C₄(r)}.
```

So the `dim_r` from the plaquette coefficient is **cancelled** by the `1/dim_r` from the
shared-link Haar orthogonality, leaving the bare eigenvalue.

### Numeric confirmation (mpmath dps 50, sympy exact — all pass)
- Per-link Schur cancellation `coeffW·(1/dim) − w^{C₄} = 0` (sympy exact 0, all `s`).
- Fundamental chain, `w = 0.9`: successive-ratio of the **genuine** (`δ/dim`) chain
  `= 0.729 = w³` at every `n`; **bare-δ** chain `= 1.458 = 2w³` at every `n`.
- Cumulative over-count `connBare/connPhys = dim^n = 1,2,4,8,16,32,…` (sympy exact).
- At `w* = 2^{−1/3}`: character rate `2w³ → 1` (bare-δ gap closes) while eigenvalue rate
  `w³ = 1/2` (margin `1/2` wide open).

## What the Lean file PROVES (all axiom-clean, `propext`/`Quot.sound`)

Genuine Peter–Weyl chain `pwChain w r n := coeffW w r · (physLinkWeight w r)^n`
(amplitude `coeffW = dim·w^C` once; `n` eigenvalue links `physLinkWeight = w^{C₄}`):

- **`pwChain_succ`** — per-step transfer eigenvalue is `physLinkWeight w r = w^{C₄(r)}`
  (the ratio ⇒ the exponential rate).
- **`pwChain_step_is_peterWeyl_orthogonality`** — that per-step factor **is**
  `coeffW · haarSubKernel` (= plaquette coefficient × the real `δ/dim`), the exact sense
  in which the `dim` cancels.
- **`pwChain_eq_dim_rate`** — `pwChain w r n ≃ dimQ r · (w^{C₄(r)})^{n+1}`:
  RATE `w^{C₄(r)}`, MULTIPLICITY `dim_r`.
- **`pwChain_fundamental`** — fundamental: `≃ dimQ 1 · (heatKernelSep w)^{n+1}` = rate `w³`,
  amplitude `2`. (`⟨χ₁(0)χ₁(n)⟩` decays as `(w³)^{n+1}`, amplitude `2`.)
- **`character_is_dim_times_eigenvalue`** — `coeffW w r = dimQ r · physLinkWeight w r`
  (`2w³ = 2·w³`): the crux identity, character = dim × eigenvalue.
- **`connChain_succ_ratio`** + **`connChain_eq_dimPow_pwChain`** — the bare-δ
  (`wilsonG`/`reconTransfer`) chain `(coeffW)^{n+1}` has per-step ratio the **character**
  `coeffW`, and over `n` links over-counts the genuine chain by exactly `dim_r^n`.
- **`recon_lam_is_dim_times_eff_lam`** — the diagnosis:
  `reconTransfer.lam i = dimQ(i+1) · effTransfer.lam i` — the naive transfer loads the
  character into the eigenvalue slot.
- **`effCorr_is_pwChainSum`** — `corr(effTransfer) = Σ pwChain` (definitional): the
  block-spin effective transfer **is** the Peter–Weyl (`δ/dim`-normalized) chain.
- **`peterWeyl_resummedClustering`** — the physical (`δ/dim`) transfer inhabits
  `ResummedClustering` **UNCONDITIONALLY** (`0<w≤1`): achieving rate `w³` is a **free**
  heat-kernel fact for the correctly-normalized transfer.
- **`peterWeyl_gap_of_physical`** — for every `0<w<1`, a genuine `LocatedSpectralGap`
  with separator `w³`, obtained by routing the physical model through the
  `ResummedClustering` producer — the residual is **discharged**, not assumed.
- **`peterWeyl_margin_pos`** (+ concrete `w9 = 9/10`, `w99 = 99/100`) — fixed-spacing
  margin `1 − w³ > 0` at every coupling in `(0,1)`, including the whole `[w*,1)` where the
  bare-δ single-edge operator has NO gap.
- **`peterWeyl_verdict`** — the bundled machine-checked verdict.

## LOUD REPORT: the fixed-spacing located gap is UNCONDITIONAL on (0,1).

Outcome (A) makes the **fixed-spacing** located gap **unconditional on all of `(0,1)`** —
a provable Peter–Weyl spectral fact, corrected of the character-vs-eigenvalue confusion.
This is the sharpest form of the core the prompt pinned: the "resummation" the adjudication
called an interacting residual is, at fixed spacing, the **free** `1/dim`-cancellation of
Schur's lemma.

## HONEST SCOPE — this is NOT Clay closure.

The continuum mass gap remains **OPEN**. The per-scale eigenvalue margin `1 − w³` is
**non-uniform** — it decreases to `0` as `w → 1` (`a → 0`), proved decidably in
**`fixedSpacing_margin_not_uniform`** (`999/1000` margin `<` `99/100` margin, both `> 0`).
So the lattice-unit fixed-spacing gaps do **not** deliver the uniform physical floor; the
continuum still requires the `tm`-recursion `singleStep` (the summable-defect AF flow,
lattice gap `1 − w³ → 0`). This is the tm-recursion, which we do **not** touch.

### Re-examination of the ResummationAdjudication verdict
- The adjudication's **Point C** (`reconTransfer_not_resummedClustering`, "non-free":
  achieving `w³` is interacting) is a statement about the **wrong (bare-δ) object**. The
  genuine free heat-kernel transfer (`effTransfer`, `δ/dim`-normalized) **does** cluster at
  `w³` (`peterWeyl_resummedClustering`). So at fixed spacing this "non-free" reading is
  **corrected**: the rate `w³` is a free Peter–Weyl fact.
- The adjudication's **Point D** (`tm`-independence + non-uniform margin) **STANDS** and is
  the genuine continuum equi-hardness. The equi-hardness lives **entirely in the `a → 0`
  coupling flow**, not in the fixed-spacing rate.

Net: "`F = 1` stands" is correct **for the continuum floor**, but its `reconTransfer`-based
justification is a fixed-spacing misidentification — now proved and quarantined.

## Guard / axiom status
- Full `lake build`: **green** (756 jobs).
- Frontier guard: **OK — 5 Clay-frontier types unconditionally uninhabited** (unchanged;
  the new file inhabits only `LocatedSpectralGap`/`ResummedClustering`, never a guarded type;
  no `:= SingleStepDefectBound` alias).
- `#print axioms` on all 17 load-bearing declarations: `[propext]`, `[propext, Quot.sound]`,
  or empty — **no `Classical.*`, no `sorryAx`, no `native_decide`**.
```
