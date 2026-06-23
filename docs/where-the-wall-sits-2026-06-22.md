# Where the wall sits, and why — the definitive account (2026-06-22)

This is the canonical, detailed explanation of exactly where the Yang–Mills mass-gap proof is blocked
in this development, what KIND of block it is, and the mathematical reasons it is hard. It synthesizes
the staged reductions (`stage1-completion-ledger`, `stage2-progress-ledger`, `continuum-wall-outstanding`).
Read this first to understand the geography.

--------------------------------------------------------------------------------
## 1. The reduction tree: what is proved, what is reduced, where the walls are

The Clay target: construct continuum 4D Yang–Mills satisfying the Osterwalder–Schrader axioms (R1), with
the theory nontrivial (R2) and possessing a mass gap Δ>0 (R3), for every compact simple gauge group.

What this development has established, top to bottom:

```
Clay target (R1 construct + R2 nontrivial + R3 gap, all compact simple G)
│
├─ [PROVED] Group dependence → ONE worst case (SU(2)).
│     mass_gap_simple_group: the Casimir-floor reduction (all fundamental weights of all SU(N)
│     clear the 3/4 floor; SU(2) is tightest). Not a wall.
│
├─ [PROVED] Fixed-spacing, finite-volume gap (strong coupling).
│     OS2 reflection positivity (Schur/Osterwalder–Seiler) + the LOCATED spectral gap of the
│     COMPACT (finite) transfer operator (sep = w³ < 1). Genuine, axiom-clean. Not a wall.
│
├─ STAGE 1: Λ→∞ thermodynamic limit at FIXED spacing.   ← KNOWN math; wall = FORMALIZATION
│     [PROVED] the reduction UniformClusterBound ⇒ positive continuum-rate mass (bridge).
│     [PROVED] a non-degenerate UniformClusterBound (real Λ-dependence, positive floor, geometric tail).
│     [PROVED] real Wilson functional (H1), inverse-limit measure + multi-edge tower (H2.1),
│              polymer identity through the first interacting case (H2.2), real correlator link
│              single-edge (H2.3), finite-order Gram PSD (N≤3).
│     [WALL 1a] all-order heat-kernel Gram PSD (MomentSquarePos / UniformGramSOS).
│     [WALL 1b] full Mayer/Ursell cluster-expansion convergence (MayerExpansion).
│
└─ STAGE 2: a→0 continuum limit.                          ← OPEN research math
      [PROVED] BetaNonzero discharged (β>0 ⇒ running real); AF schedule/rate proved.
      [PROVED] each of the three continuum requirements REDUCED to one sharp spacing-uniform input,
               and the synthesis capstone (ContinuumCertificate ⇒ gap+nontrivial+O(4) jointly).
      [WALL 2] the three certificate fields — the genuine open analytic core:
               • UniformRatioVariation  (gap survives a→0)
               • ScalingDimensionDecay  (O(4) restored)
               • LambdaPositiveLimit    (nontriviality / dimensional transmutation)
```

So there are exactly TWO walls, of two DIFFERENT KINDS.

--------------------------------------------------------------------------------
## 2. Two kinds of wall

**Stage-1 walls (1a, 1b) are KNOWN mathematics; the obstruction is FORMALIZATION.**
They are theorems that ARE proven in the literature (Osterwalder–Seiler; Seiler LNP 159; the q-total-
positivity / vicious-walker LGV results; the Penrose tree-graph + Kotecký–Preiss machinery). Nobody
doubts they are true. The block is that formalizing them constructively (no Mathlib, no LEM/AC, and —
critically — NO real integration) is a large multi-month undertaking, and for 1a the cleanest route runs
through machinery the project has repeatedly found research-grade to formalize (the uniform P_N
nonnegativity). Closing Stage 1 would give a rigorous, machine-checked INFINITE-VOLUME mass gap at FIXED
lattice spacing — a real result, but NOT the continuum theory.

**Stage-2 wall (2) is OPEN research mathematics.**
This is not "known but unformalized." The mass gap's SURVIVAL of the continuum limit a→0 is not
established even on paper, in any framework, for 4D Yang–Mills. This is the actual Clay-hard content.

--------------------------------------------------------------------------------
## 3. THE wall, stated precisely (Stage 2 core)

All three Stage-2 certificate fields are facets of ONE statement:

  **A uniform-in-lattice-spacing renormalization-group control of the Yang–Mills measure across the
  entire scaling window — from strong coupling (large a) to the continuum (a→0, g(a)→0 by asymptotic
  freedom) — that keeps the DIMENSIONLESS mass gap Δ/√σ bounded below by a positive constant and
  convergent.**

In the Lean development this is exactly: inhabit `UniformRatioVariation` (the gap-ratio's spacing-uniform
single-step bound), `ScalingDimensionDecay` (the rotation-breaking coefficient's decay), and
`LambdaPositiveLimit` (the RG-invariant scale Λ tends to a positive finite value). The capstone proves
these three JOINTLY give the continuum gap, nontriviality, and O(4) restoration. They are the open core.

--------------------------------------------------------------------------------
## 4. WHY this is the wall — the deep mathematical reasons

### 4.1 The UV/IR conflict — you must control two opposite regimes at once
Asymptotic freedom makes the theory WEAKLY coupled at short distance (the UV, a→0). That is the good
news and the reason a continuum limit should exist at all. But the mass gap is an INFRARED phenomenon
(confinement) — fully non-perturbative, living at long distance. To prove the gap survives the continuum
limit you must control the UV (where AF helps), the IR (where the gap lives), AND the crossover between
them, UNIFORMLY in the cutoff. The two regimes are governed by opposite tools and opposite limits.

### 4.2 The two tools we have govern DISJOINT regions of coupling, and neither reaches the goal
- The fixed-spacing gap (which IS proved here) comes from the convergent STRONG-coupling / cluster
  expansion — valid only for β below a finite threshold β_c (large lattice spacing).
- The continuum limit requires β→∞ (g→0, a→0).
- Perturbation theory (made available by AF in the UV) is SILENT about the gap — the gap is invisible to
  every order of perturbation theory (it is ∝ e^{−c/g²}, non-perturbative).
So the expansion that PROVES the gap DIVERGES exactly in the limit where the gap must persist, and the
expansion that controls the UV says NOTHING about the gap. You cannot "take a→0" inside the strong-
coupling result — the continuum point lies outside its domain of validity. Bridging this gap in coupling
space is the unsolved problem.

### 4.3 The RG is the only bridge, and the gap's survival through it is unproven
The renormalization group is the only object that connects scales. The proof would flow from the
strong-coupling (controllable) end toward the continuum fixed point, tracking the gap in physical units.
**Bałaban's program** (1980s, hundreds of pages of multiscale block-spin analysis) controlled the
existence of the limit / the partition function / the effective action for lattice gauge theory — a
monumental achievement — but it did NOT establish that the mass gap persists with a positive lower bound
through the flow. The gap's survival is the missing piece. No one has it, on paper or otherwise. Our
`UniformRatioVariation` is precisely the spacing-uniform single-step control of the gap ratio that this
flow would have to supply.

### 4.4 Dimensional transmutation pins the rate — too fast is trivial, too slow is infinite
In a continuum limit the correlation length DIVERGES in lattice units, so the gap in LATTICE units → 0.
The PHYSICAL gap = (lattice gap)/a must stay finite and positive. This forces the lattice gap to vanish
at EXACTLY the rate set by the running coupling via dimensional transmutation:
        Δ_phys ~ Λ ~ (1/a)·exp(−1/(2b₀ g²(a)))   (one-loop, b₀ > 0).
Vanish faster ⇒ Δ_phys → 0 (gapless/trivial); vanish slower ⇒ Δ_phys → ∞ (degenerate — exactly what
`BareAFDiagnostic` shows the NAIVE scaling does). Proving the gap vanishes at PRECISELY the transmutation
rate is the quantitative heart. `LambdaPositiveLimit` (Λ → positive finite) and `UniformRatioVariation`
(Δ/√σ → positive) are this requirement, restated as the certificate's named inputs.

### 4.5 The triviality threat — nontriviality and the gap are entangled
A 4D continuum QFT can be TRIVIAL: its limit is free/Gaussian. This is not paranoia — it is proven for
φ⁴₄ (Aizenman–Duminil-Copin 2021) and believed for QED (Landau pole). Yang–Mills is believed nontrivial
BECAUSE of asymptotic freedom (the coupling runs to zero the "good" way in the UV), but proving the
interactions survive the limit (R2) is part of the SAME wall: a trivial limit is free, hence gapless. So
nontriviality (`LambdaPositiveLimit`) and the gap cannot be separated — they stand or fall together in
the one limit.

--------------------------------------------------------------------------------
## 5. The constructive-specific obstruction (our extra wall)

This development is Mathlib-free, intuitionistic (no LEM/AC), and — decisively — has NO real integration
(`CReal` has no integral). At FIXED spacing this is not a problem: character orthogonality turns Haar
integration into FINITE character sums (Clebsch–Gordan), so the fixed-spacing theory is genuinely
discrete and constructive (this is why Stage-1's tractable pieces went through). But the a→0 limit is
genuinely a LIMIT of these discrete functionals — an analytic object. The discrete trick does not by
itself survive the limit. Whether the uniform-in-a RG control (§4) can be carried out with LOCATED /
computable moduli, WITHOUT integration, is itself an open question. A constructive closure would need
either genuinely new constructive-analysis machinery, OR a computer-assisted route (rigorous
interval-arithmetic lattice data supplying the constants, plus a uniform analytic a→0 modulus) — the
"measurement bridge," for which a constructive substrate that speaks in computable moduli is the natural
home.

--------------------------------------------------------------------------------
## 6. What it would take to close each wall

- **Stage 1 (known math, formalizable-hard).**
  - Wall 1a (all-order Gram PSD): either formalize q-total-positivity via the vicious-walker / LGV
    planar-network argument (research-grade), OR the Gauss–Chebyshev quadrature route (finite positive
    weights × pointwise K_t≥0 at the nodes ⇒ vᵀGv = Σλ_i(Σv_a U_a(x_i))² ≥ 0) — cleaner, but it rests on
    `HeatKernelPos`'s own pointwise-positivity gap (DiffJTP). Either is a deliberate scoped campaign.
  - Wall 1b (Mayer/Ursell): formalize the Penrose tree-graph identity + Kotecký–Preiss bound (combinatorial,
    multi-month; no cluster expansion has ever been formalized in any proof assistant).
  Closing both ⇒ a rigorous infinite-volume mass gap at fixed lattice spacing.

- **Stage 2 (open research math).**
  Inhabit any of the three certificate fields = solve the corresponding facet of the uniform-in-a RG
  control (§4) — the Bałaban-completion for the gap, in a constructive (located-moduli) setting. This is
  a research PROGRAM, not a formalization task: the mathematics does not yet exist.

--------------------------------------------------------------------------------
## 7. One-paragraph summary

The proof is complete and machine-checked from the group-dependence reduction (worst case SU(2)) through
the fixed-spacing, finite-volume mass gap. Beyond that there are exactly two walls. The first (Stage 1,
the infinite-volume limit at fixed spacing) is KNOWN mathematics blocked only by the labor of constructive
formalization — two sharp obligations (all-order heat-kernel Gram PSD; Mayer/Ursell convergence). The
second (Stage 2, the continuum a→0 limit) is the genuine Clay-hard wall and is OPEN research mathematics:
a uniform-in-lattice-spacing renormalization-group control that keeps the dimensionless mass gap positive
across the scaling window from strong coupling to the continuum — harnessing asymptotic freedom in the UV
to protect a non-perturbative IR gap, at exactly the dimensional-transmutation rate, in a limit that is
simultaneously the test of nontriviality. Bałaban controlled the partition function there; the gap's
survival is unproven by anyone. This development has reduced that entire frontier to ONE certificate of
three sharp, spacing-uniform, asymptotic-freedom-routed inputs, and proved they jointly suffice — so the
remaining mathematical content is precisely named and maximally isolated, but it is genuinely open, and
in the constructive setting it carries the additional open question of whether it can be done with
computable moduli and no integration.
