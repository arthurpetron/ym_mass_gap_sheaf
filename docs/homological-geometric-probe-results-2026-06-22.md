# Homological/geometric probe — results and honest terminal state (2026-06-22)

The probe asked: can the YM mass gap be a homological/geometric invariant manifestly bounded below? We
ran real, loop-until-done effort on all three routes in parallel, axiom-clean, to each route's honest
fixed point. Audit 2543 → 2618. Verdict confirmed: **pure homology is a category error for MAGNITUDE;
the geometric (curvature) route is the one that gives magnitude, and it is now built.**

## Route 1 — topological stability (STABILITY-ONLY, not magnitude). FIXED POINT.
`GapStability.lean`: the integer invariant `belowCount` (modes below a threshold); `transport_path`
(located gap persists along a path if the integer is constant / no level crossing); and — crucially —
`belowCount_blind_to_margin`, a PROVED honest caveat that the integer cannot detect the margin shrinking
to 0 (so a constant integer is NECESSARY but NOT SUFFICIENT for a positive limit; weaker than
`UniformRatioVariation`). This is the only honest topological contribution: after-the-fact stability,
never a gap lower bound. Fully extracted; nothing further is a reduction.

## Route 2 — curvature ⇒ gap MAGNITUDE (the substantive route). FIXED POINT.
The genuine new reduction, in three proved pieces:
- `BakryEmery.lean` (template): finite reversible Markov generator; carré-du-champ Γ/Γ₂; the Dirichlet
  and Bochner identities PROVED by finite-sum integration by parts (NO integration); `eigenvalue_ge_of_CD`
  — `CD(K,∞)` (Γ₂ ≥ K·Γ) ⇒ every nonzero eigenvalue ≥ K (eigenfunction route) ⇒ a `LocatedSpectralGap`
  of margin ≥ sK; concrete 2-state sanity inhabitant. The reusable "curvature ⇒ gap magnitude" bridge.
- `HeatKernelCurvature.lean` (anchor): the FREE heat-kernel generator is diagonal in characters with
  eigenvalues = Casimir; `free_DiagCD` PROVES CD(K = 3/4) (lowest Casimir IS the curvature lower bound),
  gap = lowest nonzero Casimir, tensorization preserves it, and it reproduces `HeatKernelGap.heatKernelSep`.
  The free/Haar part is genuinely curved-positive — the route is grounded, not vacuous.
- `UniformCurvatureBound.lean` (capstone reframing): the GEOMETRIC analog of `UniformClusterBound`. One
  curvature constant K>0 with `uniform_CD` (∀ spacing, CD K) ⇒ per-spacing located gaps with uniform
  margin sK ⇒ `curvatureBound_continuum_mass_isPositive` (positive continuum mass), PROVED via
  `toUniformClusterBound`. Named open input: `uniform_CD` — the spacing-uniform INTERACTING curvature
  bound as a→0 (the reshaped continuum wall, Bałaban-class; Shen–Zhu–Zhu CMP 2023 is the strong-coupling
  precedent). This route gives genuine gap MAGNITUDE (unlike Routes 1, 3).

## Route 3 — center symmetry / sector structure (PHASE/SECTOR-ONLY, not magnitude). FIXED POINT.
`CenterSymmetry.lean`: the center ℤ_N action on characters by N-ality phase; N-ality additivity under
fusion; `polyakov_vanishes` (unbroken center symmetry ⇒ charged-observable expectations vanish = the
confinement order parameter); the winding/instanton sector label; and a machine-checkable `Role` ledger
asserting `does_not_provide_gapMagnitude`. Genuine phase/sector structure; the magnitude is set by the
coupling (Karabali–Nair m = e²c_A/2π), not topology. Fully extracted.

## Net result — a THIRD independent reduction of the continuum gap

The probe delivered a genuinely new, magnitude-giving reduction. The continuum mass gap is now reducible
to ANY of three precisely-named inputs, each axiom-clean and proved-to-suffice:
1. `UniformClusterBound` — the cluster-expansion (analytic/combinatorial) route.
2. `ContinuumCertificate` (UniformRatioVariation + ScalingDimensionDecay + LambdaPositiveLimit) — the
   asymptotic-freedom / dimensionless-ratio route.
3. `UniformCurvatureBound.uniform_CD` — the geometric (Bakry–Émery curvature) route.

All three bottom out at the SAME open analytic content — a uniform-in-spacing control of the YM measure
as a→0 — but now expressed in three different, mutually-illuminating languages (cluster activities;
dimensionless RG-invariant ratios; Bakry–Émery curvature). The curvature language is the one that connects
to an active rigorous external program (Shen–Zhu–Zhu; Bauerschmidt–Bodineau–Dagallier) and routes onto
controlled objects (SU(2)=S³ positive Ricci, product tensorization).

## Honest terminal verdict (loop fixed point)

- The user's homology instinct is a CATEGORY ERROR for magnitude (Routes 1, 3) — confirmed and the genuine
  stability/phase content extracted with the honesty proved in-Lean.
- The adjacent MANIFOLD/curvature instinct is correct (Route 2) — a real magnitude reduction, now built.
- All three routes RESHAPE the continuum content; none closes it. The remaining wall is unchanged in
  substance — uniform-in-a control of the YM measure (Bałaban-class) — now available in a third (geometric)
  language. The probe's value: a new, better-connected reduction + a definitive, machine-checked answer to
  "can topology bound the gap?" (no for magnitude; yes for stability/phase; geometry yes for magnitude).
- Loop terminates: each route is at the point where further work would elaborate, not reduce.
