# Build plan: the strong-coupling cluster expansion (Option B, 2026-06-22)

Goal: formalize the convergent Kotecký–Preiss / polymer expansion for the SU(2) heat-kernel lattice
gauge measure at fixed strong coupling → genuinely inhabit `ClusterGapReduction.UniformClusterBound`
(volume-uniform gap floor + geometric connected-correlator tail) → a genuine Λ→∞ fixed-spacing mass
gap via the already-proved bridge (the Osterwalder–Seiler / Seiler / Shen–Zhu–Zhu theorem).

## Executive picture (from the deep machinery map)

**The plumbing is genuine and complete; the physics input is entirely absent.** Two fully-proved
engines wait to CONSUME a real cluster bound:
- KP limit engine (`KPLimit.crealOfGeoIncrement`, `KPIncrement.kpIncrementBound`): two-sided
  geometric single-step increment ⇒ `CReal` limit + explicit modulus. DONE.
- The reduction (`ClusterGapReduction.continuumGapPersistence_of_clusterBound`): `UniformClusterBound`
  ⇒ positive continuum-rate mass. DONE.
- Summation engine (`CharacterTail.geom_dom`/`geom_series_le`) + per-rep term bound
  (`CharacterTermBound.charTerm_leRat`: `dim²·e^{−tc} ≤ dim²/(1+tc)`). DONE.

Absent (the entire mathematical content): the polymer model itself (`Sheaf/Site` has only an abstract
`PolySub`; no plaquette sets, `|X|`, connectivity, or Haar link-constraint), the activities (hardcoded
Python fiducials — `SU2KP.rho_sf=25/3`, `ExpBound.Z_upper=1/1000`), the KP criterion (`KPCertificate.P`
is an abstract placeholder), and the clustering⇒gap converse (ABSENT; `SpectralModel` carries no real
operator). Every existing `UniformClusterBound` inhabitant is degenerate (`tailConst=0`, constant-in-Λ
family — uniformity is vacuous).

## Layered decomposition (critical path L0 → L1 → L2 → L3; L4 trivial)

- **L0 — polymer model + character activities.**
  - L0a (activity arithmetic, TRACTABLE): sum the proved per-rep bounds into a genuine per-plaquette
    activity bound `∑_{r≥1} c_r ≤ <explicit>` (`c_r=(dim r)w^{C₂(r)}`), replacing the hardcoded
    `Z_upper=1/1000`. Rigorously known + engine exists ⇒ closeable.
  - L0b (polymer model, HARD/research-grade): define polymers as connected finite plaquette sets with
    `|X|`, connectivity, and the **Haar-orthogonality link constraint** (reps around each link cancel) —
    zero precedent in the repo; the analytic heart that makes activities small at strong coupling.
- **L1 — KP criterion verification** (sequential after L0): state `∑_{X∋p}|ζ(X)|e^{|X|} ≤ a(p)` over the
  L0 model and verify it at small `w` from the L0a activity bound. Known (Friedli–Velenik Ch.5);
  formalizable once L0 exists; the single-site cluster summability is moderately subtle.
- **L2 — convergence ⇒ geometric increment** (sequential after L1): populate `KPIncrementData`
  non-trivially (only `constData` exists) — derive `a(n+1)≤r·a(n)` (`r≤½`) + the margin single-step
  bound from the KP criterion. Engine-shaped downstream; the correlator→margin identification is subtle.
- **L3 — decay ⇒ uniform floor + tail** (after L2; L3a ∥ L3b):
  - L3a (floor, HARD): `floorRate>0`, `uniform_floor` from a volume-uniform clustering bound — needs the
    **clustering⇒gap converse** (ABSENT) over a constructed transfer operator. Deepest analytic content
    after L0b.
  - L3b (tail, tractable): `tailConst>0` + `incr_up/lo` from L2's increment (engine-shaped).
- **L4 — assemble `UniformClusterBound`** (trivial): bundle L3a+L3b; the interface is proved to compose.

## The single hardest obligation

Construct the polymer/cluster model with the **Haar-orthogonality link constraint** and prove the
**volume-uniform KP bound** on the connected-correlator tail of the SU(2) heat-kernel measure at small
`w` (`tailConst>0` + a volume-independent floor for a *volume-dependent* margin family). Hard for three
compounding reasons: the combinatorial object doesn't exist in Lean and must be built from scratch
(project memory flags related uniform-coefficient combinatorics as research-novel); the Haar
link-cancellation has zero precedent; and volume-uniformity is exactly what every degenerate inhabitant
evades. Its companion (L3a, the clustering⇒gap converse over a real operator) is the second hardest.

## Honest assessment

This is a LARGE, mostly-sequential, multi-wave build whose hardest layers (L0b, L3a) are research-grade
constructive formalizations with no precedent. The known-math parts (L0a activity arithmetic, L1/L2
analytic packaging given L0, L3b tail, L4 assembly) are formalizable. Realistic outcome: the foundation
(L0a + the polymer skeleton + the clustering⇒gap converse statement) is bankable; full closure to a
non-degenerate `UniformClusterBound` is a sustained effort gated on L0b + L3a, and uncertain.

## Wave 1 (launched, parallel — the tractable foundation)

- **Activity arithmetic (L0a):** derive the per-plaquette heat-kernel activity bound by summing the
  proved per-rep character bounds (`charTerm_leRat` + `geom_series_le`), replacing the hardcoded
  `Z_upper`/`SU2KP` Python fiducials with genuine in-Lean character-sum arithmetic.
- **Polymer-model skeleton (L0b-structure):** define polymers as connected finite plaquette sets with
  `|X|`, connectivity, and the link-constraint PREDICATE (the structure + definitions; the deep
  consequences are Wave 2+). Honest scope: the structure, not the full Haar-cancellation theorem.

Wave 2 (sequential, gated on Wave 1): L1 → L2 → {L3a ∥ L3b} → L4 — to be reassessed after Wave 1.
