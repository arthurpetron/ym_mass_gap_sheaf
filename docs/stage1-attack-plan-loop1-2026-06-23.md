# Stage-1 attack plan — Loop 1 (2026-06-23)

Goal (fixed): satisfy the Clay requirements intuitionistically. This loop attacks Stage 1 (fixed-spacing
infinite-volume gap, KNOWN math). Research-grounded attack surface + work outline + the parallel build.

## Attack surface (from Loop-1 deep research)

### Wall 1 — all-order Gram PSD
- The target is the CLEBSCH–GORDAN Gram matrix `G_{ab} = ⟨χ_a χ_b⟩ = Σ_{fusion} m_s` (our `gramForm`/
  `wilsonMoments`), NOT the bare Hankel of `m_s` (which is NOT PSD — fails 2×2: `3q⁸−4q⁶<0`). Our object
  is the correct one.
- Best route: LDLᵀ pivot certificate on `G_N` = the `Δ_N = S_N²·P_N` factorization (S_N=L uniform/done;
  P_N=D the pivots). Each pivot factors as (positive const)·(cyclotomic Φ_d, >0 on (0,1))·(nonneg-coeff
  poly)/(nonneg-coeff poly), Φ_1=(q−1) to EVEN powers ⇒ manifestly constructive positivity. All-orders =
  induction. `vᵀG_Nv = Σ pivot_k (Lᵀv)²_k ≥ 0` by sum_nonneg.
- Residual wall (honest): uniform (all-N) nonneg-coefficient of the P_N/pivot residuals — now a concrete
  polynomial-coefficient statement (verified through N=7/8), attacked via the Favard/SN cyclotomic recurrence.

### Wall 2 — Mayer/cluster (real correlator)
- Do NOT build Penrose/Kruskal/Cayley: single-rep Haar collapse + the inhabited lattice-animal count
  (`ClusterCount.clusterCountBound`, K=deg²) make KP convergence UNCONDITIONAL already.
- Genuine pieces: (A) Dobrushin ratio induction `Ξ_{Λ∪p} ≤ Ξ_Λ(1+w(p))` (Fialho 2001.00652) — hardest
  step `Z_step_ratio` (generalize `Z2_collapse` to arbitrary Λ; multi-plaquette link integral). (B) the
  REAL Wilson connected correlator `wilsonG` = character double-sum, with `wilsonG = double-pinned cluster
  sum` and geometric decay `ρ = deg²·2w³` — this DERIVES `sep` instead of positing it (de-fakes the
  trivial `wilsonSpectralModel ≡ gapModel`). (C) the tail is already the geometric tail of
  `kp_criterion_unconditional`.
- Key new finite lemma: `connected_spanning_size_ge` — a connected polymer touching p₀,pₙ has size ≥ n.

## Work outline (Loop 1 — the buildable frontier pieces; new files, conflict-safe)

1. **W1-atoms** (`Continuum/CyclotomicPositivity.lean`): the positivity atoms `0<q<1 ⇒ 1−q^n>0`,
   `Φ_d(q)>0 on (0,1)`, and extend the unconditional P_N/form-level PSD range beyond N≤3 (N≤5/6) reusing
   `QHankel.SN` + per-N P_N. Pushes the unconditional frontier + lays the cyclotomic groundwork. LOW risk.
2. **W1-favard** (`Continuum/FavardUniform.lean`): the N-indexed `SN`/cyclotomic recurrence
   `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²` (proved through k=5; generalize to all k) — the structural backbone
   of uniform P_N. Attempt the uniform induction; partial (the general recurrence identity) is real progress.
   MEDIUM/HARD (the research wall).
3. **W2-pinned** (`Continuum/PinnedCluster.lean`): `activity_le_leading`, `connected_spanning_size_ge`
   (the new combinatorial lemma; add a separation predicate), `pinnedClusterTail` (geometric tail of the
   KP series for size ≥ n). The finite pieces enabling the real-correlator decay. LOW/MEDIUM risk.
4. **W2-conncorr** (`Continuum/WilsonConnCorr.lean`): the REAL Wilson connected 2-point correlator
   `wilsonG` as a character double-sum (built like `Z2`), and its geometric decay bound (from W2-pinned's
   pieces, reusing the KP tail) — de-faking the trivial link. Leave `wilsonG = pinned-cluster-sum` named
   pending the Dobrushin `Z_step_ratio` (a later loop). MEDIUM risk.

Hardest cores deferred to later loops (scoped): the Dobrushin `Z_step_ratio` (Wall 2 crux) and the uniform
P_N induction closure (Wall 1 crux). Loop 1 builds the surrounding genuine frontier so those cores have
everything they need.

## Honesty
Every new obligation NAMED (Type-level), never faked; axiom-clean ([propext]/[Quot.sound]); each agent
builds + verifies. The two crux residuals stay honestly open and are the targets of subsequent loops.
