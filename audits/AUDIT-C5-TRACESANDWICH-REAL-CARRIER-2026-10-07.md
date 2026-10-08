# Audit: C5 TraceSandwich rate interval on a real carrier (ledger row F), 2026-10-07 PT

**Verdict.** I could not produce a rigorous two-sided interval for the excited rate of a real
transfer (the repo's width-1 slab at a strong-coupling nome) with the current infrastructure.

- The real carrier has a rigorous UPPER end that does not use the Doeblin floor/cap argument:
  `‖T₁|vac⊥‖ ≤ timeRate` at the pilot nome `w = 1/1024`, for every width. This already exists in the repo.
- The LOWER end is only the trivial `0`.
- There is no `specMax` (`SpectralModel`) object attached to the real carrier at all.

Row F therefore stays "model interval only" for a two-sided interval. It gains a one-sided real-carrier entry.

Labels: SU(2) (quaternion carrier), heat-kernel slab (BF4 all-nome literal-width carrier),
finite spatial width with the time limit completed, strong coupling only. Not gap evidence.
This audit adds no Lean code.

## 1. Inventory

- **Model interval (row F as it stands).**
  - `SpectralTraceSandwich.specMax_mem_of_trace_bounds`: on a finite `SpectralModel`, rational bounds on
    `s_n` and `s_{2n}` certify `ρlo ≤ specMax ≤ ρhi`.
  - `SpectralHalvingStrongCouplingCarrier`: `1/9 ≤ specMax ≤ 13/100` at `w = 1/2` for the closed-form
    `excitedCharModel` (three excited spins).
    - At `w = 1/2` the strong-coupling guards fail, so no real-carrier rate exists there.
    - `scFamily_hlink` at `w = 1/1024` is circular: the model is built from the known rate.
- **Real carrier.**
  - `BF4WilsonAllNomeCompletedTime`: `Completion hw0 hw1 width` with `completedInner` `B`, the semigroup
    `T n`, the unit state `U`, and `VacuumComplement = {x // B U x = 0}`.
  - The rate predicate is `BF4WilsonAllNomeExprMixRateContraction.WilsonVacuumSqContraction r`:
    `∀ y ∈ vac⊥, B(T₁y,T₁y) ≤ r²·B(y,y)`.
- **Doeblin no-go.**
  - `MixRateMarginScaling.mixFraction_le_width1`: `mixFraction ≤ 2^-15` at width 1.
  - `mixRate_ge`: `1 − 32^{-n(width)} ≤ mixRate`.
  - So the floor-to-cap rate is at least `1 − 2^-15` at width 1, and worse at larger widths.
- **Non-Doeblin upper bound (existing).**
  - `BF4WilsonAllNomeStrongCouplingUniformRate.existingNome_allNome_strongCoupling`, unconditional at
    `w = 1/1024`: `∀ width, WilsonVacuumSqContraction … timeRate`.
  - Constants: `timeRate = entropyRate 96 comparisonCoreRate`, with `0 < timeRate < 1` by `decide`; the
    docs quote ≈ 1/4. `twoStepRate = timeRate²`.
  - Mechanism: the selected-chain cluster bound `finite_covariance_distance_bound` plus the dyadic moment
    argument that removes the amplitude. It does not use the floor/cap.
- **Wilson T_K torus chain (Prover R1 commits 27–38, and Realizer).**
  - `SU2TransferTrace.z_eq_trace` writes Z as a periodic chain of time-shifted kernels (trace form); no
    operator `T` is defined.
  - `SU2TorusNormalizedRatio.normalized_torus_ratio` bounds one plaquette's normalised covariance with rate
    `(6/7)²` per two steps.

## 2. Candidate routes, and exactly where each stops

**(a) Floor-to-cap Doeblin.** Rate ≥ `1 − 2^-15`, which is useless (the stated obstruction). Not used.

**(b) Trace sandwich `Tr(T^n)^{1/n}` with explicit `n`.**
- The sandwich needs the excited power sums `s_n = Σ_{i≥1} λ_i^n` of a finite eigenvalue list.
- On the real BF4 carrier, no trace functional, spectral decomposition or trace-class structure is defined
  on `Completion`.
- On the Wilson T_K torus, `z_eq_trace` gives only the full `Z(N_t)`, formally `Σ_{i≥0} Λ_i^{N_t}`
  including the vacuum. Isolating `s_n` needs `Λ₀` to relative precision below `(Λ₁/Λ₀)^n`, which is
  about `w^{12n}` at strong coupling.
- Exact `Z` at several `N_t` is computationally out of reach: SU(2) polynomial Haar over `4(2M)^4` links.
- The repo also has no spectral theorem for the positive (RP) transfer.
- The torus T_K measure and the BF4 heat-kernel slab are different carriers, and no identification
  between them exists.

**(c) Positive-kernel Perron / Collatz–Wielandt.**
- Kernel positivity (`BF4ExactSlabFixedSpatialTransferPositive`, and the floor/cap sandwich) controls the
  TOP eigenvalue `Λ₀`, whose eigenvector is the vacuum.
- The excited eigenvector changes sign, so positivity gives nothing on `vac⊥`.
- Applying a positivity bound on `vac⊥` through floor and cap is exactly the Doeblin argument. So this route
  is the obstruction itself, not a way around it.

**(d) Cluster-expansion ratio route (normalized_torus_ratio / wilson_trunc_ratio).**
- It gives upper bounds on the decay of one local observable's covariance (rate `6/7` per lattice step,
  volume-uniform constant `Cw·λ`). It does not give an every-vector bound on `vac⊥`.
- Log-convexity makes `Ê(k+1)/Ê(k)` nondecreasing. A numeric lower end would still need explicit
  lower bounds `Ê(0), Ê(1) > 0`, and none exist.
- Result: an observable-specific, one-sided statement.

**(e) Real-carrier variational lower bound.**
- Any `y ∈ vac⊥` with `B(y,y) > 0` gives `ρ(T₁) ≥ ‖T₁y‖/‖y‖`.
- Using it needs a quantitative lower bound on the constructive real `B(T₁y,T₁y)` (equivalently on
  `B(y,T₂y)`, by time balance), plus an explicit upper bound on `B(y,y)`.
- Both are joint cutoff/time limits. The repo proves only UPPER bounds on connected correlators there,
  with the amplitudes removed or unspecified.
- What's needed: a strong-coupling leading term minus an explicit-amplitude cluster error, for one lag-1
  connected correlator. That does not exist yet.
- The kernel floor (`T f ≥ a·H[V f]` in the certificate cone) is a rank-one lower bound and does not stop
  `T₁` from being small on `vac⊥`.

## 3. What is rigorous today on the real carrier (row F, real-carrier entry)

- At `w = 1/1024`, for every literal width: `0 ≤ ρ(T₁|vac⊥) ≤ timeRate` (≈ 1/4).
  - This is stated in operator form, `WilsonVacuumSqContraction`, not as `specMax`.
  - Source: `existingNome_allNome_strongCoupling`. It avoids Doeblin.
- How crude it is: the strong-coupling leading excitation is expected around `w^{12} ≈ 7.5·10^-37` at
  `w = 1/1024`. That is the W=1 model scale (`W1StrongCouplingPerturbation`), a heuristic, not a theorem.
  So the proved upper end is far from sharp, and the lower end is trivial.

## 4. What would unblock a two-sided interval

1. **Lower end.** An explicit-amplitude cluster bound for the all-nome limit, plus a leading-term evaluation
   of one lag-1 connected correlator. Together these give `B(T₁y,T₁y) ≥ c·B(y,y)` for an explicit
   `y ∈ vac⊥`, with `c > 0` rational.
2. **`specMax` link.** A spin-network truncation of the W = 1 slab with exact rational matrix entries, and a
   tail/perturbation bound. Courant–Fischer: compression to `χ₀^⊥` gives an upper bound on λ₂, and a
   2-dimensional Rayleigh–Ritz gives a lower bound. This also needs the identification of the BF4 slab
   operator with that matrix, which is OPEN (`SCOPE-SLAB-PETER-WEYL-IDENTIFICATION-2026-10-06.md`,
   replacements 1–3).
3. Any of these remains strong-coupling and finite-width. It does not give AF, a continuum limit or a gap.

## 5. U(1) rule

Routes (a)–(e) and the operator-form bound are group-blind except through the carrier. The
strong-coupling upper end is a small-nome statement; no large-β claim is made, so U(1) refutes nothing here.
