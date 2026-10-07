# Scope: from strong-coupling clustering to a transfer-matrix gap (R1, 2026-10-07 PT)

Labels: strong coupling, heat-kernel (spin-truncated), not Wilson.  Also true for U(1), so it is
NOT gap evidence (the U(1) rule).  This is a SCOPE NOTE.  Nothing in it is built.

## Part 1 status (observable decay)

Proved (commit 12, `SU2ObsInsertion`):
- Observables are χ₁ plaquette characters, inserted as modified activities.
- Expectation: ⟨·⟩ = ZObs S / Z, with ZObs [] = polyPartition.
- Cross-multiplied identity `trunc_eq_Xi`: Zpq·Z − Zp·Zq ≈ Ξ(z^{pq})Ξ(z) − Ξ(z^p)Ξ(z^q), on the
  same gas and incompatibility.
- `zObs_off`: only polymers that meet S change.
- `l1_gObs`: an observable plaquette costs at most c + 513 + 513c in ℓ¹.

OPEN, still needed for |Zpq·Z − Zp·Zq| ≤ C λ^{d(p,q)} Z²:
1. Root decomposition.  Polymers that contain p are pairwise incompatible (they share p's links).
   So permute them to the head (`Xi_perm`) and apply the `Xi_block` form:
   Ξ(z^p) = Ξ(G∖G_p) + Σ_{γ∋p} z^p_γ Ξ(compatible with γ).
   Expanding the truncation gives a sum over pairs (γ∋p, δ∋q) of `U`-type terms, plus the terms
   where a single polymer contains both p and q (size ≥ d(p,q), hence exponentially small).
2. Summation over γ∋p with KP weights.  `hgroupL` with a = [p] bounds it by K = (5/3)^24
   per root.  Combine with `link_decay` at y = γ, g = δ.
3. Modified-activity bound.  At w₀ = 1e-8 the ℓ¹ route works: one factor ≤ 514/ε_L per
   observable plaquette, so C ≈ (514/ε_L)²·K²·const.  At w_H = 1e-5 the ℓ¹ route FAILS
   (charEnv(513·w_H) ≈ 5e-7).  It needs the charEnv route for χ₁(c₀+f), via
   χ₁χ_s = χ_{s−1} + χ_{s+1}, as a `charSum`.  The s = 0 term must be checked against
   `PolymerOK`.  These are Realizer's files: import them, do not edit them.
4. Uniformity: the bound must not depend on N or M.  It inherits this from `link_decay`.

## Part 2 map: clustering ⇒ transfer-matrix gap (Osterwalder–Seiler at strong coupling)

| Step | Needed | Repo status |
|---|---|---|
| RP | Reflection positivity of the SAME torus multi-link measure (`SU2TorusMultiLinkPolyGibbs.polyPartition`) under time reflection | Repo RP (`BF4ExactSlab*ReflectionPositivity`, `*VacuumReflection*`) is for the BF4 exact-slab signed law, a DIFFERENT measure.  OPEN for the torus polyPartition. |
| Transfer | Positive self-adjoint T on gauge-invariant functions of a time-slice (Lüscher/OS), with Z = Tr T^{N_t} | Abstract infrastructure exists: `CompactTransferGNS`, `LinearTransferOperator`, `GNSTransferMetric`, `CanonicalTransferFormGap`, and `PushedReconTransferGap` (single-edge reconTransfer, w ≤ 1/2).  None is built from the torus polyPartition.  OPEN. |
| Identification | Truncated χ₁ correlator at time separation n written as a `SpectralModel` corr (Σ w_j λ_j^n with w_j ≥ 0) | `SpectralGap.SpectralModel`.  The analogous obligation `TransferCorr`/`WilsonGMatchesAbstract` is OPEN.  Torus caveat: periodic time gives Tr(T^{N_t−n}AT^nB)/Tr T^{N_t}, a TWO-sided sum, not one spectral sum.  It needs N_t → ∞ (uniform in N, which we have) or a half-space/Dirichlet-in-time variant. |
| Gap from decay | Clustering C μ^n ⇒ every populated mode has λ_j ≤ μ | PROVED: `SpectralGapConverse.gap_of_decay_of_growth` (needs a `growth` hypothesis, a scalar fact). |
| Gap in the gauge-invariant sector | Weights of χ₁ cover the excited sector, or a density argument | OPEN. |

Net: the last step is closed and the RP, transfer and identification steps for this measure are
open.  Even when all of this closes, the result is a strong-coupling gap, which also holds for
U(1).  It is therefore not mass-gap evidence by the U(1) rule.
