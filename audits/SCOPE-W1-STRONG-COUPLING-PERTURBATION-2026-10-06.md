# Scope: V2 finite check, W = 1 strong coupling, electric diagonal plus magnetic perturbation (2026-10-06 PT)

Lean: `Continuum/W1StrongCouplingPerturbation.lean`.  **MODEL, not the true slab.**

## What is proved

- `schur3`: a genuine operator-norm bound (row-sum test) for any symmetric nonnegative 3×3
  rational matrix, for all rational x.  It is generic plumbing (U(1)-blind).
- The W = 1 single-plaquette model:
  - electric part `E χ_s = w^{4c4(s)} χ_s`;
  - LINEARIZED magnetic factor `1 + κ χ₁` (fusion `χ₁χ_s = χ_{s-1}+χ_{s+1}`);
  - `T = E^{1/2} M E^{1/2}`, compressed to `span{χ₁,χ₂,χ₃}`, at κ = 1.
- `w1_norm_bound_1024` and `w1_norm_bound_half`:
  `‖Tx‖² ≤ (λ_lead + ε)²‖x‖²` with λ_lead = w^{12} and ε(w) = κ·w^{22}.
  - w = 1/1024: bound w^{12}(1 + w^{10}), i.e. ε/λ_lead ≈ 8.9·10⁻³¹.
  - w = 1/2: bound 2⁻¹² + 2⁻²² (cheap, exact, certified).

## What the truncation and tail cover, and what they don't

- Covered: the compression to s ∈ {1,2,3}.
- Not covered:
  1. The vacuum coupling T₀₁ = κw⁶.  With it, the vac⊥ block of the perturbed operator
     differs from span{χ₁..}.  This needs a second-order correction of size
     κ²w¹²/(1 − w^{12}).
  2. The tail s ≥ 4.  The tail bound is NOT formalized.  The row sums for s ≥ 3 are
     ≤ w^{4c4(s)} + κ(w^{2c4(s)+2c4(s-1)} + w^{2c4(s)+2c4(s+1)}) ≤ 3w^{46}, far below
     λ_lead, so an infinite Schur test would give the same ρ.  That proof is OPEN.
  3. The exact (non-linearized) magnetic weight e^{βχ₁/2}: higher fusion terms.  Bounded
     by e^{κ}-type factors; not done.

## What breaks for W = 2

- **The basis.**  Two spatial plaquettes share a link.  The gauge-invariant sector is
  spanned by spin networks on the 7-link theta-like graph, with three spins on the shared
  and outer chains plus intertwiners.  It is not a character basis of one holonomy.
  Electric eigenvalues become Π_ℓ w^{c4(j_ℓ)} (shared link counted once), so λ_lead changes
  from w^{12} to w^{4·3} for one plaquette loop, but with degeneracy 2 (either plaquette).
  The two-plaquette loop's eigenvalue is w^{6·3}.
- **The magnetic coupling** multiplies by χ₁ of each plaquette holonomy.  It needs 6j
  (recoupling) symbols at the shared link, so the matrix entries are no longer the 0/1
  fusion pattern.  It requires SU(2) recoupling coefficients (rational at small spins,
  e.g. 1/2, 1/3) that are not in the current model.
- **Degeneracy:** the two degenerate leading states mix at first order in κ through the
  shared link.  So λ_lead + ε needs degenerate perturbation theory; the row-sum ε still
  bounds the norm, but it is no longer O(w^{10})·λ_lead relative accuracy (mixing is
  ≈ κ·w^{2·3+2·3}).
- **Truncation size:** with spins ≤ 2 per link and 7 links, the dimension is in the
  hundreds, so `schur3` must become a generic n×n row-sum test (finite-sum version).
  This is plumbing, but the 6j table is new content.

## U(1) rule

`cs3` and `schur3` are U(1)-blind plumbing.  With U(1) characters (`e^{inθ}`, c4 → n²,
fusion `χ₁χ_n = χ_{n±1}`) the same bound holds, with λ_lead = w^4.  The result is
strong-coupling only.  It makes no large-β claim, so the U(1) rule refutes nothing.
