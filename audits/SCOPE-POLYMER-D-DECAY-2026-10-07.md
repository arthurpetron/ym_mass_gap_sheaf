# Scope: graph-distance decay of truncated polymer correlations (2026-10-07)

**GROUP-BLIND PLUMBING** (U(1) rule).  The decay needs the two-sided bound
`|z X| ≤ ε^{|X|}`.  The KP bound alone needs only `z ≥ −ε^{|X|}`.

## Commit A: chain iteration (`PolymerChainDecay.lean`, PROVED)

This part is generic: any polymer type α, a symmetric `inc`, and a reference list Γ.  A list
is `Good` if it is nodup with all members in Γ.

### Ingredients
- `Xi_perm`: Ξ is invariant under permutation.
- `sumd_sub_le`: a monotonicity lemma for sums over nodup sub-lists. It is choice-free, using
  `TorusWilsonAction.rem`.
- `telescope`: the exact identity `D(A,C)Ξ_B = D(A,B)Ξ_C + D(B,C)Ξ_A`, with Ξ_B > 0 cancelled.
  It gives `|D(F, R++F)| ≤ Σ_{h∈R} c_h · Ξ(F)Ξ(R++F)` from one-polymer bounds
  `|U(y,h,X)| ≤ c_h Ξ(X)Ξ(h::X)`.

### Main result: `chain_bound`
- **Hypotheses (explicit KP environment):**
  - `0 < Ξ(l)`;
  - `Ξ(l∖N a) ≤ M_a Ξ(l)`;
  - `Ξ(l) ≤ m_x Ξ(x::l)`;
  - `|z_a| ≤ ε_a`;
  - all of these quantities `≥ 0`.

  Here l ranges over `Good` lists.
- **Conclusion:** for g at incompatibility distance ≥ d from y through Γ (`far y d g`),
  `|Ξ(y::g::l)Ξ(l) − Ξ(y::l)Ξ(g::l)| ≤ CS_d(g) · Ξ(l)Ξ(g::l)`.
- **The chain sum:**
  - `CS_0(g) = ε_g M_g m_g · 2(1+ε_y M_y)`;
  - `CS_{d+1}(g) = ε_g M_g m_g · Σ_{h∈Γ, inc g h} CS_d(h)`.

The d = ∞ limit is the exact zero `truncated_zero_of_decoupled`; this commit does not need it.

## Commit B: path count and closure (next)
Bound `CS_d(g) ≤ C·q^d·η^{|g|}` on the degree-24 box and torus gases. The planned constants:

- **Base:** `ε_g M_g m_g ≤ 2(1/6000)^{|g|}` and `2(1+ε_yM_y) ≤ 5/2`, which gives
  `CS_0 ≤ 5η^{|g|}` with η = 1/2500.
- **Step:** use the per-plaquette sum `Σ_{h∋q} η^{|h|} ≤ 1/3` (`class_sum`) and a sum-grouping
  lemma.  This gives `CS_{d+1}(g) ≤ (2/3)|g|(5/12)^{|g|} · max CS_d/η` ≤ (5/18)·….
- **Target:** q = 5/18 and C = 5.  The KP environment is instantiated with `Good` = nodup ⊆
  `B.polys`, which needs a nodup-subset product lemma.
