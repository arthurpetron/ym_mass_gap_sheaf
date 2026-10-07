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

## Commit B: closure (`PolymerDecayZ4.lean`, PROVED)

**Constants: q = 7/10, C = 1.** The earlier target was q = 5/18, C = 5.  The proved q is weaker
because the step uses the product bound
`Σ_{h∈Γ, h∩g≠∅} η^{|h|} ≤ Π(1+η^{|h|}) ≤ (5/3)^{|g|}` (`z4_hgroup`).  The sharper per-plaquette
grouping (`class_sum`, ≤ |g|/3) was not needed.  C improved to 1.

### Setting
For any `Z4BoxGas BL` with `BL.D = 24` (box `z4Chain` or torus `torusChain N`):
- Γ = `B.polys`, and `Good` = duplicate-free inside Γ;
- ε = 1/10000 and η = 1/2500;
- ε_a = ε^{|a|}, M_a = (5/3)^{|a|}, m_a = 1+η^{|a|}.

### Ingredients
- **`env_pos`, `env_M`, `env_m`, `env_z`:** the `chain_bound` hypotheses, discharged.
  - Positivity uses the new lemma `pos_of_one_le_mul` together with `kpw_lower`.
  - A new duplicate-free sub-list lemma `prodm_sub_le` (choice-free) feeds `z4_hgroup` into
    `z4_cond` for every Good list.
- **`CS_le`:** `CS_d(g) ≤ (7/10)^d·η^{|g|}`. The scalar facts are
  - `scalar_base`: `ε^s(5/3)^s(1+η^s)·2(1+ε^t(5/3)^t) ≤ η^s`;
  - `scalar_step`: `ε^s(5/3)^s(1+η^s)(5/3)^s ≤ (7/10)η^s`, using (1+η)·25/36 ≤ 7/10.

### Results
- **`deg24_decay`:** if g is at incompatibility distance ≥ d from y and y::g::l is Good, then
  `|Ξ(y::g::l)Ξ(l) − Ξ(y::l)Ξ(g::l)| ≤ (7/10)^d·η^{|g|}·Ξ(l)Ξ(g::l)`.
  - This requires the two-sided bound `|z| ≤ ε^{|X|}`.
- **`zheat_decay`:** the same bound for the explicit heat-kernel activity `zHeat` at w = 1/40.

### Scope
- **Distance notion.** "Distance" is incompatibility-graph distance inside the gas
  (`far`): y and g are not incompatible, and every Γ-neighbour of g is at distance ≥ d−1.
  Converting this to lattice distance is OPEN but routine: two polymers sharing a plaquette
  are within diameter range.
- **R1 still open.** zHeat is an envelope activity, so the Haar identity
  Z_Wilson = Ξ(gas) is still OPEN.  Until it is proved, this is decay of the envelope gas, not
  of Yang–Mills.

## Commit C1: lattice-distance decay, generic metric (`PolymerLatticeDecay.lean`, PROVED)

**Route: size-weighted chain** (not graph distance ÷ N).
- The chain budget r drops by |h| at each step to h.
- `diam_le`: a connected polymer has diameter ≤ |h| − 1 (ball growth).
- So `sepL y g R` (all pair distances ≥ R) implies `farW R R g`.
- The bound is `CSW_r(g) ≤ λ^r (λη)^{|g|}`, λ = 6/7.  The scalars are:
  - `(25/36)(1+η) ≤ 6/7`;
  - `(5/12)(1+η)·2(1+(5/12)η) ≤ 6/7`.

**Result.** `|U| ≤ (6/7)^R (λη)^{|g|} Ξ(l)Ξ(g::l)`:
- c = 1 and c' = 0, i.e. rate ln(7/6) per lattice unit;
- C = 1;
- **independent of the max polymer size N**.

Cost: the size factor drops from η^{|g|} to (6η/7)^{|g|}.  The graph-distance rate 7/10 is
unchanged in `PolymerDecayZ4`.
