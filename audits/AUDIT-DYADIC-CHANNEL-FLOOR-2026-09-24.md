# Proposed iterated channel floor: quantitative obstruction

Date: 2026-09-24 UTC. Scope: constructive rational arithmetic about a proposed
normalization. The continuum Yang--Mills / physical mass-gap goal remains OPEN.

## Mathematical result

Let M(w) be `endpointChannelFloorExponent`, defined in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean:56`.
The proposed number is rho_L=(1/2)*w^(L*M(w)). No theorem here says it bounds
the original growing-square partition. The existing
`endpointFloorPower_le_gap`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean:136`)
gives w^M<=1-w. For 0<w<1 and L>=2,

    rho_L <= (1/2)*(1-w)^L
          <= (1/2)*(1-w)^2
          <= (1/2)*(1-w^L)^2.

Consequently 1920*rho_L<=960*(1-w^L)^2. Since rho_L>0, any C paying
960*(1-w^L)^2<=C*rho_L satisfies C>=1920.

The current ORIGINAL signed channel budget has the quadratic A remainder
960*(1-w^L)^2*A, inside the factor-two upper bound on 4E+D_ch:
`BF4DyadicWilsonSquareChannelBudget.paddedSquare_terminal_signed_geometric_budget`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelBudget.lean:98`.
Even that remainder cannot acquire a small coefficient through this candidate
normalization. This does not rule out sharper signed cancellation or a better
source-dependent original-partition comparison. No factor A is cancelled
under an unproved positivity premise, and no physical energy lower bound is
inferred from an upper-bound coefficient.

## Declaration evidence

All new declarations are in `lean/YMGap/Continuum/BF4DyadicChannelFloorObstruction.lean`.

| Declaration | Line | Exact role |
|---|---:|---|
| `loopFloor` | 31 | Proposed number only. |
| `loopFloor_positive` | 41 | Positive for strict positive nome. |
| `loopFloor_le_half_loopDefect_square` | 47 | Upper bound for 0<w<1 and L>=2. |
| `nineteenTwenty_loopFloor_le_quadraticBudget` | 97 | Numerical 1920 comparison. |
| `coefficient_ge_nineteenTwenty` | 114 | Conditional coefficient obstruction. |
| `side_succ_ge_two` | 128 | Actual dyadic side guard. |
| `dyadic_coefficient_ge_nineteenTwenty` | 135 | Applies to side=2^(scale+1). |

## Causal consequence and residue

Do not extend the proposed iterated worst-case first-moment normalization
without changing its quantitative consumer. The next A03 estimate must
control the actual complete signed cost against the SAME interacting centered
variance along a justified scaling family, or give a direct response bound.
The original terminal source, odd mass, all channel weights and signed
correction remain part of that problem. No survival, completed scaling gap,
continuum/QFT/Hamiltonian or all-group conclusion follows here.

## Verification

The final narrow check used `scripts/safe_lean_build.py --jobs 1 --check`
with explicit output olean, 2 GiB worker cap, default elaboration limits and
the unchanged 12 GiB OS reserve. Final check 4 exited zero with all seven gates
within {propext, Quot.sound}, including one empty gate. Check 3 stopped on the
12 GiB reserve. Compilation paused; memory and process state were remeasured
before resumption with unchanged thresholds. Initial draft
errors concerned rational equivalence notation, explicit power base cases and
a Nat power API; they were repaired before acceptance. No source hole, new
axiom, analytic premise or canonical-field change was introduced. Independent
source/scope review passed. No full-root build, audit or guard was run.

Final log: `/tmp/ym-gap-dyadic-channel-floor-obstruction-check-4.log`.
SHA-256: `7aaa27785ed835fb47c4fc5da8b4a70c8bf8eb6f2753d794bfd589a1d3fa993d`.
The semantic root imports this leaf. Schema 1 snapshot 21 adds only evidence
of the numerical obstruction; the canonical chart block, permanent scope
registry and all goal-node statuses are unchanged.
