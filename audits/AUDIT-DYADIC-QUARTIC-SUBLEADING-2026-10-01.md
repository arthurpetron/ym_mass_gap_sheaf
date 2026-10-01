# Explicit dyadic quartic error in the original Wilson measure

Date: 2026-10-01 UTC. The complete existing quartic budget now has an
explicit heat-parameter schedule on which it is smaller than the nome
defect by a factor tending to zero. The bound applies under the original
interacting edge measure and feeds its existing Wilson energy inequality.
It does not control the mixed radial moment or centered variance, and the
schedule is not a justified physical scaling trajectory.

## Schedule and arithmetic

For m>=6, take

    h_m = 2^(-3m),  w_m = 1-h_m,  S_m = 2^(2m).

These are the data `defect`, `nome` and `split` in
`lean/YMGap/Continuum/SU2HeatQuarticDyadicSchedule.lean:32`.
`half_guard` (same file, line 139) proves 1<=2*w_m^(4*(S_m+2)).
`tail_guard` (line 186) proves w_m^(S_m^2)<=2^(-2^m), and
`tail_le_eighth` (line 197) supplies the existing tail guard.
Positivity and w_m<1 are proved, not assumed.

The tail argument uses blocks of length 2^(3m): their length times h_m is
one, so the reciprocal Bernoulli bound gives a heat factor at most 1/2
per block. There are 2^m blocks in S_m^2. The elementary inequality
10m<=2^m for m>=6 then pays the S_m^3 dimension factor.

For the actual previous budget

    B(w,S) = 32*(S+2)^4*h^4 + 296*h^2 + 80*S^3*w^(S^2),

the three contributions are at most 2592, 296 and 80 times 2^(-4m).
`SU2HeatQuarticDyadicBudget.budget_bound`
(`lean/YMGap/Continuum/SU2HeatQuarticDyadicBudget.lean:146`)
therefore proves B(w_m,S_m)<=2968*2^(-4m).

For a positive rational epsilon, `scaledTolerance` (line 179) returns
epsilon/2968 and `smallModulus` (line 181) returns the maximum of six and
that rational presentation's denominator. `budget_small` (line 186)
proves B(w_m,S_m)<=epsilon*h_m for EVERY m past that threshold. This is a
computed, presentation-dependent modulus; no existential choice or
unquantified convergence assertion is used.

## Original interacting consumer

`BF4ExactSlabFixedSpatialDyadicQuartic.dyadicCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDyadicQuartic.lean:36`)
returns max(headCutoff(w_m),S_m+3)+stage. It supplies both original cutoff
guards at every natural stage.

Let L be the number of edges in an original source loop, all of whose
occurrences are active. Let r be the squared chordal difference of the
two ordered word quaternions and Z the SAME original odd partition.
`word_quartic_geometric_bound` (same file, line 57) proves

    H[edgeDensity * r^2] <= 16*L^4*2968*2^(-4m)*Z.

`word_quartic_small` (line 86) replaces the geometric factor by epsilon*h_m
past the supplied modulus. The edge density still contains the original
spatial action, kinetic layer and both terminal messages. Cutoff stage,
width and terminal depth are quantified explicitly; the bound introduces
no extra constants depending on them. Word length remains explicit.

With M=H[edgeDensity*r*(4-f^2)], f the lower fundamental Wilson character,
`wilson_energy_small_quartic` (line 116) proves

    2*energy <= 2*M + 2*(16*L^4*epsilon*h_m*Z).

The mixed moment M is not factored or estimated. The little-o conclusion
for the word correction is relative to Z and directly applies for fixed
L. For a growing family, the displayed bound would require control of
L_m^4*2^(-m); no such family or its limit joins are constructed here.

## Remaining mathematical input

The original mixed moment, or alternatively the complete signed
Ward/Taylor remainder for a specified source family, still needs a useful
upper bound relative to that SAME centered interacting variance. Partition
control cannot replace variance control. Physical time must also be
calibrated on a justified family; h_m has no such interpretation here.
No continuum survival, spatial scaling, full QFT, all-group or Clay claim
is discharged. No new conditional survival wrapper was introduced.

The parallel source review also tested a spatial-reflection shortcut;
its boundary-face mismatch is recorded separately in
`audits/RESEARCH-TARGETED-YM-FRONTIER-2026-09-30.md` as source-level
reasoning, not as a new Lean refutation.

## Verification

Three final focused checks passed 20 printed axiom gates, all within
{propext, Quot.sound}; four gates were axiom-free. Intermediate cast and
namespace errors were fixed before accepting the checks. No sorry, new
axiom, Classical dependency, native_decide, noncomputable declaration,
canonical field or chart state changed.

Only the main agent compiled. The safe-build skill kept checks serialized
with one worker, a 20 GiB ceiling, 12 GiB OS reserve and dynamic pressure
monitoring. Preflight found no competing compiler or runner and reported
90% memory free. No full root build, full-tree audit or guard was run;
the root imports were not checked as an aggregate. The documentation skill
kept the proved estimate and its open consumer distinct in the live plan.
The unchanged canonical ASCII chart was not reprinted.

Final log SHA-256 values, under `/tmp/`:

- `ym-quartic-dyadic-schedule-final-20261001.log`:
  `60c98cef55adca74b820092933ac0f548d684679ad0756633c20775189e2a2bf`.
- `ym-quartic-dyadic-budget-final-20261001.log`:
  `ac6ed782cbddefb027fdcfd851a47934a43e5d8d19e06bb5336e25ef6790ab8e`.
- `ym-original-dyadic-quartic-final-20261001.log`:
  `cc16e6d6020dde087450cd6b2663a7b96527ca52af9962dda6b6fbad16037fe0`.
