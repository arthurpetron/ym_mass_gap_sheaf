# Scope: a coupling-dependent rate λ in `trunc_gen` (option 3, 2026-10-23 ET)

Docs only. Nothing here is proved.

## Where λ = 6/7 comes from

- `PolymerLatticeDecay.lam := 6/7` (l.153) is a literal. The same file sets `etaL := lam * etaZ`.
  `lam` is opened in about 51 files.
- The torus decay chain is `PolymerLatticeDecay` (chain/step bounds), then
  `SU2RemovalDecay.T_link_decay_sharp` (l.115: `|T(y,g)| ≤ λ^{R+1}·M_y M_g²·Ξ²` at separation R+2),
  then `SU2TruncGeneric.trunc_gen` (l.298), `SU2WilsonTrunc.wilson_trunc_ratio` (l.191) and
  finally `SU2ClusterBridge.cov_decay` (l.117) and `SU2TorusNormalizedRatio`.
- λ is paid for by the activity budget. The rooted sums carry `μ^{|a|}` with `μ = 7/6 = 1/λ`
  (`SU2ObsActivity.mu` l.46). The KP and decay scalar conditions are checked once by `decide`
  at ε_S = 10⁻¹², Kc = (3/2)²⁴ (`SU2LinkDecaySharpInst.sharp_pass`).
- So 6/7 is a bookkeeping choice that makes `ε·μ`-weighted sums converge. It is not a
  physical rate. The true strong-coupling χ₁ correlator at β_S decays per unit distance like
  a power of β, many orders of magnitude faster.

## What a coupling-dependent λ would need

1. A parallel decay chain with `λ` (and `μ = 1/λ`) as a variable. That means re-proving
   `chain_bound`/`step_bound`, the link-KP sharp bounds (`SU2LinkKPSharp`, `SU2LinkDecaySharp`),
   `T_link_decay_sharp`, `trunc_gen`, `wilson_trunc_ratio` and `cov_decay`. The `decide`d scalar
   facts become hypotheses on `(ε, λ)`, of the form `ε·Kc(λ)·(1+η) ≤ η` with
   `Kc(λ) = (c/λ)^{24}`-type entropy factors.
   The existing literal-6/7 files cannot be reused by substitution, because `lam` is a def and
   many steps `decide` numeric facts about it.
   Estimate: 1,000–2,000 lines, additive (no edits to Realizer/J04 files).
2. A pilot instance. At ε_S = 10⁻¹², any λ with `ε·(c/λ)^{24}` small enough works. Roughly,
   λ can be taken as small as about ε^{1/24}·c, for example λ ≤ 1/4 or better. That would make
   the torus χ₁ rate beat BF4's `timeRate = 1/4`, removing the rate mismatch noted in the
   TorusChiBridge scoping. It still needs `hcov` and the Realizer's `hsup`/`hshift`, and it does
   not identify the two carriers.
3. Optional: thread the improved λ through `normalized_torus_ratio` (rate λ² per two steps).
   This is cheap, since that file only consumes `cov_decay`.

## Does the rate improve as β_S grows?

No, the opposite. The admissible λ(ε) grows with ε, so the rate gets worse as β grows. It
reaches λ → 1 at the KP radius, where `sharp_pass`-type conditions fail. This is somewhere
below the β ≲ 10⁻⁴ window these files already label as strong-coupling-only. No version of
this route is uniform as β grows, and none reaches the weak-coupling or AF regime. It says
nothing about the 1/side rate that H1 needs. The r40 no-go
(`shiftedH1_forbids_uniformRate`) and `constant_rate_not_all_scale_upper` still apply.

## U(1) rule

The whole chain is a generic polymer expansion with no SU(2)-specific input beyond activity
bounds. It is U(1)-true, so it is not non-abelian gap evidence. 4D U(1) is gapless at large β,
consistent with the breakdown above.

## Recommendation

This is worth doing only if a sharper fixed-coupling torus rate is wanted, for example to make
a heat-kernel or Wilson torus comparison with BF4 rate-consistent. Budget it as a multi-commit
track (1–2k lines), not one ≤400-line commit. It does not advance the Clay obligations.
