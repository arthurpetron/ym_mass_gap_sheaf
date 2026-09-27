# Original normalized covariance and conditional sweep

## Checked result

At each finite cutoff `headCutoff(w)+stage`, with `0<w<1`, define
`Cp = p - E[p] * 1` using the EXISTING full-action finite expectation.
On the EXISTING original weighted GNS completion the new module proves

    Cov(p,q) = (1/Z) B(Cp,Cq)
             = (1/Z) B(sweep^rounds Cp,Cq)

provided the `8*rounds`-expanded link support of p avoids the support of q.
The second equality uses the checked eight-layer physical schedule. Both
centered states are explicit supported original polynomials. No new action,
partition, completion, assumed covariance identity or unit-normalizing
square root is introduced.

All source references below are in
`lean/YMGap/Continuum/BF4ExactSlabConditionalCovariance.lean`.

| Declaration | Line | Content |
|---|---:|---|
| `inversePartition` / `inversePartition_cancel` | 90 / 94 | Existing finite reciprocal; its product with the original partition is one. |
| `mean` / `centered` | 103 / 106 | Computed original finite expectation and explicit original-polynomial centering. |
| `pair_numerator` / `pair_unit` | 112 / 115 | Actual full-action pairing equals the existing insertion numerator. |
| `unit_norm` | 122 | The constant polynomial has squared norm Z, not one. |
| `centered_unit` | 135 | Actual global mean zero, proved using partition cancellation. |
| `normalized_centered_pair` | 152 | Exact rational covariance with BOTH states centered. |
| `centered_local` | 158 | Subtracting the computed constant preserves literal link support. |
| `completed_covariance` | 163 | The same exact identity on the existing completion. |
| `completed_centered_unit` | 170 | Centered embedded state is orthogonal to the original unit. |
| `sweep_centered_unit` | 178 | Actual conditional color layers preserve this global centering. |
| `covariance_as_sweep_pairing` | 190 | Exact normalized original covariance as an iterated sweep pairing before cone contact. |

`stage` is the heat-cutoff offset. `rounds` counts conditional sweeps on one
fixed carrier. Neither is reinterpreted as physical time. The reciprocal
retains its nome, cutoff and extent dependence; no uniform decay estimate
is asserted by the equality.

## Remaining mathematical work

The normalized covariance connection is now proved, but the useful strict
contraction of these actual states is not. Global mean zero is weaker than
the unproved identification with the common-fixed-space complement. The
bounded-degree final-residual energy inequality and useful original-action
coercivity also remain open. The available full-weight/Haar comparison pays
a factor per face and does not supply the needed volume-independent bound.

Sol's independent source review identified a bounded geometric next step:
prove that contact after R star expansions forces the two probe-carrier
roots to have coordinate distance at most R plus the two carrier sizes.
The existing `edge_base_comp`, `natDist_triangle` in
`lean/YMGap/Continuum/SepLatticeZ4Linf.lean`, and
`rootedAnimal_linf_size_floor` in
`lean/YMGap/Continuum/BF4ExactSlabCoreDistanceFloor.lean` support this argument.
The one-star link-distance and iterated-grow lemmas are NOT yet proved.
This would supply the current cone-separation premise, not a contraction
rate. It is separate from the missing analytic bound.

There is no new OS transfer/Hamiltonian claim, physical-spacing estimate,
continuum construction, or every-group Clay closure. No canonical frontier
field or chart marker changes.

## Verification

The final focused safe check passed in 2.18 seconds with one worker and a
20 GiB worker cap. All 11 printed axiom dependencies are within
`{propext, Quot.sound}`; no warnings or errors remained. The command was:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabConditionalCovariance.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabConditionalCovariance.olean
```

Initial checks exposed notation parsing, rational-setoid transitivity and
missing namespace opens; those were repaired without changing the
mathematical statements. No source `sorry`, new axiom or classical proof
was introduced. Sol independently reviewed the normalization, literal
support, same-carrier and separate-parameter arguments. No full-tree build
or axiom audit was run. No routine math-ph refresh was needed.
