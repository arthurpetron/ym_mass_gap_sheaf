# Growing Wilson square and its original interacting variance

## Result and scope

The literal padded dyadic Wilson square now has a proved full-slice
Casimir and an exact temporal-energy identity against its OWN interacting
variance. This joins the growing observable to the existing signed Taylor
and centered-square estimates without replacing it by a linear plaquette
family. The complete signed error is retained, not bounded usefully.

All new declarations below are in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean`.
Write s=side(scale), L=4*s, kappa=3*L=12*s and h=1-w. The nome obeys
0<w<1; the literal carrier is strictly padded, s<width.

## Exact perimeter and original mean

`paddedSquare_character_degree` (line 116) proves degree one on each
selected quaternion block, including reverse orientations. It uses actual
link distinctness, `paddedSquare_indices_nodup`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareNodup.lean:238`).
`paddedSquare_casimir` (line 180) sums the contribution three over all L
selected blocks and proves zero contribution from spectators. Its Haar
equality permits arbitrary insertions; it is NOT an interacting transfer
eigenidentity or an inference from the bare finite-heat eigenvalue.

`paddedSquare_ward` (line 213) and `paddedSquare_normalized_ward` (line 231)
retain the full original marginal, partition Z and OWN mean. They give
A+W=kappa*V, with V the existing `oddVariance`, A the normalized angular
energy and W the normalized COMPLETE-weight Ward residual.

`paddedSquare_energy_variance` (line 257) therefore proves exactly

```text
E = kappa*h*V + varianceRemainder.
```

`paddedSquare_energy_centered_square` (line 290) also proves

```text
E <= (kappa*h + h^2/8)*V + completeCenteredError.
```

The existing `completeCenteredError`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:285`)
retains the signed source correction, Ward, cubic, omitted-mode and angular
pair debts. Neither error is asserted nonpositive or small. The Ward and
energy statements require K>=headCutoff(w); the upper bound additionally requires
K>=sufficientCutoff(w). Width, time depth, scale and nome remain explicit.

`finiteSquare_energy_variance` (line 334) pins the exact identity to the
EXISTING `finiteEnergy` and `finiteVariance` of `.loop 0 paddedSquare 1`
at K=headCutoff(w)+stage and the SAME depth. Its source translation is
literally zero. These are the quantities used by `finite_reference_ratio`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:52`);
no estimate is supplied to that conditional consumer here.

## Verification

The final focused check on 2026-10-02 UTC exited 0 without warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.olean --log-file /tmp/ym-dyadic-square-variance-taylor-20261002-second.log
```

All seven printed public gates report only {propext,Quot.sound}; independent
Sol mathematics review passed. An initial default-heartbeat reduction timeout
was resolved by local irreducibility of the existing weight/message/word
definitions. No limit, axiom or theorem hypothesis was raised or weakened.

- Source SHA256: `0ad160fae1a5301d5a103804c644812adb4e3bd933e39910306f9b434a38ceac`.
- Final log SHA256: `fd814312a37dc6aa09c6e895ccc27c6feec4d74641c1bd394a1543cd6b2af5cf`.
- One monitored 20 GiB capped worker with a 12 GiB OS reserve. Memory
  pressure reported 86 percent free before and after; swap was zero and
  no competing compiler/runner was found. No parallel compiler was started.
- No sorry, new axiom, analytic premise, native oracle or erased witness.
  One root import added; broad root/tree/audit/guard/progress checks NOT run.
  CI and the canonical chart are unchanged.

## Remaining mathematical input

The new identity does NOT replace the perimeter coefficient by 12. For a
target relative-energy rate rho, its required signed estimate is
`varianceRemainder <= (rho-kappa*h)*V` on a justified changing family.
The centered-square alternative still needs control of its complete error.
The geometric assignment of spacing in `BF4DyadicWilsonSquare.spacing`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:40`) is not a physical
coupling/time trajectory. Useful signed scaling control, nontrivial continuum
survival, physical mass calibration, full SAME-theory QFT and every compact
simple group remain OPEN. No exact chart claim closed.
