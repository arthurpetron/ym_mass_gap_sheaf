# Actual original root/log squared-distance comparison

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. This increment applies the
proved diagonal estimates to the actual two finite maps. Equality of their
limits, physical calibration and changing-family control are not claimed.

## Constructed finite estimate

`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogNormComparison.lean:42`,
`errorCoefficient`, is explicit rational data e=2*half^d+invSucc(M).
:52, `errorCoefficient_positive`, proves e>0. :65, `finiteDifference`,
subtracts the EXISTING differenceQuotient_(d+2) from EXISTING logPartial_M
on the ORIGINAL completion. :68, `finiteDifference_symmetric`, proves
its symmetry using the already proved symmetry of BOTH actual maps.

Required addition/subtraction laws are then proved from symmetry and the
original positive-definite pairing, not supplied as caller hypotheses.
The proved diagonal estimates are widened to +/-e*Bxx by scalar order.
The checked rational polarization principle consequently gives :93,
`root_log_norm_bound`:

    dist(logPartial_M x,differenceQuotient_(d+2)x)
      <= (2*half^d+invSucc(M))^2 * Bxx, M>0.

Every state, 0<w<1 and width is retained, including the original boundary
kernel. There is no scalar spectral representation, inverse operator or
caller-supplied form/norm/linearity estimate. The coefficient is independent
of the state, nome and width; the SAME original norm appears on the right.
The diagonal producer evidence is retained in
`audits/AUDIT-ORIGINAL-ROOT-LOG-FORM-COMPARISON-2026-10-03.md`.

## Exact remaining frontier

The next backward target is the EXISTING explicit quotient/log limit-modulus
join, to prove derivativeAction=regularizedLog on this SAME carrier.
The derivative acts on the positive-time range; neither map is declared
here to be a self-adjoint physical Hamiltonian on the whole carrier.
The independent forward input remains complete original signed cost versus
SAME OWN variance, or a retained macro ratio, on a JUSTIFIED changing family.
No producer for it is supplied. Continuum survival, physical calibration,
full QFT, every-group construction and Clay remain OPEN.

## Focused verification boundary

One NEW target passed its focused a-check, reporting five gates: one
axiom-free definition and four within {propext, Quot.sound}. Root reviewed
the full source; Sol supplied the actual norm application. Review is not
proof. The accepted log exited zero with no error, warning, sorryAx or PANIC.

The monitored launcher used one worker, 20-GiB cap, 12-GiB reserve, after
fresh memory/process/swap checks: 84% free memory and zero swap. No concurrent
build, full root/tree build, broad audit/guard or progress metric ran.
Root import registered only. No sorry, axiom, frontier weakening, CI or
exact canonical chart change.

| Artifact | SHA-256 |
| --- | --- |
| lean/YMGap/Continuum/BF4WilsonAllNomeRootLogNormComparison.lean | 5e7602d3de42e14b312bd180ddf2b86e3f1caec05169c8a48f5c7fb6496900bd |
| /tmp/ym-original-root-log-norm-comparison-20261003-a.log | 5808ae34b033e94948344b9fcb2668782b22d0f768f5d220b5501da6cdfa5936 |

Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
