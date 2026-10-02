# Cutoff norm control on the original centered Wilson source

## Result and proof path consequence

The actual omitted heat form now has diagonal and mixed Haar-norm bounds,
without a source-degree guard or assumed linearity of the ragged mode tree.
Both omitted absolute-leaf costs are removed from an actual generic energy
ceiling. The original centered source uses its OWN mean and SAME partition,
retaining its signed variance correction. This supplies cutoff norm control,
not useful scaling control or a continuum mass gap. No Clay node is closed.

Let O_K(p,t) be `pairOmitted` and rho=w^((K+1)*(K+3)). For supported signed
polynomials and 0<=w<=1, the new proofs give

    0 <= O_K(p,p) <= rho*H[p^2],
    O_K(p,t)^2 <= rho^2*H[p^2]*H[t^2],
    -O_K(p,t) <= rho*(H[p^2]+H[t^2])/2.

## Exact declarations and causal joins

| Declaration | Source | Content |
| --- | --- | --- |
| `omittedRate` | `lean/YMGap/Continuum/SU2QuaternionCyclicOmittedNorm.lean:45` | Coupling/cutoff coefficient as data |
| `pairOmittedBudget_diagonal_eq` | same file, line 74 | Literal equality of diagonal absolute budget and signed pairing |
| `pairOmitted_diagonal_le_haar` | same file, line 88 | Monotonic coefficients and exact unweighted reassembly give norm cap |
| `pathMax` | `lean/YMGap/Continuum/SU2QuaternionCyclicOmittedOperator.lean:49` | Finite maximum over every branch and rotated descendant |
| `pathMax_retained` | same file, line 64 | Every valid path is retained at that envelope |
| `pairOmitted_at_saturation` | same file, line 113 | O_K(p,t)=kineticPair_M(t,p)-kineticPair_K(t,p) at saturation |
| `pairOmitted_symm` | same file, line 135 | ONE common maximum covers both input-dependent trees |
| `omittedGNSData` | same file, line 186 | Concrete symmetric PSD omitted form; not a physical OS carrier |
| `pairOmitted_cauchySchwarz` | same file, line 210 | Sharp constructive CS for that SAME form |
| `pairOmitted_square_le_haar` | same file, line 220 | Squared mixed cap with rho squared |
| `neg_pairOmitted_le_haar` | same file, line 244 | Negative mixed sign needed by actual source energy |
| `sourceError_le_haar` | same file, line 300 | Complete cubic-minus-omitted error, both cubic budgets retained |
| `sourceEnergy_le_secondOrder_haar` | same file, line 342 | Actual generic energy consumer; signed second-order term retained |
| `centered_diagonalOmitted_le_variance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredOmittedNorm.lean:80` | Original diagonal bounded by rho*(Z*OWNVar-C) |
| `centered_mixedOmitted_square_bound` | same file, line 95 | Original mixed source retains raw fourth moment |
| `centeredHaarBudget_pin` | same file, line 120 | Exact original-source variance correction, not q^2=qPq |
| `centered_sourceError_le_haar` | same file, line 136 | Actual original centered numerator consumer |
| `normalized_centered_sourceError_le_haar` | same file, line 149 | BOTH sides divided by SAME positive original Z |

Full-path positivity and coefficient monotonicity are reused from
`SU2QuaternionCyclicDiagonalRemainder.full_path_pairing_nonnegative`
(`lean/YMGap/Continuum/SU2QuaternionCyclicDiagonalRemainder.lean:70`) and
`SU2QuaternionDiagonalRemainderMoment.full_leafSum_diagonal_mono`
(`lean/YMGap/Continuum/SU2QuaternionDiagonalRemainderMoment.lean:86`).
Unweighted reassembly is
`SU2QuaternionCyclicPathReassembly.full_leafSum_one`
(`lean/YMGap/Continuum/SU2QuaternionCyclicPathReassembly.lean:62`).
The saturation identification uses existing actual heat pairings and their
symmetry, not an unproved common spectral decomposition.

## Original source and remaining estimate

With q=P_fringe(V*g_n) and psi centered by the ORIGINAL odd marginal,
`centered_sourceSquare_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:159`)
gives H[q^2*psi^2]=Z*OWNVar-C. No sign for C is introduced. The complete
cubic-minus-omitted numerator is bounded by

    h^3*(cubicMixedBudget+cubicDiagonalBudget)
      + rho*( (H[q^2]+H[q^2*psi^4])/2 + Z*OWNVar-C ),
    h=1-w.

The raw Haar mass and fourth moment depend on the source, hence on nome,
cutoff, depth and width. The statements do not assert uniform bounds on those
moments, beta independence, physical spacing calibration or useful
OWN-variance-relative scaling. Auxiliary M is computed separately for the
finite input trees; it is not a uniform saturation cutoff. No original heat
cutoff or action is changed.

The diagonal old absolute budget already equals the exact positive debt.
The new norm cap may be larger, so no numerical sharpening of every old
budget is claimed. The new source energy estimate bounds the actual signed
error directly; it does not assert that its mixed norm cap dominates the old
mixed absolute budget in either direction.

The existing retained-gain consumer remains
`paddedSquare_energy_projection_bound`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean:279`).
Propagation of the new error cap through the exact cancelled remainder while
retaining that gain and separate angular/Ward terms is still OPEN in this
checkpoint. Useful relative moment/debt control on a justified changing
family, nontrivial continuum survival, physical mass calibration, full QFT
structure and every-group construction remain OPEN.

## Verification boundary

All three final focused checks returned exit zero, warning/error-free:

- `/tmp/ym-cyclic-omitted-norm-20261002-accepted.log`: nine printed gates.
- `/tmp/ym-cyclic-omitted-operator-20261002-final.log`: fourteen printed gates.
- `/tmp/ym-original-centered-omitted-norm-20261002-accepted.log`: six gates.

All 29 gates use only {propext,Quot.sound}; `omittedRate` is axiom-free.
Independent Sol source/mathematics review passed for the exact final sources
and logs. No new sorry, axiom, classical premise or weakened frontier field.
One downstream root import is added; it transitively includes both generic
modules. The root itself, full tree/build/audit/guard and progress metric were
NOT run. The automatic axiom baseline is not regenerated by a narrow check.
CI stays disabled except manual dispatch; canonical chart blocks unchanged.

Checks used `scripts/safe_lean_build.py`, serialized with one worker,
20 GiB hard cap and 12 GiB OS reserve. Preflight found no competing Lean,
Lake, pytest or runner process. Pressure-free capacity was 85--86%, with
zero swap at preflight and postflight. No safety threshold or limit changed.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionCyclicOmittedNorm.lean` | `cbbc30a8c626d7ce1a350dc122e830c64a96158502b5cdc2a22e054c23e937f5` |
| `SU2QuaternionCyclicOmittedOperator.lean` | `3c21c0a230f69031c87ecce13ab19b7ce4bfa39d19303528a4e8381823a38b1e` |
| `BF4ExactSlabFixedSpatialCenteredOmittedNorm.lean` | `db14ba4847189cac54fbb3e45715a58609546d09e569e1eae518af16af170212` |
| diagonal accepted log | `e7dfc2876358617b0b72773a3b4bda556f0a954454770d8c6cf1d706bd115f06` |
| operator final log | `c0d34d4a9bd02a7805b1c08b121c6c62dcf2d4ab133b66cab01e592219a306f4` |
| original accepted log | `a335ae3c0a5457ef9f86380752af173fe1e886dc8c182fbfe0ccefe6b3e37217` |
