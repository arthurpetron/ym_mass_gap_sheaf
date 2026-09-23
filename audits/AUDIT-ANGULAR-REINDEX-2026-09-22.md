# Audit: padded-safe angular block transport (2026-09-22)

## Scope

This milestone proves the finite formal-differential and Haar-energy
transport needed to rewrite the recoded head defect in terms of the original
selected quaternion block.  It is a finite SU(2) polynomial/carrier result.
It does not identify the conjugated update with the interacting selected-link
kernel and does not assert an OS gap, a thermodynamic limit, or a continuum
Yang--Mills theory.

## Checked declarations

Source: `lean/YMGap/Continuum/SU2QuaternionAngularReindex.lean`

- `reindex_ratDerivative` transports `ratDerivative` through a block
  involution at `RatPolyCoeffEqv` level.
- `reindex_blockAngularSquare_haar` transports the six-plane
  `blockAngularSquare` Haar energy from `s.map block` to `block` after
  recoding.

The second proof uses `QuaternionPrefixPolynomialEqv` and
`quaternionHaar_prefixPolynomialEqv`; trailing-zero padding is therefore
handled by the declared finite support relation rather than by raw list
equality.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 10 \
  --check-worker-limit-gib 16 \
  --check lean/YMGap/Continuum/SU2QuaternionAngularReindex.lean \
  --log-file /tmp/ym-angular-reindex-block4.log
```

Result: exit 0.  The source-level `#print axioms` commands for both public
declarations report only `{propext, Quot.sound}`.  No `sorry`, `admit`,
`Classical`, `choice`, or `native_decide` was added.

The dependency-complete root traversal also built the new module, then
stopped at pre-existing missing declarations in
`BF4PhysicalBoundaryCutoffTwoPulledRootStrictFormGap.lean` and
`BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.lean`.

## Remaining obligation

The transported angular energy still has to be joined to the actual
interacting selected-link update and then to a signed multi-factor,
same-object uniform estimate.  The completed vacuum-complement gap,
OS/GNS/scaling passage, continuum survival, physical mass, full QFT axioms,
and every-compact-simple-group construction remain open.
