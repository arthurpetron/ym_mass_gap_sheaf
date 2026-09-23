# Audit: conjugated finite head heat defect (2026-09-22)

## Scope

This milestone transports the existing finite local estimate through an
explicit `QuaternionBlockInvolution`.  It is a polynomial/Haar carrier
result only.  It does not identify the transported operator with an
interacting selected-link kernel and does not assert an OS gap, a limit, or a
continuum theorem.

## Checked declarations

Source: `lean/YMGap/Continuum/SU2QuaternionConjugatedHeadHeat.lean`

- `conjugatedHeadMap` defines the conjugated update.
- `conjugatedHeadMap_pairing` identifies its same-carrier Haar pairing with
  the existing `heatPair` applied to the recoded polynomial.
- `conjugatedHeadMap_mean` proves preservation of the finite Haar mean.
- `conjugatedHeadMap_supported` preserves finite block support.
- `conjugatedHeadMap_defect_le_angular` proves

  `H[p^2] - H[p * conjugatedHeadMap s w K p]`
  `<= (1-w) * H[angularSquare (reindex s p)]`

  for `0 <= w < 1`, `K >= sufficientCutoff w`, and every supported `p`.

The proof uses `headMap_defect_le_angular`, `quaternionHaar_reindex`,
`reindexQuaternionPolynomial_mul`, and `reindex_pair`.  No derivative/reindex
commutation theorem is used or claimed.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \\
  --check lean/YMGap/Continuum/SU2QuaternionConjugatedHeadHeat.lean
```

Result: exit 0.  The source-level `#print axioms` commands for the five
public declarations report only `{propext, Quot.sound}`.  No `sorry`,
`admit`, `Classical`, `choice`, or `native_decide` was added.

## Remaining obligation

The next bridge must identify this conjugated finite update with the intended
selected-link update on the actual interacting carrier, then control the
multi-factor signed endpoint and SAME-object variance uniformly.  The OS/GNS,
thermodynamic/continuum, physical-mass, full-QFT, and every-compact-simple-
group nodes remain open.
