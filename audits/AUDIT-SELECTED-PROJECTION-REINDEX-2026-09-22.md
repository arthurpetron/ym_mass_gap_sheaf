# Audit: selected projection recoding

Date: 2026-09-22 UTC

## Scope

This milestone is a finite SU(2) quaternion-carrier identity.  It transports
one selected conditional Haar projection through the explicit block
involutions used to expose a selected pair as the literal head pair.  It does
not prove an angular telescope, a signed endpoint estimate, an OS/GNS
construction, a thermodynamic or continuum limit, or a physical mass gap.

## Checked declarations

| declaration | role |
| --- | --- |
| `YMGap.Continuum.SU2QuaternionSelectedProjectionReindex.reindex_integrateQuaternionBlock` | Coefficient-probe equivalence between selected-block integration followed by reindexing and reindexing followed by integration over the recoded block. |
| `YMGap.Continuum.SU2QuaternionSelectedProjectionReindex.exposeTranslationPair_project` | Composition of the head and tail block permutations, identifying the doubly recoded selected projection with the literal head projection of `exposeTranslationPairPolynomial`. |

The proof uses the explicit `clearQuaternionBlock` mask, the constructive
`QuaternionBlockInvolution`, `Nat.div_add_mod`, and
`quaternionBlockMoment_reindex`.  The raw polynomial list is not identified
by a classical extensionality theorem; the public statement is the existing
coefficient-probe relation `RatPolyCoeffEqv`.

## Verification

Focused command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/SU2QuaternionSelectedProjectionReindex.lean \
  --log-file /tmp/ym-selected-projection-reindex-clean-check.log
```

The command exited 0.  The reported axiom dependencies were:

```text
reindex_integrateQuaternionBlock depends on [propext, Quot.sound]
exposeTranslationPair_project depends on [propext, Quot.sound]
```

The module is imported by `lean/YMGap.lean`; no full-root or continuum audit
is claimed by this focused check.

## Remaining next seam

Consume the recoding in the selected local angular-defect estimate.  The
inactive Haar projections, signed endpoint correction, spatial uniformity,
same-object variance bridge, physical calibration, continuum construction,
and all compact simple groups remain open.
