# Audit: selected-block defect corollary (2026-09-22)

## Scope

This milestone composes the finite conjugated-head defect bound with the
padded-safe angular block transport.  It rewrites the right-hand side as the
angular energy of the original block selected by the explicit involution.
It remains a finite SU(2) carrier statement and is not an interacting
selected-link identification, an OS gap, or a continuum theorem.

## Checked declaration

Source: `lean/YMGap/Continuum/SU2QuaternionConjugatedHeadHeatBlockEnergy.lean`

- `conjugatedHeadMap_defect_le_selected_block_energy` proves, for
  `0 <= w < 1`, `sufficientCutoff w <= K`, and supported `p`,

  `H[p*p] - H[p*conjugatedHeadMap s w K p]`
  `<= (1-w) * H[blockAngularSquare (s.map 0) p]`.

The proof uses the existing finite defect theorem, explicit support of the
selected block energy, Haar reindexing, the padded-safe angular transport,
and nonnegative multiplication by `1-w`.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 10 \
  --check-worker-limit-gib 16 \
  --check lean/YMGap/Continuum/SU2QuaternionConjugatedHeadHeatBlockEnergy.lean \
  --log-file /tmp/ym-conjugated-head-block-energy5.log
```

Result: exit 0.  The public declaration reports only `{propext, Quot.sound}`
under `#print axioms`.  No `sorry`, `admit`, `Classical`, `choice`, or
`native_decide` was added.

## Remaining obligation

The bound is still for the explicitly conjugated local update.  The physical
selected-link kernel, signed cross-term/telescoping control, uniform
same-object variance estimate, completed gap, OS/GNS/scaling passage,
continuum survival, physical mass, full QFT axioms, and every-group route
remain open.
