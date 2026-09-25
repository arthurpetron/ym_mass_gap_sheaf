# Audit: minimal Wilson-to-OS bridge certificate

## Scope

This audit records the new checked interface in
`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean`.  It does not claim that the
interface is inhabited by the existing all-nome Wilson completion and the
strict OS completion; that concrete identification remains open.

## Checked declarations

- `YMGap.Continuum.BF4WilsonOSBridgeSpec.SameObjectBridge`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:29`) is the exact data
  bundle: two carriers, their pairings and discrete step maps, a map from the
  Wilson carrier to the OS carrier, vacuum elements, and the two
  vacuum-complement predicates.  Its fields require pairing preservation,
  step compatibility, vacuum preservation, and preservation of
  orthogonality.
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.OSFormGap`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:48`) names the OS-side
  two-step form inequality as a separate input.  The order and scaling
  operations are parameters, so the interface does not assume a particular
  scalar model.
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.OSFormFamily`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:62`) generalizes the
  input to an arbitrary lag-indexed bound, leaving its coefficient function
  explicit for a later same-object decay instantiation.
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.OSRelativeLossFamily`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:76`) names the analogous
  lag-indexed relative-energy defect, with subtraction, scaling, and defect
  coefficient all explicit inputs.
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.transfer_twoStep_form_gap`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:76`) transports that OS
  inequality to every Wilson vector whose orthogonality is preserved by the
  bridge.  Its focused check passed with no axioms (`#print axioms` reports an
  empty set).
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.transfer_form_family`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:95`) transports every
  member of the lag-indexed family to the Wilson carrier.  Its focused check
  also reports an empty axiom set.
- `YMGap.Continuum.BF4WilsonOSBridgeSpec.transfer_relative_loss_family`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:127`) transports the
  relative-loss family needed by the survival compiler.  Its focused check
  also reports an empty axiom set.

## Honest boundary

No declaration in this module constructs `SameObjectBridge`, proves
`OSFormGap`, identifies the two existing carrier types, or supplies spatial,
thermodynamic, continuum, physical-mass, QFT, or all-group control.  The
module is therefore a minimal typed consumer for the missing J02 bridge, not a
claim that the bridge has been discharged.

Verification command:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean \
  --check-output /tmp/ym-gap-os-bridge-spec-check3.log
```

Observed result: exit 0; `transfer_twoStep_form_gap` has no axioms.
