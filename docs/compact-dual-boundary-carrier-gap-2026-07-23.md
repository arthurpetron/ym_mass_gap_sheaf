# CD-2 boundary-carrier gap

## Finding

The existing compact-dual CD-1 boundary carrier is too small for the wheel
channel used by the positive-channel door.

`CompactDualBoundaryReflectionCone.DualBoundaryState` contains one
`CharacterPacket`, and its mode type is

```text
Fin (D.cutoff + 1).
```

That is the correct carrier for the one-interface Schur-diagonal cone proved
in CD-1.  It does not retain four ordered boundary slots, their cyclic
incidence, or an intertwiner basis.

The wheel manifest requires four distinct rim slots with words

```text
X0 X1^-1
X1 X2^-1
X2 X3^-1
X3 X0^-1.
```

For the pinned unit-rim example their mode values are all `1`, but equality
of values does not identify the slots.  The all-label squared-norm theorem
depends on which `m_i` appears on each side of every page, so collapsing the
four slots to one mode destroys the theorem's input data.

## Executable gate

`computations/dual_boundary_carrier_gap.py` introduces the minimal ordered
multi-link carrier and reads the four cyclic words directly from the exact
manifest.  It proves:

- required rim arity: `4`;
- existing CD-1 interface arity: `1`;
- exact cyclic orientation:
  `((i,+1),((i+1) mod 4,-1))`;
- preservation of four slot identities even for modes `(1,1,1,1)`;
- cutoff support of each slot.

The abstract manifest carrier is now closed.  The physical carrier remains
open at:

```text
physical_half_time_slot_ids_pinned
```

followed by the reflection permutation and the actual intertwiner basis.

## Required Lean correction before CD-2

CD-2 needs a new carrier indexed by an ordered finite set of interface slots,
not a reuse of the one-interface state.  Its minimum content is:

```text
MultiLinkDualBoundaryState D

slots                 : List physical-interface-slot
slotModes             : slot -> Fin (D.cutoff + 1)
intertwinerChannel     : admissible basis element for the slot packet
reflectionPermutation : slot equivalence induced by half-time reflection
packetCoefficient     : exact coefficient on the full labelled channel
```

The one-interface `DualBoundaryState` should embed as the arity-one special
case.  The four-rim wheel map must land in the arity-four carrier and prove
that its slot words and reflection permutation are those of the physical
half-time interface.

Only after that map exists can the scalar wheel activity be promoted to a
physical Gram channel.  The currently proved CD-1 self-Gram remains valid,
but it cannot serve as the missing CD-2 channel map.
