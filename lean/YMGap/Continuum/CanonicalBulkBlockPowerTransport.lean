/-
Track 11.7-fusion / R2e -- the corrected canonical bulk-localization to physical
block-power transport.

# Why this module exists

`FrontierDAG.bulkCtrl` now carries the physical, re-based finite certificate

```text
RebasedBulkLocalizationBridge.CanonicalBulkControl N w p.
```

Its proved consumer says that every mode in the effective bulk window of the
actual vacuum-normalized fusion spectrum lies below the original gap edge.  The
historical route through `DeltaFrontierLedger.BondMovingGapPreservation` cannot be
used for this certificate: that bundle requires a `SpectralLocalization w` against
the bare `p = 1` heat rate, and the intended physical `p >= 2` pin is exactly
refuted by `RebasedBulkLocalizationBridge.noBareFusionLocalizationAtFence`.

This module therefore gives the corrected, non-circular bypass.  It:

1. names the exact modewise output of `CanonicalBulkControl` as
   `CanonicalBulkLocalizationVerdict`;
2. proves that every canonical carrier supplies that verdict;
3. names the remaining physical identification

```text
canonical bulk localization -> IsBlockPower b blockingStep.Phi
```

   as `CanonicalBulkToBlockPowerBridge`; and
4. composes that bridge with the existing green
   `BlockingStepFrontier.physicalRGInput_of_blockingPower` and
   `physicalGap_of_blockingPower` consumers.

# Honesty boundary

The modewise localization verdict is PROVED from the canonical finite certificate.
The implication from that spectral verdict to the exact `CReal` block-power law is
NOT proved here for physical four-dimensional Yang--Mills.  It is a named field of
`CanonicalBulkBlockPowerTransport`, because it must identify the fusion calculation
with the genuine physical block-spin map.  The exactly-solvable hierarchical map
inhabits the bridge (`hierarchicalBulkToBlockPowerBridge`), showing the interface is
non-vacuous, but that model witness is not presented as the physical 4D discharge.

# Constructivity

Pure composition over `Q'`, `CReal`, and existing constructive carriers.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
Every load-bearing declaration is axiom-gated below.
-/

import YMGap.Continuum.RebasedBulkLocalizationBridge
import YMGap.Continuum.BlockingStepFrontier

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkLocalizationBridge

/-! ## 1. The exact proved output of the canonical finite certificate -/

/-- **The corrected canonical bulk-localization verdict.**  For every mode in the
bulk window determined by the certificate's effective heat weight, the actual
vacuum-normalized `p`-fold fusion eigenvalue lies below the original `s = 1` gap
edge.  The cutoff, bare weight, exponent, effective weight, and denominator are all
definitionally those of the same `CanonicalBulkControl`. -/
def CanonicalBulkLocalizationVerdict {N : Nat} {w : Q'} {p : Nat}
    (C : CanonicalBulkControl N w p) : Prop :=
  forall s : Nat,
    q12 <= Q'.ofNat (c4 s) * ((1 : Q') - C.weff) ->
      fusionEig N w p s (C.denomPos s) <= eigA w 1

/-- **Finite certificate to localization verdict (PROVED).**  This is the exact
output of `CanonicalBulkControl.bulk_below_gapEdge`, packaged once for the physical
block-power consumer. -/
theorem canonicalBulkLocalizationVerdict {N : Nat} {w : Q'} {p : Nat}
    (C : CanonicalBulkControl N w p) :
    CanonicalBulkLocalizationVerdict C :=
  fun s hbulk => C.bulk_below_gapEdge s hbulk

/-! ## 2. The one honest physical identification still required -/

/-- **The canonical-localization to block-power bridge.**  Given the proved
modewise verdict for the actual fusion spectrum, identify the genuine physical
single-step map with the exact `(b+1)`-power map on constructive-real separators.

This is deliberately a named `Type`-level interface.  The finite saddle-to-exp
certificate proves its premise; the conclusion additionally requires the physical
dictionary between the fusion spectrum and `blockingStep.Phi`, and therefore does
not follow from rational inequalities alone. -/
structure CanonicalBulkToBlockPowerBridge
    {N : Nat} {w : Q'} {p b : Nat} {physSep : Nat -> CReal}
    (C : CanonicalBulkControl N w p)
    (blockingStep : BlockingStepFrontier.BlockingStep physSep) : Type where
  /-- The genuine physical dictionary from the proved spectral verdict to the
  exact constructive-real block-power law. -/
  toPower : CanonicalBulkLocalizationVerdict C ->
    BlockingStepFrontier.IsBlockPower b blockingStep.Φ

/-- **Hierarchical non-vacuity.**  For the exactly-solvable hierarchical block map,
the block-power conclusion is already a theorem because the map is definitionally
the `(b+1)`-power.  Thus any canonical localization certificate supplies the bridge
there.  This validates the transport interface; it is not the physical 4D witness. -/
def hierarchicalBulkToBlockPowerBridge
    {N : Nat} {w : Q'} {p : Nat} (C : CanonicalBulkControl N w p) (b : Nat) :
    CanonicalBulkToBlockPowerBridge (b := b) C
      (BlockingStepFrontier.concreteBlockingStep b) :=
  { toPower := fun _ => BlockingStepFrontier.concreteBlockingStep_isPower b }

/-! ## 3. The corrected physical transport bundle -/

/-- **`CanonicalBulkBlockPowerTransport` -- the corrected canonical path to the
physical block-power law.**  It carries one completed canonical finite fusion
certificate, the genuine physical separator family and one-step map, and the
single named physical identification from the certificate's proved localization
verdict to `IsBlockPower`.

Unlike the legacy `DeltaToBlockPower`, no arbitrary `SpectralLocalization.eig'` and
no known-false comparison with the bare `p = 1` heat rate occur in this type. -/
structure CanonicalBulkBlockPowerTransport
    (b N : Nat) (w : Q') (p : Nat) : Type where
  /-- The corrected finite re-based fusion certificate. -/
  bulkCtrl : CanonicalBulkControl N w p
  /-- The block factor is a genuine decimation. -/
  hb : 1 <= b
  /-- The physical Yang--Mills separator family. -/
  physSep : Nat -> CReal
  /-- The genuine one-step physical block-spin relation on those separators. -/
  blockingStep : BlockingStepFrontier.BlockingStep physSep
  /-- **THE NAMED PHYSICAL RESIDUAL.**  Identify the proved modewise fusion
  localization verdict with the exact block-power law of the physical map. -/
  localizationToPower :
    CanonicalBulkToBlockPowerBridge (b := b) bulkCtrl blockingStep
  /-- The physical separators are nonnegative. -/
  sepNonneg : forall k, ExpPos.geRat (physSep k) 0
  /-- The physical separators are at most one. -/
  sepLeOne : forall k, CReal.leRat (physSep k) 1
  /-- Explicit UV-gap floor. -/
  floor0 : Q'
  /-- Strict positivity of the UV-gap floor. -/
  floor0_pos : (0 : Q') < floor0
  /-- The floor lies below the physical gap at the coarsest scale. -/
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (CodynamicPhysFloor.physGapC b physSep (RateMatchFloor.geomSpacing b) 0)

/-- **Canonical certificate to physical block power (PROVED conditional
transport).**  The certificate supplies the exact localization premise; the
bundle's sole physical identification consumes it. -/
theorem CanonicalBulkBlockPowerTransport.blockPower
    {b N : Nat} {w : Q'} {p : Nat}
    (T : CanonicalBulkBlockPowerTransport b N w p) :
    BlockingStepFrontier.IsBlockPower b T.blockingStep.Φ :=
  T.localizationToPower.toPower (canonicalBulkLocalizationVerdict T.bulkCtrl)

/-- **The corrected canonical carrier builds the physical RG input.**  This bypasses
the historical bare-reference δ bundle and feeds the resulting block-power theorem
directly to the existing constructive consumer. -/
def CanonicalBulkBlockPowerTransport.physicalRGInput
    {b N : Nat} {w : Q'} {p : Nat}
    (T : CanonicalBulkBlockPowerTransport b N w p) : PhysicalRGInput :=
  BlockingStepFrontier.physicalRGInput_of_blockingPower
    T.hb T.physSep T.blockingStep T.blockPower T.sepNonneg T.sepLeOne
    T.floor0 T.floor0_pos T.hbase0

/-- **The corrected canonical carrier builds the spacing-uniform continuum gap
floor.**  No legacy `SpectralLocalization` is introduced along this path. -/
def CanonicalBulkBlockPowerTransport.continuumGap
    {b N : Nat} {w : Q'} {p : Nat}
    (T : CanonicalBulkBlockPowerTransport b N w p) :
    UnifiedContinuumFloor.CRealFloor
      (CodynamicPhysFloor.physGapC b T.physSep (RateMatchFloor.geomSpacing b)) :=
  BlockingStepFrontier.physicalGap_of_blockingPower
    T.hb T.physSep T.blockingStep T.blockPower T.sepNonneg T.sepLeOne
    T.floor0 T.floor0_pos T.hbase0

/-- The transported physical continuum floor is strictly positive. -/
theorem CanonicalBulkBlockPowerTransport.continuumFloor_pos
    {b N : Nat} {w : Q'} {p : Nat}
    (T : CanonicalBulkBlockPowerTransport b N w p) :
    (0 : Q') < T.continuumGap.floor :=
  T.continuumGap.floor_pos

end YMGap.Continuum

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.canonicalBulkLocalizationVerdict
#print axioms YMGap.Continuum.hierarchicalBulkToBlockPowerBridge
#print axioms YMGap.Continuum.CanonicalBulkBlockPowerTransport.blockPower
#print axioms YMGap.Continuum.CanonicalBulkBlockPowerTransport.physicalRGInput
#print axioms YMGap.Continuum.CanonicalBulkBlockPowerTransport.continuumGap
#print axioms YMGap.Continuum.CanonicalBulkBlockPowerTransport.continuumFloor_pos
