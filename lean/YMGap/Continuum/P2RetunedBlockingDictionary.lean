/-
Track 11.7-fusion / R2j -- repoint the physical dictionary to the p=2 compiler.

# Result

The original `FusionSpectrumBlockingDictionary` honestly requested a completed
`CanonicalBulkControl` at every RG scale.  `P2RetunedRatioCompiler` shows that
for the physical exponent `pGamma=2`, those controls can be generated from one
strictly smaller local datum: adjacent tail ratios above the already-proved
vacuum and fundamental modes.

This module makes that reduction load-bearing.  `P2RetunedControlFamily`
contains the scale-dependent cutoffs and weights together with only the local
tail-ratio family.  Its `control` method constructs every canonical carrier.
`P2RetunedBlockingPins.toDictionary` then supplies the genuine cross-scale
dictionary.  Consequently the remaining physical interface is exactly:

* the all-scale adjacent-ratio family;
* `finePin`;
* `imagePin`;
* `fusionPower`.

No global identity for an arbitrary blocking map is assumed or inferred.

# Constructivity

Pure structure compilation and existing `Q'`/`CReal` theorems.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedRatioCertificate
import YMGap.Continuum.FusionSpectrumBlockingIdentification

namespace YMGap.Continuum.P2RetunedBlockingDictionary

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.FusionSpectrumBlockingIdentification
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CodynamicCRealFlow

/-- **Reduced all-scale p=2 certificate family.**  Vacuum and fundamental
comparisons are absent because the compiler has already discharged them for
every cutoff and every `0 <= w <= 1`. -/
structure P2RetunedControlFamily : Type where
  N : Nat -> Nat
  w : Nat -> Q'
  hN : forall k, 1 <= N k
  hw0 : forall k, (0 : Q') <= w k
  hw1 : forall k, w k <= (1 : Q')
  hnc : forall k, (1 : Q') - w k <= SpectralLocalizationCrux.q112
  tailRatio : forall k, P2RetunedTailRatio (N k) (w k) (hw0 k) (hw1 k)

/-- Compile the reduced local family into the canonical carrier at scale `k`. -/
def P2RetunedControlFamily.control (F : P2RetunedControlFamily) (k : Nat) :
    CanonicalBulkControl (F.N k) (F.w k) 2 :=
  canonicalBulkControl_p2_of_tail (F.hN k) (F.hw0 k) (F.hw1 k) (F.hnc k)
    (F.tailRatio k)

/-- **The remaining genuine blocking pins.**  The control field is no longer
an input: every occurrence below uses the carrier compiled from `F.tailRatio`.
The three equality fields retain the exact physical content and are not
weakened to inequalities. -/
structure P2RetunedBlockingPins
    (b : Nat) (physSep : Nat -> CReal)
    (blockingStep : BlockingStep physSep)
    (F : P2RetunedControlFamily) : Type where
  mode : Nat -> Nat
  modeBulk : forall k,
    q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  finePin : forall k,
    CReal.Equiv (physSep (k + 1))
      (fusionModeCReal (F.control (k + 1)) (mode (k + 1)))
  imagePin : forall k,
    CReal.Equiv (blockingStep.Φ (physSep (k + 1)))
      (fusionModeCReal (F.control k) (mode k))
  fusionPower : forall k,
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (cpow (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) (b + 1))

/-- Compile the reduced p=2 family and exact pins into the already-reviewed
cross-scale fusion-spectrum dictionary. -/
def P2RetunedBlockingPins.toDictionary
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    {F : P2RetunedControlFamily}
    (P : P2RetunedBlockingPins b physSep B F) :
    FusionSpectrumBlockingDictionary b physSep B where
  N := F.N
  w := F.w
  pGamma := fun _ => 2
  pGamma_ge_two := fun _ => by decide
  control := F.control
  mode := P.mode
  modeBulk := P.modeBulk
  finePin := P.finePin
  imagePin := P.imagePin
  fusionPower := P.fusionPower

/-- The reduced interface reaches the exact trajectory-only block power law. -/
theorem P2RetunedBlockingPins.blockPowerOnTrajectory
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    {F : P2RetunedControlFamily}
    (P : P2RetunedBlockingPins b physSep B F) :
    IsBlockPowerOnTrajectory b physSep B.Φ :=
  P.toDictionary.blockPowerOnTrajectory

/-- Every selected coarse mode is localized by the compiled p=2 carrier. -/
theorem P2RetunedBlockingPins.coarseLocalized
    {b : Nat} {physSep : Nat -> CReal} {B : BlockingStep physSep}
    {F : P2RetunedControlFamily}
    (P : P2RetunedBlockingPins b physSep B F) (k : Nat) :
    fusionEig (F.N k) (F.w k) 2 (P.mode k)
        ((F.control k).denomPos (P.mode k)) <= eigA (F.w k) 1 :=
  P.toDictionary.coarseLocalized k

/-! ## The canonical spectrum-pinned separator trajectory -/

/-- The separator trajectory selected directly from the compiled p=2 fusion
spectrum.  This is the canonical domain on which the dictionary is intended
to identify the physical blocking map. -/
def fusionSeparator (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (k : Nat) : CReal :=
  fusionModeCReal (F.control k) (mode k)

/-- On the spectrum-defined trajectory, the fine fusion pin is definitional
and therefore carries no independent physical content. -/
theorem fusionSeparator_finePin (F : P2RetunedControlFamily)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv (fusionSeparator F mode (k + 1))
      (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) := by
  unfold fusionSeparator
  exact BlockingStepFrontier.equivRefl
    (fusionModeCReal (F.control (k + 1)) (mode (k + 1)))

/-- **Two-pin spectrum trajectory interface.**  Once the physical separator
is defined by the selected fusion spectrum, only the actual block-map image
and the adjacent-scale fusion power law remain.  This does not identify an
independently supplied separator trajectory; that same-action comparison is a
separate physical theorem. -/
structure SpectrumPinnedP2BlockingData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (blockingStep : BlockingStep (fusionSeparator F mode)) : Type where
  modeBulk : forall k,
    q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  imagePin : forall k,
    CReal.Equiv (blockingStep.Φ (fusionSeparator F mode (k + 1)))
      (fusionModeCReal (F.control k) (mode k))
  fusionPower : forall k,
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (cpow (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) (b + 1))

/-- Reconstruct the reviewed three-pin interface; `finePin` is discharged by
the spectrum trajectory definition. -/
def SpectrumPinnedP2BlockingData.toPins
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2BlockingData b F mode B) :
    P2RetunedBlockingPins b (fusionSeparator F mode) B F where
  mode := mode
  modeBulk := D.modeBulk
  finePin := fusionSeparator_finePin F mode
  imagePin := D.imagePin
  fusionPower := D.fusionPower

/-- The two genuine pins imply the trajectory block-power law. -/
theorem SpectrumPinnedP2BlockingData.blockPowerOnTrajectory
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2BlockingData b F mode B) :
    IsBlockPowerOnTrajectory b (fusionSeparator F mode) B.Φ :=
  D.toPins.blockPowerOnTrajectory

/-- End-to-end physical transport whose spectral input is the reduced p=2
tail family and whose map input consists only of the two spectrum-trajectory
pins. -/
structure SpectrumPinnedP2BlockingTransport (b : Nat) : Type where
  hb : 1 <= b
  family : P2RetunedControlFamily
  mode : Nat -> Nat
  blockingStep : BlockingStep (fusionSeparator family mode)
  pins : SpectrumPinnedP2BlockingData b family mode blockingStep
  sepNonneg : forall k, ExpPos.geRat (fusionSeparator family mode k) 0
  sepLeOne : forall k, CReal.leRat (fusionSeparator family mode k) 1
  floor0 : Q'
  floor0_pos : (0 : Q') < floor0
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (CodynamicPhysFloor.physGapC b (fusionSeparator family mode)
      (RateMatchFloor.geomSpacing b) 0)

/-- The two-pin p=2 transport constructs the reviewed physical RG input. -/
def SpectrumPinnedP2BlockingTransport.physicalRGInput {b : Nat}
    (T : SpectrumPinnedP2BlockingTransport b) : PhysicalRGInput :=
  physicalRGInput_of_blockingPowerOnTrajectory T.hb
    (fusionSeparator T.family T.mode) T.blockingStep
    T.pins.blockPowerOnTrajectory T.sepNonneg T.sepLeOne T.floor0
    T.floor0_pos T.hbase0

/-- The same reduced input reaches the spacing-uniform constructive-real gap
floor; no global map identity is inserted along the way. -/
def SpectrumPinnedP2BlockingTransport.continuumGap {b : Nat}
    (T : SpectrumPinnedP2BlockingTransport b) :
    UnifiedContinuumFloor.CRealFloor
      (CodynamicPhysFloor.physGapC b (fusionSeparator T.family T.mode)
        (RateMatchFloor.geomSpacing b)) :=
  physicalGap_of_blockingPowerOnTrajectory T.hb
    (fusionSeparator T.family T.mode) T.blockingStep
    T.pins.blockPowerOnTrajectory T.sepNonneg T.sepLeOne T.floor0
    T.floor0_pos T.hbase0

end YMGap.Continuum.P2RetunedBlockingDictionary

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.P2RetunedControlFamily.control
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.P2RetunedBlockingPins.toDictionary
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.P2RetunedBlockingPins.blockPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.P2RetunedBlockingPins.coarseLocalized
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.fusionSeparator_finePin
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.SpectrumPinnedP2BlockingData.toPins
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.SpectrumPinnedP2BlockingData.blockPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.SpectrumPinnedP2BlockingTransport.physicalRGInput
#print axioms YMGap.Continuum.P2RetunedBlockingDictionary.SpectrumPinnedP2BlockingTransport.continuumGap
