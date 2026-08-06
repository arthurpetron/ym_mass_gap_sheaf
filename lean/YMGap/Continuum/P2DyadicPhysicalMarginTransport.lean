/-
Track 11.7-fusion / R2u -- dyadic spectral data to the physical-margin wall.

`P2DyadicFusionHalfFloor` reduces the spectral side of the physical dyadic
ladder to one all-scale inequality, `coarse <= fine^2`.  This file wires that
reduced carrier into the reviewed Bucket-1-to-Bucket-2 transport without
reintroducing any quotient, map-identification, or product-floor premise.

The resulting structure has one genuine scale-to-scale estimate: transport
of the dimensionless physical margin by the certified fusion factor.  The
spacing, cluster-bound, ceiling, and anchor fields name the physical objects
on which that estimate acts; all spectral factor data are compiled from the
dyadic coefficient tail, refined cutoff bound, and monotonicity carrier.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionHalfFloor

namespace YMGap.Continuum.P2DyadicPhysicalMarginTransport

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.P2DyadicFusionGapBudget
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2DyadicFusionHalfFloor
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionAdditiveGap
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RegularContinuumPipeline

/-- The physical dyadic handoff after all spectral bookkeeping has been
compiled.  Beyond the named physical spacing/cluster objects, `recursion` is
the sole new Bucket-2 inequality. -/
structure DyadicP2PhysicalMarginTransport : Type where
  coeffTail : DyadicP2CoeffTailData
  refinedCutoff : DyadicP2RefinedCutoffData coeffTail
  blockingStep : BlockingStep
    (fusionSeparator coeffTail.toControlFamily modeOne)
  spectralMonotone : DyadicP2PhysicalMonotoneInput
    coeffTail refinedCutoff blockingStep
  spacing : Nat -> Q'
  spacing_pos : forall k, (0 : Q') < spacing k
  atSpacing : Nat -> RegUniformClusterBound
  ceilConst : Q'
  physCeil : forall k,
    Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) <=
      ceilConst
  anchor : Q'
  anchor_pos : (0 : Q') < anchor
  anchor_le : anchor <=
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  /-- **The remaining physical wall.**  The actual dimensionless cluster
  margin is transported by the factor extracted from the genuine dyadic
  fusion spectrum and `BlockingStep.Phi`. -/
  recursion : forall k,
    spectralMonotone.toSandwichInput.data.toCrossMul.factor k *
        Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) <=
      Q'.divPos ((atSpacing (k + 1)).floorRate)
        (spacing (k + 1)) (spacing_pos (k + 1))

/-- Compile the reduced dyadic spectrum into the reviewed physical-margin
transport.  The summable quotient and its positive product floor are derived,
not fields of this structure. -/
def DyadicP2PhysicalMarginTransport.toDefectMarginTransport
    (T : DyadicP2PhysicalMarginTransport) :
    SpectrumPinnedP2DefectMarginTransport 1 where
  hb := by decide
  family := T.coeffTail.toControlFamily
  mode := modeOne
  blockingStep := T.blockingStep
  spectral :=
    T.spectralMonotone.toAdditiveInput.toSummableAdditive.toSummableQuotient
  spacing := T.spacing
  spacing_pos := T.spacing_pos
  atSpacing := T.atSpacing
  ceilConst := T.ceilConst
  physCeil := T.physCeil
  anchor := T.anchor
  anchor_pos := T.anchor_pos
  anchor_le := T.anchor_le
  recursion := T.recursion

/-- The dyadic physical carrier identifies the actual block map on the
mode-one fusion trajectory. -/
theorem DyadicP2PhysicalMarginTransport.blockDefectPowerOnTrajectory
    (T : DyadicP2PhysicalMarginTransport) :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator T.coeffTail.toControlFamily modeOne)
      T.blockingStep.Φ
      T.spectralMonotone.toSandwichInput.data.toCrossMul.factor :=
  T.spectralMonotone.blockDefectPowerOnTrajectory

/-- The specialized handoff reaches the reviewed per-block persistence
carrier. -/
def DyadicP2PhysicalMarginTransport.toBlockPersistence
    (T : DyadicP2PhysicalMarginTransport) :
    RGGapPersistence.RGBlockPersistence :=
  T.toDefectMarginTransport.toBlockPersistence

/-- The positive accumulated fusion factor and the physical anchor give a
uniform lower bound at every dyadic scale. -/
theorem DyadicP2PhysicalMarginTransport.uniformFloor
    (T : DyadicP2PhysicalMarginTransport) (k : Nat) :
    T.toBlockPersistence.prodFloor <=
      Q'.divPos ((T.atSpacing k).floorRate)
        (T.spacing k) (T.spacing_pos k) :=
  T.toDefectMarginTransport.uniformFloor k

/-- Once the one honest physical recursion is supplied, the dyadic route has
a strictly positive physical continuum floor. -/
theorem DyadicP2PhysicalMarginTransport.continuumFloor_pos
    (T : DyadicP2PhysicalMarginTransport) :
    (0 : Q') <
      (RGGapPersistence.toScalingBand T.toBlockPersistence.toUniform).physGapMin :=
  T.toDefectMarginTransport.continuumFloor_pos

end YMGap.Continuum.P2DyadicPhysicalMarginTransport

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicPhysicalMarginTransport.DyadicP2PhysicalMarginTransport.toDefectMarginTransport
#print axioms YMGap.Continuum.P2DyadicPhysicalMarginTransport.DyadicP2PhysicalMarginTransport.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2DyadicPhysicalMarginTransport.DyadicP2PhysicalMarginTransport.toBlockPersistence
#print axioms YMGap.Continuum.P2DyadicPhysicalMarginTransport.DyadicP2PhysicalMarginTransport.uniformFloor
#print axioms YMGap.Continuum.P2DyadicPhysicalMarginTransport.DyadicP2PhysicalMarginTransport.continuumFloor_pos
