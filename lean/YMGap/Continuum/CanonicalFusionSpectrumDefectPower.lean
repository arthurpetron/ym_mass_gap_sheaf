/-
Track 11.7-fusion / R3t -- arbitrary-positive-exponent defect transport.

The exact fusion-power law is too rigid on the first genuine finite cutoff
ladder.  The reviewed physical route therefore certifies

    coarse = fine^(b+1) * factor

and proves a positive accumulated floor from summable factor losses.  This
module lifts that route from the p=2 specialization to the scale-dependent
`pGamma k >= 2` canonical family.

The physical separator is still the selected displayed fusion mode.  Hence
`finePin` is definitional and the actual `BlockingStep.Phi` image is supplied
by `BlockingStep.step`.  The only adjacent-scale equality is the exact
integer `QDefectPowerCell`; the quotient compiler eliminates even that field
in favor of a half-to-one spectral sandwich.

This file compiles completed canonical controls and physical defect data.  It
does not construct the still-open analytic all-cutoff controls, spectral
sandwich, summable loss bound, or dimensionless-margin recursion.
-/

import YMGap.Continuum.CanonicalFusionSpectrumFamily
import YMGap.Continuum.P2RetunedFusionDefectPower

namespace YMGap.Continuum.CanonicalFusionSpectrumDefectPower

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.AFDeltaDecay
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionSpectrumBlockingIdentification
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RGTransport

/-! ## 1. Exact arbitrary-positive-exponent defect cells -/

/-- Lift one exact rational defect cell for an arbitrary canonical exponent
family to the constructive-real fusion spectrum. -/
theorem canonicalFusionDefectPower_of_cell
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {factor : Q'} {k : Nat}
    (C : QDefectPowerCell (canonicalFusionModeQ F mode k)
      (canonicalFusionModeQ F mode (k + 1)) factor (b + 1)) :
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (CReal.mul
        (CReal.cpow
          (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) (b + 1))
        (CReal.ofQ' factor)) := by
  have hlift :
      CReal.Equiv (CReal.ofQ' (canonicalFusionModeQ F mode k))
        (CReal.ofQ'
          (RGTransport.qpow
            (canonicalFusionModeQ F mode (k + 1)) (b + 1) * factor)) :=
    CReal.ofQ'_equiv_of_eqv C.eqv
  have hmul :
      CReal.Equiv
        (CReal.ofQ'
          (RGTransport.qpow
            (canonicalFusionModeQ F mode (k + 1)) (b + 1) * factor))
        (CReal.mul
          (CReal.cpow
            (CReal.ofQ' (canonicalFusionModeQ F mode (k + 1))) (b + 1))
          (CReal.ofQ' factor)) :=
    CReal.Equiv.trans
      (CRealAlg.ofQ'_mul
        (RGTransport.qpow
          (canonicalFusionModeQ F mode (k + 1)) (b + 1)) factor)
      (CReal.mul_congr_left
        (CReal.Equiv.symm
          (cpow_ofQ' (canonicalFusionModeQ F mode (k + 1)) (b + 1))))
  simpa only [fusionModeCReal, canonicalFusionModeQ] using
    (CReal.Equiv.trans hlift hmul)

/-- The selected mode is the physical gap edge of each displayed
`pGamma k` fusion row.  Bulk localization witnesses remain independent: a
running physical gap edge need not itself lie in the auxiliary bulk tail. -/
structure CanonicalPhysicalSeparatorMode
    (F : CanonicalBulkControlFamily) (mode : Nat -> Nat) : Type where
  nonvacuum : forall k, 1 <= mode k
  /-- Every positive truncated fusion power is projected back through the
  same two-input product and therefore has support at most `2*N`, independent
  of the exponent. -/
  support : forall k, mode k <= 2 * F.N k
  dominates : forall k s, 1 <= s -> s <= 2 * F.N k ->
    fusionEig (F.N k) (F.w k) (F.pGamma k) s
        ((F.control k).denomPos s) <=
      canonicalFusionModeQ F mode k

/-- Exact defect factors for a scale-dependent positive-exponent spectrum.
The actual map pin remains structural and is not repeated here. -/
structure CanonicalSpectrumCrossMulDefectPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  physicalMode : CanonicalPhysicalSeparatorMode F mode
  factor : Nat -> Q'
  factorNonneg : forall k, (0 : Q') <= factor k
  factorLeOne : forall k, factor k <= (1 : Q')
  factorPowerCell : forall k,
    QDefectPowerCell (canonicalFusionModeQ F mode k)
      (canonicalFusionModeQ F mode (k + 1)) (factor k) (b + 1)

/-- The exact cells and the physical blocking step identify the genuine map
on the spectrum-defined trajectory. -/
theorem CanonicalSpectrumCrossMulDefectPowerData.blockDefectPowerOnTrajectory
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumCrossMulDefectPowerData b F mode B) :
    IsBlockDefectPowerOnTrajectory b
      (canonicalFusionSeparator F mode) B.Φ D.factor := by
  intro k
  exact CReal.Equiv.trans
    (canonicalFusionSeparator_imagePin F mode B k)
    (by
      simpa only [canonicalFusionSeparator] using
        (canonicalFusionDefectPower_of_cell (D.factorPowerCell k)))

/-- Exact zero-defect power cells embed as factor-one defect cells. -/
def CanonicalSpectrumCrossMulDefectPowerData.ofExact
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (physicalMode : CanonicalPhysicalSeparatorMode F mode)
    (D : CanonicalSpectrumCrossMulPowerData b F mode B) :
    CanonicalSpectrumCrossMulDefectPowerData b F mode B where
  physicalMode := physicalMode
  factor := fun _ => 1
  factorNonneg := fun _ => by decide
  factorLeOne := fun _ => by decide
  factorPowerCell := fun k =>
    QDefectPowerCell.ofEqv
      (Q'.eqv_trans _ _ _ (D.fusionPowerCell k).eqv
        (Q'.eqv_symm
          (Q'.mul_one_eqv
            (RGTransport.qpow
              (canonicalFusionModeQ F mode (k + 1)) (b + 1)))))

/-! ## 2. Quotient compilation and the half-to-one spectral sandwich -/

/-- Preferred per-scale interface.  Division cancellation constructs the
canonical factor and its exact integer cell; physical work supplies only the
positive fine power and half-to-one coarse comparison. -/
structure CanonicalSpectrumQuotientDefectPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  physicalMode : CanonicalPhysicalSeparatorMode F mode
  coarseNonneg : forall k, (0 : Q') <= canonicalFusionModeQ F mode k
  finePowerPos : forall k,
    (0 : Q') < RGTransport.qpow
      (canonicalFusionModeQ F mode (k + 1)) (b + 1)
  coarseLeFinePower : forall k,
    canonicalFusionModeQ F mode k <=
      RGTransport.qpow (canonicalFusionModeQ F mode (k + 1)) (b + 1)
  halfFinePowerLeCoarse : forall k,
    HalfPow.half *
        RGTransport.qpow (canonicalFusionModeQ F mode (k + 1)) (b + 1) <=
      canonicalFusionModeQ F mode k

/-- The generic quotient compiler supplies the exact factors, range proofs,
and integer defect cells. -/
def CanonicalSpectrumQuotientDefectPowerData.toCrossMul
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumQuotientDefectPowerData b F mode B) :
    CanonicalSpectrumCrossMulDefectPowerData b F mode B where
  physicalMode := D.physicalMode
  factor := fun k => canonicalDefectFactor
    (canonicalFusionModeQ F mode k)
    (canonicalFusionModeQ F mode (k + 1)) (b + 1) (D.finePowerPos k)
  factorNonneg := fun k =>
    canonicalDefectFactor_nonneg (D.finePowerPos k) (D.coarseNonneg k)
  factorLeOne := fun k =>
    canonicalDefectFactor_le_one
      (D.finePowerPos k) (D.coarseLeFinePower k)
  factorPowerCell := fun k => canonicalDefectPowerCell
    (canonicalFusionModeQ F mode k)
    (canonicalFusionModeQ F mode (k + 1)) (b + 1) (D.finePowerPos k)

/-- The lower half of the spectral sandwich supplies the half-loss window. -/
theorem CanonicalSpectrumQuotientDefectPowerData.factorLossLeHalf
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumQuotientDefectPowerData b F mode B) (k : Nat) :
    (1 : Q') - D.toCrossMul.factor k <= HalfPow.half :=
  one_sub_le_half_of_half_le
    (half_le_canonicalDefectFactor
      (D.finePowerPos k) (D.halfFinePowerLeCoarse k))

/-- Quotient-compiled data identifies the actual physical map. -/
theorem CanonicalSpectrumQuotientDefectPowerData.blockDefectPowerOnTrajectory
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumQuotientDefectPowerData b F mode B) :
    IsBlockDefectPowerOnTrajectory b
      (canonicalFusionSeparator F mode) B.Φ D.toCrossMul.factor :=
  D.toCrossMul.blockDefectPowerOnTrajectory

/-! ## 3. Summable defects and a positive factor floor -/

/-- Summable exact factors for the arbitrary positive-exponent family. -/
structure CanonicalSpectrumSummableDefectPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  data : CanonicalSpectrumCrossMulDefectPowerData b F mode B
  lossLeHalf : forall k, (1 : Q') - data.factor k <= HalfPow.half
  lossBound : Q'
  lossSumLe : forall n,
    lossSum (fun k => (1 : Q') - data.factor k) n <= lossBound

/-- Preferred all-scale interface: a spectral sandwich and one cumulative
loss bound. -/
structure CanonicalSpectrumSummableQuotientDefectPowerData
    (b : Nat) (F : CanonicalBulkControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator F mode)) : Type where
  data : CanonicalSpectrumQuotientDefectPowerData b F mode B
  lossBound : Q'
  lossSumLe : forall n,
    lossSum (fun k => (1 : Q') - data.toCrossMul.factor k) n <= lossBound

/-- Compile the quotient form to the exact summable factor carrier. -/
def CanonicalSpectrumSummableQuotientDefectPowerData.toSummable
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B) :
    CanonicalSpectrumSummableDefectPowerData b F mode B where
  data := D.data.toCrossMul
  lossLeHalf := D.data.factorLossLeHalf
  lossBound := D.lossBound
  lossSumLe := D.lossSumLe

/-- Summable quotient data still identifies the genuine block map. -/
theorem CanonicalSpectrumSummableQuotientDefectPowerData.blockDefectPowerOnTrajectory
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B) :
    IsBlockDefectPowerOnTrajectory b
      (canonicalFusionSeparator F mode) B.Φ D.data.toCrossMul.factor :=
  D.data.blockDefectPowerOnTrajectory

/-- Summable losses construct a strictly positive accumulated factor floor. -/
def CanonicalSpectrumSummableDefectPowerData.factorProductFloor
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableDefectPowerData b F mode B) :
    Σ' (c : CReal) (eps : Q'),
      (0 : Q') < eps ∧ ExpPos.geRat c eps ∧ forall n,
        CReal.leRat c (RGGapPersistence.prodPrefix D.data.factor n) :=
  ExpProductFloor.sum_loss_to_productFloor_exp D.data.factor
    D.data.factorNonneg D.data.factorLeOne D.lossLeHalf
    D.lossBound D.lossSumLe

/-- Distill the constructive-real floor to the rational form used by physical
block persistence. -/
def CanonicalSpectrumSummableQuotientDefectPowerData.factorProductFloorRat
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B) :
    Σ' (eps : Q'), (0 : Q') < eps ∧ forall n,
      eps <= RGGapPersistence.prodPrefix D.data.toCrossMul.factor n := by
  let P := D.toSummable.factorProductFloor
  exact ⟨P.2.1, P.2.2.1, fun n =>
    AFDeltaDecay.le_of_geRat_leRat P.2.2.2.1 (P.2.2.2.2 n)⟩

/-- The rational accumulated factor floor. -/
def CanonicalSpectrumSummableQuotientDefectPowerData.factorFloor
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B) : Q' :=
  D.factorProductFloorRat.1

theorem CanonicalSpectrumSummableQuotientDefectPowerData.factorFloor_pos
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B) :
    (0 : Q') < D.factorFloor :=
  D.factorProductFloorRat.2.1

theorem CanonicalSpectrumSummableQuotientDefectPowerData.factorFloor_le
    {b : Nat} {F : CanonicalBulkControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (canonicalFusionSeparator F mode)}
    (D : CanonicalSpectrumSummableQuotientDefectPowerData b F mode B)
    (n : Nat) :
    D.factorFloor <= RGGapPersistence.prodPrefix D.data.toCrossMul.factor n :=
  D.factorProductFloorRat.2.2 n

/-! ## 4. Generic Bucket-1-to-Bucket-2 handoff -/

/-- Physical dimensionless-margin transport driven by the same generic
positive-exponent spectrum factors.  `recursion` remains the genuine Bucket-2
field. -/
structure CanonicalDefectMarginTransport (b : Nat) : Type where
  hb : 1 <= b
  family : CanonicalBulkControlFamily
  mode : Nat -> Nat
  blockingStep : BlockingStep (canonicalFusionSeparator family mode)
  spectral : CanonicalSpectrumSummableQuotientDefectPowerData
    b family mode blockingStep
  spacing : Nat -> Q'
  spacing_pos : forall k, (0 : Q') < spacing k
  atSpacing : Nat -> RegUniformClusterBound
  ceilConst : Q'
  physCeil : forall k,
    Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) <= ceilConst
  anchor : Q'
  anchor_pos : (0 : Q') < anchor
  anchor_le : anchor <=
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  recursion : forall k,
    spectral.data.toCrossMul.factor k *
        Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) <=
      Q'.divPos ((atSpacing (k + 1)).floorRate)
        (spacing (k + 1)) (spacing_pos (k + 1))

/-- Compile the arbitrary-positive-exponent spectrum and physical recursion
to the reviewed block-persistence carrier. -/
def CanonicalDefectMarginTransport.toBlockPersistence {b : Nat}
    (T : CanonicalDefectMarginTransport b) :
    RGGapPersistence.RGBlockPersistence where
  spacing := T.spacing
  spacing_pos := T.spacing_pos
  atSpacing := T.atSpacing
  ceilConst := T.ceilConst
  physCeil := T.physCeil
  rho := T.spectral.data.toCrossMul.factor
  rho_nonneg := T.spectral.data.toCrossMul.factorNonneg
  anchor := T.anchor
  anchor_pos := T.anchor_pos
  anchor_le := T.anchor_le
  recursion := T.recursion
  prodFloor := T.spectral.factorFloor * T.anchor
  prodFloor_pos := Q'.mul_pos T.spectral.factorFloor_pos T.anchor_pos
  prodFloor_le := fun k =>
    Q'.mul_le_mul_of_nonneg_right T.spectral.factorFloor
      (RGGapPersistence.prodPrefix T.spectral.data.toCrossMul.factor k)
      T.anchor (T.spectral.factorFloor_le k) (Q'.le_of_lt T.anchor_pos)

/-- The generic handoff yields a scale-uniform physical floor. -/
theorem CanonicalDefectMarginTransport.uniformFloor {b : Nat}
    (T : CanonicalDefectMarginTransport b) (k : Nat) :
    T.toBlockPersistence.prodFloor <=
      Q'.divPos ((T.atSpacing k).floorRate)
        (T.spacing k) (T.spacing_pos k) :=
  RGGapPersistence.blockPersistence_uniform_floor T.toBlockPersistence k

/-- The resulting continuum scaling floor is strictly positive. -/
theorem CanonicalDefectMarginTransport.continuumFloor_pos {b : Nat}
    (T : CanonicalDefectMarginTransport b) :
    (0 : Q') <
      (RGGapPersistence.toScalingBand T.toBlockPersistence.toUniform).physGapMin :=
  RGGapPersistence.physGapMin_pos_of_blockPersistence T.toBlockPersistence

/-! ## 5. The reviewed p=2 route is a literal specialization -/

/-- Every reviewed p=2 physical separator mode embeds in the generic
positive-exponent carrier without changing its spectrum. -/
def CanonicalPhysicalSeparatorMode.ofP2Retuned
    {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    (P : P2PhysicalSeparatorMode F mode) :
    CanonicalPhysicalSeparatorMode
      (CanonicalBulkControlFamily.ofP2Retuned F) mode where
  nonvacuum := P.nonvacuum
  support := P.support
  dominates := P.dominates

/-- The existing p=2 quotient data is definitionally an instance of the
generic defect compiler. -/
def CanonicalSpectrumQuotientDefectPowerData.ofP2Retuned
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2QuotientDefectPowerData b F mode B) :
    CanonicalSpectrumQuotientDefectPowerData b
      (CanonicalBulkControlFamily.ofP2Retuned F) mode B where
  physicalMode := CanonicalPhysicalSeparatorMode.ofP2Retuned D.physicalMode
  coarseNonneg := D.coarseNonneg
  finePowerPos := D.finePowerPos
  coarseLeFinePower := D.coarseLeFinePower
  halfFinePowerLeCoarse := D.halfFinePowerLeCoarse

end YMGap.Continuum.CanonicalFusionSpectrumDefectPower

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.canonicalFusionDefectPower_of_cell
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumCrossMulDefectPowerData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumQuotientDefectPowerData.toCrossMul
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumQuotientDefectPowerData.factorLossLeHalf
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumQuotientDefectPowerData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumSummableQuotientDefectPowerData.factorProductFloorRat
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalDefectMarginTransport.toBlockPersistence
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalDefectMarginTransport.uniformFloor
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalDefectMarginTransport.continuumFloor_pos
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalPhysicalSeparatorMode.ofP2Retuned
#print axioms YMGap.Continuum.CanonicalFusionSpectrumDefectPower.CanonicalSpectrumQuotientDefectPowerData.ofP2Retuned
