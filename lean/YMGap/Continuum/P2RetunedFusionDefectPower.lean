/-
Track 11.7-fusion / R2m -- defect-aware physical fusion-power dictionary.

The fixed-weight fence audit proves that exact zero-defect self-similarity is
too rigid even for the first non-vacuum cutoff pair.  The genuine four-
dimensional route is the summable-defect route already consumed by the
physical-margin recursion.  This module puts the spectrum/blocking-map side in
that exact form.

`QDefectPowerCell` certifies

    coarse = fine^n * factor

by one decidable integer cross product.  Generic soundness lifts it through
the rational embedding and constructive power.  On the spectrum-defined
trajectory, `BlockingStep.step` then identifies the actual `BlockingStep.Phi`
image with that defect power.  A summable family of factors is fed directly
to the existing exponential product-floor compiler.

Unlike the exact legacy dictionary, the defect route does not identify the
physical separator with an auxiliary bulk-localization mode.  It instead asks
directly that the selected non-vacuum mode dominate the displayed fusion
spectrum.  This distinction is essential along a running cutoff: the physical
gap edge can remain at mode one while the modes entering a bulk tail estimate
move outward.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionPowerCertificate
import YMGap.Continuum.ExpProductFloor
import YMGap.Continuum.AFDeltaDecay

namespace YMGap.Continuum.P2RetunedFusionDefectPower

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.FusionSpectrumBlockingIdentification
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.ProductFloor

local infix:50 " ≈ " => Q'.eqv

/-- Exact rational cell for a multiplicatively defected power law. -/
structure QDefectPowerCell (coarse fine factor : Q') (n : Nat) : Type where
  crossMul :
    coarse.num * (((RGTransport.qpow fine n) * factor).den : Int) =
      ((RGTransport.qpow fine n) * factor).num * (coarse.den : Int)

/-- Executable integer checker for a defect-power cell. -/
def qDefectPowerCellCheck (coarse fine factor : Q') (n : Nat) : Bool :=
  decide
    (coarse.num * (((RGTransport.qpow fine n) * factor).den : Int) =
      ((RGTransport.qpow fine n) * factor).num * (coarse.den : Int))

/-- Reflect a successful checker result into exact certificate data. -/
def QDefectPowerCell.ofCheck {coarse fine factor : Q'} {n : Nat}
    (h : qDefectPowerCellCheck coarse fine factor n = true) :
    QDefectPowerCell coarse fine factor n :=
  ⟨of_decide_eq_true h⟩

/-- A defect-power cell is exactly its rational equality. -/
theorem QDefectPowerCell.eqv {coarse fine factor : Q'} {n : Nat}
    (C : QDefectPowerCell coarse fine factor n) :
    coarse ≈ RGTransport.qpow fine n * factor :=
  C.crossMul

/-- Package an already-proved rational defect-power equality. -/
def QDefectPowerCell.ofEqv {coarse fine factor : Q'} {n : Nat}
    (h : coarse ≈ RGTransport.qpow fine n * factor) :
    QDefectPowerCell coarse fine factor n :=
  ⟨h⟩

/-- Kernel completeness of the executable checker. -/
theorem qDefectPowerCellCheck_eq_true_iff
    (coarse fine factor : Q') (n : Nat) :
    qDefectPowerCellCheck coarse fine factor n = true <->
      coarse ≈ RGTransport.qpow fine n * factor := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-! ## Quotient compiler: eliminate per-cell equality computation -/

/-- The canonical defect factor `coarse / fine^n`.  Positivity of the fine
power is the only guard needed to form the constructive rational quotient. -/
def canonicalDefectFactor (coarse fine : Q') (n : Nat)
    (hfinePower : (0 : Q') < RGTransport.qpow fine n) : Q' :=
  Q'.divPos coarse (RGTransport.qpow fine n) hfinePower

/-- Proof-about-computation compiler: the canonical quotient satisfies the
defect-power identity by the generic division cancellation theorem.  No large
cross product is evaluated at an individual scale. -/
def canonicalDefectPowerCell (coarse fine : Q') (n : Nat)
    (hfinePower : (0 : Q') < RGTransport.qpow fine n) :
    QDefectPowerCell coarse fine
      (canonicalDefectFactor coarse fine n hfinePower) n :=
  QDefectPowerCell.ofEqv
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.divPos_mul_eqv coarse (RGTransport.qpow fine n) hfinePower))
      (Q'.mul_comm_eqv
        (canonicalDefectFactor coarse fine n hfinePower)
        (RGTransport.qpow fine n)))

/-- Positivity/nonnegativity of the quotient factor is inherited from the
coarse eigenvalue. -/
theorem canonicalDefectFactor_nonneg {coarse fine : Q'} {n : Nat}
    (hfinePower : (0 : Q') < RGTransport.qpow fine n)
    (hcoarse : (0 : Q') <= coarse) :
    (0 : Q') <= canonicalDefectFactor coarse fine n hfinePower := by
  unfold canonicalDefectFactor Q'.divPos
  exact Q'.mul_nonneg _ _ hcoarse
    (Q'.le_of_lt (Q'.recipPos_pos _ hfinePower))

/-- The canonical factor is at most one exactly when the coarse eigenvalue is
bounded by the requested fine power. -/
theorem canonicalDefectFactor_le_one {coarse fine : Q'} {n : Nat}
    (hfinePower : (0 : Q') < RGTransport.qpow fine n)
    (hcoarseLe : coarse <= RGTransport.qpow fine n) :
    canonicalDefectFactor coarse fine n hfinePower <= (1 : Q') := by
  unfold canonicalDefectFactor
  apply Q'.divPos_le_of_le_mul coarse (RGTransport.qpow fine n) hfinePower
  exact Q'.le_trans' _ _ _ hcoarseLe
    (Q'.ge_of_eqv (Q'.one_mul_eqv (RGTransport.qpow fine n)))

/-- A half-power lower comparison gives the half-factor bound needed by the
product-floor loss window. -/
theorem half_le_canonicalDefectFactor {coarse fine : Q'} {n : Nat}
    (hfinePower : (0 : Q') < RGTransport.qpow fine n)
    (hhalf : HalfPow.half * RGTransport.qpow fine n <= coarse) :
    HalfPow.half <= canonicalDefectFactor coarse fine n hfinePower := by
  unfold canonicalDefectFactor
  exact Q'.le_divPos_of_mul_le coarse
    (RGTransport.qpow fine n) hfinePower hhalf

/-- Turn a half-factor lower bound into the half-loss upper bound used by the
product-floor engine. -/
theorem one_sub_le_half_of_half_le {factor : Q'}
    (hfactor : HalfPow.half <= factor) :
    (1 : Q') - factor <= HalfPow.half := by
  have hneg : -factor <= -HalfPow.half := Q'.neg_le_neg hfactor
  have hadd : (1 : Q') + (-factor) <= (1 : Q') + (-HalfPow.half) :=
    Q'.add_le_add_left (1 : Q') (-factor) (-HalfPow.half) hneg
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by decide))

/-- Lift one rational defect-power cell to constructive reals. -/
theorem fusionDefectPower_of_cell
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {factor : Q'} {k : Nat}
    (C : QDefectPowerCell (fusionModeQ F mode k)
      (fusionModeQ F mode (k + 1)) factor (b + 1)) :
    CReal.Equiv (fusionModeCReal (F.control k) (mode k))
      (CReal.mul
        (CReal.cpow
          (fusionModeCReal (F.control (k + 1)) (mode (k + 1))) (b + 1))
        (CReal.ofQ' factor)) := by
  have hlift :
      CReal.Equiv (CReal.ofQ' (fusionModeQ F mode k))
        (CReal.ofQ'
          (RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1) * factor)) :=
    CReal.ofQ'_equiv_of_eqv C.eqv
  have hmul :
      CReal.Equiv
        (CReal.ofQ'
          (RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1) * factor))
        (CReal.mul
          (CReal.cpow (CReal.ofQ' (fusionModeQ F mode (k + 1))) (b + 1))
          (CReal.ofQ' factor)) :=
    CReal.Equiv.trans
      (CRealAlg.ofQ'_mul
        (RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1)) factor)
      (CReal.mul_congr_left
        (CReal.Equiv.symm
          (cpow_ofQ' (fusionModeQ F mode (k + 1)) (b + 1))))
  simpa only [fusionModeCReal, fusionModeQ] using
    (CReal.Equiv.trans hlift hmul)

/-- The honest, defect-aware power law on the physical separator trajectory. -/
def IsBlockDefectPowerOnTrajectory (b : Nat) (s : Nat -> CReal)
    (Phi : CReal -> CReal) (factor : Nat -> Q') : Prop :=
  forall k, CReal.Equiv (Phi (s (k + 1)))
    (CReal.mul (CReal.cpow (s (k + 1)) (b + 1))
      (CReal.ofQ' (factor k)))

/-- The selected mode is the physical gap edge of the displayed p=2 fusion
row.  This is deliberately independent of the effective-bulk predicate used
to prove localization estimates: along a running cutoff the gap edge and a
bulk witness need not be the same representation label. -/
structure P2PhysicalSeparatorMode
    (F : P2RetunedControlFamily) (mode : Nat -> Nat) : Type where
  nonvacuum : forall k, 1 <= mode k
  support : forall k, mode k <= 2 * F.N k
  dominates : forall k s, 1 <= s -> s <= 2 * F.N k ->
    fusionEig (F.N k) (F.w k) 2 s ((F.control k).denomPos s) <=
      fusionModeQ F mode k

/-- Exact spectrum data identifying the physical map with a defected power at
every displayed physical separator. -/
structure SpectrumPinnedP2CrossMulDefectPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (fusionSeparator F mode)) : Type where
  physicalMode : P2PhysicalSeparatorMode F mode
  factor : Nat -> Q'
  factorNonneg : forall k, (0 : Q') <= factor k
  factorLeOne : forall k, factor k <= (1 : Q')
  factorPowerCell : forall k,
    QDefectPowerCell (fusionModeQ F mode k)
      (fusionModeQ F mode (k + 1)) (factor k) (b + 1)

/-- Quotient-compiled physical data.  The exact equality and all factor range
proofs are eliminated: the remaining per-scale content is the spectral
sandwich `half * fine^(b+1) <= coarse <= fine^(b+1)`. -/
structure SpectrumPinnedP2QuotientDefectPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (fusionSeparator F mode)) : Type where
  physicalMode : P2PhysicalSeparatorMode F mode
  coarseNonneg : forall k, (0 : Q') <= fusionModeQ F mode k
  finePowerPos : forall k,
    (0 : Q') < RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1)
  coarseLeFinePower : forall k,
    fusionModeQ F mode k <=
      RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1)
  halfFinePowerLeCoarse : forall k,
    HalfPow.half *
      RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1) <=
        fusionModeQ F mode k

/-- The canonical quotient compiler supplies every exact cell and factor
range proof from the spectral sandwich. -/
def SpectrumPinnedP2QuotientDefectPowerData.toCrossMul
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2QuotientDefectPowerData b F mode B) :
    SpectrumPinnedP2CrossMulDefectPowerData b F mode B where
  physicalMode := D.physicalMode
  factor := fun k => canonicalDefectFactor
    (fusionModeQ F mode k) (fusionModeQ F mode (k + 1)) (b + 1)
      (D.finePowerPos k)
  factorNonneg := fun k =>
    canonicalDefectFactor_nonneg (D.finePowerPos k) (D.coarseNonneg k)
  factorLeOne := fun k =>
    canonicalDefectFactor_le_one (D.finePowerPos k) (D.coarseLeFinePower k)
  factorPowerCell := fun k =>
    canonicalDefectPowerCell
      (fusionModeQ F mode k) (fusionModeQ F mode (k + 1)) (b + 1)
        (D.finePowerPos k)

/-- The quotient factor's loss is automatically at most one half. -/
theorem SpectrumPinnedP2QuotientDefectPowerData.factorLossLeHalf
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2QuotientDefectPowerData b F mode B) (k : Nat) :
    (1 : Q') - D.toCrossMul.factor k <= HalfPow.half :=
  one_sub_le_half_of_half_le
    (half_le_canonicalDefectFactor (D.finePowerPos k)
      (D.halfFinePowerLeCoarse k))

/-- The rational cells and `BlockingStep.step` identify the actual physical
map on the selected trajectory; no independent image pin remains. -/
theorem SpectrumPinnedP2CrossMulDefectPowerData.blockDefectPowerOnTrajectory
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2CrossMulDefectPowerData b F mode B) :
    IsBlockDefectPowerOnTrajectory b (fusionSeparator F mode) B.Φ D.factor := by
  intro k
  exact CReal.Equiv.trans (fusionSeparator_imagePin F mode B k)
    (by
      simpa only [fusionSeparator] using
        (fusionDefectPower_of_cell (D.factorPowerCell k)))

/-- The exact zero-defect cells embed with factor one. -/
def SpectrumPinnedP2CrossMulDefectPowerData.ofExact
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (physicalMode : P2PhysicalSeparatorMode F mode)
    (D : SpectrumPinnedP2CrossMulPowerData b F mode B) :
    SpectrumPinnedP2CrossMulDefectPowerData b F mode B where
  physicalMode := physicalMode
  factor := fun _ => 1
  factorNonneg := fun _ => by decide
  factorLeOne := fun _ => by decide
  factorPowerCell := fun k =>
    QDefectPowerCell.ofEqv
      (Q'.eqv_trans _ _ _ (D.fusionPowerCell k).eqv
        (Q'.eqv_symm
          (Q'.mul_one_eqv
            (RGTransport.qpow (fusionModeQ F mode (k + 1)) (b + 1)))))

/-- Summable physical defect factors.  The remaining work is now data with a
precise analytic meaning: prove that the losses of the map-identified factors
are uniformly summable. -/
structure SpectrumPinnedP2SummableDefectPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (fusionSeparator F mode)) : Type where
  data : SpectrumPinnedP2CrossMulDefectPowerData b F mode B
  lossLeHalf : forall k, (1 : Q') - data.factor k <= HalfPow.half
  lossBound : Q'
  lossSumLe : forall n,
    lossSum (fun k => (1 : Q') - data.factor k) n <= lossBound

/-- Preferred final input: only the all-scale spectral sandwich and the sum
of its canonical quotient losses remain. -/
structure SpectrumPinnedP2SummableQuotientDefectPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (fusionSeparator F mode)) : Type where
  data : SpectrumPinnedP2QuotientDefectPowerData b F mode B
  lossBound : Q'
  lossSumLe : forall n,
    lossSum (fun k => (1 : Q') - data.toCrossMul.factor k) n <= lossBound

/-- Compile the spectral sandwich and its single summability estimate into
the full exact defect-power data. -/
def SpectrumPinnedP2SummableQuotientDefectPowerData.toSummable
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) :
    SpectrumPinnedP2SummableDefectPowerData b F mode B where
  data := D.data.toCrossMul
  lossLeHalf := D.data.factorLossLeHalf
  lossBound := D.lossBound
  lossSumLe := D.lossSumLe

/-- The preferred quotient input identifies the actual block map. -/
theorem SpectrumPinnedP2SummableQuotientDefectPowerData.blockDefectPowerOnTrajectory
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) :
    IsBlockDefectPowerOnTrajectory b (fusionSeparator F mode) B.Φ
      D.data.toCrossMul.factor :=
  D.data.toCrossMul.blockDefectPowerOnTrajectory

/-- A summable family of physically identified fusion defects has a strictly
positive accumulated product floor, constructively and for arbitrary finite
loss bound. -/
def SpectrumPinnedP2SummableDefectPowerData.factorProductFloor
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableDefectPowerData b F mode B) :
    Σ' (c : CReal) (eps : Q'),
      (0 : Q') < eps ∧ ExpPos.geRat c eps
        ∧ forall n, CReal.leRat c
          (RGGapPersistence.prodPrefix D.data.factor n) :=
  ExpProductFloor.sum_loss_to_productFloor_exp D.data.factor
    D.data.factorNonneg D.data.factorLeOne D.lossLeHalf
    D.lossBound D.lossSumLe

/-- The quotient-form input inherits the same constructive-real product
floor. -/
def SpectrumPinnedP2SummableQuotientDefectPowerData.factorProductFloor
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) :
    Σ' (c : CReal) (eps : Q'),
      (0 : Q') < eps ∧ ExpPos.geRat c eps
        ∧ forall n, CReal.leRat c
          (RGGapPersistence.prodPrefix D.data.toCrossMul.factor n) :=
  D.toSummable.factorProductFloor

/-- Distill the constructive-real product floor to the rational form consumed
by `RGBlockPersistence`. -/
def SpectrumPinnedP2SummableQuotientDefectPowerData.factorProductFloorRat
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) :
    Σ' (eps : Q'), (0 : Q') < eps ∧ forall n,
      eps <= RGGapPersistence.prodPrefix D.data.toCrossMul.factor n := by
  let P := D.factorProductFloor
  exact ⟨P.2.1, P.2.2.1, fun n =>
    AFDeltaDecay.le_of_geRat_leRat P.2.2.2.1 (P.2.2.2.2 n)⟩

/-- The rational factor floor. -/
def SpectrumPinnedP2SummableQuotientDefectPowerData.factorFloor
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) : Q' :=
  D.factorProductFloorRat.1

theorem SpectrumPinnedP2SummableQuotientDefectPowerData.factorFloor_pos
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) :
    (0 : Q') < D.factorFloor :=
  D.factorProductFloorRat.2.1

theorem SpectrumPinnedP2SummableQuotientDefectPowerData.factorFloor_le
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B) (n : Nat) :
    D.factorFloor <=
      RGGapPersistence.prodPrefix D.data.toCrossMul.factor n :=
  D.factorProductFloorRat.2.2 n

/-! ## Handoff to the physical dimensionless-margin recursion -/

open YMGap.Continuum.RegularContinuumPipeline

/-- The exact Bucket-1-to-Bucket-2 handoff.  The spectrum and actual block map
are identified by `spectral`; the sole new physical estimate is `recursion`,
the dimensionless margin transport by the same certified factors. -/
structure SpectrumPinnedP2DefectMarginTransport (b : Nat) : Type where
  hb : 1 <= b
  family : P2RetunedControlFamily
  mode : Nat -> Nat
  blockingStep : BlockingStep (fusionSeparator family mode)
  spectral : SpectrumPinnedP2SummableQuotientDefectPowerData
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
  /-- **The genuine Bucket-2 field.**  The certified fusion/map contraction
  factor transports the dimensionless physical margin across one scale. -/
  recursion : forall k,
    spectral.data.toCrossMul.factor k *
        Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) <=
      Q'.divPos ((atSpacing (k + 1)).floorRate)
        (spacing (k + 1)) (spacing_pos (k + 1))

/-- Compile the fusion-spectrum map data and the one physical recursion into
the reviewed per-block persistence carrier. -/
def SpectrumPinnedP2DefectMarginTransport.toBlockPersistence {b : Nat}
    (T : SpectrumPinnedP2DefectMarginTransport b) :
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

/-- The handoff yields the uniform physical gap floor. -/
theorem SpectrumPinnedP2DefectMarginTransport.uniformFloor {b : Nat}
    (T : SpectrumPinnedP2DefectMarginTransport b) (k : Nat) :
    T.toBlockPersistence.prodFloor <=
      Q'.divPos ((T.atSpacing k).floorRate)
        (T.spacing k) (T.spacing_pos k) :=
  RGGapPersistence.blockPersistence_uniform_floor T.toBlockPersistence k

/-- The resulting physical continuum floor is strictly positive. -/
theorem SpectrumPinnedP2DefectMarginTransport.continuumFloor_pos {b : Nat}
    (T : SpectrumPinnedP2DefectMarginTransport b) :
    (0 : Q') <
      (RGGapPersistence.toScalingBand T.toBlockPersistence.toUniform).physGapMin :=
  RGGapPersistence.physGapMin_pos_of_blockPersistence T.toBlockPersistence

end YMGap.Continuum.P2RetunedFusionDefectPower

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.QDefectPowerCell.ofCheck
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.qDefectPowerCellCheck_eq_true_iff
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.canonicalDefectPowerCell
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.canonicalDefectFactor_nonneg
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.canonicalDefectFactor_le_one
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.half_le_canonicalDefectFactor
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.one_sub_le_half_of_half_le
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.fusionDefectPower_of_cell
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2CrossMulDefectPowerData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2QuotientDefectPowerData.toCrossMul
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2QuotientDefectPowerData.factorLossLeHalf
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableQuotientDefectPowerData.toSummable
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableQuotientDefectPowerData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2CrossMulDefectPowerData.ofExact
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableDefectPowerData.factorProductFloor
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableQuotientDefectPowerData.factorProductFloorRat
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableQuotientDefectPowerData.factorFloor_pos
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2DefectMarginTransport.toBlockPersistence
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2DefectMarginTransport.uniformFloor
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2DefectMarginTransport.continuumFloor_pos
