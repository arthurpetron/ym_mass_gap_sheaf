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

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionPowerCertificate
import YMGap.Continuum.ExpProductFloor

namespace YMGap.Continuum.P2RetunedFusionDefectPower

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux
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

/-- Exact spectrum data identifying the physical map with a defected power at
every displayed, bulk mode. -/
structure SpectrumPinnedP2CrossMulDefectPowerData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (_blockingStep : BlockingStep (fusionSeparator F mode)) : Type where
  modeSupport : forall k, mode k <= 2 * F.N k
  modeBulk : forall k,
    q12 <= Q'.ofNat (c4 (mode k)) *
      ((1 : Q') - (F.control k).weff)
  factor : Nat -> Q'
  factorNonneg : forall k, (0 : Q') <= factor k
  factorLeOne : forall k, factor k <= (1 : Q')
  factorPowerCell : forall k,
    QDefectPowerCell (fusionModeQ F mode k)
      (fusionModeQ F mode (k + 1)) (factor k) (b + 1)

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
    (D : SpectrumPinnedP2CrossMulPowerData b F mode B) :
    SpectrumPinnedP2CrossMulDefectPowerData b F mode B where
  modeSupport := D.modeSupport
  modeBulk := D.modeBulk
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

end YMGap.Continuum.P2RetunedFusionDefectPower

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.QDefectPowerCell.ofCheck
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.qDefectPowerCellCheck_eq_true_iff
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.fusionDefectPower_of_cell
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2CrossMulDefectPowerData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2CrossMulDefectPowerData.ofExact
#print axioms YMGap.Continuum.P2RetunedFusionDefectPower.SpectrumPinnedP2SummableDefectPowerData.factorProductFloor
