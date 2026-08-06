/-
Track 11.7-fusion / R2p -- additive-gap compiler for physical fusion defects.

The quotient factor is exact but analytically inconvenient:

    factor = coarse / fine^(b+1).

This module removes the division from the remaining summability estimate.  If
the fine power is at least one half, then

    1 - factor
      = (fine^(b+1) - coarse) / fine^(b+1)
      <= 2 * (fine^(b+1) - coarse).

Thus a summable additive power-gap envelope compiles to the quotient-loss
budget already consumed by the constructive product-floor and physical-margin
transport.  The proof uses generic positive-division cancellation; no large
per-scale quotient is evaluated.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionPhysicalMode

namespace YMGap.Continuum.P2RetunedFusionAdditiveGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.ProductFloor

/-- Multiplying by two cancels the rational half, without normalization or a
field tactic. -/
theorem two_mul_mul_half_eqv (x : Q') :
    ((Q'.ofNat 2 * x) * HalfPow.half).eqv x := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ HalfPow.half) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half (Q'.ofNat 2) x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ x
      (by decide : (HalfPow.half * Q'.ofNat 2).eqv (1 : Q'))) ?_
  exact Q'.one_mul_eqv x

/-- **Division-free quotient-loss bound.**  A half-floor on the fine power
turns its additive mismatch into a factor-loss estimate. -/
theorem canonicalDefectFactor_loss_le_twice_powerGap
    {coarse finePower : Q'}
    (hfinePower : (0 : Q') < finePower)
    (hcoarseLe : coarse <= finePower)
    (hhalf : HalfPow.half <= finePower) :
    (1 : Q') - Q'.divPos coarse finePower hfinePower <=
      Q'.ofNat 2 * (finePower - coarse) := by
  let gap := finePower - coarse
  have hgap0 : (0 : Q') <= gap := Q'.sub_nonneg_of_le hcoarseLe
  have htwoGap0 : (0 : Q') <= Q'.ofNat 2 * gap :=
    Q'.mul_nonneg _ _ (by decide) hgap0
  have hscaled :
      (Q'.ofNat 2 * gap) * HalfPow.half <=
        (Q'.ofNat 2 * gap) * finePower :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hhalf htwoGap0
  have hcross : gap <= (Q'.ofNat 2 * gap) * finePower :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (two_mul_mul_half_eqv gap)))
      hscaled
  have hdiv : Q'.divPos gap finePower hfinePower <= Q'.ofNat 2 * gap :=
    Q'.divPos_le_of_le_mul gap finePower hfinePower hcross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (HeatKernelRGStep.one_sub_divPos_eqv coarse finePower hfinePower)) hdiv

/-- Termwise monotonicity of the finite loss sum. -/
theorem lossSum_le_termwise {f g : Nat -> Q'} (h : forall k, f k <= g k) :
    forall n, lossSum f n <= lossSum g n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show lossSum f n + f n <= lossSum g n + g n
      exact Q'.add_le_add (lossSum_le_termwise h n) (h n)

/-- Preferred analytic input after quotient elimination.  The all-scale work
is now an additive mismatch envelope and its finite-sum bound. -/
structure SpectrumPinnedP2SummableAdditiveGapData
    (b : Nat) (F : P2RetunedControlFamily) (mode : Nat -> Nat)
    (B : BlockingStep (fusionSeparator F mode)) : Type where
  data : SpectrumPinnedP2QuotientDefectPowerData b F mode B
  finePowerHalf : forall k,
    HalfPow.half <= qpow (fusionModeQ F mode (k + 1)) (b + 1)
  envelope : Nat -> Q'
  powerGapLe : forall k,
    qpow (fusionModeQ F mode (k + 1)) (b + 1) -
        fusionModeQ F mode k <= envelope k
  lossBound : Q'
  envelopeSumLe : forall n,
    lossSum (fun k => Q'.ofNat 2 * envelope k) n <= lossBound

/-- The quotient loss is bounded pointwise by twice the supplied additive
power-gap envelope. -/
theorem SpectrumPinnedP2SummableAdditiveGapData.factorLossLeEnvelope
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableAdditiveGapData b F mode B) (k : Nat) :
    (1 : Q') - D.data.toCrossMul.factor k <=
      Q'.ofNat 2 * D.envelope k := by
  let coarse := fusionModeQ F mode k
  let finePower := qpow (fusionModeQ F mode (k + 1)) (b + 1)
  have hquot :
      (1 : Q') - Q'.divPos coarse finePower (D.data.finePowerPos k) <=
        Q'.ofNat 2 * (finePower - coarse) :=
    canonicalDefectFactor_loss_le_twice_powerGap
      (D.data.finePowerPos k) (D.data.coarseLeFinePower k)
      (D.finePowerHalf k)
  have hscale :
      Q'.ofNat 2 * (finePower - coarse) <= Q'.ofNat 2 * D.envelope k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (D.powerGapLe k) (by decide)
  exact Q'.le_trans' _ _ _ hquot hscale

/-- Compile an additive mismatch envelope into the existing summable quotient
carrier, and hence into the physical map/product-floor pipeline. -/
def SpectrumPinnedP2SummableAdditiveGapData.toSummableQuotient
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableAdditiveGapData b F mode B) :
    SpectrumPinnedP2SummableQuotientDefectPowerData b F mode B where
  data := D.data
  lossBound := D.lossBound
  lossSumLe := fun n =>
    Q'.le_trans' _ _ _
      (lossSum_le_termwise D.factorLossLeEnvelope n) (D.envelopeSumLe n)

/-- The additive-gap input identifies the genuine `BlockingStep.Phi` image on
the physical separator trajectory. -/
theorem SpectrumPinnedP2SummableAdditiveGapData.blockDefectPowerOnTrajectory
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableAdditiveGapData b F mode B) :
    IsBlockDefectPowerOnTrajectory b (fusionSeparator F mode) B.Φ
      D.data.toCrossMul.factor :=
  D.toSummableQuotient.blockDefectPowerOnTrajectory

/-- The additive-gap input inherits the strictly positive factor floor. -/
def SpectrumPinnedP2SummableAdditiveGapData.factorProductFloorRat
    {b : Nat} {F : P2RetunedControlFamily} {mode : Nat -> Nat}
    {B : BlockingStep (fusionSeparator F mode)}
    (D : SpectrumPinnedP2SummableAdditiveGapData b F mode B) :
    Σ' (eps : Q'), (0 : Q') < eps ∧ forall n,
      eps <= RGGapPersistence.prodPrefix D.data.toCrossMul.factor n :=
  D.toSummableQuotient.factorProductFloorRat

end YMGap.Continuum.P2RetunedFusionAdditiveGap

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.two_mul_mul_half_eqv
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.canonicalDefectFactor_loss_le_twice_powerGap
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.lossSum_le_termwise
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.SpectrumPinnedP2SummableAdditiveGapData.factorLossLeEnvelope
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.SpectrumPinnedP2SummableAdditiveGapData.toSummableQuotient
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.SpectrumPinnedP2SummableAdditiveGapData.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2RetunedFusionAdditiveGap.SpectrumPinnedP2SummableAdditiveGapData.factorProductFloorRat
