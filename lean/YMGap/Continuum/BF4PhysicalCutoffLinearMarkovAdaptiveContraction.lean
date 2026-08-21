/-
# Iterated contraction of the adaptive completed physical BF4 transfer

The pointwise-data adaptive construction now gives an actual rational-linear
transfer on the actual completed physical vacuum complement.  A constructively
cofinal family of finite `1/16` estimates compiles into a strict same-object
contraction for that transfer.

This file makes the temporal consequence explicit.  It defines natural powers
of the adaptive restricted transfer and proves geometric squared-norm decay for
every power.  The theorem accepts the abstract adaptive strict-contraction
certificate, while its concrete corollaries use the cofinal `1/16` certificate
and the stronger local-gluing certificate.

The result remains at fixed nome and fixed finite half-volume.  It neither
constructs the pointwise dense Cauchy data or the cofinal finite certificate,
nor asserts a thermodynamic, continuum, spectral, or Clay mass gap.

## Axiom gate

Only the constructed adaptive transfer, completed-real order and rational
scaling, and induction on natural powers are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy

/-! ## 1. Natural powers of the adaptive restricted transfer -/

/-- Natural powers of the pointwise-data adaptive transfer on the actual
completed physical vacuum complement. -/
def centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    Nat ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
        pointwise
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector)

theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
      pointwise 0 vector = vector :=
  rfl

theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_succ
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
        pointwise (n + 1) vector =
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
        pointwise
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector) :=
  rfl

/-! ## 2. Geometric squared-norm decay -/

/-- Any adaptive same-object strict contraction iterates geometrically on every
completed vacuum-orthogonal vector. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    (gap : CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half pointwise)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1)
      (CReal.RCscale ((gap.rate * gap.rate) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  induction n with
  | zero =>
      rw [centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_zero,
        Q'.pow_zero, CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_succ]
      have hstep := gap.contraction
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise k vector)
      refine CReal.RCle_trans hstep ?_
      have hrateSqNonnegative : (0 : Q') <= gap.rate * gap.rate :=
        Q'.mul_nonneg gap.rate gap.rate
          gap.rate_nonnegative gap.rate_nonnegative
      have hscaled := CReal.RCscale_mono hrateSqNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-! ## 3. Concrete cofinal `1/16` corollaries -/

/-- The constructively cofinal finite `1/16` certificate gives geometric
completed squared-norm decay at the literal rate `(1/16)^2`. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1)
      (CReal.RCscale
        ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  simpa only [centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData]
    using
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay
        (centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
          hw0 hw1 half pointwise certificate)
        n vector

/-- The local-gluing package supplies the same concrete geometric decay through
its cofinal centered-sixteenth projection. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_norm_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
          pointwise n vector).1)
      (CReal.RCscale
        ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  simpa only [
      centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData,
      centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData]
    using
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay
        (centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
          hw0 hw1 half pointwise certificate)
        n vector

/-! ## Axiom audit -/

#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_norm_decay

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction
