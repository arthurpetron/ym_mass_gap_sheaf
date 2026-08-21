/-
# Correlation decay for the adaptive completed physical BF4 transfer

The pointwise-data adaptive transfer is an actual rational-linear endomorphism
of the cutoff-removed completed physical carrier, preserves its actual vacuum
complement, and—given a constructively cofinal finite `1/16` certificate—is a
strict contraction there.  Its natural powers therefore have geometric
squared-norm decay.

This file combines that result with the already proved Cauchy--Schwarz theorem
for the same completed physical inner form.  Every squared matrix coefficient
of a propagated vacuum-orthogonal vector then decays geometrically against an
arbitrary test vector in the same completed carrier.  Concrete corollaries use
the literal rate `1/16` from the cofinal and local-gluing certificates.

The result remains conditional on the pointwise dense Cauchy data and a
cofinal finite certificate, and remains at fixed nome and fixed finite
half-volume.  It is not a thermodynamic, continuum, spectral, or Clay theorem.

## Axiom gate

Only the constructed adaptive powers, completed Cauchy--Schwarz,
completed-real monotonicity, and rational scaling are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy

/-- Multiplication in `RC` preserves order in its right argument when the
left factor is nonnegative. -/
private theorem RCmul_mono_nonnegative_left
    {factor left right : CReal.RC}
    (hfactor : CReal.RCnonneg factor)
    (hle : CReal.RCle left right) :
    CReal.RCle
      (CReal.RCmul factor left)
      (CReal.RCmul factor right) := by
  revert hfactor hle
  refine Quotient.inductionOn₃ factor left right ?_
  intro F L R hF hLR
  exact CReal.leEv_mul_nonneg_left hF hLR

/-! ## 1. Adaptive same-object matrix-coefficient decay -/

/-- Every squared matrix coefficient of a propagated vacuum-orthogonal vector
inherits the adaptive geometric norm decay.  The test vector is arbitrary in
the same actual completed physical carrier. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    (gap : CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half pointwise)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale ((gap.rate * gap.rate) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) := by
  let propagated :=
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
      pointwise n vector
  have hcs := centralPhysicalCutoffCompletedInner_cauchy_schwarz
    hw0 hw1 half propagated.1 test
  have hnorm :=
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay
      gap n vector
  have htestNonnegative :=
    centralPhysicalCutoffCompletedInner_self_nonneg
      hw0 hw1 half test
  have hmul := RCmul_mono_nonnegative_left htestNonnegative hnorm
  rw [CReal.RCmul_comm
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test),
      CReal.RCmul_comm
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)] at hmul
  exact CReal.RCle_trans hcs hmul

/-! ## 2. Concrete cofinal `1/16` correlation decay -/

/-- A cofinal finite sixteenth gives literal geometric same-object
matrix-coefficient decay for the actual adaptive completed transfer. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) := by
  simpa only [centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData]
    using
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay
        (centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
          hw0 hw1 half pointwise certificate)
        n vector test

/-- A cofinal local-gluing package gives the same literal `1/16`
matrix-coefficient decay through its centered-sixteenth projection. -/
theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_matrixCoefficientSq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
            pointwise n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) := by
  simpa only [
      centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData,
      centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData]
    using
      centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay
        (centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
          hw0 hw1 half pointwise certificate)
        n vector test

/-! ## Axiom audit -/

#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_matrixCoefficientSq_decay

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay
