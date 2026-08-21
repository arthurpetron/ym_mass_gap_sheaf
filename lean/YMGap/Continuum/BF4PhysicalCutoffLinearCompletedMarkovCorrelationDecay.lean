/-
# Same-object correlation decay for the completed physical BF4 transfer

The cutoff-limit physical BF4 completion already carries an actual positive
`RC`-valued inner form.  Its dense finite-linear approximants obey sharp
Cauchy--Schwarz at every representation cutoff.  This file transports that
inequality through the explicit outer pairing limit and the completion
quotient.

Combining the resulting completed Cauchy--Schwarz theorem with the conditional
strict contraction of the actual restricted transfer gives geometric decay
of every squared matrix coefficient on that same completed object.  Only the
propagated vector must lie in the vacuum complement; the test vector is an
arbitrary completed physical vector.

No strict-contraction certificate is inhabited here.  This theorem therefore
does not transport the separate finite or matched-cutoff `1/16` result, and it
does not assert a thermodynamic, continuum, spectral, or Clay mass gap.

## Axiom gate

Only explicit convergence, finite-stage Cauchy--Schwarz, quotient induction,
and completed-real monotonicity are used.  There is no classical choice,
noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

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

/-! ## 1. Cauchy--Schwarz on the actual completed physical carrier -/

/-- The outer pairing limit preserves the sharp dense Cauchy--Schwarz
inequality. -/
theorem physicalCauchyPairingLimit_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.leEv
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half X Y)
        (physicalCauchyPairingLimit hw0 hw1 half X Y))
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half X X)
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Y)
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Y))
    (CReal.convergesTo_mul_general
      (physicalCauchyPairingSeq_converges hw0 hw1 half X X)
      (physicalCauchyPairingSeq_converges hw0 hw1 half Y Y))
  intro n
  exact innerLimit_cauchy_schwarz
    hw0 hw1 half (X.seq n) (Y.seq n)

/-- Sharp Cauchy--Schwarz for the `RC`-valued inner form on the actual
cutoff-limit physical BF4 completion. -/
theorem centralPhysicalCutoffCompletedInner_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left right)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left right))
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left left)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half right right)) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact physicalCauchyPairingLimit_cauchy_schwarz hw0 hw1 half X Y

/-! ## 2. Squared matrix-coefficient decay on the same completed object -/

/-- Every squared matrix coefficient of a propagated vacuum-orthogonal
vector inherits the conditional geometric norm decay.  The test vector is an
arbitrary element of the same completed physical carrier. -/
theorem centralPhysicalCutoffCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    {pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M}
    (gap : CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M pairingInvariant)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
            M pairingInvariant n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
            M pairingInvariant n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale ((gap.rate * gap.rate) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) := by
  let propagated :=
    centralPhysicalCutoffCompletedVacuumComplementMarkovPower
      M pairingInvariant n vector
  have hcs := centralPhysicalCutoffCompletedInner_cauchy_schwarz
    hw0 hw1 half propagated.1 test
  have hnorm :=
    centralPhysicalCutoffCompletedVacuumComplementMarkovPower_norm_decay
      gap n vector
  have htestNonnegative :=
    centralPhysicalCutoffCompletedInner_self_nonneg
      hw0 hw1 half test
  have hmul := RCmul_mono_nonnegative_left
    htestNonnegative hnorm
  rw [CReal.RCmul_comm
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test),
      CReal.RCmul_comm
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)] at hmul
  exact CReal.RCle_trans hcs hmul

/-! ## Axiom audit -/

#print axioms physicalCauchyPairingLimit_cauchy_schwarz
#print axioms centralPhysicalCutoffCompletedInner_cauchy_schwarz
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
