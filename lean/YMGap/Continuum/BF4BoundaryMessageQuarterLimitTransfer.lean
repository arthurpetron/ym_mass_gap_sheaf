/-
# Effective cutoff removal for boundary-message quarter contraction

The finite boundary-message certificate proves an exact rational inequality

  outputDistance j <= (1/4) * inputDistance j

at every regulator `j`.  Passing this statement to a continuum object is not
automatic constructively: bounded sequences need not come with computable
limits.  This file records the missing data honestly.  Both distance streams
carry `ModCauchyEv` moduli, their limits are constructed from those same
streams, and scalar multiplication by a nonnegative rational at most one is
proved sequentially continuous.

The resulting theorem is a general finite-to-limit principle specialized by
an adapter to `UniformBoundaryMessageQuarterCertificate`.  It uses neither
compactness nor subsequence choice.  In particular, numerical sampling alone
cannot inhabit the Cauchy-modulus fields or the uniform finite certificate.

## Axiom gate

All regulator data are Type-level witnesses.  The only limit relation used is
the constructive eventual order on `CReal`.
-/

import YMGap.Constructive.CRealCompleteCauchy
import YMGap.Constructive.CRealMul
import YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh

namespace YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. General constructive limit lemmas -/

/-- Pointwise order between two constructively convergent `CReal` streams
passes to their limits in the transitive eventual order.  The proof uses the
same late regulator for both streams and splits the requested tolerance in
half. -/
theorem leEv_of_convergesTo_approx_le_convergesTo
    {left right : Nat -> CReal} {leftLimit rightLimit : CReal}
    (leftConverges : CReal.ConvergesTo left leftLimit)
    (rightConverges : CReal.ConvergesTo right rightLimit)
    (pointwise : forall stage approximation : Nat,
      (left stage).approx approximation <=
        (right stage).approx approximation) :
    CReal.leEv leftLimit rightLimit := by
  intro epsilon hepsilon
  let halfEpsilon : Q' := HalfPow.half * epsilon
  have halfEpsilon_pos : (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨leftStage, leftAfter⟩ :=
    leftConverges halfEpsilon halfEpsilon_pos
  obtain ⟨rightStage, rightAfter⟩ :=
    rightConverges halfEpsilon halfEpsilon_pos
  let stage : Nat := max leftStage rightStage
  obtain ⟨leftApproximation, leftClose⟩ :=
    leftAfter stage (Nat.le_max_left _ _)
  obtain ⟨rightApproximation, rightClose⟩ :=
    rightAfter stage (Nat.le_max_right _ _)
  refine ⟨max leftApproximation rightApproximation, fun approximation happroximation => ?_⟩
  have hleft : leftApproximation <= approximation :=
    Nat.le_trans (Nat.le_max_left _ _) happroximation
  have hright : rightApproximation <= approximation :=
    Nat.le_trans (Nat.le_max_right _ _) happroximation
  obtain ⟨_, limitLeft_le⟩ := leftClose approximation hleft
  obtain ⟨right_le_limit, _⟩ := rightClose approximation hright
  have firstStep :
      leftLimit.approx approximation <=
        (right stage).approx approximation + halfEpsilon :=
    Q'.le_trans' _ _ _ limitLeft_le
      (Q'.add_le_add_right _ _ halfEpsilon
        (pointwise stage approximation))
  have secondStep :
      leftLimit.approx approximation <=
        (rightLimit.approx approximation + halfEpsilon) + halfEpsilon :=
    Q'.le_trans' _ _ _ firstStep
      (Q'.add_le_add_right _ _ halfEpsilon right_le_limit)
  refine Q'.le_trans' _ _ _ secondStep (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      (rightLimit.approx approximation) halfEpsilon halfEpsilon) ?_
  exact Q'.add_eqv_congr_left
    (rightLimit.approx approximation)
    (halfEpsilon + halfEpsilon) epsilon
    (ExpNeg.two_halves epsilon)

/-- Multiplication by a nonnegative rational `scale <= 1` preserves
constructive convergence without any global boundedness hypothesis. -/
theorem convergesTo_ofQ'_scalar_mul
    (scale : Q')
    (scale_nonnegative : (0 : Q') <= scale)
    (scale_le_one : scale <= (1 : Q'))
    {values : Nat -> Q'} {limit : CReal}
    (converges :
      CReal.ConvergesTo (fun stage => CReal.ofQ' (values stage)) limit) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ' (scale * values stage))
      (CReal.mul (CReal.ofQ' scale) limit) := by
  intro epsilon hepsilon
  obtain ⟨stage, afterStage⟩ := converges epsilon hepsilon
  refine ⟨stage, fun index hindex => ?_⟩
  obtain ⟨approximation, close⟩ := afterStage index hindex
  refine ⟨approximation, fun n hn => ?_⟩
  obtain ⟨value_le_limit, limit_le_value⟩ := close n hn
  have scale_epsilon_le : scale * epsilon <= epsilon := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        scale 1 epsilon scale_le_one (Q'.le_of_lt hepsilon)) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv epsilon)
  have scale_bound : forall a b : Q',
      a <= b + epsilon -> scale * a <= scale * b + epsilon := by
    intro a b hab
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        a (b + epsilon) scale hab scale_nonnegative) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv scale b epsilon)) ?_
    exact Q'.add_le_add_left (scale * b)
      (scale * epsilon) epsilon scale_epsilon_le
  change
    scale * values index <= scale * limit.approx n + epsilon /\
      scale * limit.approx n <= scale * values index + epsilon
  exact ⟨scale_bound _ _ value_le_limit,
    scale_bound _ _ limit_le_value⟩

/-! ## 2. Exact rational streams with effective limits -/

/-- Embed an exact rational stream into constructive reals without changing
any of its finite values. -/
def rationalStream (values : Nat -> Q') : Nat -> CReal :=
  fun stage => CReal.ofQ' (values stage)

/-- The proof-carrying data needed to remove a cutoff from a termwise quarter
contraction.  Mere boundedness or sampled convergence is deliberately absent:
the two effective Cauchy moduli are explicit fields. -/
structure QuarterContractionLimitData
    (inputDistance outputDistance : Nat -> Q') : Type 1 where
  finite_contraction : forall stage : Nat,
    outputDistance stage <= quarterRate * inputDistance stage
  inputCauchy : CReal.ModCauchyEv (rationalStream inputDistance)
  outputCauchy : CReal.ModCauchyEv (rationalStream outputDistance)

namespace QuarterContractionLimitData

/-- The continuum input distance constructed from the exact finite input
stream and its supplied effective modulus. -/
def inputLimit
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) : CReal :=
  CReal.completeLimitCauchy
    (rationalStream inputDistance) data.inputCauchy

/-- The continuum output distance constructed from the exact finite output
stream and its supplied effective modulus. -/
def outputLimit
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) : CReal :=
  CReal.completeLimitCauchy
    (rationalStream outputDistance) data.outputCauchy

theorem input_converges
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) :
    CReal.ConvergesTo
      (rationalStream inputDistance) data.inputLimit :=
  CReal.convergesTo_completeLimitCauchy
    (rationalStream inputDistance) data.inputCauchy

theorem output_converges
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) :
    CReal.ConvergesTo
      (rationalStream outputDistance) data.outputLimit :=
  CReal.convergesTo_completeLimitCauchy
    (rationalStream outputDistance) data.outputCauchy

/-- The scaled exact input stream converges to one quarter times the limit of
the same unscaled input stream.  This is the explicit same-object scaling pin. -/
theorem scaled_input_converges
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) :
    CReal.ConvergesTo
      (rationalStream (fun stage => quarterRate * inputDistance stage))
      (CReal.mul (CReal.ofQ' quarterRate) data.inputLimit) := by
  exact convergesTo_ofQ'_scalar_mul
    quarterRate (by decide) (by decide) data.input_converges

/-- **Effective finite-to-limit quarter contraction.**  The exact finite
inequality survives in the constructive limit because both limits are built
from the same streams appearing in the finite certificate. -/
theorem limit_contraction
    {inputDistance outputDistance : Nat -> Q'}
    (data : QuarterContractionLimitData inputDistance outputDistance) :
    CReal.leEv data.outputLimit
      (CReal.mul (CReal.ofQ' quarterRate) data.inputLimit) := by
  apply leEv_of_convergesTo_approx_le_convergesTo
    data.output_converges data.scaled_input_converges
  intro stage approximation
  exact data.finite_contraction stage

end QuarterContractionLimitData

/-! ## 3. Adapter from uniform finite boundary-message refresh data -/

/-- Input `L1` distance at one cutoff. -/
def boundaryInputDistance
    {Source : Nat -> Type}
    (sources : forall stage, List (Source stage))
    (left right : forall stage, Source stage -> Q')
    (stage : Nat) : Q' :=
  finiteL1Distance (sources stage) (left stage) (right stage)

/-- Output `L1` distance after the exact terminal-dependent refresh at one
cutoff. -/
def boundaryOutputDistance
    {Source Target : Nat -> Type}
    {kernel : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Nat Source Target kernel sources targets)
    (terminal : forall stage, Target stage -> Q')
    (terminal_pos : forall stage target,
      target ∈ targets stage -> (0 : Q') < terminal stage target)
    (denominator_pos : forall stage source,
      (0 : Q') < terminalWeightedDenominator
        (targets stage) (kernel stage) (terminal stage) source)
    (left right : forall stage, Source stage -> Q')
    (stage : Nat) : Q' :=
  let refresh := certificate.refreshAt stage (terminal stage)
    (terminal_pos stage) (denominator_pos stage)
  finiteL1Distance (targets stage)
    (finiteKernelPushforward (sources stage) (left stage) refresh.kernel)
    (finiteKernelPushforward (sources stage) (right stage) refresh.kernel)

/-- A regulator-indexed physical boundary-message family together with the
effective data required for cutoff removal.  The finite quarter certificate
and the Cauchy moduli remain separate obligations. -/
structure UniformBoundaryMessageQuarterLimitInputs
    (Source Target : Nat -> Type)
    (kernel : forall stage, Source stage -> Target stage -> Q')
    (sources : forall stage, List (Source stage))
    (targets : forall stage, List (Target stage))
    (certificate :
      UniformBoundaryMessageQuarterCertificate
        Nat Source Target kernel sources targets) : Type 1 where
  terminal : forall stage, Target stage -> Q'
  terminal_pos : forall stage target,
    target ∈ targets stage -> (0 : Q') < terminal stage target
  denominator_pos : forall stage source,
    (0 : Q') < terminalWeightedDenominator
      (targets stage) (kernel stage) (terminal stage) source
  left : forall stage, Source stage -> Q'
  right : forall stage, Source stage -> Q'
  equalMass : forall stage,
    finiteMass (sources stage) (left stage) ≈
      finiteMass (sources stage) (right stage)
  inputCauchy : CReal.ModCauchyEv
    (rationalStream (boundaryInputDistance sources left right))
  outputCauchy : CReal.ModCauchyEv
    (rationalStream
      (boundaryOutputDistance certificate terminal terminal_pos
        denominator_pos left right))

namespace UniformBoundaryMessageQuarterLimitInputs

/-- Package the actual finite boundary distances and their effective moduli
into the general cutoff-removal theorem. -/
def toQuarterContractionLimitData
    {Source Target : Nat -> Type}
    {kernel : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    {certificate :
      UniformBoundaryMessageQuarterCertificate
        Nat Source Target kernel sources targets}
    (inputs :
      UniformBoundaryMessageQuarterLimitInputs
        Source Target kernel sources targets certificate) :
    QuarterContractionLimitData
      (boundaryInputDistance sources inputs.left inputs.right)
      (boundaryOutputDistance certificate inputs.terminal
        inputs.terminal_pos inputs.denominator_pos
        inputs.left inputs.right) where
  finite_contraction := by
    intro stage
    exact certificate.refreshAt_l1_quarter_contraction
      stage (inputs.terminal stage) (inputs.terminal_pos stage)
      (inputs.denominator_pos stage)
      (inputs.left stage) (inputs.right stage)
      (inputs.equalMass stage)
  inputCauchy := inputs.inputCauchy
  outputCauchy := inputs.outputCauchy

/-- The exact finite boundary-message contraction survives cutoff removal
under the explicitly supplied effective moduli. -/
theorem continuum_l1_quarter_contraction
    {Source Target : Nat -> Type}
    {kernel : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    {certificate :
      UniformBoundaryMessageQuarterCertificate
        Nat Source Target kernel sources targets}
    (inputs :
      UniformBoundaryMessageQuarterLimitInputs
        Source Target kernel sources targets certificate) :
    let data := inputs.toQuarterContractionLimitData
    CReal.leEv data.outputLimit
      (CReal.mul (CReal.ofQ' quarterRate) data.inputLimit) := by
  dsimp only
  exact inputs.toQuarterContractionLimitData.limit_contraction

end UniformBoundaryMessageQuarterLimitInputs

end YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer

#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.leEv_of_convergesTo_approx_le_convergesTo
#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.convergesTo_ofQ'_scalar_mul
#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.QuarterContractionLimitData.scaled_input_converges
#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.QuarterContractionLimitData.limit_contraction
#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.UniformBoundaryMessageQuarterLimitInputs.toQuarterContractionLimitData
#print axioms YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer.UniformBoundaryMessageQuarterLimitInputs.continuum_l1_quarter_contraction
