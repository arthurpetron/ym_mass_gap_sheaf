/-
# Division-free tail criteria for boundary-message relative error

The finite-prefix certificate leaves one infinite analytic obligation: the
relative error must be antitone after a threshold.  When that error is a
positive-denominator ratio `numerator / denominator`, it is enough to prove
the division-free cross-product inequality

  numerator (k+1) * denominator k
    <= numerator k * denominator (k+1).

This file turns that inequality into the exact `QuarterErrorPrefixTail`
consumed by the uniform rank-one quarter theorem.  The cross products are a
natural target for exact symbolic algebra, interval arithmetic, or generated
polynomial certificates; only Lean's checked implication is trusted.

No assertion here supplies the inequality for the physical BF4 kernel.
-/

import YMGap.Continuum.FusionMarginMono
import YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

namespace YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter
open YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

/-! ## 1. A checked quotient tail from division-free cross products -/

/-- The positive-denominator rational relative-error ratio. -/
def relativeErrorRatio
    (numerator denominator : Nat -> Q')
    (denominator_pos : forall stage, (0 : Q') < denominator stage)
    (stage : Nat) : Q' :=
  Q'.divPos (numerator stage) (denominator stage) (denominator_pos stage)

/-- Finite prefix data plus a division-free cross-product theorem for the
infinite tail of a relative-error ratio. -/
structure CrossProductQuarterErrorTail
    (numerator denominator : Nat -> Q') : Type where
  threshold : Nat
  denominator_pos : forall stage, (0 : Q') < denominator stage
  prefix_bound : forall stage : Nat, stage < threshold ->
    relativeErrorRatio numerator denominator denominator_pos stage <=
      relativeRankOneTolerance
  threshold_bound :
    relativeErrorRatio numerator denominator denominator_pos threshold <=
      relativeRankOneTolerance
  tail_cross : forall stage : Nat, threshold <= stage ->
    numerator (stage + 1) * denominator stage <=
      numerator stage * denominator (stage + 1)

namespace CrossProductQuarterErrorTail

/-- Cross-product monotonicity implies monotonicity of the positive quotient. -/
theorem tail_step
    {numerator denominator : Nat -> Q'}
    (certificate : CrossProductQuarterErrorTail numerator denominator)
    (stage : Nat) (hstage : certificate.threshold <= stage) :
    relativeErrorRatio numerator denominator certificate.denominator_pos
        (stage + 1) <=
      relativeErrorRatio numerator denominator certificate.denominator_pos
        stage := by
  exact YMGap.Continuum.FusionMarginMono.divPos_le_divPos_of_cross
    (numerator (stage + 1)) (denominator (stage + 1))
    (numerator stage) (denominator stage)
    (certificate.denominator_pos (stage + 1))
    (certificate.denominator_pos stage)
    (certificate.tail_cross stage hstage)

/-- Package the finite quotient checks and cross-product tail as the generic
all-regulator quarter-error budget. -/
def toQuarterErrorPrefixTail
    {numerator denominator : Nat -> Q'}
    (certificate : CrossProductQuarterErrorTail numerator denominator) :
    QuarterErrorPrefixTail
      (relativeErrorRatio numerator denominator certificate.denominator_pos) where
  threshold := certificate.threshold
  prefix_bound := certificate.prefix_bound
  threshold_bound := certificate.threshold_bound
  tail_step := certificate.tail_step

/-- Every quotient error is at most `1/16`. -/
theorem bound_all
    {numerator denominator : Nat -> Q'}
    (certificate : CrossProductQuarterErrorTail numerator denominator)
    (stage : Nat) :
    relativeErrorRatio numerator denominator certificate.denominator_pos stage <=
      relativeRankOneTolerance :=
  certificate.toQuarterErrorPrefixTail.bound_all stage

end CrossProductQuarterErrorTail

/-! ## 2. Adapter to the uniform boundary-message certificate -/

/-- A physical rank-one enclosure whose scalar relative error is a checked
positive quotient with a division-free antitone tail certificate. -/
structure CrossProductRelativeRankOneQuarterWitness
    (Source Target : Nat -> Type)
    (physical : forall stage, Source stage -> Target stage -> Q')
    (sources : forall stage, List (Source stage))
    (targets : forall stage, List (Target stage)) : Type where
  sourceProfile : forall stage, Source stage -> Q'
  targetProfile : forall stage, Target stage -> Q'
  sourceProfile_pos : forall stage source,
    source ∈ sources stage -> (0 : Q') < sourceProfile stage source
  targetProfile_pos : forall stage target,
    target ∈ targets stage -> (0 : Q') < targetProfile stage target
  numerator : Nat -> Q'
  denominator : Nat -> Q'
  errorTail : CrossProductQuarterErrorTail numerator denominator
  relative_error : forall stage source,
    source ∈ sources stage -> forall target,
    target ∈ targets stage ->
      Q'.abs
          (physical stage source target +
            -(sourceProfile stage source * targetProfile stage target)) <=
        relativeErrorRatio numerator denominator errorTail.denominator_pos stage *
          (sourceProfile stage source * targetProfile stage target)
  reference : forall stage, Source stage
  reference_mem : forall stage, reference stage ∈ sources stage

namespace CrossProductRelativeRankOneQuarterWitness

/-- The cross-product tail witness supplies the existing prefix/tail rank-one
witness without changing the physical kernel or profiles. -/
def toPrefixTailRelativeRankOneQuarterWitness
    {Source Target : Nat -> Type}
    {physical : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (witness :
      CrossProductRelativeRankOneQuarterWitness
        Source Target physical sources targets) :
    PrefixTailRelativeRankOneQuarterWitness
      Source Target physical sources targets where
  sourceProfile := witness.sourceProfile
  targetProfile := witness.targetProfile
  sourceProfile_pos := witness.sourceProfile_pos
  targetProfile_pos := witness.targetProfile_pos
  error := relativeErrorRatio witness.numerator witness.denominator
    witness.errorTail.denominator_pos
  errorBudget := witness.errorTail.toQuarterErrorPrefixTail
  relative_error := witness.relative_error
  reference := witness.reference
  reference_mem := witness.reference_mem

/-- The complete terminal-independent quarter certificate obtained from a
finite quotient prefix and division-free analytic cross-product tail. -/
def toUniformBoundaryMessageQuarterCertificate
    {Source Target : Nat -> Type}
    {physical : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (witness :
      CrossProductRelativeRankOneQuarterWitness
        Source Target physical sources targets) :
    UniformBoundaryMessageQuarterCertificate
      Nat Source Target physical sources targets :=
  witness.toPrefixTailRelativeRankOneQuarterWitness
    |>.toUniformBoundaryMessageQuarterCertificate

end CrossProductRelativeRankOneQuarterWitness

end YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail

#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail.CrossProductQuarterErrorTail.tail_step
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail.CrossProductQuarterErrorTail.toQuarterErrorPrefixTail
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail.CrossProductQuarterErrorTail.bound_all
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail.CrossProductRelativeRankOneQuarterWitness.toPrefixTailRelativeRankOneQuarterWitness
#print axioms YMGap.Continuum.BF4BoundaryMessageRelativeErrorCrossTail.CrossProductRelativeRankOneQuarterWitness.toUniformBoundaryMessageQuarterCertificate
