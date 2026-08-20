/-
# Finite-prefix plus analytic-tail boundary-message certificate

Heavy exact computation can verify only finitely many regulators.  A uniform
boundary-message theorem therefore needs a separate mathematical argument for
the infinite tail.  This file packages the useful constructive split:

* exact prefix checks below a chosen threshold;
* one checked bound at the threshold; and
* an analytic proof that the scalar relative-error budget is antitone after
  the threshold.

Induction then proves the `1/16` budget at every regulator.  An entrywise
physical-kernel envelope by that scalar budget constructs the existing
`UniformRelativeRankOneQuarterWitness`, hence the uniform projective quarter
certificate.

An external Rust, C, or Python program may emit the finite prefix checks.  The
tail step and every emitted rational inequality are checked by Lean.  Random
sampling without a deterministic coverage certificate cannot inhabit these
fields.

## Axiom gate

Natural-number induction and exact rational order only; no compactness,
subsequence extraction, or opaque external computation is trusted.
-/

import YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter

namespace YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter

/-! ## 1. Constructive finite-prefix/tail induction -/

/-- A proof-carrying all-regulator bound assembled from finite prefix checks
and an antitone analytic tail. -/
structure QuarterErrorPrefixTail (error : Nat -> Q') : Type where
  threshold : Nat
  prefix_bound : forall stage : Nat, stage < threshold ->
    error stage <= relativeRankOneTolerance
  threshold_bound : error threshold <= relativeRankOneTolerance
  tail_step : forall stage : Nat, threshold <= stage ->
    error (stage + 1) <= error stage

namespace QuarterErrorPrefixTail

/-- Once inside the certified tail, every later error is below the starting
error. -/
theorem tail_antitone_add
    {error : Nat -> Q'}
    (budget : QuarterErrorPrefixTail error)
    (start : Nat) (hstart : budget.threshold <= start) :
    forall offset : Nat, error (start + offset) <= error start
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      refine Q'.le_trans' _ _ _ ?_
        (budget.tail_antitone_add start hstart offset)
      rw [show start + (offset + 1) = (start + offset) + 1 by omega]
      exact budget.tail_step (start + offset)
        (Nat.le_trans hstart (Nat.le_add_right start offset))

/-- The finite prefix and antitone tail cover every natural regulator. -/
theorem bound_all
    {error : Nat -> Q'}
    (budget : QuarterErrorPrefixTail error)
    (stage : Nat) :
    error stage <= relativeRankOneTolerance := by
  rcases Nat.lt_or_ge stage budget.threshold with hprefix | htail
  · exact budget.prefix_bound stage hprefix
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le htail
    exact Q'.le_trans' _ _ _
      (budget.tail_antitone_add budget.threshold
        (Nat.le_refl _) offset)
      budget.threshold_bound

end QuarterErrorPrefixTail

/-! ## 2. Physical entry envelope controlled by the scalar budget -/

/-- A regulator-indexed physical rank-one approximation whose entrywise error
is controlled by one scalar prefix/tail budget.  This separates the finite
enumeration problem from the analytic tail theorem. -/
structure PrefixTailRelativeRankOneQuarterWitness
    (Source Target : Nat -> Type)
    (physical : forall stage, Source stage -> Target stage -> Q')
    (sources : forall stage, List (Source stage))
    (targets : forall stage, List (Target stage)) : Type where
  sourceProfile : forall stage, Source stage -> Q'
  targetProfile : forall stage, Target stage -> Q'
  sourceProfile_pos : forall stage source,
    source ∈ sources stage ->
      (0 : Q') < sourceProfile stage source
  targetProfile_pos : forall stage target,
    target ∈ targets stage ->
      (0 : Q') < targetProfile stage target
  error : Nat -> Q'
  errorBudget : QuarterErrorPrefixTail error
  relative_error : forall stage source,
    source ∈ sources stage -> forall target,
    target ∈ targets stage ->
      Q'.abs
          (physical stage source target +
            -(sourceProfile stage source * targetProfile stage target)) <=
        error stage *
          (sourceProfile stage source * targetProfile stage target)
  reference : forall stage, Source stage
  reference_mem : forall stage, reference stage ∈ sources stage

namespace PrefixTailRelativeRankOneQuarterWitness

/-- The profile product is nonnegative on every selected source-target pair. -/
theorem profileProduct_nonnegative
    {Source Target : Nat -> Type}
    {physical : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (witness :
      PrefixTailRelativeRankOneQuarterWitness
        Source Target physical sources targets)
    (stage : Nat)
    (source : Source stage) (hsource : source ∈ sources stage)
    (target : Target stage) (htarget : target ∈ targets stage) :
    (0 : Q') <=
      witness.sourceProfile stage source *
        witness.targetProfile stage target :=
  Q'.le_of_lt
    (Q'.mul_pos
      (witness.sourceProfile_pos stage source hsource)
      (witness.targetProfile_pos stage target htarget))

/-- Prefix computation plus tail monotonicity constructs the uniform relative
rank-one witness consumed by the projective refresh theorem. -/
def toUniformRelativeRankOneQuarterWitness
    {Source Target : Nat -> Type}
    {physical : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (witness :
      PrefixTailRelativeRankOneQuarterWitness
        Source Target physical sources targets) :
    UniformRelativeRankOneQuarterWitness
      Nat Source Target physical sources targets where
  sourceProfile := witness.sourceProfile
  targetProfile := witness.targetProfile
  sourceProfile_pos := witness.sourceProfile_pos
  targetProfile_pos := witness.targetProfile_pos
  relative_error := by
    intro stage source hsource target htarget
    refine Q'.le_trans' _ _ _
      (witness.relative_error
        stage source hsource target htarget) ?_
    exact Q'.mul_le_mul_of_nonneg_right
      (witness.error stage) relativeRankOneTolerance
      (witness.sourceProfile stage source *
        witness.targetProfile stage target)
      (witness.errorBudget.bound_all stage)
      (witness.profileProduct_nonnegative
        stage source hsource target htarget)
  reference := witness.reference
  reference_mem := witness.reference_mem

/-- The complete uniform terminal-independent quarter certificate obtained
from the checked prefix and analytic tail. -/
def toUniformBoundaryMessageQuarterCertificate
    {Source Target : Nat -> Type}
    {physical : forall stage, Source stage -> Target stage -> Q'}
    {sources : forall stage, List (Source stage)}
    {targets : forall stage, List (Target stage)}
    (witness :
      PrefixTailRelativeRankOneQuarterWitness
        Source Target physical sources targets) :
    UniformBoundaryMessageQuarterCertificate
      Nat Source Target physical sources targets :=
  UniformRelativeRankOneQuarterWitness.toUniformBoundaryMessageQuarterCertificate
    witness.toUniformRelativeRankOneQuarterWitness

end PrefixTailRelativeRankOneQuarterWitness

end YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter.QuarterErrorPrefixTail.tail_antitone_add
#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter.QuarterErrorPrefixTail.bound_all
#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter.PrefixTailRelativeRankOneQuarterWitness.profileProduct_nonnegative
#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter.PrefixTailRelativeRankOneQuarterWitness.toUniformRelativeRankOneQuarterWitness
#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter.PrefixTailRelativeRankOneQuarterWitness.toUniformBoundaryMessageQuarterCertificate
