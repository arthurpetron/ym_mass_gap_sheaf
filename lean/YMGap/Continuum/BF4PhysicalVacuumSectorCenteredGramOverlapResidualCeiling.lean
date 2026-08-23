/-
# A uniform ceiling for the exact BF4 posterior-overlap residual rate

At every finite cutoff, both exact posterior overlap floors are strictly
positive and at most one.  Consequently each residual factor

    2 * (1 - floor_K)

lies in `[0,2)`, and the one scalar consumed by the centered-Gram row
estimate lies in `[0,4)`.  This module proves that unconditional all-cutoff
ceiling.

The strict ceiling `4` is not the contraction threshold needed for a mass
gap: the completed gap compiler requires a cofinal bound by one fixed
`q < 1`.  The point of the theorem is to quantify the remaining analytic
improvement without introducing a new certificate or hiding it behind an
asymptotic statement.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate

/-! ## 1. Each residual factor is strictly below two -/

private theorem one_add_neg_lt_one_of_pos {epsilon : Q'}
    (hpositive : (0 : Q') < epsilon) :
    (1 : Q') + (-epsilon) < (1 : Q') := by
  show ((1 : Q') + -epsilon).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -epsilon).den : Int)
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hpositive
  change
    (((1 : Int) * (epsilon.den : Int) + (-epsilon.num) * (1 : Int)) *
      (1 : Int)) <
      ((1 : Int) *
        (((1 : Nat) * epsilon.den : Nat) : Int))
  push_cast
  omega

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_lt_two
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
        w hw cutoff half < (2 : Q') := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
  have hsub :
      (1 : Q') +
          (-centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
            w hw cutoff half) <
        (1 : Q') :=
    one_add_neg_lt_one_of_pos
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_pos
        w hw cutoff half)
  exact Q'.mul_lt_mul_of_pos_left (by decide) hsub

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_lt_two
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
        w hw cutoff half < (2 : Q') := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
  have hsub :
      (1 : Q') +
          (-centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
            w hw cutoff half) <
        (1 : Q') :=
    one_add_neg_lt_one_of_pos
      (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_pos
        w hw cutoff half)
  exact Q'.mul_lt_mul_of_pos_left (by decide) hsub

/-! ## 2. The exact centered-Gram residual scalar is uniformly below four -/

/-- The actual product residual rate is strictly below four at every cutoff.

This is an unconditional uniform estimate on the exact scalar controlling
the literal centered-Gram row majorant.  It does not inhabit the cofinal gap
certificate, whose rate must be strictly below one. -/
theorem centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_lt_four
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w hw cutoff half < (4 : Q') := by
  unfold centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
  have htarget_le :
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
          w hw cutoff half ≤ (2 : Q') :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_lt_two
        w hw cutoff half)
  have hsource_nonnegative :
      (0 : Q') ≤
        centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
          w hw cutoff half :=
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_nonnegative
      w hw cutoff half
  have hproduct_le :
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
            w hw cutoff half *
          centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
            w hw cutoff half ≤
        (2 : Q') *
          centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
            w hw cutoff half :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ htarget_le hsource_nonnegative
  have htwice_source_lt :
      (2 : Q') *
          centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
            w hw cutoff half <
        (2 : Q') * (2 : Q') :=
    Q'.mul_lt_mul_of_pos_left (by decide)
      (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_lt_two
        w hw cutoff half)
  exact Q'.lt_of_le_of_lt hproduct_le htwice_source_lt

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_lt_two
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_lt_two
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling.centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_lt_four
