/-
# One normalized crossed-link recoupling interface for every slab valence

The four-dimensional slab exposes link degrees zero through six.  The local
analytic compiler is trivial below degree four, uses one physical Schur move
at degree four, two dependent moves at degree five, and three dependent moves
at degree six.  This module contracts those cases into one proof-carrying
finite normalized kernel package.

There is no default high-valence branch: degree greater than six is eliminated
from the proved cubical incidence bound carried by the actual link datum.
This makes subsequent finite products independent of local target types while
retaining their exact definitions internally.

Constructive contract: exact `Q'`, finite lists, structural degree cases, no
choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
import YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler

namespace YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite exact normalized row as one object -/

structure FiniteNormalizedQKernel where
  Target : Type
  targets : List Target
  weight : Target → Q'
  weight_nonnegative : ∀ target, (0 : Q') ≤ weight target
  row_normalized : listQSum weight targets ≈ 1

/-- The unique identity row used when no reassociation is required. -/
def unitFiniteNormalizedQKernel : FiniteNormalizedQKernel where
  Target := Unit
  targets := [()]
  weight := fun _ => 1
  weight_nonnegative := fun _ => Q'.zero_le_one
  row_normalized := by
    exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-! ## 2. Reuse generic switch data in the degree-four compiler -/

def CrossedSlabSwitchData.toValenceFour {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 4) :
    ValenceFourCrossReplicaSwitchData K extent where
  leftPhysical := D.leftPhysical
  rightPhysical := D.rightPhysical
  link := D.link
  leftAuxiliary := D.leftAuxiliary
  rightAuxiliary := D.rightAuxiliary
  leftAuxiliary_mem := D.leftAuxiliary_mem
  rightAuxiliary_mem := D.rightAuxiliary_mem
  mask := D.mask
  leftBounded := D.leftBounded
  rightBounded := D.rightBounded
  leftSelection := D.leftSelection
  rightSelection := D.rightSelection
  leftConstant := D.leftConstant
  rightConstant := D.rightConstant
  degree_eq_four := D.degree_eq

/-- Every actual switch datum is automatically in the complete 4D incidence
range. -/
theorem CrossedSlabSwitchData.degree_le_six
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree) :
    degree ≤ 6 := by
  rw [← D.degree_eq]
  exact slabIncidentPlaqIds_length_le_six extent D.link

/-! ## 3. All local degrees in one dependent package -/

/-- The exact normalized recoupling row at an actual crossed slab link.

Degrees zero through three need no associator move.  Degree four uses one
Schur row, degree five uses the two-level tower, and degree six uses the
three-level bulk tower.  The final pattern is uninhabited by
`degree_le_six`. -/
def crossedLinkRecouplingKernel {K extent : Nat} :
    (degree : Nat) → CrossedSlabSwitchData K extent degree →
      FiniteNormalizedQKernel
  | 0, _ => unitFiniteNormalizedQKernel
  | 1, _ => unitFiniteNormalizedQKernel
  | 2, _ => unitFiniteNormalizedQKernel
  | 3, _ => unitFiniteNormalizedQKernel
  | 4, D =>
      let D₄ := CrossedSlabSwitchData.toValenceFour D
      { Target := CrossedSchurTarget D₄
        targets := crossedSchurTargets D₄
        weight := crossedSchurKernelAt D₄
        weight_nonnegative := crossedSchurKernelAt_nonnegative D₄
        row_normalized := crossedSchurKernel_row_normalized D₄ }
  | 5, D =>
      { Target := CrossedValenceFiveTarget D
        targets := crossedValenceFiveTargets D
        weight := crossedValenceFiveKernelAt D
        weight_nonnegative := crossedValenceFiveKernelAt_nonnegative D
        row_normalized := crossedValenceFiveKernel_row_normalized D }
  | 6, D =>
      { Target := CrossedValenceSixTarget D
        targets := crossedValenceSixTargets D
        weight := crossedValenceSixKernelAt D
        weight_nonnegative := crossedValenceSixKernelAt_nonnegative D
        row_normalized := crossedValenceSixKernel_row_normalized D }
  | degree + 7, D => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

theorem crossedLinkRecouplingKernel_weight_nonnegative
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree)
    (target : (crossedLinkRecouplingKernel degree D).Target) :
    (0 : Q') ≤ (crossedLinkRecouplingKernel degree D).weight target :=
  (crossedLinkRecouplingKernel degree D).weight_nonnegative target

/-- **Every actual crossed slab link, independent of its local valence, now
has one exact normalized analytic recoupling row.** -/
theorem crossedLinkRecouplingKernel_row_normalized
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree) :
    listQSum (crossedLinkRecouplingKernel degree D).weight
        (crossedLinkRecouplingKernel degree D).targets ≈ 1 :=
  (crossedLinkRecouplingKernel degree D).row_normalized

#print axioms unitFiniteNormalizedQKernel
#print axioms CrossedSlabSwitchData.toValenceFour
#print axioms CrossedSlabSwitchData.degree_le_six
#print axioms crossedLinkRecouplingKernel
#print axioms crossedLinkRecouplingKernel_weight_nonnegative
#print axioms crossedLinkRecouplingKernel_row_normalized

end YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel
