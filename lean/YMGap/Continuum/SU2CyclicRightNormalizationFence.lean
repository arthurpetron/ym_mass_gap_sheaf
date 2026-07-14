/-
# Cyclic right coordinates are not raw `triRight` coordinates

Cyclically presenting `(a,b,c)` as `(b,c,a)` reverses the two inputs of the
outer transvectant.  At odd outer order this changes sign.  The smallest
closed example below permanently fences the tempting but false identification
of the cyclic right coordinate package with the repository's ordered
`triRight` normalization.
-/

import YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases
import YMGap.Continuum.SU2TransvectantMixedPentagon

namespace YMGap.Continuum.SU2CyclicRightNormalizationFence

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases

/-- Coefficients of the pure tensor `mono 0 ⊗ mono 1 ⊗ mono 0`. -/
def oddOuterPureTensor : TriForm :=
  fun i j l => mono 0 i * (mono 1 j * mono 0 l)

/-- Inner order zero and outer order one for the cyclic presentation
`(1,0,1)`. -/
def oddOuterCyclicChannel : LeftNestedCGChannel 1 0 1 :=
  { k := 0
    k_le := by decide
    outer :=
      { k := 1
        k_le := by decide
        s := 0
        s_le := by decide } }

/-- The cyclic coordinate has coefficient `+1`. -/
theorem cyclic_odd_outer_value :
    (rightNestedCoordinates 1 1 0 oddOuterPureTensor
      oddOuterCyclicChannel).eqv 1 := by
  decide

/-- The ordered raw `triRight` coefficient has value `-1`. -/
theorem ordered_triRight_odd_outer_value :
    (triRight 1 1 0 0 1 (mono 0) (mono 1) (mono 0) 0).eqv (-1) := by
  decide

/-- **Normalization fence.**  Cyclic right coordinates cannot be used as
ordered raw `triRight` coordinates without the outer swap sign. -/
theorem cyclic_right_ne_ordered_triRight :
    ¬ (rightNestedCoordinates 1 1 0 oddOuterPureTensor
        oddOuterCyclicChannel).eqv
      (triRight 1 1 0 0 1 (mono 0) (mono 1) (mono 0) 0) := by
  decide

end YMGap.Continuum.SU2CyclicRightNormalizationFence

#print axioms YMGap.Continuum.SU2CyclicRightNormalizationFence.cyclic_odd_outer_value
#print axioms YMGap.Continuum.SU2CyclicRightNormalizationFence.ordered_triRight_odd_outer_value
#print axioms YMGap.Continuum.SU2CyclicRightNormalizationFence.cyclic_right_ne_ordered_triRight
