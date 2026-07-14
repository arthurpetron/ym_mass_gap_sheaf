/-
# The full dependent pentagon for the certified cyclic CG charts

The four cyclic comb charts and the direct balanced chart are constructive
coordinate bases of the same physical four-form box.  Consequently their
full dependent basis changes satisfy the three-edge/two-edge pentagon for all
external degrees and all physical intermediate channels.

Exact scope: the theorem is for the certified cyclic tensor-order conventions.
No identification is made here with the repository's fixed ordered raw
`triRight`/F normalization; the odd-outer sign bridge remains a separate
normalization theorem.
-/

import YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases
import YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnCyclicPentagon

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases
open YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

/-- Five certified charts in pentagon order. -/
inductive CyclicPentagonTree where
  | p0 | p1 | p2 | p3 | p4

/-- **All five certified charts as coordinate bases of one four-form box.** -/
def cyclicPentagonCoordinateBases (a b c d : Nat) :
    CoordinateBases CyclicPentagonTree QuadForm where
  Index := fun
    | .p0 => LeftComb4Channel a b c d
    | .p1 => LeftComb4Channel b c a d
    | .p2 => LeftComb4Channel b c d a
    | .p3 => LeftComb4Channel c d b a
    | .p4 => Balanced4Channel a b c d
  Rel := PhysicalQuadBoxEqv a b c d
  rel_refl := fun x i j l r hi hj hl hr => Q'.eqv_refl _
  rel_symm := fun h i j l r hi hj hl hr =>
    Q'.eqv_symm (h i j l r hi hj hl hr)
  rel_trans := fun h₁ h₂ i j l r hi hj hl hr =>
    Q'.eqv_trans _ _ _ (h₁ i j l r hi hj hl hr)
      (h₂ i j l r hi hj hl hr)
  synth := fun
    | .p0, u => leftComb4Reconstruct a b c d u
    | .p1, u => p1Reconstruct a b c d u
    | .p2, u => p2Reconstruct a b c d u
    | .p3, u => p3Reconstruct a b c d u
    | .p4, u => balanced4Reconstruct a b c d u
  coords := fun
    | .p0, x => leftComb4Coordinates a b c d x
    | .p1, x => p1Coordinates a b c d x
    | .p2, x => p2Coordinates a b c d x
    | .p3, x => p3Coordinates a b c d x
    | .p4, x => balanced4Coordinates a b c d x
  coords_congr := by
    intro T x z hxz q
    cases T with
    | p0 => exact leftComb4Coordinates_congr a b c d x z hxz q
    | p1 => exact p1Coordinates_congr a b c d x z hxz q
    | p2 => exact p2Coordinates_congr a b c d x z hxz q
    | p3 => exact p3Coordinates_congr a b c d x z hxz q
    | p4 => exact balanced4Coordinates_congr a b c d x z hxz q
  synth_coords := by
    intro T x
    cases T with
    | p0 =>
        intro i j l r hi hj hl hr
        exact leftComb4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p1 =>
        intro i j l r hi hj hl hr
        exact p1Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p2 =>
        intro i j l r hi hj hl hr
        exact p2Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p3 =>
        intro i j l r hi hj hl hr
        exact p3Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p4 =>
        intro i j l r hi hj hl hr
        exact balanced4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
  coords_synth := by
    intro T u q
    cases T with
    | p0 => exact leftComb4Coordinates_reconstruct a b c d u q
    | p1 => exact p1Coordinates_reconstruct a b c d u q
    | p2 => exact p2Coordinates_reconstruct a b c d u q
    | p3 => exact p3Coordinates_reconstruct a b c d u q
    | p4 => exact balanced4Coordinates_reconstruct a b c d u q

/-- **Full all-degree, all-channel pentagon for the certified cyclic charts.**
The channel functions are genuinely dependent and may have different types
at all five vertices. -/
theorem cyclic_allLabel_pentagon (a b c d : Nat)
    (u : LeftComb4Channel a b c d → Q') :
    CoordEqv (cyclicPentagonCoordinateBases a b c d) .p3
      (basisChange (cyclicPentagonCoordinateBases a b c d) .p2 .p3
        (basisChange (cyclicPentagonCoordinateBases a b c d) .p1 .p2
          (basisChange (cyclicPentagonCoordinateBases a b c d) .p0 .p1 u)))
      (basisChange (cyclicPentagonCoordinateBases a b c d) .p4 .p3
        (basisChange (cyclicPentagonCoordinateBases a b c d) .p0 .p4 u)) := by
  exact pentagon_from_coordinate_bases
    (cyclicPentagonCoordinateBases a b c d)
    .p0 .p1 .p2 .p3 .p4 u

end YMGap.Continuum.SU2GeneralHahnCyclicPentagon

#print axioms YMGap.Continuum.SU2GeneralHahnCyclicPentagon.cyclicPentagonCoordinateBases
#print axioms YMGap.Continuum.SU2GeneralHahnCyclicPentagon.cyclic_allLabel_pentagon
