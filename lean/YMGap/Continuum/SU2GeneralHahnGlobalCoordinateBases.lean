/-
# The actual all-label SU(2) Clebsch--Gordan coordinate basis

For fixed input bidegree `(m,n)`, the common semantic carrier is the complete
physical coefficient rectangle.  Its dependent coordinates are the projected
raw transvectants indexed by every physical contraction order and output
monomial.  The explicit global Hahn reconstruction supplies a constructive
inverse in both directions, so this is an actual `CoordinateBases` package,
not merely a Hahn-matrix surrogate.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
import YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates

namespace YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Equality on the physical `(m+1) x (n+1)` coefficient rectangle. -/
def PhysicalRectangleEqv (m n : Nat) (x z : BForm2) : Prop :=
  ∀ i j, i ≤ m → j ≤ n → x i j ≈ z i j

/-- Global Hahn analysis depends only on the physical source rectangle. -/
theorem globalHahnCoordinates_congr (m n : Nat) (x z : BForm2)
    (hxz : PhysicalRectangleEqv m n x z)
    (q : PhysicalCGChannel m n) :
    globalHahnCoordinates m n x q ≈ globalHahnCoordinates m n z q := by
  unfold globalHahnCoordinates
  apply physicalHahnAction_congr
  intro a ha
  have hsrc := sourceActive_of_index m n q.shell a q.shell_le
    (Nat.lt_succ_iff.mp ha)
  unfold sourceShellCoordinates
  exact hxz _ _ hsrc.2.1 hsrc.2.2

/-- Projected raw transvectant coordinates descend to physical-rectangle
semantics. -/
theorem globalTransvectCoordinates_congr (m n : Nat) (x z : BForm2)
    (hxz : PhysicalRectangleEqv m n x z)
    (q : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n x q ≈
      globalTransvectCoordinates m n z q := by
  exact Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn m n x q)
    (Q'.eqv_trans _ _ _
      (globalHahnCoordinates_congr m n x z hxz q)
      (Q'.eqv_symm (globalTransvectCoordinates_eq_hahn m n z q)))

/-- **Actual all-label binary Clebsch--Gordan coordinate basis.**  Coordinates
are the projected raw transvectants themselves, while synthesis is the exact
choice-free global Hahn solver. -/
def globalCGCoordinateBases (m n : Nat) : CoordinateBases Unit BForm2 where
  Index := fun _ => PhysicalCGChannel m n
  Rel := PhysicalRectangleEqv m n
  rel_refl := fun x i j hi hj => Q'.eqv_refl _
  rel_symm := fun h i j hi hj => Q'.eqv_symm (h i j hi hj)
  rel_trans := fun h₁ h₂ i j hi hj =>
    Q'.eqv_trans _ _ _ (h₁ i j hi hj) (h₂ i j hi hj)
  synth := fun _ c => globalHahnReconstruct m n c
  coords := fun _ x => globalTransvectCoordinates m n x
  coords_congr := by
    intro T x z hxz q
    exact globalTransvectCoordinates_congr m n x z hxz q
  synth_coords := by
    intro T x i j hi hj
    exact globalHahnReconstruct_transvectCoordinates m n x i j hi hj
  coords_synth := by
    intro T c q
    exact Q'.eqv_trans _ _ _
      (globalTransvectCoordinates_eq_hahn m n
        (globalHahnReconstruct m n c) q)
      (globalHahnCoordinates_reconstruct m n c q)

end YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases.globalHahnCoordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases.globalTransvectCoordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases.globalCGCoordinateBases
