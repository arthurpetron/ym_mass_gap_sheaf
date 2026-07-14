/-
# Actual raw transvectants of global Clebsch--Gordan sections

The global synthesis is definitionally zero outside its physical coefficient
rectangle.  Consequently its explicit rectangle projection is pointwise
equivalent to the synthesis itself, and the projected-coordinate equivalence
immediately upgrades to a statement about the raw transvectant of every
global section.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases

namespace YMGap.Continuum.SU2GlobalSectionActualTransvectant

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates

local infix:50 " ≈ " => Q'.eqv

/-- Global synthesis is already the zero-outside representative selected by
physical rectangle projection. -/
theorem globalHahnReconstruct_eqv_rectProject (m n : Nat)
    (c : PhysicalCGChannel m n → Q') :
    BForm2Eqv (globalHahnReconstruct m n c)
      (rectProject m n (globalHahnReconstruct m n c)) := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · exact Q'.eqv_symm
        (rectProject_apply_physical m n
          (globalHahnReconstruct m n c) i j hi hj)
    · have hzero := rectProject_zero_outside m n
        (globalHahnReconstruct m n c) i j (Or.inr (by omega))
      unfold globalHahnReconstruct
      rw [dif_pos hi, dif_neg hj]
      exact Q'.eqv_symm hzero
  · have hzero := rectProject_zero_outside m n
      (globalHahnReconstruct m n c) i j (Or.inl (by omega))
    unfold globalHahnReconstruct
    rw [dif_neg hi]
    exact Q'.eqv_symm hzero

/-- **Raw-section right inverse.**  The actual unprojected transvectant of a
global synthesized tensor recovers arbitrary dependent physical channel data
at every channel. -/
theorem transvect_globalHahnReconstruct (m n : Nat)
    (c : PhysicalCGChannel m n → Q') (q : PhysicalCGChannel m n) :
    transvect m n q.k (globalHahnReconstruct m n c) q.s ≈ c q := by
  have hcongr := transvect_congr m n q.k
    (globalHahnReconstruct_eqv_rectProject m n c) q.s
  exact Q'.eqv_trans _ _ _ hcongr
    (Q'.eqv_trans _ _ _
      (globalTransvectCoordinates_eq_hahn m n
        (globalHahnReconstruct m n c) q)
      (globalHahnCoordinates_reconstruct m n c q))

/-- A single-order global section is analyzed by the raw transvectant as the
requested output form on that order and zero on every other physical order. -/
theorem transvect_globalOrderSection (m n k : Nat) (v : BForm)
    (q : PhysicalCGChannel m n) :
    transvect m n q.k (globalOrderSection m n k v) q.s ≈
      (if q.k = k then v q.s else 0) := by
  exact transvect_globalHahnReconstruct m n (orderChannelData k v) q

end YMGap.Continuum.SU2GlobalSectionActualTransvectant

#print axioms YMGap.Continuum.SU2GlobalSectionActualTransvectant.globalHahnReconstruct_eqv_rectProject
#print axioms YMGap.Continuum.SU2GlobalSectionActualTransvectant.transvect_globalHahnReconstruct
#print axioms YMGap.Continuum.SU2GlobalSectionActualTransvectant.transvect_globalOrderSection
