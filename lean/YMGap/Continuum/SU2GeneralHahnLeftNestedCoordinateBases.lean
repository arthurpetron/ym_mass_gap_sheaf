/-
# A constructive left-associated three-factor CG coordinate basis

The actual all-label binary Clebsch--Gordan basis composes fiberwise.  First
couple degrees `(m,n)` at a physical contraction order `k`; its output form,
of degree `m+n-2k`, is then coupled with degree `p`.  This file carries out
that dependent composition explicitly and proves both nested round trips on
the complete physical coefficient box.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient tensor of three binary forms. -/
abbrev TriForm : Type := Nat → Nat → Nat → Q'

/-- Equality on the complete physical three-factor coefficient box. -/
def PhysicalBoxEqv (m n p : Nat) (x z : TriForm) : Prop :=
  ∀ i j l, i ≤ m → j ≤ n → l ≤ p → x i j l ≈ z i j l

/-- A left-associated nested channel: first contraction order `k`, followed
by an arbitrary physical channel for the intermediate output and third leg. -/
structure LeftNestedCGChannel (m n p : Nat) where
  k : Nat
  k_le : k ≤ min m n
  outer : PhysicalCGChannel (m + n - 2 * k) p

/-- Fix the third coefficient and view a three-form as a two-form. -/
def triSlice (x : TriForm) (l : Nat) : BForm2 :=
  fun i j => x i j l

/-- The complete output form of the first pair at contraction order `k`,
still tensored with the third input coefficient. -/
def firstPairOutput (m n : Nat) (x : TriForm) (k : Nat) : BForm2 :=
  fun s l => transvect m n k (rectProject m n (triSlice x l)) s

/-- Extract the coordinate family belonging to one first contraction order. -/
def leftOuterData {m n p : Nat}
    (c : LeftNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min m n) :
    PhysicalCGChannel (m + n - 2 * k) p → Q' :=
  fun q => c { k := k, k_le := hk, outer := q }

/-- Reconstruct the intermediate-output/third-leg tensor at one first order. -/
def leftOuterReconstruct {m n p : Nat}
    (c : LeftNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min m n) : BForm2 :=
  globalHahnReconstruct (m + n - 2 * k) p (leftOuterData c k hk)

/-- Feed the reconstructed outer tensors back as the complete dependent data
for the first binary reconstruction, at fixed third coefficient `l`. -/
def leftInnerData {m n p : Nat}
    (c : LeftNestedCGChannel m n p → Q') (l : Nat) :
    PhysicalCGChannel m n → Q' :=
  fun q => leftOuterReconstruct c q.k q.k_le q.s l

/-- Explicit synthesis for the left-associated nested channel family. -/
def leftNestedReconstruct (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q') : TriForm :=
  fun i j l => globalHahnReconstruct m n (leftInnerData c l) i j

/-- Actual projected transvectant coordinates for the left-associated tree. -/
def leftNestedCoordinates (m n p : Nat) (x : TriForm) :
    LeftNestedCGChannel m n p → Q' :=
  fun q => globalTransvectCoordinates (m + n - 2 * q.k) p
    (firstPairOutput m n x q.k) q.outer

private def firstChannel (m n k s : Nat) (hk : k ≤ min m n)
    (hs : s ≤ m + n - 2 * k) : PhysicalCGChannel m n :=
  { k := k, k_le := hk, s := s, s_le := hs }

/-- Reconstructing all nested data makes the first-pair output at order `k`
equal to the corresponding reconstructed outer tensor. -/
theorem firstPairOutput_leftNestedReconstruct (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min m n) (s l : Nat)
    (hs : s ≤ m + n - 2 * k) :
    firstPairOutput m n (leftNestedReconstruct m n p c) k s l ≈
      leftOuterReconstruct c k hk s l := by
  let q := firstChannel m n k s hk hs
  have hright := Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn m n
      (globalHahnReconstruct m n (leftInnerData c l)) q)
    (globalHahnCoordinates_reconstruct m n (leftInnerData c l) q)
  simpa only [firstPairOutput, triSlice, leftNestedReconstruct,
    leftInnerData, q, firstChannel, globalTransvectCoordinates] using hright

/-- First-pair output respects equality of the physical three-factor box. -/
theorem firstPairOutput_congr (m n p : Nat) (x z : TriForm)
    (hxz : PhysicalBoxEqv m n p x z)
    (k : Nat) (hk : k ≤ min m n) :
    PhysicalRectangleEqv (m + n - 2 * k) p
      (firstPairOutput m n x k) (firstPairOutput m n z k) := by
  intro s l hs hl
  let q := firstChannel m n k s hk hs
  have hslice : PhysicalRectangleEqv m n (triSlice x l) (triSlice z l) := by
    intro i j hi hj
    exact hxz i j l hi hj hl
  have hcongr := globalTransvectCoordinates_congr m n
    (triSlice x l) (triSlice z l) hslice q
  simpa only [firstPairOutput, q, firstChannel,
    globalTransvectCoordinates] using hcongr

/-- Nested actual coordinates respect equality on the source box. -/
theorem leftNestedCoordinates_congr (m n p : Nat) (x z : TriForm)
    (hxz : PhysicalBoxEqv m n p x z)
    (q : LeftNestedCGChannel m n p) :
    leftNestedCoordinates m n p x q ≈
      leftNestedCoordinates m n p z q := by
  exact globalTransvectCoordinates_congr (m + n - 2 * q.k) p
    (firstPairOutput m n x q.k) (firstPairOutput m n z q.k)
    (firstPairOutput_congr m n p x z hxz q.k q.k_le) q.outer

/-- **Nested coordinate right inverse.** -/
theorem leftNestedCoordinates_reconstruct (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q')
    (q : LeftNestedCGChannel m n p) :
    leftNestedCoordinates m n p (leftNestedReconstruct m n p c) q ≈
      c q := by
  cases q with
  | mk k hk outer =>
      have hrel : PhysicalRectangleEqv (m + n - 2 * k) p
          (firstPairOutput m n (leftNestedReconstruct m n p c) k)
          (leftOuterReconstruct c k hk) := by
        intro s l hs hl
        exact firstPairOutput_leftNestedReconstruct m n p c k hk s l hs
      have hcongr := globalTransvectCoordinates_congr
        (m + n - 2 * k) p
        (firstPairOutput m n (leftNestedReconstruct m n p c) k)
        (leftOuterReconstruct c k hk) hrel outer
      have hright := Q'.eqv_trans _ _ _
        (globalTransvectCoordinates_eq_hahn (m + n - 2 * k) p
          (leftOuterReconstruct c k hk) outer)
        (globalHahnCoordinates_reconstruct (m + n - 2 * k) p
          (leftOuterData c k hk) outer)
      exact Q'.eqv_trans _ _ _ hcongr
        (by simpa only [leftOuterReconstruct, leftOuterData] using hright)

/-- **Nested semantic left inverse.** -/
theorem leftNestedReconstruct_coordinates (m n p : Nat) (x : TriForm)
    (i j l : Nat) (hi : i ≤ m) (hj : j ≤ n) (hl : l ≤ p) :
    leftNestedReconstruct m n p (leftNestedCoordinates m n p x) i j l ≈
      x i j l := by
  let direct : PhysicalCGChannel m n → Q' :=
    globalTransvectCoordinates m n (triSlice x l)
  have hdata : ∀ q : PhysicalCGChannel m n,
      leftInnerData (leftNestedCoordinates m n p x) l q ≈ direct q := by
    intro q
    have hout := globalHahnReconstruct_transvectCoordinates
      (m + n - 2 * q.k) p (firstPairOutput m n x q.k)
      q.s l q.s_le hl
    simpa only [leftInnerData, leftOuterReconstruct, leftOuterData,
      leftNestedCoordinates, direct, firstPairOutput, triSlice,
      globalTransvectCoordinates] using hout
  have hcongr := globalHahnReconstruct_congr m n
    (leftInnerData (leftNestedCoordinates m n p x) l) direct hdata
    i j hi hj
  have hright := globalHahnReconstruct_transvectCoordinates m n
    (triSlice x l) i j hi hj
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftNestedReconstruct] using hcongr)
    (by simpa only [direct, triSlice] using hright)

/-- The actual left-associated three-factor coordinate basis. -/
def leftNestedCGCoordinateBases (m n p : Nat) :
    CoordinateBases Unit TriForm where
  Index := fun _ => LeftNestedCGChannel m n p
  Rel := PhysicalBoxEqv m n p
  rel_refl := fun x i j l hi hj hl => Q'.eqv_refl _
  rel_symm := fun h i j l hi hj hl => Q'.eqv_symm (h i j l hi hj hl)
  rel_trans := fun h₁ h₂ i j l hi hj hl =>
    Q'.eqv_trans _ _ _ (h₁ i j l hi hj hl) (h₂ i j l hi hj hl)
  synth := fun _ c => leftNestedReconstruct m n p c
  coords := fun _ x => leftNestedCoordinates m n p x
  coords_congr := by
    intro T x z hxz q
    exact leftNestedCoordinates_congr m n p x z hxz q
  synth_coords := by
    intro T x i j l hi hj hl
    exact leftNestedReconstruct_coordinates m n p x i j l hi hj hl
  coords_synth := by
    intro T c q
    exact leftNestedCoordinates_reconstruct m n p c q

end YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.firstPairOutput_leftNestedReconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.firstPairOutput_congr
#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.leftNestedCoordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.leftNestedCoordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.leftNestedReconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases.leftNestedCGCoordinateBases
