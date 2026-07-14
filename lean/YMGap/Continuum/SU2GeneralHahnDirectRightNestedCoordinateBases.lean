/-
# Ordered right-associated three-factor CG coordinate basis

The cyclic transport of a left-nested basis reverses the two inputs of the
outer transvectant.  This module instead constructs the right-associated
basis directly: first couple `(n,p)`, then couple the original first factor
on the left of the intermediate output.  Its ordering therefore agrees with
the repository's raw `triRight` normalization without an outer swap sign.
-/

import YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- An ordered right-associated channel: first contract the second and third
degrees, then couple the original first degree on the left. -/
structure DirectRightNestedCGChannel (m n p : Nat) where
  k : Nat
  k_le : k ≤ min n p
  outer : PhysicalCGChannel m (n + p - 2 * k)

/-- Fix the first coefficient and view the last two factors as a two-form. -/
def rightTriSlice (x : TriForm) (i : Nat) : BForm2 :=
  fun j l => x i j l

/-- Complete output of the last pair, with the original first factor kept as
the left coordinate of the outer tensor. -/
def lastPairOutput (n p : Nat) (x : TriForm) (k : Nat) : BForm2 :=
  fun i s => transvect n p k (rectProject n p (rightTriSlice x i)) s

/-- Extract the outer channel data belonging to one inner order. -/
def directRightOuterData {m n p : Nat}
    (c : DirectRightNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min n p) :
    PhysicalCGChannel m (n + p - 2 * k) → Q' :=
  fun q => c { k := k, k_le := hk, outer := q }

/-- Reconstruct the ordered `(first, intermediate)` tensor at one inner
order. -/
def directRightOuterReconstruct {m n p : Nat}
    (c : DirectRightNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min n p) : BForm2 :=
  globalHahnReconstruct m (n + p - 2 * k)
    (directRightOuterData c k hk)

/-- Feed the reconstructed outer tensors back as dependent data for the
inner `(n,p)` reconstruction, at a fixed first coefficient. -/
def directRightInnerData {m n p : Nat}
    (c : DirectRightNestedCGChannel m n p → Q') (i : Nat) :
    PhysicalCGChannel n p → Q' :=
  fun q => directRightOuterReconstruct c q.k q.k_le i q.s

/-- Explicit ordered right-associated synthesis. -/
def directRightNestedReconstruct (m n p : Nat)
    (c : DirectRightNestedCGChannel m n p → Q') : TriForm :=
  fun i j l => globalHahnReconstruct n p (directRightInnerData c i) j l

/-- Actual ordered right-associated projected transvectant coordinates. -/
def directRightNestedCoordinates (m n p : Nat) (x : TriForm) :
    DirectRightNestedCGChannel m n p → Q' :=
  fun q => globalTransvectCoordinates m (n + p - 2 * q.k)
    (lastPairOutput n p x q.k) q.outer

private def innerChannel (n p k s : Nat) (hk : k ≤ min n p)
    (hs : s ≤ n + p - 2 * k) : PhysicalCGChannel n p :=
  { k := k, k_le := hk, s := s, s_le := hs }

/-- Reconstructing all nested data makes the last-pair output at order `k`
equal to the corresponding ordered outer tensor. -/
theorem lastPairOutput_directRightNestedReconstruct (m n p : Nat)
    (c : DirectRightNestedCGChannel m n p → Q')
    (k : Nat) (hk : k ≤ min n p) (i s : Nat)
    (hs : s ≤ n + p - 2 * k) :
    lastPairOutput n p (directRightNestedReconstruct m n p c) k i s ≈
      directRightOuterReconstruct c k hk i s := by
  let q := innerChannel n p k s hk hs
  have hright := Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn n p
      (globalHahnReconstruct n p (directRightInnerData c i)) q)
    (globalHahnCoordinates_reconstruct n p (directRightInnerData c i) q)
  simpa only [lastPairOutput, rightTriSlice,
    directRightNestedReconstruct, directRightInnerData, q, innerChannel,
    globalTransvectCoordinates] using hright

/-- Last-pair output respects equality of the physical three-factor box. -/
theorem lastPairOutput_congr (m n p : Nat) (x z : TriForm)
    (hxz : PhysicalBoxEqv m n p x z)
    (k : Nat) (hk : k ≤ min n p) :
    PhysicalRectangleEqv m (n + p - 2 * k)
      (lastPairOutput n p x k) (lastPairOutput n p z k) := by
  intro i s hi hs
  let q := innerChannel n p k s hk hs
  have hslice : PhysicalRectangleEqv n p
      (rightTriSlice x i) (rightTriSlice z i) := by
    intro j l hj hl
    exact hxz i j l hi hj hl
  have hcongr := globalTransvectCoordinates_congr n p
    (rightTriSlice x i) (rightTriSlice z i) hslice q
  simpa only [lastPairOutput, q, innerChannel,
    globalTransvectCoordinates] using hcongr

/-- Ordered right coordinates respect equality on the source box. -/
theorem directRightNestedCoordinates_congr (m n p : Nat) (x z : TriForm)
    (hxz : PhysicalBoxEqv m n p x z)
    (q : DirectRightNestedCGChannel m n p) :
    directRightNestedCoordinates m n p x q ≈
      directRightNestedCoordinates m n p z q := by
  exact globalTransvectCoordinates_congr m (n + p - 2 * q.k)
    (lastPairOutput n p x q.k) (lastPairOutput n p z q.k)
    (lastPairOutput_congr m n p x z hxz q.k q.k_le) q.outer

/-- **Ordered nested coordinate right inverse.** -/
theorem directRightNestedCoordinates_reconstruct (m n p : Nat)
    (c : DirectRightNestedCGChannel m n p → Q')
    (q : DirectRightNestedCGChannel m n p) :
    directRightNestedCoordinates m n p
      (directRightNestedReconstruct m n p c) q ≈ c q := by
  cases q with
  | mk k hk outer =>
      have hrel : PhysicalRectangleEqv m (n + p - 2 * k)
          (lastPairOutput n p
            (directRightNestedReconstruct m n p c) k)
          (directRightOuterReconstruct c k hk) := by
        intro i s hi hs
        exact lastPairOutput_directRightNestedReconstruct
          m n p c k hk i s hs
      have hcongr := globalTransvectCoordinates_congr
        m (n + p - 2 * k)
        (lastPairOutput n p (directRightNestedReconstruct m n p c) k)
        (directRightOuterReconstruct c k hk) hrel outer
      have hright := Q'.eqv_trans _ _ _
        (globalTransvectCoordinates_eq_hahn m (n + p - 2 * k)
          (directRightOuterReconstruct c k hk) outer)
        (globalHahnCoordinates_reconstruct m (n + p - 2 * k)
          (directRightOuterData c k hk) outer)
      exact Q'.eqv_trans _ _ _ hcongr
        (by simpa only [directRightOuterReconstruct,
          directRightOuterData] using hright)

/-- **Ordered nested semantic left inverse.** -/
theorem directRightNestedReconstruct_coordinates (m n p : Nat)
    (x : TriForm) (i j l : Nat)
    (hi : i ≤ m) (hj : j ≤ n) (hl : l ≤ p) :
    directRightNestedReconstruct m n p
      (directRightNestedCoordinates m n p x) i j l ≈ x i j l := by
  let direct : PhysicalCGChannel n p → Q' :=
    globalTransvectCoordinates n p (rightTriSlice x i)
  have hdata : ∀ q : PhysicalCGChannel n p,
      directRightInnerData (directRightNestedCoordinates m n p x) i q ≈
        direct q := by
    intro q
    have hout := globalHahnReconstruct_transvectCoordinates
      m (n + p - 2 * q.k) (lastPairOutput n p x q.k)
      i q.s hi q.s_le
    simpa only [directRightInnerData, directRightOuterReconstruct,
      directRightOuterData, directRightNestedCoordinates, direct,
      lastPairOutput, rightTriSlice, globalTransvectCoordinates] using hout
  have hcongr := globalHahnReconstruct_congr n p
    (directRightInnerData (directRightNestedCoordinates m n p x) i)
    direct hdata j l hj hl
  have hright := globalHahnReconstruct_transvectCoordinates n p
    (rightTriSlice x i) j l hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [directRightNestedReconstruct] using hcongr)
    (by simpa only [direct, rightTriSlice] using hright)

/-- The actual ordered right-associated three-factor coordinate basis. -/
def directRightNestedCGCoordinateBases (m n p : Nat) :
    CoordinateBases Unit TriForm where
  Index := fun _ => DirectRightNestedCGChannel m n p
  Rel := PhysicalBoxEqv m n p
  rel_refl := fun x i j l hi hj hl => Q'.eqv_refl _
  rel_symm := fun h i j l hi hj hl => Q'.eqv_symm (h i j l hi hj hl)
  rel_trans := fun h₁ h₂ i j l hi hj hl =>
    Q'.eqv_trans _ _ _ (h₁ i j l hi hj hl) (h₂ i j l hi hj hl)
  synth := fun _ c => directRightNestedReconstruct m n p c
  coords := fun _ x => directRightNestedCoordinates m n p x
  coords_congr := by
    intro T x z hxz q
    exact directRightNestedCoordinates_congr m n p x z hxz q
  synth_coords := by
    intro T x i j l hi hj hl
    exact directRightNestedReconstruct_coordinates
      m n p x i j l hi hj hl
  coords_synth := by
    intro T c q
    exact directRightNestedCoordinates_reconstruct m n p c q

end YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.lastPairOutput_directRightNestedReconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.lastPairOutput_congr
#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.directRightNestedCoordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.directRightNestedCoordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.directRightNestedReconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases.directRightNestedCGCoordinateBases
