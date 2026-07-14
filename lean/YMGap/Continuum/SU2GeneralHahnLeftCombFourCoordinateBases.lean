/-
# A constructive four-factor left-comb CG coordinate basis

The certified three-factor basis composes once more with the fourth leg.  The
dependent channel records the first two contraction orders and a final
physical CG channel.  All coordinates are actual projected nested
transvectants, and the explicit three-level reconstruction is inverse in both
directions on the complete four-factor coefficient box.
-/

import YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient tensor of four binary forms. -/
abbrev QuadForm : Type := Nat → Nat → Nat → Nat → Q'

/-- Equality on the complete physical four-factor coefficient box. -/
def PhysicalQuadBoxEqv (a b c d : Nat) (x z : QuadForm) : Prop :=
  ∀ i j l r, i ≤ a → j ≤ b → l ≤ c → r ≤ d →
    x i j l r ≈ z i j l r

/-- Congruence of one reconstructed outer tensor under pointwise nested
channel equivalence. -/
theorem leftOuterReconstruct_congr {a b c : Nat}
    (u v : LeftNestedCGChannel a b c → Q')
    (huv : ∀ q, u q ≈ v q)
    (k : Nat) (hk : k ≤ min a b) (s l : Nat)
    (hs : s ≤ a + b - 2 * k) (hl : l ≤ c) :
    leftOuterReconstruct u k hk s l ≈ leftOuterReconstruct v k hk s l := by
  apply globalHahnReconstruct_congr
  intro q
  exact huv { k := k, k_le := hk, outer := q }
  · exact hs
  · exact hl

/-- The complete left-nested reconstruction respects pointwise equivalence
of dependent channel data. -/
theorem leftNestedReconstruct_congr (a b c : Nat)
    (u v : LeftNestedCGChannel a b c → Q')
    (huv : ∀ q, u q ≈ v q) :
    PhysicalBoxEqv a b c
      (leftNestedReconstruct a b c u) (leftNestedReconstruct a b c v) := by
  intro i j l hi hj hl
  apply globalHahnReconstruct_congr
  intro q
  exact leftOuterReconstruct_congr u v huv q.k q.k_le q.s l q.s_le hl
  · exact hi
  · exact hj

/-- A left-comb four-factor channel records the first pair order, the order
coupling its output with `c`, and the final physical channel with `d`. -/
structure LeftComb4Channel (a b c d : Nat) where
  k₁ : Nat
  k₁_le : k₁ ≤ min a b
  k₂ : Nat
  k₂_le : k₂ ≤ min (a + b - 2 * k₁) c
  outer : PhysicalCGChannel
    ((a + b - 2 * k₁) + c - 2 * k₂) d

/-- Fix the fourth coefficient and view a four-form as a three-form. -/
def quadSlice (x : QuadForm) (r : Nat) : TriForm :=
  fun i j l => x i j l r

/-- The output form at fixed first and second contraction orders, still
tensored with the fourth input coefficient. -/
def leftTripleOrderOutput (a b c : Nat) (x : QuadForm)
    (k₁ k₂ : Nat) : BForm2 :=
  fun s r => transvect (a + b - 2 * k₁) c k₂
    (rectProject (a + b - 2 * k₁) c
      (firstPairOutput a b (quadSlice x r) k₁)) s

/-- Extract the final-channel data at fixed first two orders. -/
def quadOuterData {a b c d : Nat}
    (u : LeftComb4Channel a b c d → Q')
    (k₁ : Nat) (hk₁ : k₁ ≤ min a b)
    (k₂ : Nat) (hk₂ : k₂ ≤ min (a + b - 2 * k₁) c) :
    PhysicalCGChannel ((a + b - 2 * k₁) + c - 2 * k₂) d → Q' :=
  fun q => u ⟨k₁, hk₁, k₂, hk₂, q⟩

/-- Reconstruct the final output/fourth-leg tensor at fixed first orders. -/
def quadOuterReconstruct {a b c d : Nat}
    (u : LeftComb4Channel a b c d → Q')
    (k₁ : Nat) (hk₁ : k₁ ≤ min a b)
    (k₂ : Nat) (hk₂ : k₂ ≤ min (a + b - 2 * k₁) c) :
    BForm2 :=
  globalHahnReconstruct ((a + b - 2 * k₁) + c - 2 * k₂) d
    (quadOuterData u k₁ hk₁ k₂ hk₂)

/-- Repackage all reconstructed final tensors as the full three-factor
dependent data at a fixed fourth coefficient. -/
def quadInnerData {a b c d : Nat}
    (u : LeftComb4Channel a b c d → Q') (r : Nat) :
    LeftNestedCGChannel a b c → Q' :=
  fun q => quadOuterReconstruct u q.k q.k_le q.outer.k q.outer.k_le
    q.outer.s r

/-- Explicit synthesis for the four-factor left comb. -/
def leftComb4Reconstruct (a b c d : Nat)
    (u : LeftComb4Channel a b c d → Q') : QuadForm :=
  fun i j l r => leftNestedReconstruct a b c (quadInnerData u r) i j l

/-- Actual projected nested-transvectant coordinates of the four-factor left
comb. -/
def leftComb4Coordinates (a b c d : Nat) (x : QuadForm) :
    LeftComb4Channel a b c d → Q' :=
  fun q => globalTransvectCoordinates
    ((a + b - 2 * q.k₁) + c - 2 * q.k₂) d
    (leftTripleOrderOutput a b c x q.k₁ q.k₂) q.outer

private def secondChannel (a b c k₁ k₂ s : Nat)
    (hk₁ : k₁ ≤ min a b)
    (hk₂ : k₂ ≤ min (a + b - 2 * k₁) c)
    (hs : s ≤ (a + b - 2 * k₁) + c - 2 * k₂) :
    LeftNestedCGChannel a b c :=
  { k := k₁
    k_le := hk₁
    outer := { k := k₂, k_le := hk₂, s := s, s_le := hs } }

/-- After full synthesis, the fixed-order triple output is the corresponding
reconstructed final tensor. -/
theorem leftTripleOrderOutput_reconstruct (a b c d : Nat)
    (u : LeftComb4Channel a b c d → Q')
    (k₁ : Nat) (hk₁ : k₁ ≤ min a b)
    (k₂ : Nat) (hk₂ : k₂ ≤ min (a + b - 2 * k₁) c)
    (s r : Nat)
    (hs : s ≤ (a + b - 2 * k₁) + c - 2 * k₂) :
    leftTripleOrderOutput a b c (leftComb4Reconstruct a b c d u)
        k₁ k₂ s r ≈
      quadOuterReconstruct u k₁ hk₁ k₂ hk₂ s r := by
  let q := secondChannel a b c k₁ k₂ s hk₁ hk₂ hs
  have hright := leftNestedCoordinates_reconstruct a b c
    (quadInnerData u r) q
  simpa only [leftTripleOrderOutput, leftComb4Reconstruct, quadSlice,
    leftNestedCoordinates, quadInnerData, q, secondChannel,
    globalTransvectCoordinates] using hright

/-- Fixed-order triple output respects equality of the physical four-box. -/
theorem leftTripleOrderOutput_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (k₁ : Nat) (hk₁ : k₁ ≤ min a b)
    (k₂ : Nat) (hk₂ : k₂ ≤ min (a + b - 2 * k₁) c) :
    PhysicalRectangleEqv ((a + b - 2 * k₁) + c - 2 * k₂) d
      (leftTripleOrderOutput a b c x k₁ k₂)
      (leftTripleOrderOutput a b c z k₁ k₂) := by
  intro s r hs hr
  let q := secondChannel a b c k₁ k₂ s hk₁ hk₂ hs
  have hslice : PhysicalBoxEqv a b c (quadSlice x r) (quadSlice z r) := by
    intro i j l hi hj hl
    exact hxz i j l r hi hj hl hr
  have hcongr := leftNestedCoordinates_congr a b c
    (quadSlice x r) (quadSlice z r) hslice q
  simpa only [leftTripleOrderOutput, leftNestedCoordinates, quadSlice,
    q, secondChannel, globalTransvectCoordinates] using hcongr

/-- Four-factor left-comb coordinates respect source-box equality. -/
theorem leftComb4Coordinates_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : LeftComb4Channel a b c d) :
    leftComb4Coordinates a b c d x q ≈
      leftComb4Coordinates a b c d z q := by
  exact globalTransvectCoordinates_congr
    ((a + b - 2 * q.k₁) + c - 2 * q.k₂) d
    (leftTripleOrderOutput a b c x q.k₁ q.k₂)
    (leftTripleOrderOutput a b c z q.k₁ q.k₂)
    (leftTripleOrderOutput_congr a b c d x z hxz
      q.k₁ q.k₁_le q.k₂ q.k₂_le) q.outer

/-- **Four-factor coordinate right inverse.** -/
theorem leftComb4Coordinates_reconstruct (a b c d : Nat)
    (u : LeftComb4Channel a b c d → Q')
    (q : LeftComb4Channel a b c d) :
    leftComb4Coordinates a b c d (leftComb4Reconstruct a b c d u) q ≈
      u q := by
  cases q with
  | mk k₁ hk₁ k₂ hk₂ outer =>
      have hrel : PhysicalRectangleEqv
          ((a + b - 2 * k₁) + c - 2 * k₂) d
          (leftTripleOrderOutput a b c (leftComb4Reconstruct a b c d u)
            k₁ k₂)
          (quadOuterReconstruct u k₁ hk₁ k₂ hk₂) := by
        intro s r hs hr
        exact leftTripleOrderOutput_reconstruct a b c d u
          k₁ hk₁ k₂ hk₂ s r hs
      have hcongr := globalTransvectCoordinates_congr
        ((a + b - 2 * k₁) + c - 2 * k₂) d
        (leftTripleOrderOutput a b c (leftComb4Reconstruct a b c d u)
          k₁ k₂)
        (quadOuterReconstruct u k₁ hk₁ k₂ hk₂) hrel outer
      have hright := Q'.eqv_trans _ _ _
        (globalTransvectCoordinates_eq_hahn
          ((a + b - 2 * k₁) + c - 2 * k₂) d
          (quadOuterReconstruct u k₁ hk₁ k₂ hk₂) outer)
        (globalHahnCoordinates_reconstruct
          ((a + b - 2 * k₁) + c - 2 * k₂) d
          (quadOuterData u k₁ hk₁ k₂ hk₂) outer)
      exact Q'.eqv_trans _ _ _ hcongr
        (by simpa only [quadOuterReconstruct, quadOuterData] using hright)

/-- **Four-factor semantic left inverse.** -/
theorem leftComb4Reconstruct_coordinates (a b c d : Nat) (x : QuadForm)
    (i j l r : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (hl : l ≤ c) (hr : r ≤ d) :
    leftComb4Reconstruct a b c d (leftComb4Coordinates a b c d x)
        i j l r ≈ x i j l r := by
  let direct : LeftNestedCGChannel a b c → Q' :=
    leftNestedCoordinates a b c (quadSlice x r)
  have hdata : ∀ q : LeftNestedCGChannel a b c,
      quadInnerData (leftComb4Coordinates a b c d x) r q ≈ direct q := by
    intro q
    have hout := globalHahnReconstruct_transvectCoordinates
      ((a + b - 2 * q.k) + c - 2 * q.outer.k) d
      (leftTripleOrderOutput a b c x q.k q.outer.k)
      q.outer.s r q.outer.s_le hr
    simpa only [quadInnerData, quadOuterReconstruct, quadOuterData,
      leftComb4Coordinates, direct, leftTripleOrderOutput,
      leftNestedCoordinates, quadSlice, globalTransvectCoordinates] using hout
  have hcongr := leftNestedReconstruct_congr a b c
    (quadInnerData (leftComb4Coordinates a b c d x) r) direct hdata
    i j l hi hj hl
  have hright := leftNestedReconstruct_coordinates a b c
    (quadSlice x r) i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [leftComb4Reconstruct] using hcongr)
    (by simpa only [direct, quadSlice] using hright)

/-- The actual four-factor left-comb coordinate basis. -/
def leftComb4CoordinateBases (a b c d : Nat) :
    CoordinateBases Unit QuadForm where
  Index := fun _ => LeftComb4Channel a b c d
  Rel := PhysicalQuadBoxEqv a b c d
  rel_refl := fun x i j l r hi hj hl hr => Q'.eqv_refl _
  rel_symm := fun h i j l r hi hj hl hr =>
    Q'.eqv_symm (h i j l r hi hj hl hr)
  rel_trans := fun h₁ h₂ i j l r hi hj hl hr =>
    Q'.eqv_trans _ _ _ (h₁ i j l r hi hj hl hr)
      (h₂ i j l r hi hj hl hr)
  synth := fun _ u => leftComb4Reconstruct a b c d u
  coords := fun _ x => leftComb4Coordinates a b c d x
  coords_congr := by
    intro T x z hxz q
    exact leftComb4Coordinates_congr a b c d x z hxz q
  synth_coords := by
    intro T x i j l r hi hj hl hr
    exact leftComb4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
  coords_synth := by
    intro T u q
    exact leftComb4Coordinates_reconstruct a b c d u q

end YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftNestedReconstruct_congr
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftTripleOrderOutput_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftTripleOrderOutput_congr
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftComb4Coordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftComb4Coordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftComb4Reconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases.leftComb4CoordinateBases
