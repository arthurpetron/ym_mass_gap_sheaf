/-
# Fixed-order normalization of the three nontrivial four-factor charts

The cyclic charts P1, P2, and P3 differ from the fixed ordered bracketings at
explicit reversed trivalent vertices.  This file defines the corresponding
raw ordered nested transvectants and derives their channelwise phases from the
uniform transvectant swap theorem.  No numerical recoupling value is used.
-/

import YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
import YMGap.Continuum.SU2GeneralHahnCyclicPentagon

namespace YMGap.Continuum.SU2OrderedFourChartNormalization

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases
open YMGap.Continuum.SU2OrderedRightNormalizationBridge

local infix:50 " ≈ " => Q'.eqv

/-- Physical projection commutes with exact rational scaling. -/
theorem rectProject_scale (m n : Nat) (q : Q') (x : BForm2) :
    BForm2Eqv (rectProject m n (bscale q x))
      (bscale q (rectProject m n x)) := by
  intro i j
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · have hleft := rectProject_apply_physical m n (bscale q x)
        i j hi hj
      have hright := Q'.mul_eqv_congr_left q _ _
        (rectProject_apply_physical m n x i j hi hj)
      exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)
    · have hleft := rectProject_zero_outside m n (bscale q x) i j
        (Or.inr (by omega))
      have hz := rectProject_zero_outside m n x i j (Or.inr (by omega))
      have hright := Q'.eqv_trans _ (q * 0) _
        (Q'.mul_eqv_congr_left q _ _ hz) (Q'.mul_zero_eqv q)
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  · have hleft := rectProject_zero_outside m n (bscale q x) i j
      (Or.inl (by omega))
    have hz := rectProject_zero_outside m n x i j (Or.inl (by omega))
    have hright := Q'.eqv_trans _ (q * 0) _
      (Q'.mul_eqv_congr_left q _ _ hz) (Q'.mul_zero_eqv q)
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

/-- Projected global transvectant coordinates are homogeneous of degree one. -/
theorem globalTransvectCoordinates_scale (m n : Nat) (q : Q')
    (x : BForm2) (ch : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n (bscale q x) ch ≈
      q * globalTransvectCoordinates m n x ch := by
  have hproj := transvect_congr m n ch.k (rectProject_scale m n q x) ch.s
  have hscale := transvect_scale m n ch.k q (rectProject m n x) ch.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [globalTransvectCoordinates] using hproj)
    (by simpa only [globalTransvectCoordinates] using hscale)

/-- Reversing the two inputs of an arbitrary projected binary coordinate has
the exact contraction-order phase. -/
theorem reversedGlobalCoordinates_eq_phase {m n : Nat} (x : BForm2)
    (ch : PhysicalCGChannel m n) :
    globalTransvectCoordinates n m (transpose2 x)
        (transposePhysicalChannel ch) ≈
      swapPhase ch.k * globalTransvectCoordinates m n x ch := by
  have hproj := transvect_congr n m ch.k
    (rectProject_transpose m n x) ch.s
  have hswap := transvect_transpose m n ch.k
    (rectProject m n x) ch.s
  exact Q'.eqv_trans _ _ _
    (by simpa only [globalTransvectCoordinates, transposePhysicalChannel]
      using hproj)
    (by simpa only [globalTransvectCoordinates] using hswap)

/-- At the second vertex of a left comb, put the third factor first and the
first-pair output second. -/
def orderedSecondOutput (u v w : Nat) (x : QuadForm)
    (k₁ k₂ : Nat) : BForm2 :=
  fun s r => transvect w (u + v - 2 * k₁) k₂
    (rectProject w (u + v - 2 * k₁)
      (transpose2 (firstPairOutput u v (quadSlice x r) k₁))) s

/-- The fixed ordered second vertex differs from the cyclic second vertex by
exactly its contraction-order phase. -/
theorem orderedSecondOutput_eq_phase (u v w : Nat) (x : QuadForm)
    (k₁ k₂ : Nat) :
    BForm2Eqv (orderedSecondOutput u v w x k₁ k₂)
      (bscale (swapPhase k₂) (leftTripleOrderOutput u v w x k₁ k₂)) := by
  intro s r
  let inner := firstPairOutput u v (quadSlice x r) k₁
  have hproj := transvect_congr w (u + v - 2 * k₁) k₂
    (rectProject_transpose (u + v - 2 * k₁) w inner) s
  have hswap := transvect_transpose (u + v - 2 * k₁) w k₂
    (rectProject (u + v - 2 * k₁) w inner) s
  exact Q'.eqv_trans _ _ _
    (by simpa only [orderedSecondOutput, inner] using hproj)
    (by simpa only [leftTripleOrderOutput, bscale, inner] using hswap)

/-- Channel phase for P1 = `(a (b c)) d`. -/
def orderedP1Phase {a b c d : Nat} (q : LeftComb4Channel b c a d) : Q' :=
  swapPhase q.k₂

/-- Raw fixed-ordered coordinates for P1 = `(a (b c)) d`. -/
def orderedP1Coordinates (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel b c a d) : Q' :=
  globalTransvectCoordinates
    ((b + c - 2 * q.k₁) + a - 2 * q.k₂) d
    (orderedSecondOutput b c a (presentP1 x) q.k₁ q.k₂) q.outer

/-- Exact raw P1/cyclic-P1 normalization bridge. -/
theorem orderedP1Coordinates_eq_phase (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel b c a d) :
    orderedP1Coordinates a b c d x q ≈
      orderedP1Phase q * p1Coordinates a b c d x q := by
  have hform := orderedSecondOutput_eq_phase b c a (presentP1 x)
    q.k₁ q.k₂
  have hcongr := globalTransvectCoordinates_congr
    ((b + c - 2 * q.k₁) + a - 2 * q.k₂) d
    (orderedSecondOutput b c a (presentP1 x) q.k₁ q.k₂)
    (bscale (swapPhase q.k₂)
      (leftTripleOrderOutput b c a (presentP1 x) q.k₁ q.k₂))
    (fun i j _ _ => hform i j) q.outer
  have hscale := globalTransvectCoordinates_scale
    ((b + c - 2 * q.k₁) + a - 2 * q.k₂) d
    (swapPhase q.k₂)
    (leftTripleOrderOutput b c a (presentP1 x) q.k₁ q.k₂) q.outer
  exact Q'.eqv_trans _ _ _
    (by simpa only [orderedP1Coordinates] using hcongr)
    (by simpa only [orderedP1Phase, p1Coordinates, leftComb4Coordinates]
      using hscale)

/-- Channel phase for P2 = `a ((b c) d)`. -/
def orderedP2Phase {a b c d : Nat} (q : LeftComb4Channel b c d a) : Q' :=
  swapPhase q.outer.k

/-- Raw fixed-ordered coordinates for P2 = `a ((b c) d)`. -/
def orderedP2Coordinates (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel b c d a) : Q' :=
  globalTransvectCoordinates a
    ((b + c - 2 * q.k₁) + d - 2 * q.k₂)
    (transpose2
      (leftTripleOrderOutput b c d (presentP2 x) q.k₁ q.k₂))
    (transposePhysicalChannel q.outer)

/-- Exact raw P2/cyclic-P2 normalization bridge. -/
theorem orderedP2Coordinates_eq_phase (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel b c d a) :
    orderedP2Coordinates a b c d x q ≈
      orderedP2Phase q * p2Coordinates a b c d x q := by
  have h := reversedGlobalCoordinates_eq_phase
    (leftTripleOrderOutput b c d (presentP2 x) q.k₁ q.k₂) q.outer
  simpa only [orderedP2Coordinates, orderedP2Phase, p2Coordinates,
    leftComb4Coordinates] using h

/-- Channel phase for P3 = `a (b (c d))`: both non-pair vertices reverse. -/
def orderedP3Phase {a b c d : Nat} (q : LeftComb4Channel c d b a) : Q' :=
  swapPhase q.outer.k * swapPhase q.k₂

/-- Raw fixed-ordered coordinates for P3 = `a (b (c d))`. -/
def orderedP3Coordinates (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel c d b a) : Q' :=
  globalTransvectCoordinates a
    ((c + d - 2 * q.k₁) + b - 2 * q.k₂)
    (transpose2
      (orderedSecondOutput c d b (presentP3 x) q.k₁ q.k₂))
    (transposePhysicalChannel q.outer)

/-- Exact raw P3/cyclic-P3 bridge, with the product of its two independently
derived vertex phases. -/
theorem orderedP3Coordinates_eq_phase (a b c d : Nat) (x : QuadForm)
    (q : LeftComb4Channel c d b a) :
    orderedP3Coordinates a b c d x q ≈
      orderedP3Phase q * p3Coordinates a b c d x q := by
  let orderedInner :=
    orderedSecondOutput c d b (presentP3 x) q.k₁ q.k₂
  let cyclicInner :=
    leftTripleOrderOutput c d b (presentP3 x) q.k₁ q.k₂
  have houter := reversedGlobalCoordinates_eq_phase orderedInner q.outer
  have hform := orderedSecondOutput_eq_phase c d b (presentP3 x)
    q.k₁ q.k₂
  have hcongr := globalTransvectCoordinates_congr
    ((c + d - 2 * q.k₁) + b - 2 * q.k₂) a
    orderedInner (bscale (swapPhase q.k₂) cyclicInner)
    (fun i j _ _ => hform i j) q.outer
  have hscale := globalTransvectCoordinates_scale
    ((c + d - 2 * q.k₁) + b - 2 * q.k₂) a
    (swapPhase q.k₂) cyclicInner q.outer
  have hinner := Q'.eqv_trans _ _ _ hcongr hscale
  have hmul := Q'.mul_eqv_congr_left (swapPhase q.outer.k) _ _ hinner
  exact Q'.eqv_trans _ _ _
    (by simpa only [orderedP3Coordinates, orderedInner] using houter)
    (Q'.eqv_trans _ _ _ hmul
      (by simpa only [orderedP3Phase, p3Coordinates, leftComb4Coordinates,
        cyclicInner] using
        (Q'.eqv_symm (Q'.mul_assoc_eqv (swapPhase q.outer.k)
          (swapPhase q.k₂)
          (globalTransvectCoordinates
            ((c + d - 2 * q.k₁) + b - 2 * q.k₂) a cyclicInner
            q.outer)))))

end YMGap.Continuum.SU2OrderedFourChartNormalization

#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.rectProject_scale
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.globalTransvectCoordinates_scale
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.reversedGlobalCoordinates_eq_phase
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.orderedSecondOutput_eq_phase
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.orderedP1Coordinates_eq_phase
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.orderedP2Coordinates_eq_phase
#print axioms YMGap.Continuum.SU2OrderedFourChartNormalization.orderedP3Coordinates_eq_phase
