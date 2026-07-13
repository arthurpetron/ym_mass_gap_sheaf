/-
# Constructive cumulative-coordinate inverse to Hahn column differences

This module makes the elementary column operation from
`SU2GeneralHahnColumnElimination` fully operational on finite coordinate
vectors.  Adjacent differences act on cumulative coordinates; conversely,
suffix accumulation reconstructs every finite source vector.  Thus the
original and column-reduced matrices have exactly equivalent finite row
actions, without invoking a generic determinant or permutation sum.
-/

import YMGap.Continuum.SU2GeneralHahnColumnElimination
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2GeneralHahnCumulativeTransform

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2GeneralHahnColumnElimination

local infix:50 " ≈ " => Q'.eqv

/-- Head-recursive finite dot product over coordinates `0,...,N-1`. -/
def finiteDot : Nat → (Nat → Q') → (Nat → Q') → Q'
  | 0, _, _ => 0
  | N + 1, row, x =>
      row 0 * x 0 + finiteDot N (fun i => row (i + 1)) (fun i => x (i + 1))

/-- Finite cumulative coordinates `z` map to source coordinates
`(z₀-z₁,...,z_(N-1)-z_N,z_N)`.  The parameter `N` is the largest
coordinate, so the active vector has size `N+1`. -/
def cumulativeDifference : Nat → (Nat → Q') → Nat → Q'
  | 0, z => z
  | N + 1, z => fun i =>
      match i with
      | 0 => z 0 + -(z 1)
      | i + 1 => cumulativeDifference N (fun j => z (j + 1)) i

/-- Suffix accumulation, defined recursively on the same finite window. -/
def suffixCoordinates : Nat → (Nat → Q') → Nat → Q'
  | 0, x => x
  | N + 1, x =>
      let tail := suffixCoordinates N (fun j => x (j + 1))
      fun i =>
        match i with
        | 0 => x 0 + tail 0
        | i + 1 => tail i

private def cancelLHS : PolyExpr :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 1))

private def cancelRHS : PolyExpr := .var 0

private theorem cancel_normal : normalize cancelLHS = normalize cancelRHS := by
  decide

private theorem add_cancel_right (x y : Q') : (x + y) + -y ≈ x := by
  let ρ : Nat → Q' := fun i => if i = 0 then x else y
  have h := poly_identity_of_normal_eq cancelLHS cancelRHS cancel_normal ρ
  simpa [cancelLHS, cancelRHS, eval, ρ] using h

/-- Suffix accumulation is a right inverse to cumulative difference at every
active coordinate. -/
theorem cumulativeDifference_suffix : ∀ N : Nat, ∀ x : Nat → Q',
    ∀ i : Nat, i < N + 1 →
      cumulativeDifference N (suffixCoordinates N x) i ≈ x i
  | 0, x, i, hi => by
      have hi0 : i = 0 := by omega
      subst i
      exact Q'.eqv_refl _
  | N + 1, x, i, hi => by
      cases i with
      | zero =>
          simp only [cumulativeDifference, suffixCoordinates]
          exact add_cancel_right _ _
      | succ i =>
          simp only [cumulativeDifference, suffixCoordinates]
          exact cumulativeDifference_suffix N (fun j => x (j + 1)) i (by omega)

private def headElimLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
    (.add (.mul (.var 1) (.var 3)) (.var 4))

private def headElimRHS : PolyExpr :=
  .add
    (.mul (.var 0) (.var 2))
    (.add
      (.mul (.add (.var 1) (.neg (.var 0))) (.var 3))
      (.var 4))

private theorem headElim_normal :
    normalize headElimLHS = normalize headElimRHS := by
  decide

private theorem head_elimination (a0 a1 z0 z1 rest : Q') :
    a0 * (z0 + -z1) + (a1 * z1 + rest) ≈
      a0 * z0 + ((a1 + -a0) * z1 + rest) := by
  let ρ : Nat → Q' := fun i =>
    if i = 0 then a0 else if i = 1 then a1 else if i = 2 then z0 else
    if i = 3 then z1 else rest
  have h := poly_identity_of_normal_eq headElimLHS headElimRHS
    headElim_normal ρ
  simpa [headElimLHS, headElimRHS, eval, ρ] using h

private theorem finiteDot_congr (N : Nat)
    (row row' x x' : Nat → Q')
    (hr : ∀ i, i < N → row i ≈ row' i)
    (hx : ∀ i, i < N → x i ≈ x' i) :
    finiteDot N row x ≈ finiteDot N row' x' := by
  induction N generalizing row row' x x' with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ (row' 0 * x 0) _
          (Q'.mul_eqv_congr_right _ _ _ (hr 0 (by omega)))
          (Q'.mul_eqv_congr_left _ _ _ (hx 0 (by omega))))
        (ih _ _ _ _
          (fun i hi => hr (i + 1) (by omega))
          (fun i hi => hx (i + 1) (by omega)))

/-- **Finite column-operation identity.**  Acting on source coordinates
obtained from cumulative `z` by adjacent differences is exactly the same as
acting on `z` with the forward-column-reduced row. -/
theorem finiteDot_cumulativeDifference : ∀ N : Nat,
    ∀ row z : Nat → Q',
      finiteDot (N + 1) row (cumulativeDifference N z) ≈
        finiteDot (N + 1)
          (fun i => forwardColumnStep (fun _ c => row c) 0 i) z
  | 0, row, z => by
      simp only [finiteDot, cumulativeDifference, forwardColumnStep]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_refl _)
  | N + 1, row, z => by
      simp only [finiteDot, cumulativeDifference, forwardColumnStep]
      have ih := finiteDot_cumulativeDifference N
        (fun i => row (i + 1)) (fun i => z (i + 1))
      refine Q'.eqv_trans _
        (row 0 * (z 0 + -z 1) +
          finiteDot (N + 1)
            (fun i => forwardColumnStep
              (fun _ c => row (c + 1)) 0 i)
            (fun i => z (i + 1))) _
        (Q'.add_eqv_congr_left _ _ _ ih) ?_
      simp only [finiteDot, forwardColumnStep]
      refine Q'.eqv_trans _
        (row 0 * (z 0 + -z 1) +
          ((row 1) * z 1 +
            finiteDot N
              (fun i => row (i + 2) + -(row (i + 1)))
              (fun i => z (i + 2)))) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_refl _)
      · exact head_elimination _ _ _ _ _

/-- Every finite source vector is represented by suffix cumulative
coordinates in the column-operation identity. -/
theorem finiteDot_suffixCoordinates (N : Nat) (row x : Nat → Q') :
    finiteDot (N + 1) row x ≈
      finiteDot (N + 1)
        (fun i => forwardColumnStep (fun _ c => row c) 0 i)
        (suffixCoordinates N x) := by
  refine Q'.eqv_trans _
    (finiteDot (N + 1) row
      (cumulativeDifference N (suffixCoordinates N x))) _ ?_ ?_
  · exact Q'.eqv_symm (finiteDot_congr (N + 1) row row
      (cumulativeDifference N (suffixCoordinates N x)) x
      (fun i hi => Q'.eqv_refl _)
      (fun i hi => cumulativeDifference_suffix N x i hi))
  · exact finiteDot_cumulativeDifference N row (suffixCoordinates N x)

/-- The cumulative transform applied to an actual central Hahn row. -/
theorem centralHahnRowAction_columnStep (m n t r : Nat) (x : Nat → Q') :
    finiteDot (m + 1) (centralHahnMatrix m n t r) x ≈
      finiteDot (m + 1)
        (forwardColumnStep (centralHahnMatrix m n t) r)
        (suffixCoordinates m x) := by
  simpa only [centralHahnMatrix] using
    finiteDot_suffixCoordinates m (centralHahnMatrix m n t r) x

end YMGap.Continuum.SU2GeneralHahnCumulativeTransform

#print axioms YMGap.Continuum.SU2GeneralHahnCumulativeTransform.cumulativeDifference_suffix
#print axioms YMGap.Continuum.SU2GeneralHahnCumulativeTransform.finiteDot_cumulativeDifference
#print axioms YMGap.Continuum.SU2GeneralHahnCumulativeTransform.finiteDot_suffixCoordinates
#print axioms YMGap.Continuum.SU2GeneralHahnCumulativeTransform.centralHahnRowAction_columnStep
