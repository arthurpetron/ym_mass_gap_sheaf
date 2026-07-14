/-
# A choice-free recursive solver for the general central Hahn matrix

The forward-column form is block lower triangular.  Row zero fixes the first
cumulative coordinate.  Each lower row is residualized against column zero,
divided by its strictly positive row pivot, and passed to the reduced central
Hahn solver.  Adjacent differences then return the original source
coordinates.  This gives a data-valued simultaneous-channel right inverse.
-/

import YMGap.Continuum.SU2GeneralHahnKernelTrivial

namespace YMGap.Continuum.SU2GeneralHahnRecursiveSolver

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnColumnElimination
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnKernelTrivial

local infix:50 " ≈ " => Q'.eqv

/-- Exact row pivot created by the forward-column operation. -/
def centralHahnRowPivot (m n k : Nat) : Q' :=
  Q'.ofNat ((k + 1) * (m + n - k))

theorem centralHahnRowPivot_pos (m n k : Nat)
    (hk : k < m) :
    (0 : Q') < centralHahnRowPivot m n k := by
  have hp : 0 < (k + 1) * (m + n - k) :=
    Nat.mul_pos (Nat.succ_pos k) (by omega)
  cases hq : (k + 1) * (m + n - k) with
  | zero => omega
  | succ q =>
      unfold centralHahnRowPivot
      rw [hq]
      exact Q'.ofNat_succ_pos q

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

private theorem finiteDot_zero_row (N : Nat) (row x : Nat → Q')
    (hr : ∀ i, i < N → row i ≈ 0) :
    finiteDot N row x ≈ 0 := by
  induction N generalizing row x with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ (0 * x 0) _
            (Q'.mul_eqv_congr_right _ _ _ (hr 0 (by omega)))
            (Q'.zero_mul_eqv _))
          (ih _ _ (fun i hi => hr (i + 1) (by omega)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem finiteDot_head_unit (N : Nat) (row z : Nat → Q')
    (h0 : row 0 ≈ 1)
    (htail : ∀ i, i < N → row (i + 1) ≈ 0) :
    finiteDot (N + 1) row z ≈ z 0 := by
  simp only [finiteDot]
  refine Q'.eqv_trans _ (z 0 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ (1 * z 0) _
        (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.one_mul_eqv _))
      (finiteDot_zero_row N (fun i => row (i + 1))
        (fun i => z (i + 1)) htail)
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem finiteDot_scale_row (N : Nat) (p : Q')
    (row z : Nat → Q') :
    finiteDot N (fun i => p * row i) z ≈ p * finiteDot N row z := by
  induction N generalizing row z with
  | zero => exact Q'.eqv_symm (Q'.mul_zero_eqv p)
  | succ N ih =>
      simp only [finiteDot]
      refine Q'.eqv_trans _
        (p * (row 0 * z 0) + p * finiteDot N
          (fun i => row (i + 1)) (fun i => z (i + 1))) _ ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (ih _ _)
      · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem pivot_recip_scale (p x : Q') (hp : (0 : Q') < p) :
    p * (Q'.recipPos p hp * x) ≈ x := by
  refine Q'.eqv_trans _ ((p * Q'.recipPos p hp) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (1 * x) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv p hp)) ?_
  exact Q'.one_mul_eqv x

private def residualCancelLHS :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.var 1))
    (.add (.var 2) (.neg (.mul (.var 0) (.var 1))))

private def residualCancelRHS :
    YMGap.Continuum.RingNormaliser.PolyExpr := .var 2

private theorem residualCancel_normal :
    YMGap.Continuum.RingNormaliser.normalize residualCancelLHS =
      YMGap.Continuum.RingNormaliser.normalize residualCancelRHS := by
  decide

private theorem residual_cancel (a z y : Q') :
    a * z + (y + -(a * z)) ≈ y := by
  let ρ : Nat → Q' := fun i => if i = 0 then a else if i = 1 then z else y
  have h := YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
    residualCancelLHS residualCancelRHS residualCancel_normal ρ
  simpa [residualCancelLHS, residualCancelRHS,
    YMGap.Continuum.RingNormaliser.eval, ρ] using h

/-- Choice-free simultaneous central-shell solver.  Values outside the active
source window are irrelevant; the theorem below pins every active row. -/
def centralHahnSolve : ∀ m n t : Nat, m ≤ t → t ≤ n →
    (Nat → Q') → Nat → Q'
  | 0, _, _, _, _, y => y
  | m + 1, n, t, hmt, htn, y =>
      let A := centralHahnMatrix (m + 1) n t
      let reducedTarget : Nat → Q' := fun k =>
        if hk : k < m + 1 then
          let p := centralHahnRowPivot (m + 1) n k
          let hp := centralHahnRowPivot_pos (m + 1) n k hk
          Q'.recipPos p hp * (y (k + 1) + -(A (k + 1) 0 * y 0))
        else 0
      let w := centralHahnSolve m (n - 1) (t - 1)
        (by omega) (by omega) reducedTarget
      let z : Nat → Q'
        | 0 => y 0
        | i + 1 => w i
      cumulativeDifference (m + 1) z

/-- **Data-valued all-channel right inverse.**  On every exact central shell,
the recursively synthesized source coordinates reproduce every requested
channel row simultaneously. -/
theorem centralHahnSolve_rightInverse : ∀ m n t : Nat,
    ∀ hmt : m ≤ t, ∀ htn : t ≤ n, ∀ y : Nat → Q',
      ∀ r, r < m + 1 →
        centralHahnAction m n t (centralHahnSolve m n t hmt htn y) r ≈ y r
  | 0, n, t, hmt, htn, y, r, hr => by
      have hr0 : r = 0 := by omega
      subst r
      simp only [centralHahnAction, centralHahnSolve, finiteDot]
      refine Q'.eqv_trans _ (1 * y 0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _
            (YMGap.Continuum.SU2GeneralShellHahnMatrix.hahnEntry_zero 0 n t 0))
          (Q'.eqv_refl _)
      · refine Q'.eqv_trans _ (y 0 + 0) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
  | m + 1, n, t, hmt, htn, y, r, hr => by
      let A := centralHahnMatrix (m + 1) n t
      let B := forwardColumnStep A
      let reducedTarget : Nat → Q' := fun k =>
        if hk : k < m + 1 then
          let p := centralHahnRowPivot (m + 1) n k
          let hp := centralHahnRowPivot_pos (m + 1) n k hk
          Q'.recipPos p hp * (y (k + 1) + -(A (k + 1) 0 * y 0))
        else 0
      let w := centralHahnSolve m (n - 1) (t - 1)
        (by omega) (by omega) reducedTarget
      let z : Nat → Q'
        | 0 => y 0
        | i + 1 => w i
      have hsolve : centralHahnSolve (m + 1) n t hmt htn y =
          cumulativeDifference (m + 1) z := by
        rfl
      rw [hsolve]
      have htransform := finiteDot_cumulativeDifference (m + 1) (A r) z
      change finiteDot ((m + 1) + 1) (A r)
        (cumulativeDifference (m + 1) z) ≈ y r
      refine Q'.eqv_trans _ (finiteDot ((m + 1) + 1) (B r) z) _
        (by simpa only [B, A] using htransform) ?_
      cases r with
      | zero =>
          have heval :=
            finiteDot_head_unit (m + 1) (B 0) z
              (forwardColumnStep_upperLeft (m + 1) n t)
              (fun i hi => by
                simpa only [B, A] using
                  forwardColumnStep_topRow_zero (m + 1) n t i)
          exact Q'.eqv_trans _ (z 0) _ heval (Q'.eqv_refl _)
      | succ k =>
          have hk : k < m + 1 := by omega
          let p := centralHahnRowPivot (m + 1) n k
          let hp := centralHahnRowPivot_pos (m + 1) n k hk
          simp only [finiteDot]
          have htailEntries : ∀ i, i < m + 1 →
              B (k + 1) (i + 1) ≈
                p * centralHahnMatrix m (n - 1) (t - 1) k i := by
            intro i hi
            simpa only [B, A, p, centralHahnRowPivot,
              show m + 1 - 1 = m by omega] using
              forwardColumnStep_lowerRight (m + 1) n t k i hmt htn hk hi
          have htail : finiteDot (m + 1)
                (fun i => B (k + 1) (i + 1)) (fun i => z (i + 1)) ≈
              p * centralHahnAction m (n - 1) (t - 1) w k := by
            refine Q'.eqv_trans _
              (finiteDot (m + 1)
                (fun i => p * centralHahnMatrix m (n - 1) (t - 1) k i) w) _
              (finiteDot_congr _ _ _ _ _ htailEntries
                (fun i hi => by exact Q'.eqv_refl _)) ?_
            exact finiteDot_scale_row _ p _ _
          have hih := centralHahnSolve_rightInverse m (n - 1) (t - 1)
            (by omega) (by omega) reducedTarget k hk
          have htailTarget : finiteDot (m + 1)
                (fun i => B (k + 1) (i + 1)) (fun i => z (i + 1)) ≈
              y (k + 1) + -(A (k + 1) 0 * y 0) := by
            refine Q'.eqv_trans _
              (p * centralHahnAction m (n - 1) (t - 1) w k) _ htail ?_
            refine Q'.eqv_trans _ (p * reducedTarget k) _
              (Q'.mul_eqv_congr_left p _ _ (by simpa only [w] using hih)) ?_
            simpa only [reducedTarget, dif_pos hk, p, hp] using
              pivot_recip_scale p (y (k + 1) + -(A (k + 1) 0 * y 0)) hp
          refine Q'.eqv_trans _
            (A (k + 1) 0 * y 0 +
              (y (k + 1) + -(A (k + 1) 0 * y 0))) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _))
              (by simpa only [z] using htailTarget)
          · exact residual_cancel _ _ _

end YMGap.Continuum.SU2GeneralHahnRecursiveSolver

#print axioms YMGap.Continuum.SU2GeneralHahnRecursiveSolver.centralHahnRowPivot_pos
#print axioms YMGap.Continuum.SU2GeneralHahnRecursiveSolver.centralHahnSolve_rightInverse
