/-
# Choice-free recursive solver on every physical Hahn shell

The recursion parameter is the exact physical `shellWidth`.  A positive-width
shell has positive labels, its predecessor has width one smaller, and the
physical-offset column operation is block lower triangular.  Thus the central
recursive solver extends verbatim to every nonempty shell `t ≤ m+n`.
-/

import YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination

namespace YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnColumnElimination
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination

local infix:50 " ≈ " => Q'.eqv

/-- Finite action of the exact physical-offset shell matrix. -/
def physicalHahnAction (m n t : Nat) (x : Nat → Q') (r : Nat) : Q' :=
  finiteDot (shellWidth m n t + 1) (physicalHahnMatrix m n t r) x

/-- A positive-width shell remains nonempty after decrementing all labels. -/
theorem predecessor_shell_bound (m n t : Nat) (ht : t ≤ m + n)
    (hw : 0 < shellWidth m n t) :
    t - 1 ≤ (m - 1) + (n - 1) := by
  have hp := positive_width_labels_pos m n t ht hw
  have hchannel := channelActive_of_index m n t 1 ht (by omega)
  have htail := hchannel.2.2.2
  omega

/-- Every active nonconstant row pivot is strictly positive. -/
theorem physicalHahnRowPivot_pos (m n t k : Nat) (ht : t ≤ m + n)
    (hk : k < shellWidth m n t) :
    (0 : Q') < centralHahnRowPivot m n k := by
  have hchannel := channelActive_of_index m n t (k + 1) ht (by omega)
  have hp : 0 < (k + 1) * (m + n - k) :=
    Nat.mul_pos (Nat.succ_pos k) (by
      have hkm := hchannel.1
      omega)
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

/-- Width-indexed total recursive solver for every physical shell. -/
def physicalHahnSolve : ∀ W m n t : Nat, t ≤ m + n →
    shellWidth m n t = W → (Nat → Q') → Nat → Q'
  | 0, _, _, _, _, _, y => y
  | W + 1, m, n, t, ht, hwidth, y =>
      let A := physicalHahnMatrix m n t
      let reducedTarget : Nat → Q' := fun k =>
        if hk : k < W + 1 then
          let p := centralHahnRowPivot m n k
          let hp := physicalHahnRowPivot_pos m n t k ht (by
            rw [hwidth]
            exact hk)
          Q'.recipPos p hp * (y (k + 1) + -(A (k + 1) 0 * y 0))
        else 0
      let hwpos : 0 < shellWidth m n t := by rw [hwidth]; omega
      let ht' := predecessor_shell_bound m n t ht hwpos
      let hwidth' : shellWidth (m - 1) (n - 1) (t - 1) = W := by
        rw [shellWidth_pred_eq m n t ht hwpos, hwidth]
        omega
      let w := physicalHahnSolve W (m - 1) (n - 1) (t - 1)
        ht' hwidth' reducedTarget
      let z : Nat → Q'
        | 0 => y 0
        | i + 1 => w i
      cumulativeDifference (W + 1) z

/-- The width-indexed solver is a simultaneous right inverse on every active
physical row. -/
theorem physicalHahnSolve_rightInverse : ∀ W m n t : Nat,
    ∀ ht : t ≤ m + n, ∀ hwidth : shellWidth m n t = W,
      ∀ y : Nat → Q', ∀ r, r < W + 1 →
        physicalHahnAction m n t
          (physicalHahnSolve W m n t ht hwidth y) r ≈ y r
  | 0, m, n, t, ht, hwidth, y, r, hr => by
      have hr0 : r = 0 := by omega
      subst r
      simp only [physicalHahnAction, physicalHahnSolve]
      have hw0 : shellWidth m n t = 0 := hwidth
      simp only [hw0, finiteDot]
      refine Q'.eqv_trans _ (1 * y 0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _
            (physical_forward_upperLeft m n t))
          (Q'.eqv_refl _)
      · refine Q'.eqv_trans _ (y 0 + 0) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
  | W + 1, m, n, t, ht, hwidth, y, r, hr => by
      let A := physicalHahnMatrix m n t
      let B := forwardColumnStep A
      let reducedTarget : Nat → Q' := fun k =>
        if hk : k < W + 1 then
          let p := centralHahnRowPivot m n k
          let hp := physicalHahnRowPivot_pos m n t k ht (by
            rw [hwidth]
            exact hk)
          Q'.recipPos p hp * (y (k + 1) + -(A (k + 1) 0 * y 0))
        else 0
      let hwpos : 0 < shellWidth m n t := by rw [hwidth]; omega
      let ht' := predecessor_shell_bound m n t ht hwpos
      let hwidth' : shellWidth (m - 1) (n - 1) (t - 1) = W := by
        rw [shellWidth_pred_eq m n t ht hwpos, hwidth]
        omega
      let w := physicalHahnSolve W (m - 1) (n - 1) (t - 1)
        ht' hwidth' reducedTarget
      let z : Nat → Q'
        | 0 => y 0
        | i + 1 => w i
      have hsolve : physicalHahnSolve (W + 1) m n t ht hwidth y =
          cumulativeDifference (W + 1) z := by
        rfl
      rw [hsolve]
      change finiteDot (shellWidth m n t + 1) (A r)
        (cumulativeDifference (W + 1) z) ≈ y r
      rw [hwidth]
      have htransform := finiteDot_cumulativeDifference (W + 1) (A r) z
      refine Q'.eqv_trans _ (finiteDot ((W + 1) + 1) (B r) z) _
        (by simpa only [B] using htransform) ?_
      cases r with
      | zero =>
          have heval := finiteDot_head_unit (W + 1) (B 0) z
            (physical_forward_upperLeft m n t)
            (fun i hi => by
              simpa only [B, A] using physical_forward_topRow_zero m n t i)
          exact Q'.eqv_trans _ (z 0) _ heval (Q'.eqv_refl _)
      | succ k =>
          have hk : k < W + 1 := by omega
          let p := centralHahnRowPivot m n k
          let hp := physicalHahnRowPivot_pos m n t k ht (by
            rw [hwidth]
            exact hk)
          simp only [finiteDot]
          have htailEntries : ∀ i, i < W + 1 →
              B (k + 1) (i + 1) ≈
                p * physicalHahnMatrix (m - 1) (n - 1) (t - 1) k i := by
            intro i hi
            simpa only [B, A, p, centralHahnRowPivot] using
              physical_forward_lowerRight m n t k i ht
                (by rw [hwidth]; exact hk)
                (by rw [hwidth]; exact hi)
          have htail : finiteDot (W + 1)
                (fun i => B (k + 1) (i + 1)) (fun i => z (i + 1)) ≈
              p * physicalHahnAction (m - 1) (n - 1) (t - 1) w k := by
            refine Q'.eqv_trans _
              (finiteDot (W + 1)
                (fun i => p * physicalHahnMatrix
                  (m - 1) (n - 1) (t - 1) k i) w) _
              (finiteDot_congr _ _ _ _ _ htailEntries
                (fun i hi => Q'.eqv_refl _)) ?_
            refine Q'.eqv_trans _
              (p * finiteDot (W + 1)
                (physicalHahnMatrix (m - 1) (n - 1) (t - 1) k) w) _
              (finiteDot_scale_row _ p _ _) ?_
            unfold physicalHahnAction
            rw [hwidth']
            exact Q'.eqv_refl _
          have hih := physicalHahnSolve_rightInverse W
            (m - 1) (n - 1) (t - 1) ht' hwidth'
            reducedTarget k hk
          have htailTarget : finiteDot (W + 1)
                (fun i => B (k + 1) (i + 1)) (fun i => z (i + 1)) ≈
              y (k + 1) + -(A (k + 1) 0 * y 0) := by
            refine Q'.eqv_trans _
              (p * physicalHahnAction (m - 1) (n - 1) (t - 1) w k) _
              htail ?_
            refine Q'.eqv_trans _ (p * reducedTarget k) _
              (Q'.mul_eqv_congr_left p _ _ (by simpa only [w] using hih)) ?_
            simpa only [reducedTarget, dif_pos hk, p, hp] using
              pivot_recip_scale p
                (y (k + 1) + -(A (k + 1) 0 * y 0)) hp
          refine Q'.eqv_trans _
            (A (k + 1) 0 * y 0 +
              (y (k + 1) + -(A (k + 1) 0 * y 0))) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _))
              (by simpa only [z] using htailTarget)
          · exact residual_cancel _ _ _

/-- Public solver with the exact physical width hidden in its definition. -/
def allShellHahnSolve (m n t : Nat) (ht : t ≤ m + n)
    (y : Nat → Q') : Nat → Q' :=
  physicalHahnSolve (shellWidth m n t) m n t ht rfl y

/-- **All-shell simultaneous right inverse.** -/
theorem allShellHahnSolve_rightInverse (m n t : Nat) (ht : t ≤ m + n)
    (y : Nat → Q') (r : Nat) (hr : r < shellWidth m n t + 1) :
    physicalHahnAction m n t (allShellHahnSolve m n t ht y) r ≈ y r :=
  physicalHahnSolve_rightInverse (shellWidth m n t) m n t ht rfl y r hr

end YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver

#print axioms YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver.predecessor_shell_bound
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver.physicalHahnRowPivot_pos
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver.physicalHahnSolve_rightInverse
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver.allShellHahnSolve_rightInverse
