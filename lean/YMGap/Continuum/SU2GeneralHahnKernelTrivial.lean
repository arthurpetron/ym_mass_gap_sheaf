/-
# Constructive kernel triviality of every central Hahn matrix

The cumulative column transform makes the central Hahn matrix block lower
triangular.  Its top row forces the first cumulative coordinate to vanish;
each remaining row is a strictly positive pivot times the corresponding row
of the reduced central Hahn matrix.  Induction therefore proves that the
actual finite matrix has trivial kernel on every central shell.
-/

import YMGap.Continuum.SU2GeneralHahnCumulativeTransform

namespace YMGap.Continuum.SU2GeneralHahnKernelTrivial

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnColumnElimination
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform

local infix:50 " ≈ " => Q'.eqv

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
      · exact Q'.add_eqv_congr'
          (Q'.mul_assoc_eqv p (row 0) (z 0))
          (ih _ _)
      · exact Q'.eqv_symm (Q'.mul_add_eqv p _ _)

private theorem right_zero_of_add (a b : Q')
    (ha : a ≈ 0) (hab : a + b ≈ 0) : b ≈ 0 := by
  have hcollapse : a + b ≈ b := by
    refine Q'.eqv_trans _ (0 + b) _
      (Q'.add_eqv_congr_right _ _ _ ha) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' b)
  exact Q'.eqv_trans _ (a + b) _ (Q'.eqv_symm hcollapse) hab

private theorem ofNat_pos_of_pos (a : Nat) (ha : 0 < a) :
    (0 : Q') < Q'.ofNat a := by
  cases a with
  | zero => omega
  | succ a => exact Q'.ofNat_succ_pos a

private theorem cumulativeDifference_zero (N : Nat) (z : Nat → Q')
    (hz : ∀ i, i < N + 1 → z i ≈ 0) :
    ∀ i, i < N + 1 → cumulativeDifference N z i ≈ 0 := by
  induction N generalizing z with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      exact hz 0 (by omega)
  | succ N ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [cumulativeDifference]
          refine Q'.eqv_trans _ (0 + -0) _
            (Q'.add_eqv_congr'
              (hz 0 (by omega)) (Q'.neg_eqv_congr _ _ (hz 1 (by omega)))) ?_
          exact Q'.eqv_refl _
      | succ i =>
          simp only [cumulativeDifference]
          exact ih (fun j => z (j + 1))
            (fun j hj => hz (j + 1) (by omega)) i (by omega)

/-- The actual central Hahn matrix acts on a finite source vector. -/
def centralHahnAction (m n t : Nat) (x : Nat → Q') (r : Nat) : Q' :=
  finiteDot (m + 1) (centralHahnMatrix m n t r) x

/-- **Constructive nonsingularity of the general central Hahn matrix.**  If
all `m+1` channel rows vanish on a source vector supported on the enumerated
coordinates `0,...,m`, then every one of those source coordinates vanishes.
The only shell guards are the exact central range `m <= t <= n`. -/
theorem centralHahn_kernel_trivial : ∀ m n t : Nat,
    m ≤ t → t ≤ n → ∀ x : Nat → Q',
      (∀ r, r < m + 1 → centralHahnAction m n t x r ≈ 0) →
      ∀ i, i < m + 1 → x i ≈ 0
  | 0, n, t, hmt, htn, x, hrows => by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      let row := forwardColumnStep (centralHahnMatrix 0 n t) 0
      have htrans := centralHahnRowAction_columnStep 0 n t 0 x
      have hrow : finiteDot 1 row (suffixCoordinates 0 x) ≈ 0 :=
        Q'.eqv_trans _ (centralHahnAction 0 n t x 0) _
          (Q'.eqv_symm htrans) (hrows 0 (by omega))
      have heval : finiteDot 1 row (suffixCoordinates 0 x) ≈
          (suffixCoordinates 0 x) 0 :=
        finiteDot_head_unit 0 row _
          (forwardColumnStep_upperLeft 0 n t) (fun i hi => by omega)
      have hz : (suffixCoordinates 0 x) 0 ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm heval) hrow
      simpa only [suffixCoordinates] using hz
  | m + 1, n, t, hmt, htn, x, hrows => by
      let z := suffixCoordinates (m + 1) x
      let B := forwardColumnStep (centralHahnMatrix (m + 1) n t)
      have hBrows : ∀ r, r < (m + 1) + 1 →
          finiteDot ((m + 1) + 1) (B r) z ≈ 0 := by
        intro r hr
        have htrans := centralHahnRowAction_columnStep (m + 1) n t r x
        exact Q'.eqv_trans _ (centralHahnAction (m + 1) n t x r) _
          (Q'.eqv_symm (by simpa only [z, B] using htrans)) (hrows r hr)
      have htopEval : finiteDot ((m + 1) + 1) (B 0) z ≈ z 0 :=
        finiteDot_head_unit (m + 1) (B 0) z
          (forwardColumnStep_upperLeft (m + 1) n t)
          (fun i hi => by
            simpa only [B] using forwardColumnStep_topRow_zero (m + 1) n t i)
      have hz0 : z 0 ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm htopEval) (hBrows 0 (by omega))
      let w : Nat → Q' := fun i => z (i + 1)
      have hredRows : ∀ k, k < m + 1 →
          centralHahnAction m (n - 1) (t - 1) w k ≈ 0 := by
        intro k hk
        let pNat := (k + 1) * ((m + 1) + n - k)
        let p := Q'.ofNat pNat
        have hpNat : 0 < pNat := by
          dsimp only [pNat]
          exact Nat.mul_pos (Nat.succ_pos k) (by omega)
        have hp : (0 : Q') < p := by
          exact ofNat_pos_of_pos pNat hpNat
        have hfirst : B (k + 1) 0 * z 0 ≈ 0 :=
          Q'.eqv_trans _ (B (k + 1) 0 * 0) _
            (Q'.mul_eqv_congr_left _ _ _ hz0) (Q'.mul_zero_eqv _)
        have hsplit := hBrows (k + 1) (by omega)
        simp only [finiteDot] at hsplit
        have htail0 : finiteDot (m + 1)
            (fun i => B (k + 1) (i + 1)) w ≈ 0 := by
          exact right_zero_of_add _ _ hfirst (by simpa only [w] using hsplit)
        have htailEntries : ∀ i, i < m + 1 →
            B (k + 1) (i + 1) ≈
              p * centralHahnMatrix m (n - 1) (t - 1) k i := by
          intro i hi
          simpa only [B, p, pNat,
            show m + 1 - 1 = m by omega] using
            forwardColumnStep_lowerRight (m + 1) n t k i hmt htn hk hi
        have htail : finiteDot (m + 1)
              (fun i => B (k + 1) (i + 1)) w ≈
            p * centralHahnAction m (n - 1) (t - 1) w k := by
          refine Q'.eqv_trans _
            (finiteDot (m + 1)
              (fun i => p * centralHahnMatrix m (n - 1) (t - 1) k i) w) _
            (finiteDot_congr _ _ _ _ _ htailEntries
              (fun i hi => Q'.eqv_refl _)) ?_
          exact finiteDot_scale_row _ p _ _
        have hprod : p * centralHahnAction m (n - 1) (t - 1) w k ≈ 0 :=
          Q'.eqv_trans _ _ _ (Q'.eqv_symm htail) htail0
        exact Q'.mul_eqv_zero_of_pos hp hprod
      have hw : ∀ i, i < m + 1 → w i ≈ 0 :=
        centralHahn_kernel_trivial m (n - 1) (t - 1)
          (by omega) (by omega) w hredRows
      have hz : ∀ i, i < (m + 1) + 1 → z i ≈ 0 := by
        intro i hi
        cases i with
        | zero => exact hz0
        | succ i => exact hw i (by omega)
      intro i hi
      have hdiff0 := cumulativeDifference_zero (m + 1) z hz i hi
      have hrecover := cumulativeDifference_suffix (m + 1) x i hi
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrecover) hdiff0

end YMGap.Continuum.SU2GeneralHahnKernelTrivial

#print axioms YMGap.Continuum.SU2GeneralHahnKernelTrivial.centralHahn_kernel_trivial
