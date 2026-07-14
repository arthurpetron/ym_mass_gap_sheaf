/-
# Constructive coordinate equivalence on every physical Hahn shell

The physical-offset column transform has a unit top row and a positive-pivot
lower-right block.  Induction on the exact shell width therefore proves that
the all-shell Hahn action has trivial kernel.  Together with the explicit
recursive right inverse, this gives a data-valued two-sided inverse and
unique source coordinates on every nonempty shell.
-/

import YMGap.Continuum.SU2GeneralHahnAllShellBasis
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnColumnElimination
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver

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
      · exact Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (ih _ _)
      · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem right_zero_of_add (a b : Q')
    (ha : a ≈ 0) (hab : a + b ≈ 0) : b ≈ 0 := by
  have hcollapse : a + b ≈ b := by
    refine Q'.eqv_trans _ (0 + b) _
      (Q'.add_eqv_congr_right _ _ _ ha) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' b)
  exact Q'.eqv_trans _ (a + b) _ (Q'.eqv_symm hcollapse) hab

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

/-- **Constructive nonsingularity on every physical shell.**  If all active
channel rows vanish, every active source coordinate vanishes. -/
theorem physicalHahn_kernel_trivial : ∀ W m n t : Nat,
    ∀ ht : t ≤ m + n, ∀ hwidth : shellWidth m n t = W,
      ∀ x : Nat → Q',
        (∀ r, r < W + 1 → physicalHahnAction m n t x r ≈ 0) →
        ∀ i, i < W + 1 → x i ≈ 0
  | 0, m, n, t, ht, hwidth, x, hrows => by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      have heval : finiteDot 1 (physicalHahnMatrix m n t 0) x ≈ x 0 :=
        finiteDot_head_unit 0 _ _
          (physical_forward_upperLeft m n t) (fun j hj => by omega)
      have hrow : finiteDot 1 (physicalHahnMatrix m n t 0) x ≈ 0 := by
        simpa only [physicalHahnAction, hwidth] using hrows 0 (by omega)
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm heval) hrow
  | W + 1, m, n, t, ht, hwidth, x, hrows => by
      let A := physicalHahnMatrix m n t
      let z := suffixCoordinates (W + 1) x
      let B := forwardColumnStep A
      have hwpos : 0 < shellWidth m n t := by rw [hwidth]; omega
      have ht' := predecessor_shell_bound m n t ht hwpos
      have hwidth' : shellWidth (m - 1) (n - 1) (t - 1) = W := by
        rw [shellWidth_pred_eq m n t ht hwpos, hwidth]
        omega
      have hBrows : ∀ r, r < (W + 1) + 1 →
          finiteDot ((W + 1) + 1) (B r) z ≈ 0 := by
        intro r hr
        have htrans := finiteDot_suffixCoordinates (W + 1) (A r) x
        have horig : finiteDot ((W + 1) + 1) (A r) x ≈ 0 := by
          simpa only [physicalHahnAction, hwidth, A] using hrows r hr
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (by simpa only [B, z] using htrans)) horig
      have htopEval : finiteDot ((W + 1) + 1) (B 0) z ≈ z 0 :=
        finiteDot_head_unit (W + 1) (B 0) z
          (by simpa only [B, A] using physical_forward_upperLeft m n t)
          (fun i hi => by
            simpa only [B, A] using physical_forward_topRow_zero m n t i)
      have hz0 : z 0 ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm htopEval) (hBrows 0 (by omega))
      let w : Nat → Q' := fun i => z (i + 1)
      have hredRows : ∀ k, k < W + 1 →
          physicalHahnAction (m - 1) (n - 1) (t - 1) w k ≈ 0 := by
        intro k hk
        let p := centralHahnRowPivot m n k
        have hp : (0 : Q') < p :=
          physicalHahnRowPivot_pos m n t k ht (by rw [hwidth]; exact hk)
        have hfirst : B (k + 1) 0 * z 0 ≈ 0 :=
          Q'.eqv_trans _ (B (k + 1) 0 * 0) _
            (Q'.mul_eqv_congr_left _ _ _ hz0) (Q'.mul_zero_eqv _)
        have hsplit := hBrows (k + 1) (by omega)
        simp only [finiteDot] at hsplit
        have htail0 : finiteDot (W + 1)
            (fun i => B (k + 1) (i + 1)) w ≈ 0 :=
          right_zero_of_add _ _ hfirst (by simpa only [w] using hsplit)
        have htailEntries : ∀ i, i < W + 1 →
            B (k + 1) (i + 1) ≈
              p * physicalHahnMatrix (m - 1) (n - 1) (t - 1) k i := by
          intro i hi
          simpa only [B, A, p, centralHahnRowPivot] using
            physical_forward_lowerRight m n t k i ht
              (by rw [hwidth]; exact hk)
              (by rw [hwidth]; exact hi)
        have htail : finiteDot (W + 1)
              (fun i => B (k + 1) (i + 1)) w ≈
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
        have hprod :
            p * physicalHahnAction (m - 1) (n - 1) (t - 1) w k ≈ 0 :=
          Q'.eqv_trans _ _ _ (Q'.eqv_symm htail) htail0
        exact Q'.mul_eqv_zero_of_pos hp hprod
      have hw : ∀ i, i < W + 1 → w i ≈ 0 :=
        physicalHahn_kernel_trivial W (m - 1) (n - 1) (t - 1)
          ht' hwidth' w hredRows
      have hz : ∀ i, i < (W + 1) + 1 → z i ≈ 0 := by
        intro i hi
        cases i with
        | zero => exact hz0
        | succ i => exact hw i (by omega)
      intro i hi
      have hdiff0 := cumulativeDifference_zero (W + 1) z hz i hi
      have hrecover := cumulativeDifference_suffix (W + 1) x i hi
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrecover) hdiff0

private def dotDifferenceLHS :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 3) (.neg (.var 4)))

private def dotDifferenceRHS :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  .add (.add (.mul (.var 0) (.var 1)) (.var 3))
    (.neg (.add (.mul (.var 0) (.var 2)) (.var 4)))

private theorem dotDifference_normal :
    YMGap.Continuum.RingNormaliser.normalize dotDifferenceLHS =
      YMGap.Continuum.RingNormaliser.normalize dotDifferenceRHS := by
  decide

private theorem dot_difference_identity (a u x U X : Q') :
    a * (u + -x) + (U + -X) ≈
      (a * u + U) + -(a * x + X) := by
  let ρ : Nat → Q' := fun i =>
    if i = 0 then a else if i = 1 then u else if i = 2 then x else
      if i = 3 then U else X
  have h := YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
    dotDifferenceLHS dotDifferenceRHS dotDifference_normal ρ
  simpa [dotDifferenceLHS, dotDifferenceRHS,
    YMGap.Continuum.RingNormaliser.eval, ρ] using h

private theorem finiteDot_difference (N : Nat)
    (row u x : Nat → Q') :
    finiteDot N row (fun i => u i + -x i) ≈
      finiteDot N row u + -(finiteDot N row x) := by
  induction N generalizing row u x with
  | zero =>
      simp only [finiteDot]
      exact Q'.eqv_symm (Q'.add_neg_self_eqv 0)
  | succ N ih =>
      simp only [finiteDot]
      refine Q'.eqv_trans _
        (row 0 * (u 0 + -x 0) +
          (finiteDot N (fun i => row (i + 1)) (fun i => u (i + 1)) +
            -(finiteDot N (fun i => row (i + 1)) (fun i => x (i + 1))))) _
        ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _) (ih _ _ _)
      · exact dot_difference_identity _ _ _ _ _

private theorem physicalHahnAction_difference (m n t r : Nat)
    (u x : Nat → Q') :
    physicalHahnAction m n t (fun i => u i + -x i) r ≈
      physicalHahnAction m n t u r +
        -(physicalHahnAction m n t x r) := by
  exact finiteDot_difference (shellWidth m n t + 1) _ _ _

/-- The active physical Hahn row map is constructively injective. -/
theorem physicalHahnAction_injective (m n t : Nat)
    (ht : t ≤ m + n) (u x : Nat → Q')
    (hrows : ∀ r, r < shellWidth m n t + 1 →
      physicalHahnAction m n t u r ≈ physicalHahnAction m n t x r) :
    ∀ i, i < shellWidth m n t + 1 → u i ≈ x i := by
  let d : Nat → Q' := fun i => u i + -x i
  have hdrows : ∀ r, r < shellWidth m n t + 1 →
      physicalHahnAction m n t d r ≈ 0 := by
    intro r hr
    refine Q'.eqv_trans _
      (physicalHahnAction m n t u r +
        -(physicalHahnAction m n t x r)) _
      (physicalHahnAction_difference m n t r u x) ?_
    refine Q'.eqv_trans _
      (physicalHahnAction m n t x r +
        -(physicalHahnAction m n t x r)) _ ?_ ?_
    · exact Q'.add_eqv_congr' (hrows r hr) (Q'.eqv_refl _)
    · exact Q'.add_neg_self_eqv _
  have hd := physicalHahn_kernel_trivial (shellWidth m n t)
    m n t ht rfl d hdrows
  intro i hi
  exact YMGap.Constructive.QPoly.q_eqv_of_sub_zero (hd i hi)

/-- Solving the active row data of a source recovers every active source
coordinate. -/
theorem allShellHahnSolve_leftInverse (m n t : Nat)
    (ht : t ≤ m + n) (x : Nat → Q') :
    ∀ i, i < shellWidth m n t + 1 →
      allShellHahnSolve m n t ht
        (fun r => physicalHahnAction m n t x r) i ≈ x i := by
  apply physicalHahnAction_injective m n t ht
  intro r hr
  exact allShellHahnSolve_rightInverse m n t ht
    (fun q => physicalHahnAction m n t x q) r hr

/-- Any active coordinate vector realizing prescribed row data agrees with
the explicit all-shell solver on every active coordinate. -/
theorem allShellHahnSolve_unique (m n t : Nat)
    (ht : t ≤ m + n) (y x : Nat → Q')
    (hrealizes : ∀ r, r < shellWidth m n t + 1 →
      physicalHahnAction m n t x r ≈ y r) :
    ∀ i, i < shellWidth m n t + 1 →
      x i ≈ allShellHahnSolve m n t ht y i := by
  apply physicalHahnAction_injective m n t ht
  intro r hr
  exact Q'.eqv_trans _ (y r) _
    (hrealizes r hr)
    (Q'.eqv_symm (allShellHahnSolve_rightInverse m n t ht y r hr))

end YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence

#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence.physicalHahn_kernel_trivial
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence.physicalHahnAction_injective
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence.allShellHahnSolve_leftInverse
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence.allShellHahnSolve_unique
