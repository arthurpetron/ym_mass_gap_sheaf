/-
# Constructive coordinate equivalence for every central Hahn shell

The explicit recursive solver is already a simultaneous right inverse.  This
module combines finite-dot linearity with central-kernel triviality to prove
injectivity, hence a pointwise left inverse and unique coordinate synthesis.
-/

import YMGap.Continuum.SU2GeneralHahnRecursiveSolver
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnKernelTrivial
open YMGap.Continuum.SU2GeneralHahnRecursiveSolver

local infix:50 " ≈ " => Q'.eqv

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

private theorem centralHahnAction_difference (m n t r : Nat)
    (u x : Nat → Q') :
    centralHahnAction m n t (fun i => u i + -x i) r ≈
      centralHahnAction m n t u r +
        -(centralHahnAction m n t x r) := by
  exact finiteDot_difference (m + 1) _ _ _

/-- The active central Hahn row map is constructively injective. -/
theorem centralHahnAction_injective (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (u x : Nat → Q')
    (hrows : ∀ r, r < m + 1 →
      centralHahnAction m n t u r ≈ centralHahnAction m n t x r) :
    ∀ i, i < m + 1 → u i ≈ x i := by
  let d : Nat → Q' := fun i => u i + -x i
  have hdrows : ∀ r, r < m + 1 →
      centralHahnAction m n t d r ≈ 0 := by
    intro r hr
    refine Q'.eqv_trans _
      (centralHahnAction m n t u r +
        -(centralHahnAction m n t x r)) _
      (centralHahnAction_difference m n t r u x) ?_
    refine Q'.eqv_trans _
      (centralHahnAction m n t x r +
        -(centralHahnAction m n t x r)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (hrows r hr)
        (Q'.eqv_refl _)
    · exact Q'.add_neg_self_eqv _
  have hd := centralHahn_kernel_trivial m n t hmt htn d hdrows
  intro i hi
  exact YMGap.Constructive.QPoly.q_eqv_of_sub_zero (hd i hi)

/-- **Data-valued two-sided coordinate inverse.**  Solving the row data of
an active source recovers every active source coordinate. -/
theorem centralHahnSolve_leftInverse (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (x : Nat → Q') :
    ∀ i, i < m + 1 →
      centralHahnSolve m n t hmt htn
        (fun r => centralHahnAction m n t x r) i ≈ x i := by
  apply centralHahnAction_injective m n t hmt htn
  intro r hr
  exact centralHahnSolve_rightInverse m n t hmt htn
    (fun q => centralHahnAction m n t x q) r hr

/-- Any active coordinate vector realizing prescribed row data agrees with
the explicit recursive solver on every active coordinate. -/
theorem centralHahnSolve_unique (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (y x : Nat → Q')
    (hrealizes : ∀ r, r < m + 1 →
      centralHahnAction m n t x r ≈ y r) :
    ∀ i, i < m + 1 →
      x i ≈ centralHahnSolve m n t hmt htn y i := by
  apply centralHahnAction_injective m n t hmt htn
  intro r hr
  exact Q'.eqv_trans _ (y r) _
    (hrealizes r hr)
    (Q'.eqv_symm
      (centralHahnSolve_rightInverse m n t hmt htn y r hr))

end YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence

#print axioms YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence.centralHahnAction_injective
#print axioms YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence.centralHahnSolve_leftInverse
#print axioms YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence.centralHahnSolve_unique
