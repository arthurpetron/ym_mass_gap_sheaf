/-
# Three independent rational color copies

This leaf constructs three disjoint-support copies of arbitrary finite rational
rows inside one larger finite product-Gaussian evaluator. Their computed Gram
is exactly color-diagonal, so the checked radial covariance trace contraction
specializes to

  Cov(S_B^2,S_D) = 60 * sigma * rho^2,

with sigma and rho the literal one-color computed row norm and cross Gram.
No independence, covariance-matrix, nondegeneracy, square-root or Gaussian
pullback premise is assumed: independence is realized by disjoint coordinate
blocks. Zero-dimensional and zero-row cases are included.

Consumer: the three-color factor in the retained trace-source quartic from the
adaptive-score audit. Actual transverse-mode rows, their CReal approximation
moduli, compact-Haar comparison and the ORIGINAL interacting estimate remain
separate obligations.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem qListSum_append : ∀ first second : List Q',
    qListSum (first ++ second) ≈ qListSum first + qListSum second
  | [], second => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (qListSum second)))
  | value :: first, second =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left value _ _ (qListSum_append first second))
        (Q'.eqv_symm (Q'.add_assoc_eqv value (qListSum first) (qListSum second)))

private theorem qListSum_congr {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≈ g i) :
    qListSum (ids.map f) ≈ qListSum (ids.map g) := by
  induction ids with
  | nil => exact Q'.eqv_refl _
  | cons i ids ih =>
      exact Q'.add_eqv_congr' (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Concatenate two coefficient rows at the coordinate boundary `leftCount`. -/
def appendRow (leftCount : Nat) (left right : Nat → Q') (coordinate : Nat) : Q' :=
  if coordinate < leftCount then left coordinate else right (coordinate - leftCount)

/-- Computed Grams split exactly across concatenated coordinate blocks. -/
theorem finiteRowGram_append (leftCount rightCount : Nat)
    (bLeft bRight dLeft dRight : Nat → Q') :
    finiteRowGram (leftCount + rightCount)
      (appendRow leftCount bLeft bRight) (appendRow leftCount dLeft dRight) ≈
      finiteRowGram leftCount bLeft dLeft + finiteRowGram rightCount bRight dRight := by
  unfold finiteRowGram
  rw [List.range_add, List.map_append]
  refine Q'.eqv_trans _ _ _ (qListSum_append _ _) ?_
  exact Q'.add_eqv_congr'
    (qListSum_congr (List.range leftCount) _ _ (fun i hi => by
      have hi' : i < leftCount := List.mem_range.mp hi
      simp only [appendRow, if_pos hi']
      exact Q'.eqv_refl _))
    (by
      simp only [List.map_map]
      exact qListSum_congr (List.range rightCount) _ _ (fun i _ => by
        have hnot : ¬ leftCount + i < leftCount := by omega
        simp only [Function.comp_apply, appendRow, if_neg hnot, Nat.add_sub_cancel_left]
        exact Q'.eqv_refl _))

private def zeroRow : Nat → Q' := fun _ => 0

private def selectedRow : Bool → (Nat → Q') → Nat → Q'
  | true, row => row
  | false, _ => zeroRow

private theorem finiteRowGram_zero_left (N : Nat) (row : Nat → Q') :
    finiteRowGram N zeroRow row ≈ 0 := by
  unfold finiteRowGram
  induction List.range N with
  | nil => exact Q'.eqv_refl _
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.zero_mul_eqv (row i)) ih)
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem finiteRowGram_zero_right (N : Nat) (row : Nat → Q') :
    finiteRowGram N row zeroRow ≈ 0 := by
  unfold finiteRowGram
  induction List.range N with
  | nil => exact Q'.eqv_refl _
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv (row i)) ih)
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem finiteRowGram_threeBlock (N : Nat)
    (b0 b1 b2 d0 d1 d2 : Nat → Q') :
    finiteRowGram (N + (N + N))
      (appendRow N b0 (appendRow N b1 b2))
      (appendRow N d0 (appendRow N d1 d2)) ≈
      finiteRowGram N b0 d0 +
        (finiteRowGram N b1 d1 + finiteRowGram N b2 d2) := by
  exact Q'.eqv_trans _ _ _
    (finiteRowGram_append N (N + N) b0 (appendRow N b1 b2) d0 (appendRow N d1 d2))
    (Q'.add_eqv_congr_left _ _ _ (finiteRowGram_append N N b1 b2 d1 d2))

/-- Three disjoint-support copies of one finite row. Colors outside `0,1,2`
are represented by the zero row. -/
def threeColorRows (N : Nat) (row : Nat → Q') : Nat → Nat → Q'
  | 0 => appendRow N row (appendRow N zeroRow zeroRow)
  | 1 => appendRow N zeroRow (appendRow N row zeroRow)
  | 2 => appendRow N zeroRow (appendRow N zeroRow row)
  | _ => zeroRow

private theorem selectedGram (N : Nat) (b d : Nat → Q')
    (bSelected dSelected : Bool) :
    finiteRowGram N (selectedRow bSelected b) (selectedRow dSelected d) ≈
      if bSelected && dSelected then finiteRowGram N b d else 0 := by
  cases bSelected <;> cases dSelected
  · exact finiteRowGram_zero_left N zeroRow
  · exact finiteRowGram_zero_left N d
  · exact finiteRowGram_zero_right N b
  · exact Q'.eqv_refl _

private theorem finiteRowGram_threeBlock_selected (N : Nat) (b d : Nat → Q')
    (b0 b1 b2 d0 d1 d2 : Bool) :
    finiteRowGram (N + (N + N))
      (appendRow N (selectedRow b0 b)
        (appendRow N (selectedRow b1 b) (selectedRow b2 b)))
      (appendRow N (selectedRow d0 d)
        (appendRow N (selectedRow d1 d) (selectedRow d2 d))) ≈
      (if b0 && d0 then finiteRowGram N b d else 0) +
        ((if b1 && d1 then finiteRowGram N b d else 0) +
          (if b2 && d2 then finiteRowGram N b d else 0)) := by
  exact Q'.eqv_trans _ _ _
    (finiteRowGram_threeBlock N _ _ _ _ _ _)
    (Q'.add_eqv_congr'
      (selectedGram N b d b0 d0)
      (Q'.add_eqv_congr'
        (selectedGram N b d b1 d1)
        (selectedGram N b d b2 d2)))

private theorem first_block_value (value : Q') :
    value + (0 + 0) ≈ value :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.add (.const 0) (.const 0))) (.var 0)
    (by decide) (fun _ => value)

private theorem second_block_value (value : Q') :
    0 + (value + 0) ≈ value :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.add (.var 0) (.const 0))) (.var 0)
    (by decide) (fun _ => value)

private theorem third_block_value (value : Q') :
    0 + (0 + value) ≈ value :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.add (.const 0) (.var 0))) (.var 0)
    (by decide) (fun _ => value)

private theorem no_block_value : (0 : Q') + (0 + 0) ≈ 0 :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.add (.const 0) (.const 0))) (.const 0)
    (by decide) (fun _ => (0 : Q'))

/-- The constructed three-color Gram is exactly diagonal in color. -/
theorem finiteRowGram_threeColorRows (N i j : Nat) (b d : Nat → Q')
    (hi : i < 3) (hj : j < 3) :
    finiteRowGram (N + (N + N)) (threeColorRows N b i) (threeColorRows N d j) ≈
      if i = j then finiteRowGram N b d else 0 := by
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hiCases with rfl | rfl | rfl
  · rcases hjCases with rfl | rfl | rfl
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d true false false true false false)
        (first_block_value (finiteRowGram N b d))
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d true false false false true false)
        no_block_value
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d true false false false false true)
        no_block_value
  · rcases hjCases with rfl | rfl | rfl
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false true false true false false)
        no_block_value
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false true false false true false)
        (second_block_value (finiteRowGram N b d))
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false true false false false true)
        no_block_value
  · rcases hjCases with rfl | rfl | rfl
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false false true true false false)
        no_block_value
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false false true false true false)
        no_block_value
    · exact Q'.eqv_trans _ _ _
        (finiteRowGram_threeBlock_selected N b d false false true false false true)
        (third_block_value (finiteRowGram N b d))

private theorem finiteRowNorm2_eq_gram (N : Nat) (row : Nat → Q') :
    finiteRowNorm2 N row ≈ finiteRowGram N row row := by
  exact Q'.eqv_refl _

private theorem threeColorNorm (N i : Nat) (row : Nat → Q') (hi : i < 3) :
    finiteRowNorm2 (N + (N + N)) (threeColorRows N row i) ≈
      finiteRowNorm2 N row := by
  exact Q'.eqv_trans _ _ _
    (finiteRowNorm2_eq_gram _ _)
    (Q'.eqv_trans _ _ _ (finiteRowGram_threeColorRows N i i row row hi hi)
      (by
        rw [if_pos rfl]
        exact Q'.eqv_symm (finiteRowNorm2_eq_gram N row)))

private theorem sum_three_constant (value : Q') :
    qListSum ((List.range 3).map fun _ => value) ≈ 3 * value := by
  change value + (value + (value + 0)) ≈ 3 * value
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 0) (.add (.var 0) (.const 0))))
    (.mul (.const 3) (.var 0)) (by decide) (fun _ => value)

private theorem sum_three_at (i : Nat) (hi : i < 3) (value : Q') :
    qListSum ((List.range 3).map fun j => if i = j then value else 0) ≈ value := by
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hiCases with rfl | rfl | rfl
  · change value + (0 + (0 + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 0) (.add (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)
  · change 0 + (value + (0 + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.var 0) (.add (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)
  · change 0 + (0 + (value + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.const 0) (.add (.var 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)

private theorem delta_square (i j : Nat) (value : Q') :
    (if i = j then value else 0) * (if i = j then value else 0) ≈
      if i = j then value * value else 0 := by
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact Q'.eqv_refl _
  · simp only [if_neg hij]
    exact Q'.zero_mul_eqv 0

private theorem sum_three_diagonal_square (value : Q') :
    qListSum ((List.range 3).map fun i =>
      qListSum ((List.range 3).map fun j =>
        (if i = j then value else 0) * (if i = j then value else 0))) ≈
      3 * (value * value) := by
  exact Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun i _ =>
      qListSum_congr (List.range 3) _ _ (fun j _ => delta_square i j value)))
    (Q'.eqv_trans _ _ _
      (qListSum_congr (List.range 3) _ _ (fun i hi =>
        sum_three_at i (List.mem_range.mp hi) (value * value)))
      (sum_three_constant (value * value)))

private theorem delta_sandwich (i k j : Nat) (sigma rho : Q') :
    (if i = k then sigma else 0) *
        (if i = j then rho else 0) * (if k = j then rho else 0) ≈
      if i = k then (if i = j then sigma * (rho * rho) else 0) else 0 := by
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact Q'.mul_assoc_eqv sigma rho rho
    · simp only [if_neg hij]
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.const 0)) (.const 0)) (.const 0)
        (by decide) (fun _ => sigma)
  · simp only [if_neg hik]
    exact poly_identity_of_normal_eq
      (.mul (.mul (.const 0) (.var 0)) (.var 1)) (.const 0)
      (by decide) (fun | 0 => if i = j then rho else 0 | _ => if k = j then rho else 0)

private theorem sum_three_sandwich_inner (i k : Nat) (hi : i < 3)
    (sigma rho : Q') :
    qListSum ((List.range 3).map fun j =>
      (if i = k then sigma else 0) *
        (if i = j then rho else 0) * (if k = j then rho else 0)) ≈
      if i = k then sigma * (rho * rho) else 0 := by
  refine Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun j _ =>
      delta_sandwich i k j sigma rho)) ?_
  by_cases hik : i = k
  · simp only [if_pos hik]
    exact sum_three_at i hi (sigma * (rho * rho))
  · simp only [if_neg hik]
    change (0 : Q') + (0 + (0 + 0)) ≈ 0
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.const 0) (.add (.const 0) (.const 0))))
      (.const 0) (by decide) (fun _ => sigma)

private theorem sum_three_diagonal_sandwich (sigma rho : Q') :
    qListSum ((List.range 3).map fun i =>
      qListSum ((List.range 3).map fun k =>
        qListSum ((List.range 3).map fun j =>
          (if i = k then sigma else 0) *
            (if i = j then rho else 0) * (if k = j then rho else 0)))) ≈
      3 * sigma * (rho * rho) := by
  exact Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun i hi =>
      qListSum_congr (List.range 3) _ _ (fun k _ =>
        sum_three_sandwich_inner i k (List.mem_range.mp hi) sigma rho)))
    (Q'.eqv_trans _ _ _
      (qListSum_congr (List.range 3) _ _ (fun i hi =>
        sum_three_at i (List.mem_range.mp hi) (sigma * (rho * rho))))
      (Q'.eqv_trans _ _ _
        (sum_three_constant (sigma * (rho * rho)))
        (poly_identity_of_normal_eq
          (.mul (.const 3) (.mul (.var 0) (.mul (.var 1) (.var 1))))
          (.mul (.mul (.const 3) (.var 0)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => sigma | _ => rho))))

/-- The row-norm trace of the concrete three-color lift is `3*sigma`. -/
theorem finiteRowGramTrace_threeColorRows (N : Nat) (row : Nat → Q') :
    finiteRowGramTrace (N + (N + N)) 3 (threeColorRows N row) ≈
      3 * finiteRowNorm2 N row := by
  unfold finiteRowGramTrace
  exact Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun i hi =>
      threeColorNorm N i row (List.mem_range.mp hi)))
    (sum_three_constant (finiteRowNorm2 N row))

/-- The cross-Gram-square trace of the concrete three-color lift is
`3*rho^2`. -/
theorem finiteCrossGramSquareTrace_threeColorRows (N : Nat)
    (b d : Nat → Q') :
    finiteCrossGramSquareTrace (N + (N + N)) 3 3
      (threeColorRows N b) (threeColorRows N d) ≈
      3 * (finiteRowGram N b d * finiteRowGram N b d) := by
  unfold finiteCrossGramSquareTrace
  refine Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun i hi =>
      qListSum_congr (List.range 3) _ _ (fun j hj => ?_)))
    (sum_three_diagonal_square (finiteRowGram N b d))
  exact mul_congr
    (finiteRowGram_threeColorRows N i j b d
      (List.mem_range.mp hi) (List.mem_range.mp hj))
    (finiteRowGram_threeColorRows N i j b d
      (List.mem_range.mp hi) (List.mem_range.mp hj))

/-- The Gram-sandwich trace of the concrete three-color lift is
`3*sigma*rho^2`. -/
theorem finiteGramSandwichTrace_threeColorRows (N : Nat)
    (b d : Nat → Q') :
    finiteGramSandwichTrace (N + (N + N)) 3 3
      (threeColorRows N b) (threeColorRows N d) ≈
      3 * finiteRowNorm2 N b *
        (finiteRowGram N b d * finiteRowGram N b d) := by
  unfold finiteGramSandwichTrace
  refine Q'.eqv_trans _ _ _
    (qListSum_congr (List.range 3) _ _ (fun i hi =>
      qListSum_congr (List.range 3) _ _ (fun k hk =>
        qListSum_congr (List.range 3) _ _ (fun j hj => ?_))))
    (sum_three_diagonal_sandwich (finiteRowNorm2 N b) (finiteRowGram N b d))
  exact mul_congr
    (mul_congr
      (Q'.eqv_trans _ _ _
        (finiteRowGram_threeColorRows N i k b b
          (List.mem_range.mp hi) (List.mem_range.mp hk))
        (by
          by_cases hik : i = k
          · simp only [if_pos hik]
            exact Q'.eqv_symm (finiteRowNorm2_eq_gram N b)
          · simp only [if_neg hik]
            exact Q'.eqv_refl _))
      (finiteRowGram_threeColorRows N i j b d
        (List.mem_range.mp hi) (List.mem_range.mp hj)))
    (finiteRowGram_threeColorRows N k j b d
      (List.mem_range.mp hk) (List.mem_range.mp hj))

/-- Exact quadratic covariance of the concrete disjoint three-color rows:
`Cov(S_B,S_D)=6*rho^2`. -/
theorem finiteGaussianRadialPairCovariance_threeColorRows (N : Nat)
    (b d : Nat → Q') :
    finiteGaussianCovariance (N + (N + N))
        (finiteGaussianRadialSquare (N + (N + N)) 3 (threeColorRows N b))
        (finiteGaussianRadialSquare (N + (N + N)) 3 (threeColorRows N d)) ≈
      6 * (finiteRowGram N b d * finiteRowGram N b d) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianRadialPairCovariance_trace (N + (N + N)) 3 3
      (threeColorRows N b) (threeColorRows N d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (finiteCrossGramSquareTrace_threeColorRows N b d))
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.const 3) (.mul (.var 0) (.var 0))))
        (.mul (.const 6) (.mul (.var 0) (.var 0)))
        (by decide) (fun _ => finiteRowGram N b d)))

/-- Exact three-color specialization on concrete disjoint rational rows:
`Cov(S_B^2,S_D)=60*sigma*rho^2`. -/
theorem finiteGaussianRadialCovariance_threeColorRows (N : Nat)
    (b d : Nat → Q') :
    finiteGaussianCovariance (N + (N + N))
      (polyMul
        (finiteGaussianRadialSquare (N + (N + N)) 3 (threeColorRows N b))
        (finiteGaussianRadialSquare (N + (N + N)) 3 (threeColorRows N b)))
      (finiteGaussianRadialSquare (N + (N + N)) 3 (threeColorRows N d)) ≈
      60 * finiteRowNorm2 N b *
        (finiteRowGram N b d * finiteRowGram N b d) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianRadialCovariance_trace (N + (N + N)) 3 3
      (threeColorRows N b) (threeColorRows N d))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left 8 _ _
          (finiteGramSandwichTrace_threeColorRows N b d))
        (mul_congr
          (Q'.mul_eqv_congr_left 4 _ _
            (finiteRowGramTrace_threeColorRows N b))
          (finiteCrossGramSquareTrace_threeColorRows N b d)))
      (poly_identity_of_normal_eq
        (.add
          (.mul (.const 8)
            (.mul (.mul (.const 3) (.var 0)) (.mul (.var 1) (.var 1))))
          (.mul (.mul (.const 4) (.mul (.const 3) (.var 0)))
            (.mul (.const 3) (.mul (.var 1) (.var 1)))))
        (.mul (.mul (.const 60) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun
          | 0 => finiteRowNorm2 N b
          | _ => finiteRowGram N b d)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteRowGram_threeColorRows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteRowGramTrace_threeColorRows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteCrossGramSquareTrace_threeColorRows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteGramSandwichTrace_threeColorRows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteGaussianRadialPairCovariance_threeColorRows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows.finiteGaussianRadialCovariance_threeColorRows
