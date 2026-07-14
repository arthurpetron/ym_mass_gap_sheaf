/-
# First-label contiguous identity for every factorial Hahn row

Moving one unit of degree from the first label to the second label gives a
two-branch contiguous relation.  This is exactly the residual carrier exposed
by the ordered Racah endpoint Casimir calculation.  The proof is constructive
induction on the contraction order, using the universal factorial recurrence;
zero coordinate scales discharge every truncating-natural boundary.
-/

import YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction

namespace YMGap.Continuum.SU2HahnFirstLabelContiguous

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem ofNat_add_eq (a b : Nat) :
    Q'.ofNat (a + b) = Q'.ofNat a + Q'.ofNat b := by
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem ofNat_mul_eq (a b : Nat) :
    Q'.ofNat (a * b) = Q'.ofNat a * Q'.ofNat b := by
  change Q'.ofNat (a * b) = Q'.mul (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.mul Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = Q'.ofNat a + -(Q'.ofNat b) := by
  change Q'.ofNat (a - b) =
    Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofNat b))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private theorem ofNat_sub_add (m i : Nat) (hi : i ≤ m) :
    Q'.ofNat (m - i) + Q'.ofNat i ≈ Q'.ofNat m := by
  rw [ofNat_sub_eq m i hi]
  refine Q'.eqv_trans _
    (Q'.ofNat m + (-Q'.ofNat i + Q'.ofNat i)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (Q'.ofNat m + 0) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem factorial_recurrence_product (m n k i j : Nat) :
    (Q'.ofNat i * Q'.ofNat (n - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
      (-(Q'.ofNat (m - i) * Q'.ofNat j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1) ≈
      transvectFactorialCoeff m n (k + 1) i j := by
  have h := transvectFactorialCoeff_succ m n k i j
  rw [ofNat_mul_eq i (n - j), ofNat_mul_eq (m - i) j] at h
  exact h

private theorem scale_eq_of_zero (S X Y : Q') (hS : S ≈ 0) :
    S * X ≈ S * Y := by
  refine Q'.eqv_trans _ (0 * X) _
    (Q'.mul_eqv_congr_right _ _ X hS) ?_
  refine Q'.eqv_trans _ 0 _ (q_zero_mul X) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ (0 * Y) _
    (Q'.mul_eqv_congr_right _ _ Y hS) (q_zero_mul Y))

private theorem product_zero_of_left (A B : Q') (hA : A ≈ 0) :
    A * B ≈ 0 :=
  Q'.eqv_trans _ (0 * B) _
    (Q'.mul_eqv_congr_right _ _ B hA) (q_zero_mul B)

private theorem product_zero_of_right (A B : Q') (hB : B ≈ 0) :
    A * B ≈ 0 := by
  refine Q'.eqv_trans _ (B * A) _ (Q'.mul_comm_eqv A B) ?_
  exact product_zero_of_left B A hB

private def contiguousRegroupLHS : PolyExpr :=
  .add
    (.mul (.var 0)
      (.add
        (.mul (.mul (.var 1) (.add (.var 4) (.const 1))) (.var 7))
        (.mul (.neg (.mul (.var 5) (.var 3))) (.var 8))))
    (.mul (.var 1)
      (.add
        (.mul (.mul (.var 2) (.var 4)) (.var 9))
        (.mul (.neg (.mul (.var 0) (.add (.var 3) (.const 1))))
          (.var 7))))

private def contiguousRegroupRHS : PolyExpr :=
  .add
    (.mul (.mul (.var 1) (.var 4))
      (.add (.mul (.var 0) (.var 7)) (.mul (.var 2) (.var 9))))
    (.mul (.neg (.mul (.var 0) (.var 3)))
      (.add (.mul (.var 5) (.var 8)) (.mul (.var 1) (.var 7))))

private theorem contiguousRegroup_normal :
    normalize contiguousRegroupLHS = normalize contiguousRegroupRHS := by decide

private theorem contiguous_regroup
    (A I IP J NJ AM X Y Z : Q') :
    A * (I * (NJ + 1) * X + (-(AM * J)) * Y) +
        I * (IP * NJ * Z + (-(A * (J + 1))) * X) ≈
      I * NJ * (A * X + IP * Z) +
        (-(A * J)) * (AM * Y + I * X) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then A else if r = 1 then I else if r = 2 then IP else
    if r = 3 then J else if r = 4 then NJ else if r = 5 then AM else
    if r = 7 then X else if r = 8 then Y else Z
  have h := poly_identity_of_normal_eq contiguousRegroupLHS
    contiguousRegroupRHS contiguousRegroup_normal ρ
  simpa [contiguousRegroupLHS, contiguousRegroupRHS, eval, ρ] using h

private def contiguousFactorLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.mul (.var 2) (.var 3)))
    (.mul (.neg (.var 1)) (.mul (.var 2) (.var 4)))

private def contiguousFactorRHS : PolyExpr :=
  .mul (.var 2)
    (.add (.mul (.var 0) (.var 3)) (.mul (.neg (.var 1)) (.var 4)))

private theorem contiguousFactor_normal :
    normalize contiguousFactorLHS = normalize contiguousFactorRHS := by decide

private theorem contiguous_factor (D E S P R : Q') :
    D * (S * P) + (-E) * (S * R) ≈
      S * (D * P + (-E) * R) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then D else if r = 1 then E else if r = 2 then S else
    if r = 3 then P else R
  have h := poly_identity_of_normal_eq contiguousFactorLHS
    contiguousFactorRHS contiguousFactor_normal ρ
  simpa [contiguousFactorLHS, contiguousFactorRHS, eval, ρ] using h

/-- **All-order first-label Hahn contiguity.**  The statement includes every
physical coordinate boundary; no extension to negative indices or classical
case selection is hidden in the formula. -/
theorem hahn_first_label_contiguous : ∀ k m n i j : Nat,
    k ≤ m → k ≤ n → i ≤ m → j ≤ n →
    Q'.ofNat (m - i) *
        transvectFactorialCoeff (m - 1) (n + 1) k i j +
      Q'.ofNat i *
        transvectFactorialCoeff (m - 1) (n + 1) k (i - 1) (j + 1) ≈
      Q'.ofNat (m - k) * transvectFactorialCoeff m n k i j
  | 0, m, n, i, j, _, _, hi, _ => by
      have h0 := transvectFactorialCoeff_zero (m - 1) (n + 1) i j
      have h1 := transvectFactorialCoeff_zero (m - 1) (n + 1) (i - 1) (j + 1)
      have h2 := transvectFactorialCoeff_zero m n i j
      refine Q'.eqv_trans _
        (Q'.ofNat (m - i) * 1 + Q'.ofNat i * 1) _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h0)
          (Q'.mul_eqv_congr_left _ _ _ h1)) ?_
      refine Q'.eqv_trans _ (Q'.ofNat m) _ ?_ ?_
      · refine Q'.eqv_trans _
          (Q'.ofNat (m - i) + Q'.ofNat i) _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)) ?_
        exact ofNat_sub_add m i hi
      · simp only [Nat.sub_zero]
        exact Q'.eqv_symm (Q'.eqv_trans _ (Q'.ofNat m * 1) _
          (Q'.mul_eqv_congr_left _ _ _ h2) (Q'.mul_one_eqv _))
  | k + 1, m, n, i, j, hkm, hkn, hi, hj => by
      have hm0 : 0 < m := by omega
      have hn0 : 0 < n := by omega
      let A : Q' := Q'.ofNat (m - i)
      let I : Q' := Q'.ofNat i
      let IP : Q' := Q'.ofNat (i - 1)
      let J : Q' := Q'.ofNat j
      let NJ : Q' := Q'.ofNat (n - j)
      let AM : Q' := Q'.ofNat ((m - 1) - i)
      let S : Q' := Q'.ofNat ((m - 1) - k)
      let U : Q' := transvectFactorialCoeff (m - 1) (n + 1) (k + 1) i j
      let V : Q' :=
        transvectFactorialCoeff (m - 1) (n + 1) (k + 1) (i - 1) (j + 1)
      let H : Q' := transvectFactorialCoeff m n (k + 1) i j
      let X : Q' := transvectFactorialCoeff (m - 2) n k (i - 1) j
      let Y : Q' := transvectFactorialCoeff (m - 2) n k i (j - 1)
      let Z : Q' := transvectFactorialCoeff (m - 2) n k (i - 2) (j + 1)
      let P : Q' := transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j
      let R : Q' := transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1)

      have hU0 := factorial_recurrence_product (m - 1) (n + 1) k i j
      have hU : U ≈ I * (NJ + 1) * X + (-(AM * J)) * Y := by
        have hnj : n + 1 - j = (n - j) + 1 := by omega
        rw [hnj, ofNat_add_eq (n - j) 1] at hU0
        exact Q'.eqv_symm (by
          simpa only [U, I, NJ, X, AM, J, Y] using hU0)

      have hVscaled : I * V ≈
          I * (IP * NJ * Z + (-(A * (J + 1))) * X) := by
        by_cases hi0 : i = 0
        · subst i
          have hIz : I ≈ 0 := by
            dsimp only [I]
            exact Q'.ofNat_zero_eqv
          exact scale_eq_of_zero I V _ hIz
        · have hi0' : 0 < i := by omega
          have hV0 := factorial_recurrence_product
            (m - 1) (n + 1) k (i - 1) (j + 1)
          have hni : n + 1 - (j + 1) = n - j := by omega
          have hmi : (m - 1) - (i - 1) = m - i := by omega
          rw [hni, hmi, ofNat_add_eq j 1] at hV0
          exact Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm (by
            simpa only [V, IP, NJ, Z, A, J, X] using hV0))

      have hExpanded : A * U + I * V ≈
          A * (I * (NJ + 1) * X + (-(AM * J)) * Y) +
            I * (IP * NJ * Z + (-(A * (J + 1))) * X) :=
        Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left A _ _ hU) hVscaled

      have hFirstScaled : I * NJ * (A * X + IP * Z) ≈
          I * NJ * (S * P) := by
        by_cases hi0 : i = 0
        · have hIz : I ≈ 0 := by
            dsimp only [I]
            rw [hi0]
            exact Q'.ofNat_zero_eqv
          have hs0 := product_zero_of_left I NJ hIz
          exact scale_eq_of_zero (I * NJ) _ _ hs0
        · by_cases hjn : j = n
          · have hNJz : NJ ≈ 0 := by
              dsimp only [NJ]
              rw [hjn, Nat.sub_self]
              exact Q'.ofNat_zero_eqv
            have hs0 := product_zero_of_right I NJ hNJz
            exact scale_eq_of_zero (I * NJ) _ _ hs0
          · have hih := hahn_first_label_contiguous k (m - 1) (n - 1)
              (i - 1) j (by omega) (by omega) (by omega) (by omega)
            have hih' : A * X + IP * Z ≈ S * P := by
              simpa only [A, X, IP, Z, S, P,
                show (m - 1) - (i - 1) = m - i by omega,
                show (n - 1) + 1 = n by omega] using hih
            exact Q'.mul_eqv_congr_left (I * NJ) _ _ hih'

      have hSecondScaled : (-(A * J)) * (AM * Y + I * X) ≈
          (-(A * J)) * (S * R) := by
        by_cases him : i = m
        · have hAz : A ≈ 0 := by
            dsimp only [A]
            rw [him, Nat.sub_self]
            exact Q'.ofNat_zero_eqv
          have hAJ0 := product_zero_of_left A J hAz
          have hneg0 : -(A * J) ≈ 0 := by
            refine Q'.eqv_trans _ (-0) _
              (Q'.neg_eqv_congr _ _ hAJ0) ?_
            exact Q'.neg_add_self_eqv 0
          exact scale_eq_of_zero (-(A * J)) _ _ hneg0
        · by_cases hj0 : j = 0
          · have hJz : J ≈ 0 := by
              dsimp only [J]
              rw [hj0]
              exact Q'.ofNat_zero_eqv
            have hAJ0 := product_zero_of_right A J hJz
            have hneg0 : -(A * J) ≈ 0 := by
              refine Q'.eqv_trans _ (-0) _
                (Q'.neg_eqv_congr _ _ hAJ0) ?_
              exact Q'.neg_add_self_eqv 0
            exact scale_eq_of_zero (-(A * J)) _ _ hneg0
          · have hih := hahn_first_label_contiguous k (m - 1) (n - 1)
              i (j - 1) (by omega) (by omega) (by omega) (by omega)
            have hih' : AM * Y + I * X ≈ S * R := by
              simpa only [AM, Y, I, X, S, R,
                show (n - 1) + 1 = n by omega,
                show j - 1 + 1 = j by omega] using hih
            exact Q'.mul_eqv_congr_left (-(A * J)) _ _ hih'

      have hJ0 := factorial_recurrence_product m n k i j
      have hJ : I * NJ * P + (-(A * J)) * R ≈ H := by
        simpa only [I, NJ, P, A, J, R, H] using hJ0

      refine Q'.eqv_trans _ (A * U + I * V) _ (Q'.eqv_refl _) ?_
      refine Q'.eqv_trans _
        (A * (I * (NJ + 1) * X + (-(AM * J)) * Y) +
          I * (IP * NJ * Z + (-(A * (J + 1))) * X)) _ hExpanded ?_
      refine Q'.eqv_trans _
        (I * NJ * (A * X + IP * Z) +
          (-(A * J)) * (AM * Y + I * X)) _
        (contiguous_regroup A I IP J NJ AM X Y Z) ?_
      refine Q'.eqv_trans _
        (I * NJ * (S * P) + (-(A * J)) * (S * R)) _
        (Q'.add_eqv_congr' hFirstScaled hSecondScaled) ?_
      refine Q'.eqv_trans _ (S * (I * NJ * P + (-(A * J)) * R)) _
        (contiguous_factor (I * NJ) (A * J) S P R) ?_
      refine Q'.eqv_trans _ (S * H) _
        (Q'.mul_eqv_congr_left S _ _ hJ) ?_
      simpa only [A, U, I, V, S, H,
        show m - (k + 1) = (m - 1) - k by omega] using
        Q'.eqv_refl (S * H)

end YMGap.Continuum.SU2HahnFirstLabelContiguous

#print axioms YMGap.Continuum.SU2HahnFirstLabelContiguous.hahn_first_label_contiguous
