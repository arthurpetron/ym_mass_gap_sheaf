/-
# A four-weight obstruction to inferring small conditional angles

The literal positive joint weight on Bool x Bool is [[M,m],[m,M]].
Its two marginals are uniform; both sign probes are centered and have
unit squared norm. Their correlation is (M-m)/(M+m), and the actual
row-conditional sign average has squared norm equal to that ratio squared.

This is a finite rational counterexample to a proposed inference from an
absolute density window alone. It is NOT a Yang--Mills model, an estimate
of the original physical conditional operators, or a mass-gap claim.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalTwoStateWindowWitness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The four actual weights, not an assumed correlation parameter. -/
def weight (m M : Q') : Bool → Bool → Q'
  | false, false => M
  | false, true => m
  | true, false => m
  | true, true => M

def sign : Bool → Q'
  | false => 1
  | true => -1

def moment (m M : Q') (f : Bool → Bool → Q') : Q' :=
  ((weight m M false false * f false false + weight m M false true * f false true) +
    weight m M true false * f true false) + weight m M true true * f true true

def mass (m M : Q') : Q' := moment m M (fun _ _ => 1)

private theorem qadd {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem pos_mono {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) : (0 : Q') < b := by
  have hp : (0 : Int) < b.num * (a.den : Int) :=
    Int.lt_of_lt_of_le (Int.mul_pos (Q'.num_pos_of_pos ha) (by exact_mod_cast b.den_pos)) hab
  have hb : (0 : Int) < b.num := by
    by_cases h : (0 : Int) < b.num
    · exact h
    · have hn := Int.mul_nonpos_of_nonpos_of_nonneg (Int.not_lt.mp h)
        (show (0 : Int) ≤ (a.den : Int) from by exact_mod_cast Nat.zero_le a.den)
      omega
  change (0 : Int) * (b.den : Int) < b.num * (1 : Int)
  simpa only [Int.zero_mul, Int.mul_one] using hb

theorem weight_window (m M : Q') (hMm : m ≤ M) (i j : Bool) :
    m ≤ weight m M i j ∧ weight m M i j ≤ M := by
  cases i <;> cases j
  · exact ⟨hMm, Q'.le_refl' M⟩
  · exact ⟨Q'.le_refl' m, hMm⟩
  · exact ⟨Q'.le_refl' m, hMm⟩
  · exact ⟨hMm, Q'.le_refl' M⟩

theorem weight_positive (m M : Q') (hm : (0 : Q') < m) (hMm : m ≤ M) (i j : Bool) :
    (0 : Q') < weight m M i j := pos_mono hm (weight_window m M hMm i j).1

theorem sum_positive (m M : Q') (hm : (0 : Q') < m) (hMm : m ≤ M) :
    (0 : Q') < M+m := Q'.add_pos (pos_mono hm hMm) hm

theorem row_mass (m M : Q') (i : Bool) :
    weight m M i false + weight m M i true ≈ M+m := by
  cases i
  · exact Q'.eqv_refl _
  · exact Q'.add_comm_eqv _ _

theorem column_mass (m M : Q') (j : Bool) :
    weight m M false j + weight m M true j ≈ M+m := by
  cases j
  · exact Q'.eqv_refl _
  · exact Q'.add_comm_eqv _ _

theorem mass_eq (m M : Q') : mass m M ≈ 2*(M+m) :=
  poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 1) (.const 1)) (.mul (.var 0) (.const 1)))
      (.mul (.var 0) (.const 1))) (.mul (.var 1) (.const 1)))
    (.mul (.const 2) (.add (.var 1) (.var 0))) (by decide) (fun | 0 => m | _ => M)

theorem mass_positive (m M : Q') (hm : (0 : Q') < m) (hMm : m ≤ M) :
    (0 : Q') < mass m M :=
  pos_mono (Q'.mul_pos (by decide : (0 : Q') < 2) (sum_positive m M hm hMm))
    (Q'.ge_of_eqv (mass_eq m M))

/-- A computable normalizer; `normalization` proves it inverts the actual mass. -/
def normalizer (m M : Q') (hs : (0 : Q') < M+m) : Q' :=
  HalfPow.half * Q'.recipPos (M+m) hs

def expectation (m M : Q') (hs : (0 : Q') < M+m) (f : Bool → Bool → Q') : Q' :=
  moment m M f * normalizer m M hs

def rho (m M : Q') (hs : (0 : Q') < M+m) : Q' :=
  (M + -m) * Q'.recipPos (M+m) hs

/-- The conditional average is computed from the actual two row weights. -/
def conditionalSign (m M : Q') (hs : (0 : Q') < M+m) (i : Bool) : Q' :=
  (weight m M i false * sign false + weight m M i true * sign true) * Q'.recipPos (M+m) hs

private theorem twice_normalized (m M : Q') (hs : (0 : Q') < M+m) (a : Q') :
    (2*a)*normalizer m M hs ≈ a * Q'.recipPos (M+m) hs := by
  have h := poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => a | 1 => HalfPow.half | _ => Q'.recipPos (M+m) hs)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide : (2 : Q')*HalfPow.half ≈ 1))
    (Q'.one_mul_eqv _))

theorem normalization (m M : Q') (hs : (0 : Q') < M+m) :
    mass m M * normalizer m M hs ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (mass_eq m M))
    (Q'.eqv_trans _ _ _ (twice_normalized m M hs (M+m)) (Q'.mul_recipPos_eqv _ hs))

private theorem marginal_normalization (m M : Q') (hs : (0 : Q') < M+m) :
    (M+m)*normalizer m M hs ≈ HalfPow.half := by
  have h := poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => M+m | 1 => HalfPow.half | _ => Q'.recipPos (M+m) hs)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hs)) (Q'.mul_one_eqv _))

theorem row_probability (m M : Q') (hs : (0 : Q') < M+m) (i : Bool) :
    (weight m M i false + weight m M i true)*normalizer m M hs ≈ HalfPow.half :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (row_mass m M i))
    (marginal_normalization m M hs)

theorem column_probability (m M : Q') (hs : (0 : Q') < M+m) (j : Bool) :
    (weight m M false j + weight m M true j)*normalizer m M hs ≈ HalfPow.half :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (column_mass m M j))
    (marginal_normalization m M hs)

private theorem expectation_congr (m M : Q') (hs : (0 : Q') < M+m)
    {f g : Bool → Bool → Q'} (h : ∀ i j, f i j ≈ g i j) :
    expectation m M hs f ≈ expectation m M hs g :=
  Q'.mul_eqv_congr_right _ _ _ (qadd (qadd (qadd
    (Q'.mul_eqv_congr_left _ _ _ (h false false))
    (Q'.mul_eqv_congr_left _ _ _ (h false true)))
    (Q'.mul_eqv_congr_left _ _ _ (h true false)))
    (Q'.mul_eqv_congr_left _ _ _ (h true true)))

private theorem expectation_const (m M : Q') (hs : (0 : Q') < M+m) (a : Q') :
    expectation m M hs (fun _ _ => a) ≈ a := by
  have h : moment m M (fun _ _ => a) ≈ a * mass m M :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
      (.mul (.var 2)
        (.add (.add (.add (.mul (.var 1) (.const 1)) (.mul (.var 0) (.const 1)))
          (.mul (.var 0) (.const 1))) (.mul (.var 1) (.const 1))))
      (by decide) (fun | 0 => m | 1 => M | _ => a)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (normalization m M hs)) (Q'.mul_one_eqv _)))

theorem sign_means (m M : Q') (hs : (0 : Q') < M+m) :
    expectation m M hs (fun i _ => sign i) ≈ 0 ∧
      expectation m M hs (fun _ j => sign j) ≈ 0 := by
  have hx : moment m M (fun i _ => sign i) ≈ 0 :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 1) (.const 1)) (.mul (.var 0) (.const 1)))
        (.mul (.var 0) (.neg (.const 1)))) (.mul (.var 1) (.neg (.const 1))))
      (.const 0) (by decide) (fun | 0 => m | _ => M)
  have hy : moment m M (fun _ j => sign j) ≈ 0 :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 1) (.const 1)) (.mul (.var 0) (.neg (.const 1))))
        (.mul (.var 0) (.const 1))) (.mul (.var 1) (.neg (.const 1))))
      (.const 0) (by decide) (fun | 0 => m | _ => M)
  exact ⟨Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx) (QPoly.q_zero_mul _),
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hy) (QPoly.q_zero_mul _)⟩

theorem sign_squared_norms (m M : Q') (hs : (0 : Q') < M+m) :
    expectation m M hs (fun i _ => sign i * sign i) ≈ 1 ∧
      expectation m M hs (fun _ j => sign j * sign j) ≈ 1 := by
  have hsign (i : Bool) : sign i * sign i ≈ 1 := by cases i <;> decide
  exact ⟨Q'.eqv_trans _ _ _ (expectation_congr m M hs (fun i _ => hsign i))
      (expectation_const m M hs 1),
    Q'.eqv_trans _ _ _ (expectation_congr m M hs (fun _ j => hsign j))
      (expectation_const m M hs 1)⟩

theorem correlation (m M : Q') (hs : (0 : Q') < M+m) :
    expectation m M hs (fun i j => sign i * sign j) ≈ rho m M hs := by
  have h : moment m M (fun i j => sign i * sign j) ≈ 2*(M + -m) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 1) (.mul (.const 1) (.const 1)))
        (.mul (.var 0) (.mul (.const 1) (.neg (.const 1)))))
        (.mul (.var 0) (.mul (.neg (.const 1)) (.const 1))))
        (.mul (.var 1) (.mul (.neg (.const 1)) (.neg (.const 1)))))
      (.mul (.const 2) (.add (.var 1) (.neg (.var 0))))
      (by decide) (fun | 0 => m | _ => M)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (twice_normalized m M hs (M + -m))

theorem conditionalSign_eq (m M : Q') (hs : (0 : Q') < M+m) (i : Bool) :
    conditionalSign m M hs i ≈ rho m M hs * sign i := by
  cases i
  · exact poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 1) (.const 1)) (.mul (.var 0) (.neg (.const 1)))) (.var 2))
      (.mul (.mul (.add (.var 1) (.neg (.var 0))) (.var 2)) (.const 1))
      (by decide) (fun | 0 => m | 1 => M | _ => Q'.recipPos (M+m) hs)
  · exact poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.const 1)) (.mul (.var 1) (.neg (.const 1)))) (.var 2))
      (.mul (.mul (.add (.var 1) (.neg (.var 0))) (.var 2)) (.neg (.const 1)))
      (by decide) (fun | 0 => m | 1 => M | _ => Q'.recipPos (M+m) hs)

/-- The squared conditional norm attains the squared window ratio exactly. -/
theorem conditional_squared_norm (m M : Q') (hs : (0 : Q') < M+m) :
    expectation m M hs (fun i _ => conditionalSign m M hs i * conditionalSign m M hs i) ≈
      rho m M hs * rho m M hs := by
  have h (i : Bool) : (rho m M hs * sign i) * (rho m M hs * sign i) ≈
      rho m M hs * rho m M hs := by
    cases i
    · exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.const 1)) (.mul (.var 0) (.const 1)))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => rho m M hs)
    · exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.neg (.const 1))) (.mul (.var 0) (.neg (.const 1))))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => rho m M hs)
  exact Q'.eqv_trans _ _ _ (expectation_congr m M hs (fun i _ =>
    Q'.eqv_trans _ _ _ (qmul (conditionalSign_eq m M hs i) (conditionalSign_eq m M hs i)) (h i)))
    (expectation_const m M hs (rho m M hs * rho m M hs))

end YMGap.Continuum.RationalTwoStateWindowWitness

#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.weight
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.sign
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.moment
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.mass
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.weight_window
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.weight_positive
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.sum_positive
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.row_mass
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.column_mass
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.mass_eq
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.mass_positive
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.normalizer
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.expectation
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.rho
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.conditionalSign
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.normalization
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.row_probability
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.column_probability
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.sign_means
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.sign_squared_norms
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.correlation
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.conditionalSign_eq
#print axioms YMGap.Continuum.RationalTwoStateWindowWitness.conditional_squared_norm
