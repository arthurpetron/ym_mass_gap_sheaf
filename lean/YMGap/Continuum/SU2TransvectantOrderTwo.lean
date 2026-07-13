/-
# Symbolic order-two Cayley coefficient

The arbitrary-order monomial recurrence has two branches.  At order two the
two mixed branches coincide and therefore acquire the Pascal multiplicity
`2`.  This module proves that cancellation constructively with the internal
reflective `Q'` ring normaliser, then uses it to identify the actual second
Cayley transvectant with the already-derived factorial coefficient.

No finite label cutoff, classical choice, native decision procedure, proof
hole, or new axiom is used.
-/

import YMGap.Continuum.SU2TransvectantMonomialRecurrence
import YMGap.Continuum.SU2TransvectantFactorialSeed
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2TransvectantOrderTwo

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMonomialRecurrence
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.RingNormaliser

/-! ## The nonlinear two-branch cancellation -/

/-- Reflective syntax for `A(A₁-B)-B(A-B₁)`. -/
def orderTwoBranchLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.mul (.neg (.var 2)) (.add (.var 0) (.neg (.var 3))))

/-- Reflective syntax for `AA₁-2AB+BB₁`. -/
def orderTwoBranchRHS : PolyExpr :=
  .add
    (.add
      (.mul (.var 0) (.var 1))
      (.neg (.mul (.mul (.const 2) (.var 0)) (.var 2))))
    (.mul (.var 2) (.var 3))

/-- The two order-two branch expressions have the same canonical polynomial. -/
theorem orderTwoBranch_normal_eq :
    normalize orderTwoBranchLHS = normalize orderTwoBranchRHS := by decide

/-- The two mixed derivative branches combine to the Pascal coefficient `2`. -/
theorem orderTwo_branch_identity (A A₁ B B₁ : Q') :
    (A * (A₁ + -B) + (-B) * (A + -B₁)).eqv
      ((A * A₁ + -(((2 : Q') * A) * B)) + B * B₁) := by
  let ρ : Nat → Q' := fun t =>
    if t = 0 then A else if t = 1 then A₁ else if t = 2 then B else B₁
  have h := poly_identity_of_normal_eq orderTwoBranchLHS orderTwoBranchRHS
    orderTwoBranch_normal_eq ρ
  simpa [orderTwoBranchLHS, orderTwoBranchRHS, eval, ρ] using h

private theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem mul_congr {a b c d : Q'} (ha : a.eqv c) (hb : b.eqv d) :
    (a * b).eqv (c * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a c b ha)
    (Q'.mul_eqv_congr_left c b d hb)

/-! ## The actual interior order-two coefficient -/

/-- For positive monomial indices, the actual second Cayley transvectant is
the three-term factorial/Pascal coefficient.  This is the first symbolic
coefficient beyond the order-one seed: the middle multiplicity `2` is derived
from the two recurrence branches, not inserted by a finite table. -/
theorem transvect_two_matches_factorial_interior
    (m n i j : Nat) (hi : 0 < i) (hj : 0 < j) :
    (transvect m n 2 (tprod (mono i) (mono j)) (i + j - 2)).eqv
      (transvectFactorialCoeff m n 2 i j) := by
  let s := i + j - 2
  let A := i * (n - j)
  let A₁ := (i - 1) * (n - j - 1)
  let B := (m - i) * j
  let B₁ := (m - i - 1) * (j - 1)

  have hs₁ : s + 1 = (i - 1) + j := by
    simp only [s]
    omega
  have hs₂ : s + 1 = i + (j - 1) := by
    simp only [s]
    omega
  have hn₁ : (n - 1) - j = n - j - 1 := by omega
  have hm₁ : (m - 1) - (i - 1) = m - i := by omega
  have hn₂ : (n - 1) - (j - 1) = n - j := by omega
  have hm₂ : (m - 1) - i = m - i - 1 := by omega

  have hfirst :
      (transvect (m - 1) (n - 1) 1
        (tprod (mono (i - 1)) (mono j)) s).eqv
        (Q'.ofNat A₁ + -(Q'.ofNat B)) := by
    have h :=
      YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
        (m - 1) (n - 1) (i - 1) j s
    simpa only [if_pos hs₁, hn₁, hm₁, A₁, B] using h
  have hsecond :
      (transvect (m - 1) (n - 1) 1
        (tprod (mono i) (mono (j - 1))) s).eqv
        (Q'.ofNat A + -(Q'.ofNat B₁)) := by
    have h :=
      YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
        (m - 1) (n - 1) i (j - 1) s
    simpa only [if_pos hs₂, hn₂, hm₂, A, B₁] using h

  have hrec := transvect_succ_monomial m n 1 i j s
  have hbranches :
      (transvect m n 2 (tprod (mono i) (mono j)) s).eqv
        (Q'.ofNat A * (Q'.ofNat A₁ + -(Q'.ofNat B)) +
          (-(Q'.ofNat B)) * (Q'.ofNat A + -(Q'.ofNat B₁))) := by
    refine Q'.eqv_trans _ _ _ (by simpa only [A, B] using hrec) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat A) _ _ hfirst)
      (Q'.mul_eqv_congr_left (-(Q'.ofNat B)) _ _ hsecond)

  have hpoly := orderTwo_branch_identity
    (Q'.ofNat A) (Q'.ofNat A₁) (Q'.ofNat B) (Q'.ofNat B₁)

  let X := (i * (i - 1)) * ((n - j) * (n - j - 1))
  let Y := 2 * i * (m - i) * j * (n - j)
  let Z := ((m - i) * (m - i - 1)) * (j * (j - 1))
  have hX : A * A₁ = X := by
    simp only [A, A₁, X]
    ac_rfl
  have hY : (2 * A) * B = Y := by
    simp only [A, B, Y]
    ac_rfl
  have hZ : B * B₁ = Z := by
    simp only [B, B₁, Z]
    ac_rfl

  have hAA : (Q'.ofNat A * Q'.ofNat A₁).eqv (Q'.ofNat X) := by
    refine Q'.eqv_trans _ (Q'.ofNat (A * A₁)) _ (ofNat_mul_eqv A A₁) ?_
    rw [hX]
    exact Q'.eqv_refl _
  have hAB : (((2 : Q') * Q'.ofNat A) * Q'.ofNat B).eqv
      (Q'.ofNat Y) := by
    have h2A : ((2 : Q') * Q'.ofNat A).eqv (Q'.ofNat (2 * A)) :=
      ofNat_mul_eqv 2 A
    refine Q'.eqv_trans _ (Q'.ofNat (2 * A) * Q'.ofNat B) _
      (Q'.mul_eqv_congr_right _ _ _ h2A) ?_
    refine Q'.eqv_trans _ (Q'.ofNat ((2 * A) * B)) _
      (ofNat_mul_eqv (2 * A) B) ?_
    rw [hY]
    exact Q'.eqv_refl _
  have hBB : (Q'.ofNat B * Q'.ofNat B₁).eqv (Q'.ofNat Z) := by
    refine Q'.eqv_trans _ (Q'.ofNat (B * B₁)) _ (ofNat_mul_eqv B B₁) ?_
    rw [hZ]
    exact Q'.eqv_refl _
  have hclosed :
      ((Q'.ofNat A * Q'.ofNat A₁ +
          -(((2 : Q') * Q'.ofNat A) * Q'.ofNat B)) +
        Q'.ofNat B * Q'.ofNat B₁).eqv
        ((Q'.ofNat X + -(Q'.ofNat Y)) + Q'.ofNat Z) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hAA (Q'.neg_eqv_congr _ _ hAB)) hBB

  refine Q'.eqv_trans _ _ _ hbranches ?_
  refine Q'.eqv_trans _ _ _ hpoly ?_
  refine Q'.eqv_trans _ _ _ hclosed ?_
  exact Q'.eqv_symm (by
    simpa only [X, Y, Z] using
      (transvectFactorialCoeff_two m n i j))

/-- The order-two coefficient also agrees on the `i=0` boundary once the
remaining index can actually support two derivatives. -/
theorem transvect_two_matches_factorial_left_boundary
    (m n j : Nat) (hj : 2 ≤ j) :
    (transvect m n 2 (tprod (mono 0) (mono j)) (j - 2)).eqv
      (transvectFactorialCoeff m n 2 0 j) := by
  let s := j - 2
  let B := m * j
  let B₁ := (m - 1) * (j - 1)
  let Z := (m * (m - 1)) * (j * (j - 1))
  have hs : s + 1 = 0 + (j - 1) := by
    simp only [s]
    omega
  have hm : (m - 1) - 0 = m - 1 := by omega
  have hn : (n - 1) - (j - 1) = n - j := by omega
  have hsecond0 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
      (m - 1) (n - 1) 0 (j - 1) s
  have hsecond :
      (transvect (m - 1) (n - 1) 1
        (tprod (mono 0) (mono (j - 1))) s).eqv
        (-(Q'.ofNat B₁)) := by
    refine Q'.eqv_trans _ (Q'.ofNat 0 + -(Q'.ofNat B₁)) _ ?_ ?_
    · simpa only [if_pos hs, Nat.zero_mul, hm, hn, B₁] using hsecond0
    · change ((0 : Q') + -(Q'.ofNat B₁)).eqv (-(Q'.ofNat B₁))
      exact Q'.eqv_of_eq (Q'.zero_add' _)

  have hrec := transvect_succ_monomial m n 1 0 j s
  have hzero :
      (Q'.ofNat (0 * (n - j)) *
        transvect (m - 1) (n - 1) 1
          (tprod (mono (0 - 1)) (mono j)) s).eqv 0 := by
    simp only [Nat.zero_mul, Nat.zero_sub]
    change ((0 : Q') *
      transvect (m - 1) (n - 1) 1 (tprod (mono 0) (mono j)) s).eqv 0
    exact Q'.zero_mul_eqv _
  have hscaled :
      ((-(Q'.ofNat B)) *
        transvect (m - 1) (n - 1) 1
          (tprod (mono 0) (mono (j - 1))) s).eqv
        ((-(Q'.ofNat B)) * (-(Q'.ofNat B₁))) :=
    Q'.mul_eqv_congr_left (-(Q'.ofNat B)) _ _ hsecond
  have hbranches :
      (transvect m n 2 (tprod (mono 0) (mono j)) s).eqv
        ((-(Q'.ofNat B)) * (-(Q'.ofNat B₁))) := by
    refine Q'.eqv_trans _ _ _ (by simpa only [B] using hrec) ?_
    refine Q'.eqv_trans _ (0 + ((-(Q'.ofNat B)) * (-(Q'.ofNat B₁)))) _ ?_ ?_
    · exact Q'.add_eqv_congr' hzero hscaled
    · exact Q'.eqv_of_eq (Q'.zero_add' _)
  have hnegneg :
      ((-(Q'.ofNat B)) * (-(Q'.ofNat B₁))).eqv
        (Q'.ofNat B * Q'.ofNat B₁) := by
    refine Q'.eqv_trans _ (-(Q'.ofNat B * (-(Q'.ofNat B₁)))) _
      (Q'.neg_mul_eqv (Q'.ofNat B) (-(Q'.ofNat B₁))) ?_
    refine Q'.eqv_trans _ (-(-(Q'.ofNat B * Q'.ofNat B₁))) _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (Q'.ofNat B) (Q'.ofNat B₁))) ?_
    exact Q'.neg_neg_eqv _
  have hBZ : B * B₁ = Z := by
    simp only [B, B₁, Z]
    ac_rfl
  have hprod : (Q'.ofNat B * Q'.ofNat B₁).eqv (Q'.ofNat Z) := by
    refine Q'.eqv_trans _ (Q'.ofNat (B * B₁)) _ (ofNat_mul_eqv B B₁) ?_
    rw [hBZ]
    exact Q'.eqv_refl _
  have hfac0 := transvectFactorialCoeff_two m n 0 j
  have hfac : (transvectFactorialCoeff m n 2 0 j).eqv (Q'.ofNat Z) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 0 + -(Q'.ofNat 0) + Q'.ofNat Z) _
      (by simpa [Z] using hfac0) ?_
    have hz : (Q'.ofNat 0).eqv 0 := Q'.ofNat_zero_eqv
    have hnz : (-(Q'.ofNat 0)).eqv 0 := by
      refine Q'.eqv_trans _ (-(0 : Q')) _
        (Q'.neg_eqv_congr _ _ hz) ?_
      exact Q'.eqv_refl 0
    have hp : (Q'.ofNat 0 + -(Q'.ofNat 0)).eqv 0 := by
      refine Q'.eqv_trans _ ((0 : Q') + 0) _
        (Q'.add_eqv_congr' hz hnz) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)
    refine Q'.eqv_trans _ ((0 : Q') + Q'.ofNat Z) _
      (Q'.add_eqv_congr_right _ _ _ hp) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  refine Q'.eqv_trans _ _ _ hbranches ?_
  refine Q'.eqv_trans _ _ _ hnegneg ?_
  refine Q'.eqv_trans _ _ _ hprod ?_
  exact Q'.eqv_symm hfac

/-- Symmetric `j=0` order-two boundary. -/
theorem transvect_two_matches_factorial_right_boundary
    (m n i : Nat) (hi : 2 ≤ i) :
    (transvect m n 2 (tprod (mono i) (mono 0)) (i - 2)).eqv
      (transvectFactorialCoeff m n 2 i 0) := by
  let s := i - 2
  let A := i * n
  let A₁ := (i - 1) * (n - 1)
  let X := (i * (i - 1)) * (n * (n - 1))
  have hs : s + 1 = (i - 1) + 0 := by
    simp only [s]
    omega
  have hn : (n - 1) - 0 = n - 1 := by omega
  have hm : (m - 1) - (i - 1) = m - i := by omega
  have hfirst0 :=
    YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
      (m - 1) (n - 1) (i - 1) 0 s
  have hfirst :
      (transvect (m - 1) (n - 1) 1
        (tprod (mono (i - 1)) (mono 0)) s).eqv
        (Q'.ofNat A₁) := by
    refine Q'.eqv_trans _ (Q'.ofNat A₁ + -(Q'.ofNat 0)) _ ?_ ?_
    · simpa only [if_pos hs, Nat.mul_zero, hn, hm, A₁] using hfirst0
    · have hz : (-(Q'.ofNat 0)).eqv 0 := by
        refine Q'.eqv_trans _ (-(0 : Q')) _
          (Q'.neg_eqv_congr _ _ Q'.ofNat_zero_eqv) ?_
        exact Q'.eqv_refl 0
      refine Q'.eqv_trans _ (Q'.ofNat A₁ + 0) _
        (Q'.add_eqv_congr_left _ _ _ hz) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)

  have hrec := transvect_succ_monomial m n 1 i 0 s
  have hscaled :
      (Q'.ofNat A *
        transvect (m - 1) (n - 1) 1
          (tprod (mono (i - 1)) (mono 0)) s).eqv
        (Q'.ofNat A * Q'.ofNat A₁) :=
    Q'.mul_eqv_congr_left (Q'.ofNat A) _ _ hfirst
  have hzero :
      ((-(Q'.ofNat ((m - i) * 0))) *
        transvect (m - 1) (n - 1) 1
          (tprod (mono i) (mono (0 - 1))) s).eqv 0 := by
    simp only [Nat.mul_zero, Nat.zero_sub]
    change ((0 : Q') *
      transvect (m - 1) (n - 1) 1 (tprod (mono i) (mono 0)) s).eqv 0
    exact Q'.zero_mul_eqv _
  have hbranches :
      (transvect m n 2 (tprod (mono i) (mono 0)) s).eqv
        (Q'.ofNat A * Q'.ofNat A₁) := by
    refine Q'.eqv_trans _ _ _ (by simpa only [A] using hrec) ?_
    refine Q'.eqv_trans _ ((Q'.ofNat A * Q'.ofNat A₁) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr' hscaled hzero
    · exact Q'.eqv_of_eq (Q'.add_zero' _)
  have hAX : A * A₁ = X := by
    simp only [A, A₁, X]
    ac_rfl
  have hprod : (Q'.ofNat A * Q'.ofNat A₁).eqv (Q'.ofNat X) := by
    refine Q'.eqv_trans _ (Q'.ofNat (A * A₁)) _ (ofNat_mul_eqv A A₁) ?_
    rw [hAX]
    exact Q'.eqv_refl _
  have hfac0 := transvectFactorialCoeff_two m n i 0
  have hfac : (transvectFactorialCoeff m n 2 i 0).eqv (Q'.ofNat X) := by
    refine Q'.eqv_trans _
      (Q'.ofNat X + -(Q'.ofNat 0) + Q'.ofNat 0) _
      (by simpa [X] using hfac0) ?_
    have hz : (Q'.ofNat 0).eqv 0 := Q'.ofNat_zero_eqv
    have hnz : (-(Q'.ofNat 0)).eqv 0 := by
      refine Q'.eqv_trans _ (-(0 : Q')) _
        (Q'.neg_eqv_congr _ _ hz) ?_
      exact Q'.eqv_refl 0
    have hleft : (Q'.ofNat X + -(Q'.ofNat 0)).eqv (Q'.ofNat X) := by
      refine Q'.eqv_trans _ (Q'.ofNat X + 0) _
        (Q'.add_eqv_congr_left _ _ _ hnz) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
    refine Q'.eqv_trans _ (Q'.ofNat X + 0) _
      (Q'.add_eqv_congr' hleft hz) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  refine Q'.eqv_trans _ _ _ hbranches ?_
  refine Q'.eqv_trans _ _ _ hprod ?_
  exact Q'.eqv_symm hfac

private theorem three_zero_terms :
    ((Q'.ofNat 0 + -(Q'.ofNat 0)) + Q'.ofNat 0).eqv 0 := by
  have hz : (Q'.ofNat 0).eqv 0 := Q'.ofNat_zero_eqv
  have hnz : (-(Q'.ofNat 0)).eqv 0 := by
    refine Q'.eqv_trans _ (-(0 : Q')) _
      (Q'.neg_eqv_congr _ _ hz) ?_
    exact Q'.eqv_refl 0
  have hp : (Q'.ofNat 0 + -(Q'.ofNat 0)).eqv 0 := by
    refine Q'.eqv_trans _ ((0 : Q') + 0) _
      (Q'.add_eqv_congr' hz hnz) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' 0)
  refine Q'.eqv_trans _ ((0 : Q') + 0) _
    (Q'.add_eqv_congr' hp hz) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem factorial_two_zero_00 (m n : Nat) :
    (transvectFactorialCoeff m n 2 0 0).eqv 0 := by
  refine Q'.eqv_trans _ _ _ (transvectFactorialCoeff_two m n 0 0) ?_
  simpa using three_zero_terms

private theorem factorial_two_zero_01 (m n : Nat) :
    (transvectFactorialCoeff m n 2 0 1).eqv 0 := by
  refine Q'.eqv_trans _ _ _ (transvectFactorialCoeff_two m n 0 1) ?_
  simpa using three_zero_terms

private theorem factorial_two_zero_10 (m n : Nat) :
    (transvectFactorialCoeff m n 2 1 0).eqv 0 := by
  refine Q'.eqv_trans _ _ _ (transvectFactorialCoeff_two m n 1 0) ?_
  simpa using three_zero_terms

/-- **Complete arbitrary-label order-two coefficient theorem.**  The actual
second Cayley transvectant agrees with the factorial/Pascal formula at its
unique (saturating) output index for every pair of natural monomial labels.
The three inputs of total degree below two vanish by the all-order support
theorem; every other input is covered by the interior or one of the exact
zero-index boundary calculations above. -/
theorem transvect_two_matches_factorial (m n i j : Nat) :
    (transvect m n 2 (tprod (mono i) (mono j)) (i + j - 2)).eqv
      (transvectFactorialCoeff m n 2 i j) := by
  cases i with
  | zero =>
      cases j with
      | zero =>
          have hz :=
            YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
              m n 2 0 0 0 (by omega)
          refine Q'.eqv_trans _ 0 _ (by simpa using hz) ?_
          exact Q'.eqv_symm (factorial_two_zero_00 m n)
      | succ j =>
          cases j with
          | zero =>
              have hz :=
                YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
                  m n 2 0 1 0 (by omega)
              refine Q'.eqv_trans _ 0 _ (by simpa using hz) ?_
              exact Q'.eqv_symm (factorial_two_zero_01 m n)
          | succ k =>
              simpa using transvect_two_matches_factorial_left_boundary
                m n (k + 2) (by omega)
  | succ i =>
      cases j with
      | zero =>
          cases i with
          | zero =>
              have hz :=
                YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
                  m n 2 1 0 0 (by omega)
              refine Q'.eqv_trans _ 0 _ (by simpa using hz) ?_
              exact Q'.eqv_symm (factorial_two_zero_10 m n)
          | succ k =>
              simpa using transvect_two_matches_factorial_right_boundary
                m n (k + 2) (by omega)
      | succ j =>
          exact transvect_two_matches_factorial_interior m n (i + 1) (j + 1)
            (by omega) (by omega)

end YMGap.Continuum.SU2TransvectantOrderTwo

#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.orderTwoBranch_normal_eq
#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.orderTwo_branch_identity
#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.transvect_two_matches_factorial_interior
#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.transvect_two_matches_factorial_left_boundary
#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.transvect_two_matches_factorial_right_boundary
#print axioms YMGap.Continuum.SU2TransvectantOrderTwo.transvect_two_matches_factorial
