/-
# Exact parity-sector orthogonality for quaternion product Haar

The all-degree positivity route first splits a polynomial into the 256 parity
sectors of its eight quaternion coordinates.  This file proves the atomic
orthogonality statement: if two monomials have different parity vectors,
their product has exactly zero product-Haar moment.
-/

import YMGap.Continuum.SU2QuaternionHaarSphereIdealAnnihilation

namespace YMGap.Continuum.SU2QuaternionHaarParitySectors

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- The eight coordinate residues modulo two. -/
structure Parity8 : Type where
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p4 : Nat
  p5 : Nat
  p6 : Nat
  p7 : Nat
deriving DecidableEq

def exponentParity8 (m : List Nat) : Parity8 where
  p0 := exponentAt m 0 % 2
  p1 := exponentAt m 1 % 2
  p2 := exponentAt m 2 % 2
  p3 := exponentAt m 3 % 2
  p4 := exponentAt m 4 % 2
  p5 := exponentAt m 5 % 2
  p6 := exponentAt m 6 % 2
  p7 := exponentAt m 7 % 2

def ParityMismatch8 (a b : Parity8) : Prop :=
  a.p0 ≠ b.p0 ∨ a.p1 ≠ b.p1 ∨ a.p2 ≠ b.p2 ∨ a.p3 ≠ b.p3 ∨
    a.p4 ≠ b.p4 ∨ a.p5 ≠ b.p5 ∨ a.p6 ≠ b.p6 ∨ a.p7 ≠ b.p7

theorem parityMismatch8_of_ne {a b : Parity8} (h : a ≠ b) :
    ParityMismatch8 a b := by
  unfold ParityMismatch8
  by_cases h0 : a.p0 = b.p0
  · by_cases h1 : a.p1 = b.p1
    · by_cases h2 : a.p2 = b.p2
      · by_cases h3 : a.p3 = b.p3
        · by_cases h4 : a.p4 = b.p4
          · by_cases h5 : a.p5 = b.p5
            · by_cases h6 : a.p6 = b.p6
              · by_cases h7 : a.p7 = b.p7
                · exfalso
                  apply h
                  cases a
                  cases b
                  simp_all
                · exact Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr h7))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl h6))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl h5)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inl h1)
  · exact Or.inl h0

private theorem exponentAt_monoMul (a b : List Nat) (i : Nat) :
    exponentAt (monoMul a b) i = exponentAt a i + exponentAt b i := by
  induction a generalizing b i with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases b with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases i with
          | zero => simp [monoMul, exponentAt]
          | succ i =>
              change exponentAt (monoMul xs ys) i =
                exponentAt xs i + exponentAt ys i
              exact ih ys i

private theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases hb : b with
  | false => rfl
  | true => exact (h hb).elim

private theorem productHaarMono_mul_zero_of_gMoment
    (a b : List Nat)
    (hzero : sphereMoment4
        (exponentAt a 0 + exponentAt b 0)
        (exponentAt a 1 + exponentAt b 1)
        (exponentAt a 2 + exponentAt b 2)
        (exponentAt a 3 + exponentAt b 3) = 0) :
    productHaarMono (monoMul a b) ≈ 0 := by
  by_cases htail : allZero ((monoMul a b).drop 8) = true
  · unfold productHaarMono
    rw [if_pos htail]
    simp only [exponentAt_monoMul]
    rw [hzero]
    exact Q'.zero_mul_eqv _
  · have hfalse := bool_false_of_not_true htail
    simp [productHaarMono, hfalse]
    exact Q'.eqv_refl 0

private theorem productHaarMono_mul_zero_of_hMoment
    (a b : List Nat)
    (hzero : sphereMoment4
        (exponentAt a 4 + exponentAt b 4)
        (exponentAt a 5 + exponentAt b 5)
        (exponentAt a 6 + exponentAt b 6)
        (exponentAt a 7 + exponentAt b 7) = 0) :
    productHaarMono (monoMul a b) ≈ 0 := by
  by_cases htail : allZero ((monoMul a b).drop 8) = true
  · unfold productHaarMono
    rw [if_pos htail]
    simp only [exponentAt_monoMul]
    rw [hzero]
    exact Q'.mul_zero_eqv _
  · have hfalse := bool_false_of_not_true htail
    simp [productHaarMono, hfalse]
    exact Q'.eqv_refl 0

/-- Distinct eight-coordinate parity sectors are exactly orthogonal for the
explicit product-Haar monomial functional. -/
theorem productHaarMono_cross_parity_zero (a b : List Nat)
    (hpar : ParityMismatch8 (exponentParity8 a) (exponentParity8 b)) :
    productHaarMono (monoMul a b) ≈ 0 := by
  unfold ParityMismatch8 exponentParity8 at hpar
  rcases hpar with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · change exponentAt a 0 % 2 ≠ exponentAt b 0 % 2 at h0
    have hodd : (exponentAt a 0 + exponentAt b 0) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_gMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 1 % 2 ≠ exponentAt b 1 % 2 at h1
    have hodd : (exponentAt a 1 + exponentAt b 1) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_gMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 2 % 2 ≠ exponentAt b 2 % 2 at h2
    have hodd : (exponentAt a 2 + exponentAt b 2) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_gMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 3 % 2 ≠ exponentAt b 3 % 2 at h3
    have hodd : (exponentAt a 3 + exponentAt b 3) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_gMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 4 % 2 ≠ exponentAt b 4 % 2 at h4
    have hodd : (exponentAt a 4 + exponentAt b 4) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_hMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 5 % 2 ≠ exponentAt b 5 % 2 at h5
    have hodd : (exponentAt a 5 + exponentAt b 5) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_hMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 6 % 2 ≠ exponentAt b 6 % 2 at h6
    have hodd : (exponentAt a 6 + exponentAt b 6) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_hMoment
    simp [sphereMoment4, hodd]
  · change exponentAt a 7 % 2 ≠ exponentAt b 7 % 2 at h7
    have hodd : (exponentAt a 7 + exponentAt b 7) % 2 ≠ 0 := by omega
    apply productHaarMono_mul_zero_of_hMoment
    simp [sphereMoment4, hodd]

theorem productHaarMono_cross_parity_zero_of_ne (a b : List Nat)
    (hpar : exponentParity8 a ≠ exponentParity8 b) :
    productHaarMono (monoMul a b) ≈ 0 :=
  productHaarMono_cross_parity_zero a b (parityMismatch8_of_ne hpar)

end YMGap.Continuum.SU2QuaternionHaarParitySectors

#print axioms YMGap.Continuum.SU2QuaternionHaarParitySectors.parityMismatch8_of_ne
#print axioms YMGap.Continuum.SU2QuaternionHaarParitySectors.productHaarMono_cross_parity_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarParitySectors.productHaarMono_cross_parity_zero_of_ne
