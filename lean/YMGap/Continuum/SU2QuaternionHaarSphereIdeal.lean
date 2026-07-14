/-
# The exact S^3 Haar moment recurrence and sphere ideal

For the explicit quaternion moment formula, this file attacks the all-degree
sphere quotient through its atomic monomial recurrence

  sum_i M(e + 2 e_i) = M(e).

The even-exponent calculation is reduced to a common-denominator identity;
odd parity is preserved by adding two and therefore vanishes termwise.
-/

import YMGap.Continuum.SU2QuaternionWilsonWeightSOS

namespace YMGap.Continuum.SU2QuaternionHaarSphereIdeal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def totalK (k0 k1 k2 k3 : Nat) : Nat := k0 + k1 + k2 + k3

def evenNumerator (k0 k1 k2 k3 : Nat) : Nat :=
  oddDoubleFactorial k0 * oddDoubleFactorial k1 *
    oddDoubleFactorial k2 * oddDoubleFactorial k3

def evenMoment (k0 k1 k2 k3 : Nat) : Q' :=
  Q'.mkPos (Int.ofNat (evenNumerator k0 k1 k2 k3))
    (sphereFourDenominator (totalK k0 k1 k2 k3))
    (sphereFourDenominator_pos _)

private theorem oddDoubleFactorial_succ (k : Nat) :
    oddDoubleFactorial (k + 1) =
      (2 * k + 1) * oddDoubleFactorial k := by
  rfl

private theorem sphereFourDenominator_succ (k : Nat) :
    sphereFourDenominator (k + 1) =
      (4 + 2 * k) * sphereFourDenominator k := by
  rfl

theorem sphereMoment4_even (k0 k1 k2 k3 : Nat) :
    sphereMoment4 (2 * k0) (2 * k1) (2 * k2) (2 * k3) =
      evenMoment k0 k1 k2 k3 := by
  simp [sphereMoment4, evenMoment, evenNumerator, totalK]

def commonFactor (k0 k1 k2 k3 : Nat) : Nat :=
  4 + 2 * totalK k0 k1 k2 k3

def scaledEvenMoment (c k0 k1 k2 k3 : Nat) : Q' :=
  Q'.mkPos (Int.ofNat (c * evenNumerator k0 k1 k2 k3))
    (commonFactor k0 k1 k2 k3 *
      sphereFourDenominator (totalK k0 k1 k2 k3))
    (Nat.mul_pos (by unfold commonFactor; omega)
      (sphereFourDenominator_pos _))

private theorem scaledEvenMoment_add (a b k0 k1 k2 k3 : Nat) :
    scaledEvenMoment a k0 k1 k2 k3 +
        scaledEvenMoment b k0 k1 k2 k3 ≈
      scaledEvenMoment (a + b) k0 k1 k2 k3 := by
  unfold scaledEvenMoment
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  have hnum :
      Int.ofNat (a * evenNumerator k0 k1 k2 k3) +
          Int.ofNat (b * evenNumerator k0 k1 k2 k3) =
        Int.ofNat ((a + b) * evenNumerator k0 k1 k2 k3) := by
    exact congrArg Int.ofNat
      (Nat.add_mul a b (evenNumerator k0 k1 k2 k3)).symm
  rw [← Int.add_mul, hnum]
  ac_rfl

private theorem scaledEvenMoment_full (k0 k1 k2 k3 : Nat) :
    scaledEvenMoment (commonFactor k0 k1 k2 k3) k0 k1 k2 k3 ≈
      evenMoment k0 k1 k2 k3 := by
  unfold scaledEvenMoment evenMoment
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  have hnum :
      Int.ofNat
          (commonFactor k0 k1 k2 k3 * evenNumerator k0 k1 k2 k3) =
        Int.ofNat (evenNumerator k0 k1 k2 k3) *
          Int.ofNat (commonFactor k0 k1 k2 k3) := by
    exact congrArg Int.ofNat (Nat.mul_comm _ _)
  rw [hnum]
  change
    Int.ofNat (evenNumerator k0 k1 k2 k3) *
          Int.ofNat (commonFactor k0 k1 k2 k3) *
          Int.ofNat (sphereFourDenominator (totalK k0 k1 k2 k3)) =
      Int.ofNat (evenNumerator k0 k1 k2 k3) *
        (Int.ofNat (commonFactor k0 k1 k2 k3) *
          Int.ofNat (sphereFourDenominator (totalK k0 k1 k2 k3)))
  ac_rfl

private theorem successor0_scaled (k0 k1 k2 k3 : Nat) :
    evenMoment (k0 + 1) k1 k2 k3 ≈
      scaledEvenMoment (2 * k0 + 1) k0 k1 k2 k3 := by
  unfold evenMoment scaledEvenMoment evenNumerator totalK commonFactor
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  rw [show k0 + 1 + k1 + k2 + k3 = (k0 + k1 + k2 + k3) + 1 by omega]
  rw [oddDoubleFactorial_succ, sphereFourDenominator_succ]
  simp only [← Int.ofNat_mul_ofNat, ← Int.ofNat_add_ofNat]
  rw [show totalK k0 k1 k2 k3 = k0 + (k1 + (k2 + k3)) by
    unfold totalK
    omega]
  ac_rfl

private theorem successor1_scaled (k0 k1 k2 k3 : Nat) :
    evenMoment k0 (k1 + 1) k2 k3 ≈
      scaledEvenMoment (2 * k1 + 1) k0 k1 k2 k3 := by
  unfold evenMoment scaledEvenMoment evenNumerator totalK commonFactor
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  rw [show k0 + (k1 + 1) + k2 + k3 = (k0 + k1 + k2 + k3) + 1 by omega]
  rw [oddDoubleFactorial_succ, sphereFourDenominator_succ]
  simp only [← Int.ofNat_mul_ofNat, ← Int.ofNat_add_ofNat]
  rw [show totalK k0 k1 k2 k3 = k0 + (k1 + (k2 + k3)) by
    unfold totalK
    omega]
  ac_rfl

private theorem successor2_scaled (k0 k1 k2 k3 : Nat) :
    evenMoment k0 k1 (k2 + 1) k3 ≈
      scaledEvenMoment (2 * k2 + 1) k0 k1 k2 k3 := by
  unfold evenMoment scaledEvenMoment evenNumerator totalK commonFactor
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  rw [show k0 + k1 + (k2 + 1) + k3 = (k0 + k1 + k2 + k3) + 1 by omega]
  rw [oddDoubleFactorial_succ, sphereFourDenominator_succ]
  simp only [← Int.ofNat_mul_ofNat, ← Int.ofNat_add_ofNat]
  rw [show totalK k0 k1 k2 k3 = k0 + (k1 + (k2 + k3)) by
    unfold totalK
    omega]
  ac_rfl

private theorem successor3_scaled (k0 k1 k2 k3 : Nat) :
    evenMoment k0 k1 k2 (k3 + 1) ≈
      scaledEvenMoment (2 * k3 + 1) k0 k1 k2 k3 := by
  unfold evenMoment scaledEvenMoment evenNumerator totalK commonFactor
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  rw [show k0 + k1 + k2 + (k3 + 1) = (k0 + k1 + k2 + k3) + 1 by omega]
  rw [oddDoubleFactorial_succ, sphereFourDenominator_succ]
  simp only [← Int.ofNat_mul_ofNat, ← Int.ofNat_add_ofNat]
  rw [show totalK k0 k1 k2 k3 = k0 + (k1 + (k2 + k3)) by
    unfold totalK
    omega]
  ac_rfl

theorem sphereMoment4_even_radius (k0 k1 k2 k3 : Nat) :
    sphereMoment4 (2 * k0 + 2) (2 * k1) (2 * k2) (2 * k3) +
      (sphereMoment4 (2 * k0) (2 * k1 + 2) (2 * k2) (2 * k3) +
        (sphereMoment4 (2 * k0) (2 * k1) (2 * k2 + 2) (2 * k3) +
          sphereMoment4 (2 * k0) (2 * k1) (2 * k2) (2 * k3 + 2))) ≈
      sphereMoment4 (2 * k0) (2 * k1) (2 * k2) (2 * k3) := by
  rw [show 2 * k0 + 2 = 2 * (k0 + 1) by omega,
    show 2 * k1 + 2 = 2 * (k1 + 1) by omega,
    show 2 * k2 + 2 = 2 * (k2 + 1) by omega,
    show 2 * k3 + 2 = 2 * (k3 + 1) by omega]
  rw [sphereMoment4_even, sphereMoment4_even, sphereMoment4_even,
    sphereMoment4_even, sphereMoment4_even]
  refine Q'.eqv_trans _
    (scaledEvenMoment (2 * k0 + 1) k0 k1 k2 k3 +
      (scaledEvenMoment (2 * k1 + 1) k0 k1 k2 k3 +
        (scaledEvenMoment (2 * k2 + 1) k0 k1 k2 k3 +
          scaledEvenMoment (2 * k3 + 1) k0 k1 k2 k3))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (successor0_scaled _ _ _ _)
      (Q'.add_eqv_congr' (successor1_scaled _ _ _ _)
        (Q'.add_eqv_congr' (successor2_scaled _ _ _ _)
          (successor3_scaled _ _ _ _)))
  · refine Q'.eqv_trans _
      (scaledEvenMoment
        ((2 * k0 + 1) + ((2 * k1 + 1) + ((2 * k2 + 1) + (2 * k3 + 1))))
        k0 k1 k2 k3) _ ?_ ?_
    · exact Q'.eqv_trans _
        (scaledEvenMoment (2 * k0 + 1) k0 k1 k2 k3 +
          scaledEvenMoment
            ((2 * k1 + 1) + ((2 * k2 + 1) + (2 * k3 + 1)))
            k0 k1 k2 k3) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _
            (scaledEvenMoment (2 * k1 + 1) k0 k1 k2 k3 +
              scaledEvenMoment ((2 * k2 + 1) + (2 * k3 + 1)) k0 k1 k2 k3) _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (scaledEvenMoment_add _ _ _ _ _ _))
            (scaledEvenMoment_add _ _ _ _ _ _)))
        (scaledEvenMoment_add _ _ _ _ _ _)
    · have hcoeff :
        (2 * k0 + 1) + ((2 * k1 + 1) + ((2 * k2 + 1) + (2 * k3 + 1))) =
          commonFactor k0 k1 k2 k3 := by
        unfold commonFactor totalK
        omega
      rw [hcoeff]
      exact scaledEvenMoment_full _ _ _ _

end YMGap.Continuum.SU2QuaternionHaarSphereIdeal

#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.sphereMoment4_even
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.sphereMoment4_even_radius
