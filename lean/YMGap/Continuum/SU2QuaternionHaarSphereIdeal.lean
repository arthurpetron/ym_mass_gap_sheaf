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
open YMGap.Continuum.RingNormaliser
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

/-- The normalized `S^3` moment functional kills the sphere relation in every
parity sector, not only on even monomials. -/
theorem sphereMoment4_radius (e0 e1 e2 e3 : Nat) :
    sphereMoment4 (e0 + 2) e1 e2 e3 +
      (sphereMoment4 e0 (e1 + 2) e2 e3 +
        (sphereMoment4 e0 e1 (e2 + 2) e3 +
          sphereMoment4 e0 e1 e2 (e3 + 2))) ≈
      sphereMoment4 e0 e1 e2 e3 := by
  by_cases h0 : e0 % 2 = 0
  · by_cases h1 : e1 % 2 = 0
    · by_cases h2 : e2 % 2 = 0
      · by_cases h3 : e3 % 2 = 0
        · have he0 : e0 = 2 * (e0 / 2) := by omega
          have he1 : e1 = 2 * (e1 / 2) := by omega
          have he2 : e2 = 2 * (e2 / 2) := by omega
          have he3 : e3 = 2 * (e3 / 2) := by omega
          rw [he0, he1, he2, he3]
          exact sphereMoment4_even_radius _ _ _ _
        · simp [sphereMoment4, h3]
          decide
      · simp [sphereMoment4, h2]
        decide
    · simp [sphereMoment4, h1]
      decide
  · simp [sphereMoment4, h0]
    decide

private theorem four_mul_factor (a b c d h : Q') :
    a * h + (b * h + (c * h + d * h)) ≈
      (a + (b + (c + d))) * h := by
  have hcd : c * h + d * h ≈ (c + d) * h :=
    Q'.eqv_symm (Q'.add_mul_eqv c d h)
  have hbcd : b * h + (c * h + d * h) ≈
      (b + (c + d)) * h :=
    Q'.eqv_trans _ (b * h + (c + d) * h) _
      (Q'.add_eqv_congr_left _ _ _ hcd)
      (Q'.eqv_symm (Q'.add_mul_eqv b (c + d) h))
  exact Q'.eqv_trans _ (a * h + (b + (c + d)) * h) _
    (Q'.add_eqv_congr_left _ _ _ hbcd)
    (Q'.eqv_symm (Q'.add_mul_eqv a (b + (c + d)) h))

private theorem four_left_factor (h a b c d : Q') :
    h * a + (h * b + (h * c + h * d)) ≈
      h * (a + (b + (c + d))) := by
  have hcd : h * c + h * d ≈ h * (c + d) :=
    Q'.eqv_symm (Q'.mul_add_eqv h c d)
  have hbcd : h * b + (h * c + h * d) ≈
      h * (b + (c + d)) :=
    Q'.eqv_trans _ (h * b + h * (c + d)) _
      (Q'.add_eqv_congr_left _ _ _ hcd)
      (Q'.eqv_symm (Q'.mul_add_eqv h b (c + d)))
  exact Q'.eqv_trans _ (h * a + h * (b + (c + d))) _
    (Q'.add_eqv_congr_left _ _ _ hbcd)
    (Q'.eqv_symm (Q'.mul_add_eqv h a (b + (c + d))))

private theorem productHaar_single (m : List Nat) (c : Q') :
    productHaar [(m, c)] ≈ c * productHaarMono m := by
  change
    (match (productHaarMono m).num with
      | Int.ofNat 0 => 0
      | _ => c * productHaarMono m + 0) ≈
      c * productHaarMono m
  generalize hmu : productHaarMono m = mu
  cases hnum : mu.num with
  | ofNat n =>
      cases n with
      | zero =>
          simp only
          have hzero : mu ≈ 0 := by
            show mu.num * ((0 : Q').den : Int) =
              (0 : Q').num * (mu.den : Int)
            rw [hnum]
            change (0 : Int) * 1 = 0 * (mu.den : Int)
            simp
          exact Q'.eqv_trans _ (c * 0) _
            (Q'.eqv_symm (Q'.mul_zero_eqv c))
            (Q'.eqv_symm (Q'.mul_eqv_congr_left c mu 0 hzero))
      | succ n =>
          simp only
          exact Q'.eqv_of_eq (Q'.add_zero' _)
  | negSucc n =>
      simp only
      exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- The definition skips literal zero moments.  Extensionally it is the
ordinary coefficient-times-moment fold, which is the useful form for ideal
descent. -/
def productHaarLinearSum : RatPoly → Q'
  | [] => 0
  | t :: p => t.2 * productHaarMono t.1 + productHaarLinearSum p

theorem productHaar_eqv_linearSum : ∀ p : RatPoly,
    productHaar p ≈ productHaarLinearSum p
  | [] => Q'.eqv_refl 0
  | t :: p => by
      refine Q'.eqv_trans _
        (t.2 * productHaarMono t.1 + productHaar p) _ ?_ ?_
      · change productHaar ([t] ++ p) ≈
          t.2 * productHaarMono t.1 + productHaar p
        refine Q'.eqv_trans _ (productHaar [t] + productHaar p) _
          (productHaar_append_eqv [t] p) ?_
        exact Q'.add_eqv_congr' (productHaar_single t.1 t.2)
          (Q'.eqv_refl _)
      · exact Q'.add_eqv_congr_left _ _ _
          (productHaar_eqv_linearSum p)

/-- Literal first-boundary radius-square polynomial. -/
def gRadiusPolynomial : RatPoly :=
  [([2], 1), ([0, 2], 1), ([0, 0, 2], 1), ([0, 0, 0, 2], 1)]

/-- Literal second-boundary radius-square polynomial. -/
def hRadiusPolynomial : RatPoly :=
  [([0, 0, 0, 0, 2], 1), ([0, 0, 0, 0, 0, 2], 1),
    ([0, 0, 0, 0, 0, 0, 2], 1), ([0, 0, 0, 0, 0, 0, 0, 2], 1)]

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

private theorem monoMul_drop_of_length_le (a b : List Nat) (n : Nat)
    (h : b.length ≤ n) :
    (monoMul a b).drop n = a.drop n := by
  induction n generalizing a b with
  | zero =>
      cases b with
      | nil => cases a <;> rfl
      | cons y ys => simp at h
  | succ n ih =>
      cases a with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le h
      | cons x xs =>
          cases b with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at h
              simp [monoMul, ih xs ys (by omega)]

private theorem scaled_four_radius (q a b c d z : Q')
    (hradius : a + (b + (c + d)) ≈ z) :
    (q * 1) * a + ((q * 1) * b + ((q * 1) * c + (q * 1) * d)) ≈
      q * z := by
  have hq : q * 1 ≈ q := Q'.mul_one_eqv q
  refine Q'.eqv_trans _
    (q * a + (q * b + (q * c + q * d))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ hq)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hq)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ hq)
          (Q'.mul_eqv_congr_right _ _ _ hq)))
  · exact Q'.eqv_trans _ (q * (a + (b + (c + d)))) _
      (four_left_factor _ _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ hradius)

/-- The first boundary copy of the sphere relation is already annihilated at
the product-Haar monomial level. -/
theorem productHaarMono_g_radius
    (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) :
    productHaarMono [e0 + 2, e1, e2, e3, f0, f1, f2, f3] +
      (productHaarMono [e0, e1 + 2, e2, e3, f0, f1, f2, f3] +
        (productHaarMono [e0, e1, e2 + 2, e3, f0, f1, f2, f3] +
          productHaarMono [e0, e1, e2, e3 + 2, f0, f1, f2, f3])) ≈
      productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3] := by
  simp [productHaarMono, allZero, exponentAt]
  refine Q'.eqv_trans _
    ((sphereMoment4 (e0 + 2) e1 e2 e3 +
      (sphereMoment4 e0 (e1 + 2) e2 e3 +
        (sphereMoment4 e0 e1 (e2 + 2) e3 +
          sphereMoment4 e0 e1 e2 (e3 + 2)))) *
      sphereMoment4 f0 f1 f2 f3) _
    (four_mul_factor _ _ _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (sphereMoment4_radius e0 e1 e2 e3)

/-- The second boundary copy of the sphere relation is annihilated as well. -/
theorem productHaarMono_h_radius
    (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) :
    productHaarMono [e0, e1, e2, e3, f0 + 2, f1, f2, f3] +
      (productHaarMono [e0, e1, e2, e3, f0, f1 + 2, f2, f3] +
        (productHaarMono [e0, e1, e2, e3, f0, f1, f2 + 2, f3] +
          productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3 + 2])) ≈
      productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3] := by
  simp [productHaarMono, allZero, exponentAt]
  refine Q'.eqv_trans _
    (sphereMoment4 e0 e1 e2 e3 *
      (sphereMoment4 (f0 + 2) f1 f2 f3 +
        (sphereMoment4 f0 (f1 + 2) f2 f3 +
          (sphereMoment4 f0 f1 (f2 + 2) f3 +
            sphereMoment4 f0 f1 f2 (f3 + 2))))) _
    (four_left_factor _ _ _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (sphereMoment4_radius f0 f1 f2 f3)

/-- First-sphere radius descent for every exponent list, including terms with
out-of-carrier variables (which vanish on both sides). -/
theorem productHaarMono_mul_gRadius (m : List Nat) :
    productHaarMono (monoMul m [2]) +
      (productHaarMono (monoMul m [0, 2]) +
        (productHaarMono (monoMul m [0, 0, 2]) +
          productHaarMono (monoMul m [0, 0, 0, 2]))) ≈
      productHaarMono m := by
  by_cases htail : allZero (m.drop 8) = true
  · simp only [productHaarMono,
      monoMul_drop_of_length_le m [2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 2] 8 (by decide),
      htail, if_true, exponentAt_monoMul]
    simp only [exponentAt]
    simp
    refine Q'.eqv_trans _
      ((sphereMoment4 (exponentAt m 0 + 2) (exponentAt m 1)
          (exponentAt m 2) (exponentAt m 3) +
        (sphereMoment4 (exponentAt m 0) (exponentAt m 1 + 2)
            (exponentAt m 2) (exponentAt m 3) +
          (sphereMoment4 (exponentAt m 0) (exponentAt m 1)
              (exponentAt m 2 + 2) (exponentAt m 3) +
            sphereMoment4 (exponentAt m 0) (exponentAt m 1)
              (exponentAt m 2) (exponentAt m 3 + 2)))) *
        sphereMoment4 (exponentAt m 4) (exponentAt m 5)
          (exponentAt m 6) (exponentAt m 7)) _
      (four_mul_factor _ _ _ _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (sphereMoment4_radius (exponentAt m 0) (exponentAt m 1)
        (exponentAt m 2) (exponentAt m 3))
  · have hfalse : allZero (m.drop 8) = false := by
      cases hvalue : allZero (m.drop 8) with
      | false => rfl
      | true => exact (htail hvalue).elim
    simp only [productHaarMono,
      monoMul_drop_of_length_le m [2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 2] 8 (by decide),
      hfalse]
    simp
    decide

/-- Second-sphere radius descent for every exponent list. -/
theorem productHaarMono_mul_hRadius (m : List Nat) :
    productHaarMono (monoMul m [0, 0, 0, 0, 2]) +
      (productHaarMono (monoMul m [0, 0, 0, 0, 0, 2]) +
        (productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 2]) +
          productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 0, 2]))) ≈
      productHaarMono m := by
  by_cases htail : allZero (m.drop 8) = true
  · simp only [productHaarMono,
      monoMul_drop_of_length_le m [0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 0, 0, 2] 8 (by decide),
      htail, if_true, exponentAt_monoMul]
    simp only [exponentAt]
    simp
    refine Q'.eqv_trans _
      (sphereMoment4 (exponentAt m 0) (exponentAt m 1)
          (exponentAt m 2) (exponentAt m 3) *
        (sphereMoment4 (exponentAt m 4 + 2) (exponentAt m 5)
            (exponentAt m 6) (exponentAt m 7) +
          (sphereMoment4 (exponentAt m 4) (exponentAt m 5 + 2)
              (exponentAt m 6) (exponentAt m 7) +
            (sphereMoment4 (exponentAt m 4) (exponentAt m 5)
                (exponentAt m 6 + 2) (exponentAt m 7) +
              sphereMoment4 (exponentAt m 4) (exponentAt m 5)
                (exponentAt m 6) (exponentAt m 7 + 2))))) _
      (four_left_factor _ _ _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (sphereMoment4_radius (exponentAt m 4) (exponentAt m 5)
        (exponentAt m 6) (exponentAt m 7))
  · have hfalse : allZero (m.drop 8) = false := by
      cases hvalue : allZero (m.drop 8) with
      | false => rfl
      | true => exact (htail hvalue).elim
    simp only [productHaarMono,
      monoMul_drop_of_length_le m [0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 0, 2] 8 (by decide),
      monoMul_drop_of_length_le m [0, 0, 0, 0, 0, 0, 0, 2] 8 (by decide),
      hfalse]
    simp
    decide

private theorem productHaar_mul_gRadius_single (m : List Nat) (q : Q') :
    productHaar (polyMul [(m, q)] gRadiusPolynomial) ≈
      productHaar [(m, q)] := by
  refine Q'.eqv_trans _
    (productHaarLinearSum (polyMul [(m, q)] gRadiusPolynomial)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) * productHaarMono (monoMul m [2]) +
      ((q * 1) * productHaarMono (monoMul m [0, 2]) +
        ((q * 1) * productHaarMono (monoMul m [0, 0, 2]) +
          ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 2]) + 0))) ≈
      productHaar [(m, q)]
  rw [Q'.add_zero']
  refine Q'.eqv_trans _ (q * productHaarMono m) _ ?_ ?_
  · exact scaled_four_radius _ _ _ _ _ _
      (productHaarMono_mul_gRadius m)
  · exact Q'.eqv_symm (productHaar_single m q)

private theorem productHaar_mul_hRadius_single (m : List Nat) (q : Q') :
    productHaar (polyMul [(m, q)] hRadiusPolynomial) ≈
      productHaar [(m, q)] := by
  refine Q'.eqv_trans _
    (productHaarLinearSum (polyMul [(m, q)] hRadiusPolynomial)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 2]) +
      ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 0, 2]) +
        ((q * 1) * productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 2]) +
          ((q * 1) *
            productHaarMono (monoMul m [0, 0, 0, 0, 0, 0, 0, 2]) + 0))) ≈
      productHaar [(m, q)]
  rw [Q'.add_zero']
  refine Q'.eqv_trans _ (q * productHaarMono m) _ ?_ ?_
  · exact scaled_four_radius _ _ _ _ _ _
      (productHaarMono_mul_hRadius m)
  · exact Q'.eqv_symm (productHaar_single m q)

/-- Product Haar descends through the first sphere equation on the entire
finite-support polynomial carrier. -/
theorem productHaar_mul_gRadius : ∀ p : RatPoly,
    productHaar (polyMul p gRadiusPolynomial) ≈ productHaar p
  | [] => Q'.eqv_refl 0
  | t :: p => by
      have hmul :
          polyMul (t :: p) gRadiusPolynomial =
            polyMul [t] gRadiusPolynomial ++
              polyMul p gRadiusPolynomial := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [t] gRadiusPolynomial) +
          productHaar (polyMul p gRadiusPolynomial)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (productHaar [t] + productHaar p) _
        (Q'.add_eqv_congr'
          (productHaar_mul_gRadius_single t.1 t.2)
          (productHaar_mul_gRadius p)) ?_
      change productHaar [t] + productHaar p ≈ productHaar ([t] ++ p)
      exact Q'.eqv_symm (productHaar_append_eqv [t] p)

/-- Product Haar descends through the second sphere equation on the entire
finite-support polynomial carrier. -/
theorem productHaar_mul_hRadius : ∀ p : RatPoly,
    productHaar (polyMul p hRadiusPolynomial) ≈ productHaar p
  | [] => Q'.eqv_refl 0
  | t :: p => by
      have hmul :
          polyMul (t :: p) hRadiusPolynomial =
            polyMul [t] hRadiusPolynomial ++
              polyMul p hRadiusPolynomial := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [t] hRadiusPolynomial) +
          productHaar (polyMul p hRadiusPolynomial)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (productHaar [t] + productHaar p) _
        (Q'.add_eqv_congr'
          (productHaar_mul_hRadius_single t.1 t.2)
          (productHaar_mul_hRadius p)) ?_
      change productHaar [t] + productHaar p ≈ productHaar ([t] ++ p)
      exact Q'.eqv_symm (productHaar_append_eqv [t] p)

/-- On a canonical eight-coordinate monomial, multiplication by the first
radius-square polynomial does not change product Haar.  This is the concrete
monomial generator of first-sphere ideal descent. -/
theorem productHaar_mul_gRadius_canonical
    (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) (q : Q') :
    productHaar
        (polyMul [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
          gRadiusPolynomial) ≈
      productHaar [([e0, e1, e2, e3, f0, f1, f2, f3], q)] := by
  refine Q'.eqv_trans _
    (productHaarLinearSum
      (polyMul [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
        gRadiusPolynomial)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) *
          productHaarMono [e0 + 2, e1, e2, e3, f0, f1, f2, f3] +
      ((q * 1) *
          productHaarMono [e0, e1 + 2, e2, e3, f0, f1, f2, f3] +
        ((q * 1) *
            productHaarMono [e0, e1, e2 + 2, e3, f0, f1, f2, f3] +
          ((q * 1) *
            productHaarMono [e0, e1, e2, e3 + 2, f0, f1, f2, f3] + 0))) ≈
      productHaar [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
  rw [Q'.add_zero']
  refine Q'.eqv_trans _
    (q * productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3]) _ ?_ ?_
  · exact scaled_four_radius _ _ _ _ _ _
      (productHaarMono_g_radius e0 e1 e2 e3 f0 f1 f2 f3)
  · exact Q'.eqv_symm
      (productHaar_single [e0, e1, e2, e3, f0, f1, f2, f3] q)

/-- Canonical monomial descent for the second sphere radius. -/
theorem productHaar_mul_hRadius_canonical
    (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) (q : Q') :
    productHaar
        (polyMul [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
          hRadiusPolynomial) ≈
      productHaar [([e0, e1, e2, e3, f0, f1, f2, f3], q)] := by
  refine Q'.eqv_trans _
    (productHaarLinearSum
      (polyMul [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
        hRadiusPolynomial)) _
    (productHaar_eqv_linearSum _) ?_
  change
    (q * 1) *
          productHaarMono [e0, e1, e2, e3, f0 + 2, f1, f2, f3] +
      ((q * 1) *
          productHaarMono [e0, e1, e2, e3, f0, f1 + 2, f2, f3] +
        ((q * 1) *
            productHaarMono [e0, e1, e2, e3, f0, f1, f2 + 2, f3] +
          ((q * 1) *
            productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3 + 2] + 0))) ≈
      productHaar [([e0, e1, e2, e3, f0, f1, f2, f3], q)]
  rw [Q'.add_zero']
  refine Q'.eqv_trans _
    (q * productHaarMono [e0, e1, e2, e3, f0, f1, f2, f3]) _ ?_ ?_
  · exact scaled_four_radius _ _ _ _ _ _
      (productHaarMono_h_radius e0 e1 e2 e3 f0 f1 f2 f3)
  · exact Q'.eqv_symm
      (productHaar_single [e0, e1, e2, e3, f0, f1, f2, f3] q)

end YMGap.Continuum.SU2QuaternionHaarSphereIdeal

#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.sphereMoment4_even
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.sphereMoment4_even_radius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.sphereMoment4_radius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaarMono_g_radius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaarMono_h_radius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaarMono_mul_gRadius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaarMono_mul_hRadius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaar_eqv_linearSum
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaar_mul_gRadius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaar_mul_hRadius
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaar_mul_gRadius_canonical
#print axioms YMGap.Continuum.SU2QuaternionHaarSphereIdeal.productHaar_mul_hRadius_canonical
