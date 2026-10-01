/-
# Finite dyadic-power comparison for the ORIGINAL physical Cayley maps

The maps are the existing represented Wilson-bond Cayley operators.  This
module compares their actual finite Rows.iterate values at two rational
parameters.  It supplies algebraic amplification for a future product
Cauchy modulus; it does not itself take a limit or identify physical time.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
  (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le fourCopies fourCopies_eq_scale_four)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "Z" =>
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

private theorem cayley_norm (t : Q') (ht : (0 : Q') < t) (x : H) :
    N (C t ht x) = N x :=
  congrArg Prod.fst
    (BF4WilsonAllNomeComplexBondOSScaledCayley.pairing_preserved
      hw0 hw1 t ht x x)

private theorem cayley_zero (t : Q') (ht : (0 : Q') < t) :
    C t ht Z = Z := by
  have h : C t ht Z = A (C t ht Z) (C t ht Z) := by
    calc
      C t ht Z = C t ht (A Z Z) :=
        congrArg (C t ht)
          ((BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.zero_add
            hw0 hw1 Z).symm)
      _ = A (C t ht Z) (C t ht Z) :=
        BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add hw0 hw1 t ht Z Z
  apply BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_left_cancel
    hw0 hw1 (C t ht Z)
  calc
    A (C t ht Z) (C t ht Z) = C t ht Z := h.symm
    _ = A (C t ht Z) Z :=
      (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero
        hw0 hw1 (C t ht Z)).symm

private theorem cayley_neg (t : Q') (ht : (0 : Q') < t) (x : H) :
    C t ht (cneg hw0 hw1 x) = cneg hw0 hw1 (C t ht x) := by
  apply BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_left_cancel
    hw0 hw1 (C t ht x)
  calc
    A (C t ht x) (C t ht (cneg hw0 hw1 x)) =
        C t ht (A x (cneg hw0 hw1 x)) :=
          (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add
            hw0 hw1 t ht _ _).symm
    _ = C t ht Z :=
      congrArg (C t ht)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_neg
          hw0 hw1 x)
    _ = Z := cayley_zero hw0 hw1 t ht
    _ = A (C t ht x) (cneg hw0 hw1 (C t ht x)) :=
      (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_neg
        hw0 hw1 (C t ht x)).symm

private theorem cayley_diff (t : Q') (ht : (0 : Q') < t)
    (x y : H) :
    C t ht (diff hw0 hw1 x y) =
      diff hw0 hw1 (C t ht x) (C t ht y) := by
  unfold diff
  rw [BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add,cayley_neg]

/-- The existing Rows.iterate convention is right-compatible with adding
any two finite exponents. -/
theorem iterate_add_index (t : Q') (ht : (0 : Q') < t)
    (x : H) (m n : Nat) :
    iterate hw0 hw1 t ht x (m+n) =
      iterate hw0 hw1 t ht (iterate hw0 hw1 t ht x m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ,iterate,iterate,ih]

/-- Actual finite Cayley powers preserve complex addition. -/
theorem iterate_add (t : Q') (ht : (0 : Q') < t)
    (x y : H) (n : Nat) :
    iterate hw0 hw1 t ht (A x y) n =
      A (iterate hw0 hw1 t ht x n) (iterate hw0 hw1 t ht y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change C t ht (iterate hw0 hw1 t ht (A x y) n) = _
      rw [ih,BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add]
      rfl

private theorem iterate_neg (t : Q') (ht : (0 : Q') < t)
    (x : H) (n : Nat) :
    iterate hw0 hw1 t ht (cneg hw0 hw1 x) n =
      cneg hw0 hw1 (iterate hw0 hw1 t ht x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change C t ht (iterate hw0 hw1 t ht (cneg hw0 hw1 x) n) = _
      rw [ih,cayley_neg]
      rfl

/-- Difference transport for the very same represented finite power. -/
theorem iterate_diff (t : Q') (ht : (0 : Q') < t)
    (x y : H) (n : Nat) :
    iterate hw0 hw1 t ht (diff hw0 hw1 x y) n =
      diff hw0 hw1 (iterate hw0 hw1 t ht x n)
        (iterate hw0 hw1 t ht y n) := by
  unfold diff
  rw [iterate_add,iterate_neg]

/-- Squared-norm isometry of every actual finite Cayley iterate. -/
theorem iterate_norm (t : Q') (ht : (0 : Q') < t)
    (x : H) (n : Nat) :
    N (iterate hw0 hw1 t ht x n) = N x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change N (C t ht (iterate hw0 hw1 t ht x n)) = N x
      rw [cayley_norm,ih]

private theorem cayley_iterate_commute (t s : Q')
    (ht : (0 : Q') < t) (hs : (0 : Q') < s)
    (x : H) (n : Nat) :
    C t ht (iterate hw0 hw1 s hs x n) =
      iterate hw0 hw1 s hs (C t ht x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change C t ht (C s hs (iterate hw0 hw1 s hs x n)) = _
      rw [BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation.cayley_commute,ih]
      rfl

/-- Finite powers of two rational parameters of the SAME original graph
commute on every physical complex bond class. -/
theorem iterate_cross_commute (t s : Q')
    (ht : (0 : Q') < t) (hs : (0 : Q') < s)
    (x : H) (m n : Nat) :
    iterate hw0 hw1 t ht (iterate hw0 hw1 s hs x n) m =
      iterate hw0 hw1 s hs (iterate hw0 hw1 t ht x m) n := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change C t ht (iterate hw0 hw1 t ht
        (iterate hw0 hw1 s hs x n) m) = _
      rw [ih,cayley_iterate_commute]
      rfl

private theorem diff_trans (a b c : H) :
    A (diff hw0 hw1 a b) (diff hw0 hw1 b c) = diff hw0 hw1 a c := by
  have hassoc : ∀ x y z : H, A (A x y) z = A x (A y z) :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1
  have hcomm : ∀ x y : H, A x y = A y x :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_comm hw0 hw1
  unfold diff
  calc
    A (A a (cneg hw0 hw1 b)) (A b (cneg hw0 hw1 c)) =
        A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) := by
      calc
        A (A a (cneg hw0 hw1 b)) (A b (cneg hw0 hw1 c)) =
            A (A a (cneg hw0 hw1 b)) (A (cneg hw0 hw1 c) b) := by
              rw [hcomm b (cneg hw0 hw1 c)]
        _ = A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) := by
          calc
            A (A a (cneg hw0 hw1 b)) (A (cneg hw0 hw1 c) b) =
                A a (A (cneg hw0 hw1 b) (A (cneg hw0 hw1 c) b)) :=
                  hassoc _ _ _
            _ = A a (A (cneg hw0 hw1 c) (A (cneg hw0 hw1 b) b)) := by
              rw [← hassoc (cneg hw0 hw1 b) (cneg hw0 hw1 c) b,
                hcomm (cneg hw0 hw1 b) (cneg hw0 hw1 c),hassoc]
            _ = A (A a (cneg hw0 hw1 c)) (A (cneg hw0 hw1 b) b) :=
              (hassoc _ _ _).symm
    _ = A (A a (cneg hw0 hw1 c)) Z :=
      congrArg (A (A a (cneg hw0 hw1 c)))
        (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add
          hw0 hw1 b)
    _ = A a (cneg hw0 hw1 c) :=
      BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero hw0 hw1 _

/-- One squaring of two commuting actual Cayley powers costs at most four
in squared norm, without division or a zero-norm case split. -/
theorem squared_difference_norm_le (t s : Q')
    (ht : (0 : Q') < t) (hs : (0 : Q') < s)
    (x : H) (m k : Nat) :
    RCle
      (N (diff hw0 hw1
        (iterate hw0 hw1 t ht (iterate hw0 hw1 t ht x m) m)
        (iterate hw0 hw1 s hs (iterate hw0 hw1 s hs x k) k)))
      (RCscale 4 (N (diff hw0 hw1
        (iterate hw0 hw1 t ht x m) (iterate hw0 hw1 s hs x k)))) := by
  let u := iterate hw0 hw1 t ht x m
  let v := iterate hw0 hw1 s hs x k
  let δ := diff hw0 hw1 u v
  have hid : diff hw0 hw1
      (iterate hw0 hw1 t ht u m)
      (iterate hw0 hw1 s hs v k) =
      A (iterate hw0 hw1 t ht δ m) (iterate hw0 hw1 s hs δ k) := by
    calc
      diff hw0 hw1 (iterate hw0 hw1 t ht u m)
          (iterate hw0 hw1 s hs v k) =
        A (diff hw0 hw1 (iterate hw0 hw1 t ht u m)
              (iterate hw0 hw1 t ht v m))
          (diff hw0 hw1 (iterate hw0 hw1 t ht v m)
              (iterate hw0 hw1 s hs v k)) :=
          (diff_trans hw0 hw1 _ _ _).symm
      _ = A (iterate hw0 hw1 t ht δ m)
          (diff hw0 hw1 (iterate hw0 hw1 s hs u k)
            (iterate hw0 hw1 s hs v k)) := by
              rw [← iterate_diff hw0 hw1 t ht u v m]
              exact congrArg (fun z => A (iterate hw0 hw1 t ht δ m)
                (diff hw0 hw1 z (iterate hw0 hw1 s hs v k)))
                (iterate_cross_commute hw0 hw1 t s ht hs x m k)
      _ = A (iterate hw0 hw1 t ht δ m)
          (iterate hw0 hw1 s hs δ k) := by
            rw [← iterate_diff hw0 hw1 s hs u v k]
  rw [hid]
  have h := normSq_add_le hw0 hw1
    (iterate hw0 hw1 t ht δ m) (iterate hw0 hw1 s hs δ k)
  rw [iterate_norm,iterate_norm] at h
  change RCle (N (A (iterate hw0 hw1 t ht δ m)
    (iterate hw0 hw1 s hs δ k))) (fourCopies (N δ)) at h
  rw [fourCopies_eq_scale_four] at h
  exact h

/-- Dyadic amplification for the EXACT Rows.iterate physical Cayley powers,
starting from arbitrary two finite counts.  The factor is constructive
rational data, not an assumed stability field. -/
theorem dyadic_iterate_comparison (t s : Q')
    (ht : (0 : Q') < t) (hs : (0 : Q') < s)
    (x : H) (a b n : Nat) :
    RCle
      (N (diff hw0 hw1
        (iterate hw0 hw1 t ht x (a*2^n))
        (iterate hw0 hw1 s hs x (b*2^n))))
      (RCscale ((4 : Q')^n)
        (N (diff hw0 hw1
          (iterate hw0 hw1 t ht x a)
          (iterate hw0 hw1 s hs x b)))) := by
  induction n with
  | zero =>
      simp only [Nat.pow_zero,Nat.mul_one,Q'.pow_zero,RCscale_one]
      exact RCle_refl _
  | succ n ih =>
      have ha : a*2^(n+1) = (a*2^n)+(a*2^n) := by
        rw [Nat.pow_succ]
        rw [← Nat.mul_assoc]
        omega
      have hb : b*2^(n+1) = (b*2^n)+(b*2^n) := by
        rw [Nat.pow_succ]
        rw [← Nat.mul_assoc]
        omega
      rw [ha,hb,
        iterate_add_index hw0 hw1 t ht x (a*2^n) (a*2^n),
        iterate_add_index hw0 hw1 s hs x (b*2^n) (b*2^n)]
      have hsq := squared_difference_norm_le hw0 hw1 t s ht hs x
        (a*2^n) (b*2^n)
      have hscaled := RCscale_mono (by decide : (0 : Q') ≤ 4) ih
      have h := RCle_trans hsq hscaled
      rw [RCscale_RCscale] at h
      simpa only [Q'.pow_succ] using h

#print axioms iterate_add_index
#print axioms iterate_add
#print axioms iterate_diff
#print axioms iterate_norm
#print axioms iterate_cross_commute
#print axioms squared_difference_norm_le
#print axioms dyadic_iterate_comparison

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
