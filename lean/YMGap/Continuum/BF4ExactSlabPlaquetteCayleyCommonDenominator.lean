/-
# Common-denominator clearing for the exact Cayley plaquette identity

If four chart triples share a positive rational scale `e = 1/D`, multiplying
the exact cleared Cayley identity by `D^8` removes every reciprocal.  The
result is an explicit polynomial identity: the four chart factors become
`D^2 + norm3`, while the degree-two-through-six deficit terms acquire powers
`D^6` down to `D^2`.

This algebraic compiler does not yet construct the common denominator from an
actual sign sector or integrate the resulting polynomial under the ORIGINAL
law.  It is the exact denominator-clearing consumer needed by that next step.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

def pow2 (x : Q') : Q' := x * x
def pow3 (x : Q') : Q' := (x * x) * x
def pow4 (x : Q') : Q' := (x * x) * (x * x)
def pow5 (x : Q') : Q' := ((x * x) * (x * x)) * x
def pow6 (x : Q') : Q' := ((x * x) * (x * x)) * (x * x)
def pow8 (x : Q') : Q' := ((x * x) * (x * x)) * ((x * x) * (x * x))

private def ep2 (x : PE) : PE := x * x
private def ep3 (x : PE) : PE := (x * x) * x
private def ep4 (x : PE) : PE := (x * x) * (x * x)
private def ep5 (x : PE) : PE := ((x * x) * (x * x)) * x
private def ep6 (x : PE) : PE := ((x * x) * (x * x)) * (x * x)
private def ep8 (x : PE) : PE := ((x * x) * (x * x)) * ((x * x) * (x * x))

private theorem pow2_one_of_eqv_one {x : Q'} (h : x ≈ 1) : pow2 x ≈ 1 :=
  Q'.eqv_trans _ _ _ (mc h h) (by decide)

private theorem pow3_one_of_eqv_one {x : Q'} (h : x ≈ 1) : pow3 x ≈ 1 :=
  Q'.eqv_trans _ _ _ (mc (mc h h) h) (by decide)

private theorem pow4_one_of_eqv_one {x : Q'} (h : x ≈ 1) : pow4 x ≈ 1 :=
  Q'.eqv_trans _ _ _ (mc (mc h h) (mc h h)) (by decide)

private theorem pow5_one_of_eqv_one {x : Q'} (h : x ≈ 1) : pow5 x ≈ 1 :=
  Q'.eqv_trans _ _ _ (mc (mc (mc h h) (mc h h)) h) (by decide)

private theorem pow6_one_of_eqv_one {x : Q'} (h : x ≈ 1) : pow6 x ≈ 1 :=
  Q'.eqv_trans _ _ _ (mc (mc (mc h h) (mc h h)) (mc h h)) (by decide)

private theorem scale_clear_two (D e x : Q') (hDe : D * e ≈ 1) :
    pow8 D * (pow2 e * x) ≈ pow6 D * x := by
  have hpoly : pow8 D * (pow2 e * x) ≈
      pow6 D * (pow2 (D * e) * x) := by
    exact poly_identity_of_normal_eq
      (ep8 (.var 0) * (ep2 (.var 1) * .var 2))
      (ep6 (.var 0) * (ep2 (.var 0 * .var 1) * .var 2))
      (by decide) (fun | 0 => D | 1 => e | _ => x)
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow2_one_of_eqv_one hDe) (Q'.eqv_refl x))
      (Q'.one_mul_eqv x)))

private theorem scale_clear_three (D e x : Q') (hDe : D * e ≈ 1) :
    pow8 D * (pow3 e * x) ≈ pow5 D * x := by
  have hpoly : pow8 D * (pow3 e * x) ≈
      pow5 D * (pow3 (D * e) * x) := by
    exact poly_identity_of_normal_eq
      (ep8 (.var 0) * (ep3 (.var 1) * .var 2))
      (ep5 (.var 0) * (ep3 (.var 0 * .var 1) * .var 2))
      (by decide) (fun | 0 => D | 1 => e | _ => x)
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow3_one_of_eqv_one hDe) (Q'.eqv_refl x))
      (Q'.one_mul_eqv x)))

private theorem scale_clear_four (D e x : Q') (hDe : D * e ≈ 1) :
    pow8 D * (pow4 e * x) ≈ pow4 D * x := by
  have hpoly : pow8 D * (pow4 e * x) ≈
      pow4 D * (pow4 (D * e) * x) := by
    exact poly_identity_of_normal_eq
      (ep8 (.var 0) * (ep4 (.var 1) * .var 2))
      (ep4 (.var 0) * (ep4 (.var 0 * .var 1) * .var 2))
      (by decide) (fun | 0 => D | 1 => e | _ => x)
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow4_one_of_eqv_one hDe) (Q'.eqv_refl x))
      (Q'.one_mul_eqv x)))

private theorem scale_clear_five (D e x : Q') (hDe : D * e ≈ 1) :
    pow8 D * (pow5 e * x) ≈ pow3 D * x := by
  have hpoly : pow8 D * (pow5 e * x) ≈
      pow3 D * (pow5 (D * e) * x) := by
    exact poly_identity_of_normal_eq
      (ep8 (.var 0) * (ep5 (.var 1) * .var 2))
      (ep3 (.var 0) * (ep5 (.var 0 * .var 1) * .var 2))
      (by decide) (fun | 0 => D | 1 => e | _ => x)
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow5_one_of_eqv_one hDe) (Q'.eqv_refl x))
      (Q'.one_mul_eqv x)))

private theorem scale_clear_six (D e x : Q') (hDe : D * e ≈ 1) :
    pow8 D * (pow6 e * x) ≈ pow2 D * x := by
  have hpoly : pow8 D * (pow6 e * x) ≈
      pow2 D * (pow6 (D * e) * x) := by
    exact poly_identity_of_normal_eq
      (ep8 (.var 0) * (ep6 (.var 1) * .var 2))
      (ep2 (.var 0) * (ep6 (.var 0 * .var 1) * .var 2))
      (by decide) (fun | 0 => D | 1 => e | _ => x)
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow6_one_of_eqv_one hDe) (Q'.eqv_refl x))
      (Q'.one_mul_eqv x)))

/-- One denominator-cleared chart factor. -/
def clearedFactor (D : Q') (a : Triple) : Q' := pow2 D + norm3 a

/-- The polynomial common-denominator replacement for the product of four
Cayley chart factors. -/
def clearedCayleyDenominator (D : Q') (a b c d : Triple) : Q' :=
  ((clearedFactor D a * clearedFactor D b) * clearedFactor D c) *
    clearedFactor D d

/-- The polynomial common-denominator replacement for the exact degree-two
through-six Cayley deficit. -/
def clearedCayleyDeficit (D : Q') (a b c d : Triple) : Q' :=
  ((((pow6 D * H2 a b c d + pow5 D * H3 a b c d) +
      pow4 D * H4 a b c d) +
      pow3 D * H5 a b c d) +
      pow2 D * H6 a b c d)

theorem factor_common_denominator_clear (D e : Q') (a : Triple)
    (hDe : D * e ≈ 1) :
    pow2 D * factor e a ≈ clearedFactor D a := by
  have hpoly : pow2 D * factor e a ≈
      pow2 D + pow2 (D * e) * norm3 a := by
    simpa only [pow2, factor, clearedFactor] using
      (poly_identity_of_normal_eq
        (ep2 (.var 0) * (1 + ep2 (.var 1) * .var 2))
        (ep2 (.var 0) + ep2 (.var 0 * .var 1) * .var 2)
        (by decide) (fun | 0 => D | 1 => e | _ => norm3 a))
  exact Q'.eqv_trans _ _ _ hpoly
    (ac (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (pow2_one_of_eqv_one hDe) (Q'.eqv_refl _))
      (Q'.one_mul_eqv _)))

theorem cayleyDenominator_common_denominator_clear
    (D e : Q') (a b c d : Triple) (hDe : D * e ≈ 1) :
    pow8 D * cayleyDenominator e a b c d ≈
      clearedCayleyDenominator D a b c d := by
  have hpoly : pow8 D * cayleyDenominator e a b c d ≈
      (((pow2 D * factor e a) * (pow2 D * factor e b)) *
        (pow2 D * factor e c)) * (pow2 D * factor e d) := by
    simpa only [pow2, pow8, cayleyDenominator] using
      (poly_identity_of_normal_eq
        (ep8 (.var 0) * (((.var 1 * .var 2) * .var 3) * .var 4))
        ((((ep2 (.var 0) * .var 1) * (ep2 (.var 0) * .var 2)) *
          (ep2 (.var 0) * .var 3)) * (ep2 (.var 0) * .var 4))
        (by decide) (fun
          | 0 => D
          | 1 => factor e a
          | 2 => factor e b
          | 3 => factor e c
          | _ => factor e d))
  exact Q'.eqv_trans _ _ _ hpoly
    (mc (mc (mc
      (factor_common_denominator_clear D e a hDe)
      (factor_common_denominator_clear D e b hDe))
      (factor_common_denominator_clear D e c hDe))
      (factor_common_denominator_clear D e d hDe))

theorem cayleyDeficit_common_denominator_clear
    (D e : Q') (a b c d : Triple) (hDe : D * e ≈ 1) :
    pow8 D * cayleyDeficit e a b c d ≈
      clearedCayleyDeficit D a b c d := by
  have hpoly : pow8 D * cayleyDeficit e a b c d ≈
      ((((pow8 D * (pow2 e * H2 a b c d) +
          pow8 D * (pow3 e * H3 a b c d)) +
          pow8 D * (pow4 e * H4 a b c d)) +
          pow8 D * (pow5 e * H5 a b c d)) +
          pow8 D * (pow6 e * H6 a b c d)) := by
    simpa only [pow2, pow3, pow4, pow5, pow6, pow8, cayleyDeficit] using
      (poly_identity_of_normal_eq
        (ep8 (.var 0) *
          ((((ep2 (.var 1) * .var 2 + ep3 (.var 1) * .var 3) +
            ep4 (.var 1) * .var 4) +
            ep5 (.var 1) * .var 5) +
            ep6 (.var 1) * .var 6))
        ((((ep8 (.var 0) * (ep2 (.var 1) * .var 2) +
            ep8 (.var 0) * (ep3 (.var 1) * .var 3)) +
            ep8 (.var 0) * (ep4 (.var 1) * .var 4)) +
            ep8 (.var 0) * (ep5 (.var 1) * .var 5)) +
            ep8 (.var 0) * (ep6 (.var 1) * .var 6))
        (by decide)
        (fun
          | 0 => D
          | 1 => e
          | 2 => H2 a b c d
          | 3 => H3 a b c d
          | 4 => H4 a b c d
          | 5 => H5 a b c d
          | _ => H6 a b c d))
  exact Q'.eqv_trans _ _ _ hpoly
    (ac (ac (ac (ac
      (scale_clear_two D e (H2 a b c d) hDe)
      (scale_clear_three D e (H3 a b c d) hDe))
      (scale_clear_four D e (H4 a b c d) hDe))
      (scale_clear_five D e (H5 a b c d) hDe))
      (scale_clear_six D e (H6 a b c d) hDe))

/-- Exact reciprocal-free polynomial form of the stereographic plaquette
identity for any supplied common denominator witness `D*e≈1`. -/
theorem plaquetteWord_cayley_common_denominator_cleared
    (D e : Q') (a b c d : Triple) (hDe : D * e ≈ 1) :
    clearedCayleyDenominator D a b (neg3 c) (neg3 d) *
        (2 + -(2 * (plaquetteWord
          (stereographic (scale3 e a))
          (stereographic (scale3 e b))
          (stereographic (scale3 e c))
          (stereographic (scale3 e d))).val.r)) ≈
      clearedCayleyDeficit D a b (neg3 c) (neg3 d) := by
  let source := 2 + -(2 * (plaquetteWord
    (stereographic (scale3 e a))
    (stereographic (scale3 e b))
    (stereographic (scale3 e c))
    (stereographic (scale3 e d))).val.r)
  have hden := cayleyDenominator_common_denominator_clear
    D e a b (neg3 c) (neg3 d) hDe
  have hbase := plaquetteWord_cayley_cleared e a b c d
  have h0 : clearedCayleyDenominator D a b (neg3 c) (neg3 d) * source ≈
      (pow8 D * cayleyDenominator e a b (neg3 c) (neg3 d)) * source :=
    mc (Q'.eqv_symm hden) (Q'.eqv_refl _)
  have h1 : (pow8 D * cayleyDenominator e a b (neg3 c) (neg3 d)) * source ≈
      pow8 D * (cayleyDenominator e a b (neg3 c) (neg3 d) * source) :=
    poly_identity_of_normal_eq
      ((.var 0 * .var 1) * .var 2) (.var 0 * (.var 1 * .var 2))
      (by decide) (fun
        | 0 => pow8 D
        | 1 => cayleyDenominator e a b (neg3 c) (neg3 d)
        | _ => source)
  have h2 : pow8 D * (cayleyDenominator e a b (neg3 c) (neg3 d) * source) ≈
      pow8 D * cayleyDeficit e a b (neg3 c) (neg3 d) :=
    mc (Q'.eqv_refl _) hbase
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2
      (cayleyDeficit_common_denominator_clear
        D e a b (neg3 c) (neg3 d) hDe)))

/-- Canonical specialization to the constructive positive reciprocal. -/
theorem plaquetteWord_cayley_reciprocal_denominator_cleared
    (D : Q') (hD : (0 : Q') < D) (a b c d : Triple) :
    clearedCayleyDenominator D a b (neg3 c) (neg3 d) *
        (2 + -(2 * (plaquetteWord
          (stereographic (scale3 (Q'.recipPos D hD) a))
          (stereographic (scale3 (Q'.recipPos D hD) b))
          (stereographic (scale3 (Q'.recipPos D hD) c))
          (stereographic (scale3 (Q'.recipPos D hD) d))).val.r)) ≈
      clearedCayleyDeficit D a b (neg3 c) (neg3 d) :=
  plaquetteWord_cayley_common_denominator_cleared
    D (Q'.recipPos D hD) a b c d (Q'.mul_recipPos_eqv D hD)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator.factor_common_denominator_clear
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator.cayleyDenominator_common_denominator_clear
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator.cayleyDeficit_common_denominator_clear
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator.plaquetteWord_cayley_common_denominator_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator.plaquetteWord_cayley_reciprocal_denominator_cleared
