/-
# A logarithmic executable cutoff for strict geometric decay

The legacy geometric cutoff uses the reciprocal Archimedean modulus
`1 / ((1-q) * epsilon)`.  That is constructive but can be much larger than
necessary when the prefactor itself grows exponentially in a support size.

This module first blocks an arbitrary strict rate down to `1/2`, then uses
`DyadicPrecision.least`, the certified finite search for the first exponent
whose half-power lies below the rescaled tolerance.  The resulting cutoff is
still explicit data and its minimality interface permits later linear bounds
in the bit-size of a prefactor.
-/

import YMGap.Constructive.DyadicPrecision
import YMGap.Constructive.DyadicTimeRationals
import YMGap.Continuum.PolynomialGeometricDecay

namespace YMGap.Continuum.DyadicGeometricCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.DyadicPrecision
open YMGap.Constructive.DyadicTimeRationals
open YMGap.Continuum.PolynomialGeometricDecay

/-- Closed logarithmic half-power precision supplied by the denominator of a
positive rational tolerance. -/
def denominatorBitPrecision (epsilon : Q') : Nat :=
  Nat.log2 epsilon.den + 1

/-- The denominator of a positive rational fits below the dyadic scale chosen
by `denominatorBitPrecision`. -/
theorem denominator_le_two_pow_bitPrecision (epsilon : Q') :
    epsilon.den ≤ 2 ^ denominatorBitPrecision epsilon := by
  unfold denominatorBitPrecision
  exact Nat.le_of_lt
    ((Nat.log2_lt (n := epsilon.den) (k := Nat.log2 epsilon.den + 1)
      (Nat.ne_of_gt (Q'.den_pos epsilon))).mp (Nat.lt_succ_self _))

/-- The closed denominator-bit precision is a successful half-power witness
for every positive rational tolerance. -/
theorem half_pow_denominatorBitPrecision_le
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    HalfPow.half ^ denominatorBitPrecision epsilon ≤ epsilon := by
  show (HalfPow.half ^ denominatorBitPrecision epsilon).num *
      (epsilon.den : Int) ≤
    epsilon.num *
      ((HalfPow.half ^ denominatorBitPrecision epsilon).den : Int)
  rw [half_power_num, half_power_den, Int.one_mul]
  have hden : (epsilon.den : Int) ≤
      ((2 ^ denominatorBitPrecision epsilon : Nat) : Int) := by
    exact_mod_cast denominator_le_two_pow_bitPrecision epsilon
  have hnum : (1 : Int) ≤ epsilon.num :=
    Int.add_one_le_iff.mpr (CReal.num_pos_of_pos hepsilon)
  exact Int.le_trans hden
    (by
      have hpow : (0 : Int) ≤
          ((2 ^ denominatorBitPrecision epsilon : Nat) : Int) :=
        Int.natCast_nonneg _
      have hmul := Int.mul_le_mul_of_nonneg_right hnum hpow
      simpa only [Int.one_mul] using hmul)

/-- The executable least precision is bounded by the closed logarithmic
denominator precision. -/
theorem least_le_denominatorBitPrecision
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    least epsilon ≤ denominatorBitPrecision epsilon :=
  least_le_of_half_pow_le (half_pow_denominatorBitPrecision_le hepsilon)

private theorem half_pow_mul_ofNat_le_one {count bits : Nat}
    (hcount : count ≤ 2 ^ bits) :
    HalfPow.half ^ bits * Q'.ofNat count ≤ (1 : Q') := by
  show (HalfPow.half ^ bits * Q'.ofNat count).num * (1 : Int) ≤
    (1 : Int) * ((HalfPow.half ^ bits * Q'.ofNat count).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast, half_power_num,
    half_power_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  simp only [Int.one_mul, Int.mul_one]
  exact_mod_cast hcount

private theorem half_pow_mul_one_add_mul_of_count_le
    {B : Q'} (hB : (0 : Q') ≤ B) {count bits : Nat}
    (hcountPos : 0 < count) (hcount : count ≤ 2 ^ bits) :
    HalfPow.half ^ bits * (1 + B * Q'.ofNat count) ≤ 1 + B := by
  have hcountOne : (1 : Q') ≤ Q'.ofNat count :=
    CReal.ofNat_le_ofNat hcountPos
  have hsum : 1 + B * Q'.ofNat count ≤
      (1 + B) * Q'.ofNat count := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add hcountOne (Q'.le_refl' _))
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_symm (Q'.one_mul_eqv (Q'.ofNat count)))
            (Q'.eqv_refl _))
          (Q'.eqv_symm (Q'.add_mul_eqv 1 B (Q'.ofNat count)))))
  have hhalfCount :
      HalfPow.half ^ bits * Q'.ofNat count ≤ (1 : Q') :=
    half_pow_mul_ofNat_le_one hcount
  have hhalfNonnegative : (0 : Q') ≤ HalfPow.half ^ bits :=
    Q'.pow_nonneg _ HalfPow.half_nonneg bits
  have hbaseNonnegative : (0 : Q') ≤ 1 + B :=
    Q'.zero_le_add 1 B Q'.zero_le_one hB
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum hhalfNonnegative)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by
        show Q'.eqv
          (HalfPow.half ^ bits * ((1 + B) * Q'.ofNat count))
          ((1 + B) * (HalfPow.half ^ bits * Q'.ofNat count))
        show _ * (_ : Int) = _ * (_ : Int)
        simp only [Q'.mul_num_cast, Q'.mul_den_cast]
        ac_rfl))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (1 + B)
          hhalfCount hbaseNonnegative)
        (Q'.le_of_eqv (Q'.mul_one_eqv (1 + B)))))

private theorem le_hkDivPos_of_mul_le {p D b : Q'}
    (hD : (0 : Q') < D) (h : b * D ≤ p) :
    b ≤ HKConv.divPos p D := by
  have hq : b ≤ Q'.divPos p D hD :=
    Q'.le_divPos_of_mul_le p D hD h
  have heq : Q'.eqv (Q'.divPos p D hD) (HKConv.divPos p D) := by
    show (Q'.divPos p D hD).num * ((HKConv.divPos p D).den : Int) =
      (HKConv.divPos p D).num * ((Q'.divPos p D hD).den : Int)
    rw [HKConv.divPos_num,
      HKConv.divPos_den_cast (CReal.num_pos_of_pos hD)]
    unfold Q'.divPos
    rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.recipPos_num,
      Q'.recipPos_den]
  exact Q'.le_trans' _ _ _ hq (Q'.le_of_eqv heq)

/-- Block an arbitrary strict rate down to `1/2`, then use the least certified
dyadic precision for the amplitude-rescaled tolerance. -/
def cutoff (q C epsilon : Q') : Nat :=
  if (0 : Q') < q then
    blockLength q 0 * least (HKConv.divPos epsilon (1 + C))
  else 1

/-- Any explicit half-power witness bounds the executable cutoff.  This is
the interface used to prove support-linear moduli without unfolding the
finite first-success search. -/
theorem cutoff_le_of_half_power_le {q C epsilon : Q'}
    (hq : (0 : Q') < q) (precision : Nat)
    (hprecision :
      HalfPow.half ^ precision ≤ HKConv.divPos epsilon (1 + C)) :
    cutoff q C epsilon ≤ blockLength q 0 * precision := by
  simp only [cutoff, if_pos hq]
  exact Nat.mul_le_mul_left _ (least_le_of_half_pow_le hprecision)

/-- Closed logarithmic upper bound for the executable geometric cutoff. -/
theorem cutoff_le_denominatorBitPrecision {q C epsilon : Q'}
    (hq : (0 : Q') < q) (hepsilon : (0 : Q') < epsilon) :
    cutoff q C epsilon ≤
      blockLength q 0 *
        denominatorBitPrecision (HKConv.divPos epsilon (1 + C)) := by
  apply cutoff_le_of_half_power_le hq
  exact half_pow_denominatorBitPrecision_le
    (HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon))

/-- If a nonnegative prefactor is bounded by a support-free base times a
positive natural count, then the executable cutoff costs only the closed base
precision plus the dyadic bit bound for that count. -/
theorem cutoff_le_base_precision_add_count_bits
    {q C B epsilon : Q'} (hq : (0 : Q') < q)
    (hC0 : (0 : Q') ≤ C) (hB : (0 : Q') ≤ B)
    (hepsilon : (0 : Q') < epsilon)
    {count bits : Nat} (hcountPos : 0 < count)
    (hcount : count ≤ 2 ^ bits)
    (hC : C ≤ B * Q'.ofNat count) :
    cutoff q C epsilon ≤
      blockLength q 0 *
        (denominatorBitPrecision (HKConv.divPos epsilon (1 + B)) + bits) := by
  let basePrecision :=
    denominatorBitPrecision (HKConv.divPos epsilon (1 + B))
  have hbaseDenominator : (0 : Q') < 1 + B :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.add_le_self_of_nonneg 1 B hB)
  have hactualDenominator : (0 : Q') < 1 + C :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.add_le_self_of_nonneg 1 C hC0)
  have hbaseTolerance :
      HalfPow.half ^ basePrecision ≤ HKConv.divPos epsilon (1 + B) := by
    exact half_pow_denominatorBitPrecision_le
      (HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon))
  have hcountScale :
      HalfPow.half ^ bits * (1 + B * Q'.ofNat count) ≤ 1 + B :=
    half_pow_mul_one_add_mul_of_count_le hB hcountPos hcount
  have hdenominatorBound : 1 + C ≤ 1 + B * Q'.ofNat count :=
    Q'.add_le_add_left 1 C (B * Q'.ofNat count) hC
  have hscaledCount :
      HalfPow.half ^ bits * (1 + C) ≤ 1 + B :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominatorBound
        (Q'.pow_nonneg _ HalfPow.half_nonneg bits))
      hcountScale
  have hbaseToleranceNonnegative :
      (0 : Q') ≤ HKConv.divPos epsilon (1 + B) :=
    HKConv.divPos_nonneg (Q'.le_of_lt hepsilon)
  have hproduct :
      (HalfPow.half ^ basePrecision) *
          (HalfPow.half ^ bits * (1 + C)) ≤ epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbaseTolerance
        (Q'.mul_nonneg _ _
          (Q'.pow_nonneg _ HalfPow.half_nonneg bits)
          (Q'.le_of_lt hactualDenominator)))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hscaledCount
          hbaseToleranceNonnegative)
        (Q'.le_of_eqv (HKConv.divPos_mul_eqv
          (CReal.num_pos_of_pos hbaseDenominator))))
  apply cutoff_le_of_half_power_le hq
  apply le_hkDivPos_of_mul_le hactualDenominator
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (1 + C)
          (Q'.pow_add_eqv HalfPow.half basePrecision bits))
        (Q'.mul_assoc_eqv (HalfPow.half ^ basePrecision)
          (HalfPow.half ^ bits) (1 + C))))
    hproduct

/-- All-rate form of the support-bit cutoff bound.  When the rate is not
strictly positive the executable cutoff is `1`, while a positive bit budget
keeps the same displayed upper bound valid. -/
theorem cutoff_le_base_precision_add_count_bits_of_positive_bits
    {q C B epsilon : Q'}
    (hC0 : (0 : Q') ≤ C) (hB : (0 : Q') ≤ B)
    (hepsilon : (0 : Q') < epsilon)
    {count bits : Nat} (hcountPos : 0 < count) (hbits : 0 < bits)
    (hcount : count ≤ 2 ^ bits)
    (hC : C ≤ B * Q'.ofNat count) :
    cutoff q C epsilon ≤
      blockLength q 0 *
        (denominatorBitPrecision (HKConv.divPos epsilon (1 + B)) + bits) := by
  by_cases hq : (0 : Q') < q
  · exact cutoff_le_base_precision_add_count_bits hq hC0 hB hepsilon
      hcountPos hcount hC
  · simp only [cutoff, if_neg hq]
    have hblock : 0 < blockLength q 0 := blockLength_pos q 0
    have hprecision : 0 <
        denominatorBitPrecision (HKConv.divPos epsilon (1 + B)) + bits := by
      omega
    have hproduct : 0 < blockLength q 0 *
        (denominatorBitPrecision (HKConv.divPos epsilon (1 + B)) + bits) :=
      Nat.mul_pos hblock hprecision
    omega

/-- The dyadic cutoff controls every later geometric term.  Unlike the legacy
reciprocal cutoff, the executable `least` search may later be bounded by any
analytically supplied half-power witness. -/
theorem bound {q C epsilon : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : cutoff q C epsilon ≤ n) :
    q^n * C ≤ epsilon := by
  by_cases hqpos : (0 : Q') < q
  · simp only [cutoff, if_pos hqpos] at hn
    have hden : (0 : Q') < 1 + C :=
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (Q'.add_le_self_of_nonneg 1 C hC)
    have ht : (0 : Q') < HKConv.divPos epsilon (1 + C) :=
      HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon)
    have hindex :
        least (HKConv.divPos epsilon (1 + C)) ≤ n / blockLength q 0 := by
      apply (Nat.le_div_iff_mul_le (blockLength_pos q 0)).mpr
      simpa only [Nat.mul_comm] using hn
    have hblocked := blocked_bound hq0 hq1 0 n
    have hqhalf : q^n ≤ HalfPow.half^(n / blockLength q 0) := by
      simp only [Nat.pow_zero, Nat.mul_one] at hblocked
      have hleft : Q'.eqv (q ^ n * Q'.ofNat 1) (q ^ n) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (q ^ n) (Q'.ofNat 1) 1 (by decide))
          (Q'.mul_one_eqv (q ^ n))
      have hright : Q'.eqv
          (Q'.ofNat 1 * (HalfPow.half ^ (n / blockLength q 0)))
          (HalfPow.half ^ (n / blockLength q 0)) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1
            (HalfPow.half ^ (n / blockLength q 0)) (by decide))
          (Q'.one_mul_eqv (HalfPow.half ^ (n / blockLength q 0)))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
        (Q'.le_trans' _ _ _ hblocked (Q'.le_of_eqv hright))
    have hhalf :
        HalfPow.half^(n / blockLength q 0) ≤
          HalfPow.half^(least (HKConv.divPos epsilon (1 + C))) :=
      HKConvGen.pow_base_antitone HalfPow.half_nonneg
        (by decide : HalfPow.half ≤ (1 : Q')) hindex
    have htolerance :
        HalfPow.half^(least (HKConv.divPos epsilon (1 + C))) ≤
          HKConv.divPos epsilon (1 + C) :=
      half_pow_le_at_least ht
    have hp : q^n ≤ HKConv.divPos epsilon (1 + C) :=
      Q'.le_trans' _ _ _ hqhalf (Q'.le_trans' _ _ _ hhalf htolerance)
    have hC1 : C ≤ 1 + C :=
      Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg C 1 Q'.zero_le_one)
        (Q'.le_of_eqv (Q'.add_comm_eqv C 1))
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ C hp hC)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hC1 (Q'.le_of_lt ht))
        (Q'.le_of_eqv
          (HKConv.divPos_mul_eqv
            (CReal.num_pos_of_pos hden))))
  · simp only [cutoff, if_neg hqpos] at hn
    have hnum : q.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hqpos (CReal.pos_of_num_pos h))
    have hqle0 : q ≤ (0 : Q') := by
      change q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    have hp : q^n ≤ (0 : Q') := by
      cases n with
      | zero => omega
      | succ k =>
          exact Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right q 0 (q^k) hqle0
              (Q'.pow_nonneg q hq0 k))
            (Q'.le_of_eqv (Q'.zero_mul_eqv (q^k)))
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ C hp hC)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv C))
        (Q'.le_of_lt hepsilon))

end YMGap.Continuum.DyadicGeometricCutoff

#print axioms YMGap.Continuum.DyadicGeometricCutoff.cutoff
#print axioms YMGap.Continuum.DyadicGeometricCutoff.denominatorBitPrecision
#print axioms YMGap.Continuum.DyadicGeometricCutoff.denominator_le_two_pow_bitPrecision
#print axioms YMGap.Continuum.DyadicGeometricCutoff.half_pow_denominatorBitPrecision_le
#print axioms YMGap.Continuum.DyadicGeometricCutoff.least_le_denominatorBitPrecision
#print axioms YMGap.Continuum.DyadicGeometricCutoff.cutoff_le_of_half_power_le
#print axioms YMGap.Continuum.DyadicGeometricCutoff.cutoff_le_denominatorBitPrecision
#print axioms YMGap.Continuum.DyadicGeometricCutoff.cutoff_le_base_precision_add_count_bits
#print axioms YMGap.Continuum.DyadicGeometricCutoff.cutoff_le_base_precision_add_count_bits_of_positive_bits
#print axioms YMGap.Continuum.DyadicGeometricCutoff.bound
