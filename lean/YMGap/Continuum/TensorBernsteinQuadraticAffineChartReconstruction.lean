/-
# Exact affine chart reconstruction for tensor power tables

The chart-B coefficient kernel clears the substitution

  affineChartBScale * r = affineChartBScale * z + x * (1 - z)

by `affineChartBScale^degreeY`.  This module proves the corresponding semantic identity
over the constructive rational substrate.  The proof is deliberately split
into finite-sum, signed-binomial, and shifted-support lemmas; no large
normalisation call is used.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
import YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction

namespace YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact finite integer sums cast to `Q'` -/

/-- Casting the coefficient kernel's integer finite sum commutes with the
constructive rational finite sum. -/
theorem ofInt_intFinSum (f : Nat → Int) : ∀ count,
    Q'.ofInt (intFinSum f count) ≈
      finSum (fun i => Q'.ofInt (f i)) count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      unfold intFinSum
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_add
          (intFinSum f count) (f count)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (ofInt_intFinSum f count)

/-- Evaluation commutes with an integer finite sum of coefficient rows. -/
theorem signedPowerEval_intFinSum
    (degree count : Nat) (coeff : Nat → Nat → Int) (z : Q') :
    signedPowerEval degree
        (fun b => intFinSum (fun i => coeff i b) count) z ≈
      finSum (fun i => signedPowerEval degree (coeff i) z) count := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _
      (fun b =>
        finSum (fun i => Q'.ofInt (coeff i b) * z ^ b) count)
      (degree + 1) (fun b hb => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (z ^ b)
        (ofInt_intFinSum (fun i => coeff i b) count)) ?_
    exact finSum_mul_const
      (fun i => Q'.ofInt (coeff i b)) (z ^ b) count
  · exact finSum_swap
      (fun b i => Q'.ofInt (coeff i b) * z ^ b)
      (degree + 1) count

theorem signedPowerEval_zero (degree : Nat) (z : Q') :
    signedPowerEval degree (fun _ => 0) z ≈ 0 := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q'))
      (degree + 1) (fun i hi => Q'.zero_mul_eqv _)) ?_
  rw [finSum_zero_seq]
  exact Q'.eqv_refl 0

/-! ## Small algebraic helpers -/

theorem pow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ exponent : Nat,
    a ^ exponent ≈ b ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := pow_eqv_congr h exponent
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a ^ exponent) h)
        (Q'.mul_eqv_congr_left b _ _ ih)

theorem rearrange4 (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (a * b) c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b))) ?_
  exact Q'.mul_assoc_eqv (a * c) b d

theorem mul_pow_eqv (a b : Q') : ∀ exponent : Nat,
    (a * b) ^ exponent ≈ a ^ exponent * b ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have ih := mul_pow_eqv a b exponent
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      exact rearrange4 a b (a ^ exponent) (b ^ exponent)

theorem pow_add_eqv (value : Q') (a : Nat) : ∀ b : Nat,
    value ^ (a + b) ≈ value ^ a * value ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (value ^ a))
  | b + 1 => by
      have ih := pow_add_eqv value a b
      show value * value ^ (a + b) ≈
        value ^ a * (value * value ^ b)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left value _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv value (value ^ a) (value ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (value ^ b)
          (Q'.mul_comm_eqv value (value ^ a))) ?_
      exact Q'.mul_assoc_eqv (value ^ a) value (value ^ b)

theorem mul_swap_first (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

theorem neg_mul_swap_first (a b c : Q') :
    (-a) * (b * c) ≈ (-b) * (a * c) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (b * c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (mul_swap_first a b c)) ?_
  exact Q'.eqv_symm (Q'.neg_mul_eqv b (a * c))

theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  change Q'.ofInt (Int.ofNat (a * b)) ≈
    Q'.ofInt (Int.ofNat a) * Q'.ofInt (Int.ofNat b)
  exact YMGap.Continuum.RingNormaliser.ofInt_mul
    (Int.ofNat a) (Int.ofNat b)

theorem ofNat_pow_eqv (base : Nat) : ∀ exponent : Nat,
    Q'.ofNat (base ^ exponent) ≈ (Q'.ofNat base) ^ exponent
  | 0 => by
      change Q'.ofNat 1 ≈ (1 : Q')
      decide
  | exponent + 1 => by
      rw [Nat.pow_succ]
      refine Q'.eqv_trans _ _ _
        (ofNat_mul_eqv (base ^ exponent) base) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat base)
          (ofNat_pow_eqv base exponent)) ?_
      exact Q'.mul_comm_eqv
        ((Q'.ofNat base) ^ exponent) (Q'.ofNat base)

private def chartBProductL :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let X := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let Xa := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let g := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  let C := YMGap.Continuum.RingNormaliser.PolyExpr.var 3
  let sp := YMGap.Continuum.RingNormaliser.PolyExpr.var 4
  let sr := YMGap.Continuum.RingNormaliser.PolyExpr.var 5
  let Z := YMGap.Continuum.RingNormaliser.PolyExpr.var 6
  let O := YMGap.Continuum.RingNormaliser.PolyExpr.var 7
  .mul (.mul X Xa)
    (.mul (.mul g (.mul C (.mul sp sr))) (.mul Z O))

private def chartBProductR :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let X := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let Xa := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let g := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  let C := YMGap.Continuum.RingNormaliser.PolyExpr.var 3
  let sp := YMGap.Continuum.RingNormaliser.PolyExpr.var 4
  let sr := YMGap.Continuum.RingNormaliser.PolyExpr.var 5
  let Z := YMGap.Continuum.RingNormaliser.PolyExpr.var 6
  let O := YMGap.Continuum.RingNormaliser.PolyExpr.var 7
  .mul (.mul g Xa)
    (.mul sp (.mul C (.mul (.mul X O) (.mul sr Z))))

private theorem chartBProduct_normal :
    YMGap.Continuum.RingNormaliser.normalize chartBProductL =
      YMGap.Continuum.RingNormaliser.normalize chartBProductR := by
  decide

theorem chartB_product_rearrange
    (X Xa g C sp sr Z O : Q') :
    (X * Xa) * ((g * (C * (sp * sr))) * (Z * O)) ≈
      (g * Xa) * (sp * (C * ((X * O) * (sr * Z)))) := by
  have h := YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
    chartBProductL chartBProductR chartBProduct_normal
    (fun index =>
      match index with
      | 0 => X
      | 1 => Xa
      | 2 => g
      | 3 => C
      | 4 => sp
      | 5 => sr
      | 6 => Z
      | _ => O)
  simpa [chartBProductL, chartBProductR,
    YMGap.Continuum.RingNormaliser.eval] using h

/-! ## Shifted finite-sum padding -/

/-- A leading block of zero terms followed by `count` shifted terms and a
zero suffix evaluates to the unpadded block. -/
theorem finSum_shifted_block (term shifted : Nat → Q')
    (offset count tail : Nat)
    (hprefix : ∀ i, i < offset → term i ≈ 0)
    (hmiddle : ∀ i, i < count → term (offset + i) ≈ shifted i)
    (hsuffix : ∀ i, i < tail →
      term (offset + count + i) ≈ 0) :
    finSum term (offset + count + tail) ≈ finSum shifted count := by
  rw [Nat.add_assoc offset count tail]
  have hp : finSum term offset ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt term (fun _ => (0 : Q')) offset hprefix) ?_
    rw [finSum_zero_seq]
    exact Q'.eqv_refl 0
  have hm : finSum (fun i => term (offset + i)) count ≈
      finSum shifted count :=
    finSum_eqv_congr_lt _ _ count hmiddle
  have hs : finSum (fun i => term (offset + count + i)) tail ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt _ (fun _ => (0 : Q')) tail hsuffix) ?_
    rw [finSum_zero_seq]
    exact Q'.eqv_refl 0
  have hsplit1 := YMGap.Constructive.finSum_split term offset (count + tail)
  have hsplit2 :
      finSum (fun i => term (offset + i)) (count + tail) ≈
        finSum (fun i => term (offset + i)) count +
          finSum (fun i => term (offset + count + i)) tail := by
    simpa [Nat.add_assoc] using
      (YMGap.Constructive.finSum_split
        (fun i => term (offset + i)) count tail)
  refine Q'.eqv_trans _ _ _ hsplit1 ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (finSum term offset) _ _ hsplit2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hp) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hm) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hs) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem const_mul_double_finSum
    (term : Nat → Nat → Q') (constant : Q')
    (outer inner : Nat) :
    constant * finSum (fun i => finSum (term i) inner) outer ≈
      finSum (fun i =>
        finSum (fun j => constant * term i j) inner) outer := by
  refine Q'.eqv_trans _ _ _
    (const_mul_finSum (fun i => finSum (term i) inner)
      constant outer) ?_
  refine finSum_eqv_congr_lt _ _ outer ?_
  intro i hi
  exact const_mul_finSum (term i) constant inner

/-! ## Finite-list support -/

theorem list_getD_eq_default_of_length_le
    {alpha : Type} (fallback : alpha) :
    ∀ (values : List alpha) (index : Nat),
      values.length ≤ index → values.getD index fallback = fallback
  | [], index, h => by simp only [List.getD_nil]
  | value :: values, 0, h => by simp at h
  | value :: values, index + 1, h => by
      rw [List.getD_cons_succ]
      exact list_getD_eq_default_of_length_le fallback values index (by
        simp only [List.length_cons] at h
        omega)

theorem gridCoeff_zero_of_length_le
    (rows : List (List Int)) (degreeX row column : Nat)
    (hrows : rows.length ≤ degreeX + 1)
    (hrow : degreeX < row) :
    gridCoeff rows row column = 0 := by
  unfold gridCoeff
  rw [list_getD_eq_default_of_length_le [] rows row (by omega)]
  exact List.getD_nil

/-! ## Alternating signs and the signed binomial block -/

theorem alternatingIntSign_succ (exponent : Nat) :
    alternatingIntSign (exponent + 1) =
      -alternatingIntSign exponent := by
  unfold alternatingIntSign
  omega

theorem alternatingIntSign_mul_pow (z : Q') : ∀ exponent : Nat,
    Q'.ofInt (alternatingIntSign exponent) * z ^ exponent ≈
      (-z) ^ exponent
  | 0 => by
      change (Q'.ofInt 1 * (1 : Q')) ≈ (1 : Q')
      decide
  | exponent + 1 => by
      rw [alternatingIntSign_succ]
      have hcast : Q'.ofInt (-alternatingIntSign exponent) ≈
          -(Q'.ofInt (alternatingIntSign exponent)) := by
        rfl
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (z * z ^ exponent) hcast) ?_
      refine Q'.eqv_trans _ _ _
        (neg_mul_swap_first
          (Q'.ofInt (alternatingIntSign exponent)) z (z ^ exponent)) ?_
      exact Q'.mul_eqv_congr_left (-z) _ _
        (alternatingIntSign_mul_pow z exponent)

/-- The integer row `C(ell,q)(-1)^q` evaluates exactly to `(1-z)^ell`. -/
theorem signedBinomial_finSum (ell : Nat) (z : Q') :
    finSum (fun q =>
      Q'.ofInt
          (Int.ofNat (binom ell q) * alternatingIntSign q) *
        z ^ q) (ell + 1) ≈
      ((1 : Q') + -z) ^ ell := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _
      (YMGap.Continuum.BernsteinVariance.S0seq ell (-z) 1)
      (ell + 1) (fun q hq => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (z ^ q)
        (YMGap.Continuum.RingNormaliser.ofInt_mul
          (Int.ofNat (binom ell q)) (alternatingIntSign q))) ?_
    change
      (Q'.ofNat (binom ell q) *
          Q'.ofInt (alternatingIntSign q)) * z ^ q ≈
        Q'.ofNat (binom ell q) *
          ((-z) ^ q * (1 : Q') ^ (ell - q))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (binom ell q))
        (Q'.ofInt (alternatingIntSign q)) (z ^ q)) ?_
    refine Q'.mul_eqv_congr_left (Q'.ofNat (binom ell q)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (alternatingIntSign_mul_pow z q) ?_
    have hone : (1 : Q') ^ (ell - q) ≈ 1 := by
      exact YMGap.Continuum.BernsteinVariance.eqv_one_pow
        1 (Q'.eqv_refl 1) _
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left ((-z) ^ q) _ _ hone)
        (Q'.mul_one_eqv ((-z) ^ q)))
  · refine Q'.eqv_trans _ _ _
      (YMGap.Continuum.BinomialTheorem.binomialTheorem ell (-z) 1) ?_
    exact pow_eqv_congr (Q'.add_comm_eqv (-z) 1) ell

/-- The guarded row occurring inside `affineChartBClearedCoeff`, with the
factors independent of the output `z`-exponent removed. -/
def affineChartBSignedRow (ell i b : Nat) : Int :=
  if ell ≤ i ∧ i ≤ b + ell ∧ b + ell - i ≤ ell then
    Int.ofNat (binom ell (b + ell - i)) *
      alternatingIntSign (b + ell - i)
  else
    0

theorem affineChartBSignedRow_zero_of_lt
    {ell i b : Nat} (helli : ell ≤ i) (hb : b < i - ell) :
    affineChartBSignedRow ell i b = 0 := by
  unfold affineChartBSignedRow
  rw [if_neg]
  intro hguard
  omega

theorem affineChartB_shift_guard
    {ell i q : Nat} (helli : ell ≤ i) (hq : q ≤ ell) :
    ell ≤ i ∧
      i ≤ (i - ell + q) + ell ∧
      (i - ell + q) + ell - i ≤ ell := by
  refine ⟨helli, ?_, ?_⟩
  · omega
  · omega

theorem affineChartB_shift_index
    {ell i q : Nat} (helli : ell ≤ i) :
    (i - ell + q) + ell - i = q := by
  omega

theorem affineChartBSignedRow_shift
    {ell i q : Nat} (helli : ell ≤ i) (hq : q ≤ ell) :
    affineChartBSignedRow ell i (i - ell + q) =
      Int.ofNat (binom ell q) * alternatingIntSign q := by
  have hguard := affineChartB_shift_guard helli hq
  have hindex := affineChartB_shift_index (q := q) helli
  unfold affineChartBSignedRow
  rw [if_pos hguard, hindex]

theorem affineChartBSignedRow_zero_of_gt
    {ell i b : Nat} (hb : i < b) :
    affineChartBSignedRow ell i b = 0 := by
  unfold affineChartBSignedRow
  rw [if_neg]
  intro hguard
  omega

/-- For `ell ≤ i ≤ degree`, the guarded output row occupies precisely the
indices `i-ell,…,i` and evaluates to `z^(i-ell)(1-z)^ell`. -/
theorem signedPowerEval_affineChartBSignedRow
    (degree ell i : Nat) (z : Q')
    (helli : ell ≤ i) (hidegree : i ≤ degree) :
    signedPowerEval degree (affineChartBSignedRow ell i) z ≈
      z ^ (i - ell) * ((1 : Q') + -z) ^ ell := by
  unfold signedPowerEval
  have hlength : degree + 1 =
      (i - ell) + (ell + 1) + (degree - i) := by
    omega
  rw [hlength]
  let middle : Nat → Q' := fun q =>
    z ^ (i - ell) *
      (Q'.ofInt
          (Int.ofNat (binom ell q) * alternatingIntSign q) *
        z ^ q)
  refine Q'.eqv_trans _ _ _
    (finSum_shifted_block
      (fun b => Q'.ofInt (affineChartBSignedRow ell i b) * z ^ b)
      middle (i - ell) (ell + 1) (degree - i) ?_ ?_ ?_) ?_
  · intro b hb
    change Q'.ofInt (affineChartBSignedRow ell i b) * z ^ b ≈ 0
    rw [affineChartBSignedRow_zero_of_lt helli hb]
    exact Q'.zero_mul_eqv _
  · intro q hq
    have hqell : q ≤ ell := by omega
    change
      Q'.ofInt (affineChartBSignedRow ell i (i - ell + q)) *
          z ^ (i - ell + q) ≈ middle q
    rw [affineChartBSignedRow_shift helli hqell]
    unfold middle
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofInt
          (Int.ofNat (binom ell q) * alternatingIntSign q))
        _ _ (pow_add_eqv z (i - ell) q)) ?_
    exact mul_swap_first
      (Q'.ofInt
        (Int.ofNat (binom ell q) * alternatingIntSign q))
      (z ^ (i - ell)) (z ^ q)
  · intro t ht
    change
      Q'.ofInt
          (affineChartBSignedRow ell i
            (i - ell + (ell + 1) + t)) *
        z ^ (i - ell + (ell + 1) + t) ≈ 0
    rw [affineChartBSignedRow_zero_of_gt (by omega)]
    exact Q'.zero_mul_eqv _
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (const_mul_finSum
          (fun q =>
            Q'.ofInt
                (Int.ofNat (binom ell q) * alternatingIntSign q) *
              z ^ q)
          (z ^ (i - ell)) (ell + 1))) ?_
    exact Q'.mul_eqv_congr_left (z ^ (i - ell)) _ _
      (signedBinomial_finSum ell z)

/-! ## The full inner chart-B row -/

/-- The `i`-summand in the chart-B coefficient kernel, isolated as a row in
the output exponent `b`. -/
def affineChartBInnerCoeff (degree : Nat)
    (preChart : List (List Int)) (a ell i b : Nat) : Int :=
  if ell ≤ i ∧ i ≤ b + ell ∧ b + ell - i ≤ ell then
    let q := b + ell - i
    gridCoeff preChart (a - ell) i *
        Int.ofNat
          (binom i ell * binom ell q * affineChartBScale ^ (degree - ell)) *
      alternatingIntSign q
  else
    0

/-- The full inner coefficient is a constant integer multiple of the signed
binomial row. -/
theorem affineChartBInnerCoeff_factor
    (degree : Nat) (preChart : List (List Int))
    (a ell i b : Nat) :
    affineChartBInnerCoeff degree preChart a ell i b =
      (gridCoeff preChart (a - ell) i *
          Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
        affineChartBSignedRow ell i b := by
  unfold affineChartBInnerCoeff affineChartBSignedRow
  by_cases hguard :
      ell ≤ i ∧ i ≤ b + ell ∧ b + ell - i ≤ ell
  · rw [if_pos hguard, if_pos hguard]
    dsimp only
    have hnat :
        binom i ell * binom ell (b + ell - i) *
            affineChartBScale ^ (degree - ell) =
          (binom i ell * affineChartBScale ^ (degree - ell)) *
            binom ell (b + ell - i) := by
      ac_rfl
    rw [hnat]
    change
      (gridCoeff preChart (a - ell) i *
          (Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell)) *
            Int.ofNat (binom ell (b + ell - i)))) *
          alternatingIntSign (b + ell - i) =
        (gridCoeff preChart (a - ell) i *
            Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
          (Int.ofNat (binom ell (b + ell - i)) *
            alternatingIntSign (b + ell - i))
    ac_rfl
  · rw [if_neg hguard, if_neg hguard]
    simp

/-- Semantic form of a supported inner row. -/
theorem signedPowerEval_affineChartBInnerCoeff_of_le
    (degree : Nat) (preChart : List (List Int))
    (a ell i : Nat) (z : Q')
    (helli : ell ≤ i) (hidegree : i ≤ degree) :
    signedPowerEval degree
        (affineChartBInnerCoeff degree preChart a ell i) z ≈
      Q'.ofInt
          (gridCoeff preChart (a - ell) i *
            Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
        (z ^ (i - ell) * ((1 : Q') + -z) ^ ell) := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _
      (fun b =>
        Q'.ofInt
            (gridCoeff preChart (a - ell) i *
              Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
          (Q'.ofInt (affineChartBSignedRow ell i b) * z ^ b))
      (degree + 1) (fun b hb => ?_)) ?_
  · rw [affineChartBInnerCoeff_factor]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (z ^ b)
        (YMGap.Continuum.RingNormaliser.ofInt_mul
          (gridCoeff preChart (a - ell) i *
            Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell)))
          (affineChartBSignedRow ell i b))) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (const_mul_finSum
          (fun b => Q'.ofInt (affineChartBSignedRow ell i b) * z ^ b)
          (Q'.ofInt
            (gridCoeff preChart (a - ell) i *
              Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))))
          (degree + 1))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (signedPowerEval_affineChartBSignedRow
        degree ell i z helli hidegree)

/-- An unsupported inner row (`i < ell`) is identically zero. -/
theorem signedPowerEval_affineChartBInnerCoeff_of_lt
    (degree : Nat) (preChart : List (List Int))
    (a ell i : Nat) (z : Q') (hiell : i < ell) :
    signedPowerEval degree
        (affineChartBInnerCoeff degree preChart a ell i) z ≈ 0 := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q'))
      (degree + 1) (fun b hb => ?_)) ?_
  · unfold affineChartBInnerCoeff
    rw [if_neg]
    · exact Q'.zero_mul_eqv _
    · intro hguard
      omega
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

/-! ## Unfolding the two integer coefficient sums -/

def affineChartBClearedCoeffExpanded (degree : Nat)
    (preChart : List (List Int)) (a b : Nat) : Int :=
  intFinSum (fun ell =>
    if ell ≤ a then
      intFinSum (fun i =>
        affineChartBInnerCoeff degree preChart a ell i b)
        (degree + 1)
    else
      0) (degree + 1)

theorem affineChartBClearedCoeff_eq_expanded
    (degree : Nat) (preChart : List (List Int)) (a b : Nat) :
    affineChartBClearedCoeff degree preChart a b =
      affineChartBClearedCoeffExpanded degree preChart a b := by
  rfl

theorem signedPowerEval_coeff_eq
    (degree : Nat) (p q : Nat → Int) (z : Q')
    (h : ∀ b, b < degree + 1 → p b = q b) :
    signedPowerEval degree p z ≈ signedPowerEval degree q z := by
  unfold signedPowerEval
  exact finSum_eqv_congr_lt _ _ (degree + 1) (fun b hb => by
    rw [h b hb]
    exact Q'.eqv_refl _)

/-- At a fixed output `x`-exponent, evaluation of the generated row is the
finite sum of the isolated `(ell,i)` rows. -/
theorem signedPowerEval_affineChartBClearedCoeff_by_inner
    (degree : Nat) (preChart : List (List Int))
    (a : Nat) (z : Q') :
    signedPowerEval degree
        (affineChartBClearedCoeff degree preChart a) z ≈
      finSum (fun ell =>
        if ell ≤ a then
          finSum (fun i =>
            signedPowerEval degree
              (affineChartBInnerCoeff degree preChart a ell i) z)
            (degree + 1)
        else
          0) (degree + 1) := by
  refine Q'.eqv_trans _ _ _
    (signedPowerEval_coeff_eq degree
      (affineChartBClearedCoeff degree preChart a)
      (affineChartBClearedCoeffExpanded degree preChart a) z
      (fun b hb => affineChartBClearedCoeff_eq_expanded
        degree preChart a b)) ?_
  refine Q'.eqv_trans _ _ _
    (signedPowerEval_intFinSum degree (degree + 1)
      (fun ell b =>
        if ell ≤ a then
          intFinSum (fun i =>
            affineChartBInnerCoeff degree preChart a ell i b)
            (degree + 1)
        else
          0) z) ?_
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro ell hell
  by_cases hle : ell ≤ a
  · simp only [if_pos hle]
    exact signedPowerEval_intFinSum degree (degree + 1)
      (fun i b => affineChartBInnerCoeff degree preChart a ell i b) z
  · simp only [if_neg hle]
    exact signedPowerEval_zero degree z

/-- The explicit supported `(ell,i)` contribution at a fixed output
`x`-exponent. -/
def affineChartBFixedATerm (degree : Nat)
    (preChart : List (List Int)) (a ell i : Nat) (z : Q') : Q' :=
  if ell ≤ a then
    if ell ≤ i then
      Q'.ofInt
          (gridCoeff preChart (a - ell) i *
            Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
        (z ^ (i - ell) * ((1 : Q') + -z) ^ ell)
    else
      0
  else
    0

/-- Exact fixed-`a` semantic expansion of the chart-B row. -/
theorem signedPowerEval_affineChartBClearedCoeff_expansion
    (degree : Nat) (preChart : List (List Int))
    (a : Nat) (z : Q') :
    signedPowerEval degree
        (affineChartBClearedCoeff degree preChart a) z ≈
      finSum (fun ell =>
        finSum (fun i =>
          affineChartBFixedATerm degree preChart a ell i z)
          (degree + 1)) (degree + 1) := by
  refine Q'.eqv_trans _ _ _
    (signedPowerEval_affineChartBClearedCoeff_by_inner
      degree preChart a z) ?_
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro ell hell
  by_cases hlea : ell ≤ a
  · simp only [if_pos hlea]
    refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
    intro i hi
    by_cases hlei : ell ≤ i
    · simp only [affineChartBFixedATerm, if_pos hlea, if_pos hlei]
      exact signedPowerEval_affineChartBInnerCoeff_of_le
        degree preChart a ell i z hlei (by omega)
    · have hiell : i < ell := by omega
      simp only [affineChartBFixedATerm, if_pos hlea, if_neg hlei]
      exact signedPowerEval_affineChartBInnerCoeff_of_lt
        degree preChart a ell i z hiell
  · simp only [if_neg hlea, affineChartBFixedATerm]
    rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

/-! ## Tensor-level triple expansion -/

def affineChartBTensorTerm (degree : Nat)
    (preChart : List (List Int)) (a ell i : Nat)
    (x z : Q') : Q' :=
  x ^ a * affineChartBFixedATerm degree preChart a ell i z

/-- Shift the output exponent `a = a₀+ell`.  The finite-list support
hypothesis kills the padding between the input `x` degree and the enlarged
output degree. -/
theorem finSum_affineChartBTensorTerm_shift_of_le
    (degreeX degree : Nat) (preChart : List (List Int))
    (ell i : Nat) (x z : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (hellDegree : ell ≤ degree) (helli : ell ≤ i) :
    finSum (fun a =>
      affineChartBTensorTerm degree preChart a ell i x z)
      (degreeX + degree + 1) ≈
    finSum (fun a₀ =>
      affineChartBTensorTerm degree preChart (ell + a₀) ell i x z)
      (degreeX + 1) := by
  have hlength : degreeX + degree + 1 =
      ell + (degreeX + 1) + (degree - ell) := by
    omega
  rw [hlength]
  refine finSum_shifted_block
    (fun a => affineChartBTensorTerm degree preChart a ell i x z)
    (fun a₀ =>
      affineChartBTensorTerm degree preChart (ell + a₀) ell i x z)
    ell (degreeX + 1) (degree - ell) ?_ ?_ ?_
  · intro a ha
    change affineChartBTensorTerm degree preChart a ell i x z ≈ 0
    unfold affineChartBTensorTerm affineChartBFixedATerm
    rw [if_neg (by omega)]
    exact Q'.mul_zero_eqv _
  · intro a₀ ha₀
    exact Q'.eqv_refl _
  · intro t ht
    have hlea : ell ≤ ell + (degreeX + 1) + t := by omega
    have hrow : degreeX <
        (ell + (degreeX + 1) + t) - ell := by
      omega
    have hzero := gridCoeff_zero_of_length_le preChart degreeX
      ((ell + (degreeX + 1) + t) - ell) i hrows hrow
    change
      affineChartBTensorTerm degree preChart
        (ell + (degreeX + 1) + t) ell i x z ≈ 0
    unfold affineChartBTensorTerm affineChartBFixedATerm
    rw [if_pos hlea, if_pos helli, hzero]
    have hinner :
        Q'.ofInt
            (0 * Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) *
          (z ^ (i - ell) * ((1 : Q') + -z) ^ ell) ≈ 0 := by
      rw [Int.zero_mul]
      exact Q'.zero_mul_eqv _
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 hinner) ?_
    exact Q'.mul_zero_eqv _

theorem finSum_affineChartBTensorTerm_zero_of_lt
    (degreeX degree : Nat) (preChart : List (List Int))
    (ell i : Nat) (x z : Q') (hiell : i < ell) :
    finSum (fun a =>
      affineChartBTensorTerm degree preChart a ell i x z)
      (degreeX + degree + 1) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q'))
      (degreeX + degree + 1) (fun a ha => ?_)) ?_
  · unfold affineChartBTensorTerm affineChartBFixedATerm
    by_cases hlea : ell ≤ a
    · rw [if_pos hlea, if_neg (by omega)]
      exact Q'.mul_zero_eqv _
    · rw [if_neg hlea]
      exact Q'.mul_zero_eqv _
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

theorem finSum_affineChartBShiftedTerm_zero_of_lt
    (degreeX degree : Nat) (preChart : List (List Int))
    (ell i : Nat) (x z : Q') (hiell : i < ell) :
    finSum (fun a₀ =>
      affineChartBTensorTerm degree preChart (ell + a₀) ell i x z)
      (degreeX + 1) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q'))
      (degreeX + 1) (fun a₀ ha₀ => ?_)) ?_
  · unfold affineChartBTensorTerm affineChartBFixedATerm
    rw [if_pos (by omega), if_neg (by omega)]
    exact Q'.mul_zero_eqv _
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

/-- Uniform shifted-support theorem; the `i<ell` case vanishes on both sides. -/
theorem finSum_affineChartBTensorTerm_shift
    (degreeX degree : Nat) (preChart : List (List Int))
    (ell i : Nat) (x z : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (hellDegree : ell ≤ degree) :
    finSum (fun a =>
      affineChartBTensorTerm degree preChart a ell i x z)
      (degreeX + degree + 1) ≈
    finSum (fun a₀ =>
      affineChartBTensorTerm degree preChart (ell + a₀) ell i x z)
      (degreeX + 1) := by
  by_cases helli : ell ≤ i
  · exact finSum_affineChartBTensorTerm_shift_of_le
      degreeX degree preChart ell i x z hrows hellDegree helli
  · have hiell : i < ell := by omega
    refine Q'.eqv_trans _ _ _
      (finSum_affineChartBTensorTerm_zero_of_lt
        degreeX degree preChart ell i x z hiell) ?_
    exact Q'.eqv_symm
      (finSum_affineChartBShiftedTerm_zero_of_lt
        degreeX degree preChart ell i x z hiell)

/-- The cleared chart evaluator is the finite triple sum over the input
exponent `i`, the selected affine factor `ell`, and the shifted input
`x`-exponent. -/
theorem tensorPowerEval_affineChartBClearedCoeff_triple
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z : Q') :
    tensorPowerEval (degreeX + degree) degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      finSum (fun ell =>
        finSum (fun i =>
          finSum (fun a =>
            affineChartBTensorTerm degree preChart a ell i x z)
            (degreeX + degree + 1))
          (degree + 1))
        (degree + 1) := by
  refine Q'.eqv_trans _ _ _
    (tensorPowerEval_by_first (degreeX + degree) degree
      (affineChartBClearedCoeff degree preChart) x z) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + degree + 1)
      (fun a ha =>
        Q'.mul_eqv_congr_left (x ^ a) _ _
          (signedPowerEval_affineChartBClearedCoeff_expansion
            degree preChart a z))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + degree + 1)
      (fun a ha =>
        const_mul_double_finSum
          (fun ell i => affineChartBFixedATerm degree preChart a ell i z)
          (x ^ a) (degree + 1) (degree + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_swap
      (fun a ell =>
        finSum (fun i =>
          affineChartBTensorTerm degree preChart a ell i x z)
          (degree + 1))
      (degreeX + degree + 1) (degree + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro ell hell
  exact finSum_swap
    (fun a i => affineChartBTensorTerm degree preChart a ell i x z)
    (degreeX + degree + 1) (degree + 1)

/-- After the support shift, the sum order is `(i,a₀,ell)`, matching the
input tensor evaluator and the binomial theorem in `ell`. -/
theorem tensorPowerEval_affineChartBClearedCoeff_shifted
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z : Q') (hrows : preChart.length ≤ degreeX + 1) :
    tensorPowerEval (degreeX + degree) degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      finSum (fun i =>
        finSum (fun a₀ =>
          finSum (fun ell =>
            affineChartBTensorTerm degree preChart
              (ell + a₀) ell i x z)
            (degree + 1))
          (degreeX + 1))
        (degree + 1) := by
  refine Q'.eqv_trans _ _ _
    (tensorPowerEval_affineChartBClearedCoeff_triple
      degreeX degree preChart x z) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degree + 1) (fun ell hell =>
      finSum_eqv_congr_lt _ _ (degree + 1) (fun i hi =>
        finSum_affineChartBTensorTerm_shift
          degreeX degree preChart ell i x z hrows (by omega)))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_swap
      (fun ell i =>
        finSum (fun a₀ =>
          affineChartBTensorTerm degree preChart
            (ell + a₀) ell i x z)
          (degreeX + 1))
      (degree + 1) (degree + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro i hi
  exact finSum_swap
    (fun ell a₀ =>
      affineChartBTensorTerm degree preChart
        (ell + a₀) ell i x z)
    (degree + 1) (degreeX + 1)

/-! ## Binomial collapse in the affine-factor index -/

def affineChartBBinomialTerm (degree : Nat)
    (preChart : List (List Int)) (a₀ i ell : Nat)
    (x z : Q') : Q' :=
  let scale := Q'.ofNat affineChartBScale
  let oneMinusZ := (1 : Q') + -z
  (Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀) *
    (scale ^ (degree - i) *
      YMGap.Continuum.BernsteinVariance.S0seq i
        (x * oneMinusZ) (scale * z) ell)

/-- A supported shifted chart term is exactly the corresponding binomial
summand.  All coefficient casts and scale splitting are derived here. -/
theorem affineChartBTensorTerm_eqv_binomialTerm
    (degree : Nat) (preChart : List (List Int))
    (a₀ i ell : Nat) (x z : Q')
    (helli : ell ≤ i) (hidegree : i ≤ degree) :
    affineChartBTensorTerm degree preChart
        (ell + a₀) ell i x z ≈
      affineChartBBinomialTerm degree preChart a₀ i ell x z := by
  let scale : Q' := Q'.ofNat affineChartBScale
  let oneMinusZ : Q' := (1 : Q') + -z
  let X : Q' := x ^ ell
  let Xa : Q' := x ^ a₀
  let g : Q' := Q'.ofInt (gridCoeff preChart a₀ i)
  let C : Q' := Q'.ofNat (binom i ell)
  let sp : Q' := scale ^ (degree - i)
  let sr : Q' := scale ^ (i - ell)
  let Z : Q' := z ^ (i - ell)
  let O : Q' := oneMinusZ ^ ell
  have hsub : ell + a₀ - ell = a₀ := by omega
  have hscaleExp : degree - ell = (degree - i) + (i - ell) := by
    omega
  have hxpow : x ^ (ell + a₀) ≈ X * Xa :=
    pow_add_eqv x ell a₀
  have hscaleCast :
      Q'.ofNat (affineChartBScale ^ (degree - ell)) ≈ scale ^ (degree - ell) := by
    exact ofNat_pow_eqv affineChartBScale (degree - ell)
  have hcoeffCast :
      Q'.ofInt
          (gridCoeff preChart a₀ i *
            Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell))) ≈
        g * (C * scale ^ (degree - ell)) := by
    refine Q'.eqv_trans _ _ _
      (YMGap.Continuum.RingNormaliser.ofInt_mul
        (gridCoeff preChart a₀ i)
        (Int.ofNat (binom i ell * affineChartBScale ^ (degree - ell)))) ?_
    change
      Q'.ofInt (gridCoeff preChart a₀ i) *
          Q'.ofNat (binom i ell * affineChartBScale ^ (degree - ell)) ≈
        g * (C * scale ^ (degree - ell))
    refine Q'.mul_eqv_congr_left g _ _ ?_
    refine Q'.eqv_trans _ _ _
      (ofNat_mul_eqv (binom i ell) (affineChartBScale ^ (degree - ell))) ?_
    exact Q'.mul_eqv_congr_left C _ _ hscaleCast
  have hscaleSplit : scale ^ (degree - ell) ≈ sp * sr := by
    rw [hscaleExp]
    exact pow_add_eqv scale (degree - i) (i - ell)
  unfold affineChartBTensorTerm affineChartBFixedATerm
  rw [if_pos (by omega), if_pos helli, hsub]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hxpow) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (X * Xa) _ _
      (Q'.mul_eqv_congr_right _ _ (Z * O) hcoeffCast)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (X * Xa) _ _
      (Q'.mul_eqv_congr_right _ _ (Z * O)
        (Q'.mul_eqv_congr_left g _ _
          (Q'.mul_eqv_congr_left C _ _ hscaleSplit)))) ?_
  refine Q'.eqv_trans _ _ _
    (chartB_product_rearrange X Xa g C sp sr Z O) ?_
  unfold affineChartBBinomialTerm
  change
    (g * Xa) * (sp * (C * ((X * O) * (sr * Z)))) ≈
      (g * Xa) *
        (sp *
          (C *
            ((x * oneMinusZ) ^ ell *
              (scale * z) ^ (i - ell))))
  refine Q'.mul_eqv_congr_left (g * Xa) _ _ ?_
  refine Q'.mul_eqv_congr_left sp _ _ ?_
  refine Q'.mul_eqv_congr_left C _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (sr * Z)
      (Q'.eqv_symm (mul_pow_eqv x oneMinusZ ell))) ?_
  exact Q'.mul_eqv_congr_left ((x * oneMinusZ) ^ ell) _ _
    (Q'.eqv_symm (mul_pow_eqv scale z (i - ell)))

/-- Summing the affine selections reconstructs the exact binomial power. -/
theorem finSum_affineChartBTensorTerm_binomial
    (degree : Nat) (preChart : List (List Int))
    (a₀ i : Nat) (x z : Q') (hidegree : i ≤ degree) :
    finSum (fun ell =>
      affineChartBTensorTerm degree preChart
        (ell + a₀) ell i x z)
      (degree + 1) ≈
    (Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀) *
      ((Q'.ofNat affineChartBScale) ^ (degree - i) *
        (x * ((1 : Q') + -z) + Q'.ofNat affineChartBScale * z) ^ i) := by
  have hlength : degree + 1 =
      0 + (i + 1) + (degree - i) := by
    omega
  rw [hlength]
  refine Q'.eqv_trans _ _ _
    (finSum_shifted_block
      (fun ell =>
        affineChartBTensorTerm degree preChart
          (ell + a₀) ell i x z)
      (fun ell =>
        affineChartBBinomialTerm degree preChart a₀ i ell x z)
      0 (i + 1) (degree - i) ?_ ?_ ?_) ?_
  · intro ell hell
    omega
  · intro ell hell
    simpa only [Nat.zero_add] using
      (affineChartBTensorTerm_eqv_binomialTerm
        degree preChart a₀ i ell x z (by omega) hidegree)
  · intro t ht
    simp only [Nat.zero_add]
    let ell := i + 1 + t
    have hiell : ¬ ell ≤ i := by
      unfold ell
      omega
    change
      affineChartBTensorTerm degree preChart
          (ell + a₀) ell i x z ≈ 0
    unfold affineChartBTensorTerm affineChartBFixedATerm
    rw [if_pos (by omega), if_neg hiell]
    exact Q'.mul_zero_eqv _
  · let K : Q' :=
      Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀
    let sp : Q' := (Q'.ofNat affineChartBScale) ^ (degree - i)
    let A : Q' := x * ((1 : Q') + -z)
    let B : Q' := Q'.ofNat affineChartBScale * z
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (const_mul_finSum
          (fun ell =>
            sp * YMGap.Continuum.BernsteinVariance.S0seq i A B ell)
          K (i + 1))) ?_
    refine Q'.mul_eqv_congr_left K _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (const_mul_finSum
          (YMGap.Continuum.BernsteinVariance.S0seq i A B)
          sp (i + 1))) ?_
    exact Q'.mul_eqv_congr_left sp _ _
      (YMGap.Continuum.BinomialTheorem.binomialTheorem i A B)

/-! ## Physical affine relation and final reconstruction -/

theorem affineChartB_scale_power_collapse
    (degree i : Nat) (x z r : Q') (hidegree : i ≤ degree)
    (hr : Q'.ofNat affineChartBScale * r ≈
      Q'.ofNat affineChartBScale * z + x * ((1 : Q') + -z)) :
    (Q'.ofNat affineChartBScale) ^ (degree - i) *
        (x * ((1 : Q') + -z) + Q'.ofNat affineChartBScale * z) ^ i ≈
      r ^ i * (Q'.ofNat affineChartBScale) ^ degree := by
  let scale : Q' := Q'.ofNat affineChartBScale
  let affine : Q' := x * ((1 : Q') + -z) + scale * z
  have haffine : affine ≈ scale * r := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv
        (x * ((1 : Q') + -z)) (scale * z)) ?_
    exact Q'.eqv_symm hr
  have hpow : affine ^ i ≈ scale ^ i * r ^ i :=
    Q'.eqv_trans _ _ _ (pow_eqv_congr haffine i)
      (mul_pow_eqv scale r i)
  have hdegree : degree = (degree - i) + i := by omega
  have hscale : scale ^ (degree - i) * scale ^ i ≈
      scale ^ degree := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (pow_add_eqv scale (degree - i) i)) ?_
    rw [← hdegree]
    exact Q'.eqv_refl _
  change scale ^ (degree - i) * affine ^ i ≈
    r ^ i * scale ^ degree
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (scale ^ (degree - i)) _ _ hpow) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (scale ^ (degree - i)) (scale ^ i) (r ^ i))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (r ^ i) hscale) ?_
  exact Q'.mul_comm_eqv (scale ^ degree) (r ^ i)

/-- The complete affine-factor sum at one input monomial is the input
monomial times the common clearing scale. -/
theorem finSum_affineChartBTensorTerm_physical
    (degree : Nat) (preChart : List (List Int))
    (a₀ i : Nat) (x z r : Q') (hidegree : i ≤ degree)
    (hr : Q'.ofNat affineChartBScale * r ≈
      Q'.ofNat affineChartBScale * z + x * ((1 : Q') + -z)) :
    finSum (fun ell =>
      affineChartBTensorTerm degree preChart
        (ell + a₀) ell i x z)
      (degree + 1) ≈
    (Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀) *
      (r ^ i * (Q'.ofNat affineChartBScale) ^ degree) := by
  refine Q'.eqv_trans _ _ _
    (finSum_affineChartBTensorTerm_binomial
      degree preChart a₀ i x z hidegree) ?_
  exact Q'.mul_eqv_congr_left
    (Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀) _ _
    (affineChartB_scale_power_collapse
      degree i x z r hidegree hr)

/-- **Generic exact chart-B reconstruction.**  Evaluation of the cleared
coefficient table at `(x,z)` is `affineChartBScale^degree` times evaluation of the original
table at `(x,r)`, under the constructive affine relation.  The only support
hypothesis says that the finite input row table fits its declared `x` degree. -/
theorem tensorPowerEval_affineChartBClearedCoeff
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z r : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (hr : Q'.ofNat affineChartBScale * r ≈
      Q'.ofNat affineChartBScale * z + x * ((1 : Q') + -z)) :
    tensorPowerEval (degreeX + degree) degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      tensorPowerEval degreeX degree (gridCoeff preChart) x r *
        Q'.ofNat (affineChartBScale ^ degree) := by
  let scalePow : Q' := (Q'.ofNat affineChartBScale) ^ degree
  refine Q'.eqv_trans _ _ _
    (tensorPowerEval_affineChartBClearedCoeff_shifted
      degreeX degree preChart x z hrows) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degree + 1) (fun i hi =>
      finSum_eqv_congr_lt _ _ (degreeX + 1) (fun a₀ ha₀ =>
        finSum_affineChartBTensorTerm_physical
          degree preChart a₀ i x z r (by omega) hr))) ?_
  refine Q'.eqv_trans _
    (finSum (fun i =>
      (signedPowerEval degreeX
          (fun a₀ => gridCoeff preChart a₀ i) x * r ^ i) *
        scalePow) (degree + 1)) _
    (finSum_eqv_congr_lt _ _ (degree + 1) (fun i hi => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finSum_mul_const
          (fun a₀ =>
            Q'.ofInt (gridCoeff preChart a₀ i) * x ^ a₀)
          (r ^ i * scalePow) (degreeX + 1))) ?_
    change
      signedPowerEval degreeX
          (fun a₀ => gridCoeff preChart a₀ i) x *
          (r ^ i * scalePow) ≈
        (signedPowerEval degreeX
            (fun a₀ => gridCoeff preChart a₀ i) x * r ^ i) *
          scalePow
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (signedPowerEval degreeX
          (fun a₀ => gridCoeff preChart a₀ i) x)
        (r ^ i) scalePow)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finSum_mul_const
        (fun i =>
          signedPowerEval degreeX
              (fun a₀ => gridCoeff preChart a₀ i) x *
            r ^ i)
        scalePow (degree + 1))) ?_
  change
    tensorPowerEval degreeX degree (gridCoeff preChart) x r *
        scalePow ≈
      tensorPowerEval degreeX degree (gridCoeff preChart) x r *
        Q'.ofNat (affineChartBScale ^ degree)
  exact Q'.mul_eqv_congr_left
    (tensorPowerEval degreeX degree (gridCoeff preChart) x r) _ _
    (Q'.eqv_symm (ofNat_pow_eqv affineChartBScale degree))

/-! ## Triangular-support truncation -/

/-- Closed finite check for the support condition needed to retain the
original `x` degree after the affine substitution. -/
def GridTriangularSupport (degreeX degree : Nat)
    (grid : Nat → Nat → Int) : Bool :=
  allNat (degreeX + 1) (fun a =>
    allNat (degree + 1) (fun i =>
      decide (degreeX < a + i → grid a i = 0)))

/-- Extract one supported coefficient from a successful closed triangular
support check. -/
theorem gridTriangularSupport_true_at
    {degreeX degree : Nat} {grid : Nat → Nat → Int}
    (h : GridTriangularSupport degreeX degree grid = true)
    {a i : Nat} (ha : a < degreeX + 1)
    (hi : i < degree + 1) (hdegree : degreeX < a + i) :
    grid a i = 0 := by
  unfold GridTriangularSupport at h
  have haTrue := allNat_true_at h ha
  have hiTrue := allNat_true_at haTrue hi
  exact (of_decide_eq_true hiTrue) hdegree

/-- Row-sliced variant of `GridTriangularSupport`, used to keep kernel
reduction shallow for very large generated tables.  The grid is indexed by
the local row while the support inequality uses the global row. -/
def GridTriangularSupportSlice (start height degreeX degree : Nat)
    (grid : Nat → Nat → Int) : Bool :=
  allNat height (fun localRow =>
    allNat (degree + 1) (fun i =>
      decide (degreeX < start + localRow + i → grid localRow i = 0)))

/-- Extract one supported coefficient from a successful sliced check. -/
theorem gridTriangularSupportSlice_true_at
    {start height degreeX degree : Nat} {grid : Nat → Nat → Int}
    (h : GridTriangularSupportSlice start height degreeX degree grid = true)
    {localRow i : Nat} (hrow : localRow < height)
    (hi : i < degree + 1)
    (hdegree : degreeX < start + localRow + i) :
    grid localRow i = 0 := by
  unfold GridTriangularSupportSlice at h
  have hrowTrue := allNat_true_at h hrow
  have hiTrue := allNat_true_at hrowTrue hi
  exact (of_decide_eq_true hiTrue) hdegree

/-- Transport a local sliced support certificate through a checked
local-to-global row relation. -/
theorem gridTriangularSupportSlice_to_global
    (start height degreeX degree : Nat)
    (localGrid globalGrid : Nat → Nat → Int)
    (hsupport :
      GridTriangularSupportSlice start height degreeX degree localGrid = true)
    (haggregate :
      GridRelationSlice start height (degree + 1)
        localGrid globalGrid = true)
    {a i : Nat} (hstart : start ≤ a) (ha : a < start + height)
    (hi : i < degree + 1) (hdegree : degreeX < a + i) :
    globalGrid a i = 0 := by
  have hlocal := gridTriangularSupportSlice_true_at hsupport
    (localRow := a - start) (i := i) (by omega) hi (by omega)
  have hrelation := gridRelationSlice_true_at haggregate
    (localRow := a - start) (j := i) (by omega) hi
  have hindex : start + (a - start) = a := by omega
  rw [hindex] at hrelation
  exact Eq.trans (Eq.symm hrelation) hlocal

theorem intFinSum_eq_zero_of
    (f : Nat → Int) : ∀ count,
    (∀ i, i < count → f i = 0) → intFinSum f count = 0
  | 0, h => rfl
  | count + 1, h => by
      unfold intFinSum
      rw [intFinSum_eq_zero_of f count (fun i hi => h i (by omega)),
        h count (by omega), Int.zero_add]

/-- Triangular support of the input table forces every affine coefficient
above the declared output `x` degree to vanish. -/
theorem affineChartBClearedCoeff_zero_of_triangular
    (degreeX degree : Nat) (preChart : List (List Int))
    (hrows : preChart.length ≤ degreeX + 1)
    (htriangular : ∀ a, a < degreeX + 1 →
      ∀ i, i < degree + 1 → degreeX < a + i →
        gridCoeff preChart a i = 0)
    {a b : Nat} (ha : degreeX < a) :
    affineChartBClearedCoeff degree preChart a b = 0 := by
  rw [affineChartBClearedCoeff_eq_expanded]
  unfold affineChartBClearedCoeffExpanded
  apply intFinSum_eq_zero_of
  intro ell hell
  by_cases hlea : ell ≤ a
  · rw [if_pos hlea]
    apply intFinSum_eq_zero_of
    intro i hi
    unfold affineChartBInnerCoeff
    by_cases hguard :
        ell ≤ i ∧ i ≤ b + ell ∧ b + ell - i ≤ ell
    · rw [if_pos hguard]
      dsimp only
      have hzero : gridCoeff preChart (a - ell) i = 0 := by
        by_cases hrow : a - ell < degreeX + 1
        · exact htriangular (a - ell) hrow i hi (by omega)
        · exact gridCoeff_zero_of_length_le preChart degreeX
            (a - ell) i hrows (by omega)
      rw [hzero, Int.zero_mul, Int.zero_mul]
    · rw [if_neg hguard]
  · rw [if_neg hlea]

/-- Enlarging the affine output degree by `degree` adds only zero terms when
the pre-chart table has triangular support. -/
theorem tensorPowerEval_affineChartBClearedCoeff_truncate
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (htriangular : ∀ a, a < degreeX + 1 →
      ∀ i, i < degree + 1 → degreeX < a + i →
        gridCoeff preChart a i = 0) :
    tensorPowerEval (degreeX + degree) degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      tensorPowerEval degreeX degree
        (affineChartBClearedCoeff degree preChart) x z := by
  unfold tensorPowerEval
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro b hb
  refine Q'.mul_eqv_congr_right _ _ (z ^ b) ?_
  unfold signedPowerEval
  have hlength : degreeX + degree + 1 =
      (degreeX + 1) + degree := by omega
  rw [hlength]
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.finSum_split
      (fun a =>
        Q'.ofInt (affineChartBClearedCoeff degree preChart a b) * x ^ a)
      (degreeX + 1) degree) ?_
  have hsuffix :
      finSum (fun t =>
        Q'.ofInt
            (affineChartBClearedCoeff degree preChart
              (degreeX + 1 + t) b) *
          x ^ (degreeX + 1 + t)) degree ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt _ (fun _ => (0 : Q')) degree
        (fun t ht => ?_)) ?_
    · rw [affineChartBClearedCoeff_zero_of_triangular
          degreeX degree preChart hrows htriangular (by omega)]
      exact Q'.zero_mul_eqv _
    · rw [finSum_zero_seq]
      exact Q'.eqv_refl 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hsuffix) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Chart-B reconstruction at the original output degree, using the natural
triangular-support invariant `grid[a,i] = 0` whenever `degreeX < a+i`. -/
theorem tensorPowerEval_affineChartBClearedCoeff_triangular
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z r : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (htriangular : ∀ a, a < degreeX + 1 →
      ∀ i, i < degree + 1 → degreeX < a + i →
        gridCoeff preChart a i = 0)
    (hr : Q'.ofNat affineChartBScale * r ≈
      Q'.ofNat affineChartBScale * z + x * ((1 : Q') + -z)) :
    tensorPowerEval degreeX degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      tensorPowerEval degreeX degree (gridCoeff preChart) x r *
        Q'.ofNat (affineChartBScale ^ degree) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (tensorPowerEval_affineChartBClearedCoeff_truncate
        degreeX degree preChart x z hrows htriangular)) ?_
  exact tensorPowerEval_affineChartBClearedCoeff
    degreeX degree preChart x z r hrows hr

/-- Convenience form of chart-B reconstruction whose triangular support is
supplied by a closed finite certificate. -/
theorem tensorPowerEval_affineChartBClearedCoeff_of_support_check
    (degreeX degree : Nat) (preChart : List (List Int))
    (x z r : Q')
    (hrows : preChart.length ≤ degreeX + 1)
    (htriangular :
      GridTriangularSupport degreeX degree (gridCoeff preChart) = true)
    (hr : Q'.ofNat affineChartBScale * r ≈
      Q'.ofNat affineChartBScale * z + x * ((1 : Q') + -z)) :
    tensorPowerEval degreeX degree
        (affineChartBClearedCoeff degree preChart) x z ≈
      tensorPowerEval degreeX degree (gridCoeff preChart) x r *
        Q'.ofNat (affineChartBScale ^ degree) := by
  exact tensorPowerEval_affineChartBClearedCoeff_triangular
    degreeX degree preChart x z r hrows
    (fun a ha i hi hdegree =>
      gridTriangularSupport_true_at htriangular ha hi hdegree)
    hr

#print axioms ofInt_intFinSum
#print axioms signedPowerEval_affineChartBSignedRow
#print axioms affineChartBTensorTerm_eqv_binomialTerm
#print axioms affineChartB_scale_power_collapse
#print axioms tensorPowerEval_affineChartBClearedCoeff
#print axioms tensorPowerEval_affineChartBClearedCoeff_triangular
#print axioms tensorPowerEval_affineChartBClearedCoeff_of_support_check

end YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction
