/-
# Separable coefficient reconstruction for tensor Bernstein tables

Large exact tensor tables should not be expanded by the ring normaliser.
This module instead checks the two Pascal transforms at coefficient level
and proves once that they reconstruct the corresponding bivariate power
polynomial.  The transform is staged in the two coordinate directions, so a
closed certificate costs two one-dimensional passes rather than a dense
four-variable normalization.
-/

import YMGap.Continuum.BernsteinMonomialReconstruction

namespace YMGap.Continuum.TensorBernsteinSeparableReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.BernsteinMonomialReconstruction

local infix:50 " ≈ " => Q'.eqv

/-! ## Integer Pascal transforms -/

def rowAdd (a b : Nat → Int) : Nat → Int :=
  fun j => a j + b j

def rowScale (z : Int) (a : Nat → Int) : Nat → Int :=
  fun j => z * a j

/-- Prefix of the Pascal elevation of an integer power row. -/
def pascalPrefix (degree : Nat) (coefficients : Nat → Int) :
    Nat → Nat → Int
  | 0 => fun _ => 0
  | exponent + 1 =>
      rowAdd (pascalPrefix degree coefficients exponent)
        (rowScale (coefficients exponent)
          (fun index => Int.ofNat
            (elevatedMonoCoeff degree exponent index)))

/-- Complete integer Pascal elevation at one output index. -/
def pascalTransformRow (degree : Nat) (coefficients : Nat → Int)
    (index : Nat) : Int :=
  pascalPrefix degree coefficients (degree + 1) index

/-- First (x-coordinate) pass of the tensor transform. -/
def tensorPascalMid (degreeX : Nat) (power : Nat → Nat → Int)
    (indexX exponentY : Nat) : Int :=
  pascalTransformRow degreeX (fun exponentX => power exponentX exponentY)
    indexX

/-- Second (y-coordinate) pass of the tensor transform. -/
def tensorPascalTransform (degreeX degreeY : Nat)
    (power : Nat → Nat → Int) (indexX indexY : Nat) : Int :=
  pascalTransformRow degreeY
    (fun exponentY => tensorPascalMid degreeX power indexX exponentY)
    indexY

theorem pascalTransformRow_congr (degree : Nat) (a b : Nat → Int)
    (index : Nat) (h : ∀ exponent, exponent < degree + 1 →
      a exponent = b exponent) :
    pascalTransformRow degree a index =
      pascalTransformRow degree b index := by
  unfold pascalTransformRow
  have hprefix : ∀ count, count ≤ degree + 1 →
      pascalPrefix degree a count index =
        pascalPrefix degree b count index := by
    intro count hcount
    induction count with
    | zero => rfl
    | succ count ih =>
        unfold pascalPrefix rowAdd rowScale
        rw [ih (by omega), h count (by omega)]
  exact hprefix (degree + 1) (Nat.le_refl _)

/-! ## Closed grid checks -/

def allNat : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | count + 1, predicate =>
      allNat count predicate && predicate count

theorem allNat_true_at {count : Nat} {predicate : Nat → Bool}
    (h : allNat count predicate = true) {index : Nat}
    (hindex : index < count) : predicate index = true := by
  induction count with
  | zero => omega
  | succ count ih =>
      have hsplit := (Bool.and_eq_true _ _).mp h
      by_cases heq : index = count
      · simpa [heq] using hsplit.2
      · exact ih hsplit.1 (by omega)

def GridRelation (height width : Nat) (actual expected : Nat → Nat → Int) :
    Bool :=
  allNat height (fun i =>
    allNat width (fun j => decide (actual i j = expected i j)))

theorem gridRelation_true_at {height width : Nat}
    {actual expected : Nat → Nat → Int}
    (h : GridRelation height width actual expected = true)
    {i j : Nat} (hi : i < height) (hj : j < width) :
    actual i j = expected i j := by
  have hiTrue := allNat_true_at h hi
  have hjTrue := allNat_true_at hiTrue hj
  exact of_decide_eq_true hjTrue

def GridNonnegative (height width : Nat) (grid : Nat → Nat → Int) : Bool :=
  allNat height (fun i =>
    allNat width (fun j => decide ((0 : Int) ≤ grid i j)))

theorem gridNonnegative_true_at {height width : Nat}
    {grid : Nat → Nat → Int}
    (h : GridNonnegative height width grid = true)
    {i j : Nat} (hi : i < height) (hj : j < width) :
    (0 : Int) ≤ grid i j := by
  have hiTrue := allNat_true_at h hi
  have hjTrue := allNat_true_at hiTrue hj
  exact of_decide_eq_true hjTrue

def gridCoeff (rows : List (List Int)) (i j : Nat) : Int :=
  (rows.getD i []).getD j 0

/-! ## One-dimensional semantic reconstruction -/

def signedPowerEval (degree : Nat) (coefficients : Nat → Int)
    (w : Q') : Q' :=
  finSum (fun exponent => Q'.ofInt (coefficients exponent) * w ^ exponent)
    (degree + 1)

private theorem signedEval_add (degree : Nat) (a b : Nat → Int) (w : Q') :
    signedBernsteinEval degree (rowAdd a b) w ≈
      signedBernsteinEval degree a w + signedBernsteinEval degree b w := by
  unfold signedBernsteinEval rowAdd
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun j => Q'.ofInt (a j + b j) * bernsteinBasis degree w j)
      (fun j => Q'.ofInt (a j) * bernsteinBasis degree w j +
        Q'.ofInt (b j) * bernsteinBasis degree w j)
      (degree + 1) (fun j _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_add (a j) (b j))) ?_
    exact Q'.add_mul_eqv (Q'.ofInt (a j)) (Q'.ofInt (b j))
      (bernsteinBasis degree w j)
  · exact RationalTail.finSum_add
      (fun j => Q'.ofInt (a j) * bernsteinBasis degree w j)
      (fun j => Q'.ofInt (b j) * bernsteinBasis degree w j)
      (degree + 1)

private theorem signedEval_scale (degree : Nat) (z : Int)
    (a : Nat → Int) (w : Q') :
    signedBernsteinEval degree (rowScale z a) w ≈
      Q'.ofInt z * signedBernsteinEval degree a w := by
  unfold signedBernsteinEval rowScale
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun j => Q'.ofInt (z * a j) * bernsteinBasis degree w j)
      (fun j => Q'.ofInt z *
        (Q'.ofInt (a j) * bernsteinBasis degree w j))
      (degree + 1) (fun j _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_mul z (a j))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofInt z) (Q'.ofInt (a j))
      (bernsteinBasis degree w j)
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun j => Q'.ofInt (a j) * bernsteinBasis degree w j)
        (Q'.ofInt z) (degree + 1))

private theorem signedEval_zero (degree : Nat) (w : Q') :
    signedBernsteinEval degree (fun _ => 0) w ≈ 0 := by
  unfold signedBernsteinEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun j => Q'.ofInt 0 * bernsteinBasis degree w j)
      (fun _ => (0 : Q')) (degree + 1) (fun j _ => ?_)) ?_
  · exact Q'.zero_mul_eqv (bernsteinBasis degree w j)
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

private theorem signedEval_pascalPrefix (degree : Nat)
    (coefficients : Nat → Int) (w : Q') :
    ∀ count, count ≤ degree + 1 →
      signedBernsteinEval degree
          (pascalPrefix degree coefficients count) w ≈
        finSum (fun exponent =>
          Q'.ofInt (coefficients exponent) * w ^ exponent) count
  | 0, _ => signedEval_zero degree w
  | count + 1, hcount => by
      have hcountDegree : count ≤ degree := by omega
      have ih := signedEval_pascalPrefix degree coefficients w count (by omega)
      let elevated : Nat → Int := fun index =>
        Int.ofNat (elevatedMonoCoeff degree count index)
      have helevated :
          signedBernsteinEval degree elevated w =
            elevatedMonoEval degree count w := by
        rfl
      have hmono : signedBernsteinEval degree elevated w ≈ w ^ count := by
        rw [helevated]
        exact elevatedMonoEval_eqv_pow degree count w hcountDegree
      unfold pascalPrefix
      refine Q'.eqv_trans _ _ _
        (signedEval_add degree
          (pascalPrefix degree coefficients count)
          (rowScale (coefficients count) elevated) w) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (signedEval_scale degree (coefficients count) elevated w)) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofInt (coefficients count)) _ _ hmono)

/-- A complete integer Pascal transform evaluates to its power row. -/
theorem signedBernsteinEval_pascalTransformRow
    (degree : Nat) (coefficients : Nat → Int) (w : Q') :
    signedBernsteinEval degree
        (fun index => pascalTransformRow degree coefficients index) w ≈
      signedPowerEval degree coefficients w := by
  unfold pascalTransformRow signedPowerEval
  exact signedEval_pascalPrefix degree coefficients w (degree + 1)
    (Nat.le_refl _)

/-! ## Upper-binomial shift reconstruction -/

def upperBinomialPrefix (coefficients : Nat → Int) : Nat → Nat → Int
  | 0 => fun _ => 0
  | exponent + 1 =>
      rowAdd (upperBinomialPrefix coefficients exponent)
        (rowScale (coefficients exponent)
          (fun index => Int.ofNat (binom exponent index)))

def upperBinomialTransform (degree : Nat) (coefficients : Nat → Int)
    (index : Nat) : Int :=
  upperBinomialPrefix coefficients (degree + 1) index

private theorem signedPowerEval_add (degree : Nat)
    (a b : Nat → Int) (w : Q') :
    signedPowerEval degree (rowAdd a b) w ≈
      signedPowerEval degree a w + signedPowerEval degree b w := by
  unfold signedPowerEval rowAdd
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun j => Q'.ofInt (a j + b j) * w ^ j)
      (fun j => Q'.ofInt (a j) * w ^ j + Q'.ofInt (b j) * w ^ j)
      (degree + 1) (fun j _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_add (a j) (b j))) ?_
    exact Q'.add_mul_eqv (Q'.ofInt (a j)) (Q'.ofInt (b j)) (w ^ j)
  · exact RationalTail.finSum_add
      (fun j => Q'.ofInt (a j) * w ^ j)
      (fun j => Q'.ofInt (b j) * w ^ j) (degree + 1)

private theorem signedPowerEval_scale (degree : Nat) (z : Int)
    (a : Nat → Int) (w : Q') :
    signedPowerEval degree (rowScale z a) w ≈
      Q'.ofInt z * signedPowerEval degree a w := by
  unfold signedPowerEval rowScale
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun j => Q'.ofInt (z * a j) * w ^ j)
      (fun j => Q'.ofInt z * (Q'.ofInt (a j) * w ^ j))
      (degree + 1) (fun j _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.RingNormaliser.ofInt_mul z (a j))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofInt z) (Q'.ofInt (a j)) (w ^ j)
  · exact Q'.eqv_symm
      (const_mul_finSum (fun j => Q'.ofInt (a j) * w ^ j)
        (Q'.ofInt z) (degree + 1))

private theorem signedPowerEval_zero (degree : Nat) (w : Q') :
    signedPowerEval degree (fun _ => 0) w ≈ 0 := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q')) (degree + 1)
      (fun j _ => Q'.zero_mul_eqv (w ^ j))) ?_
  rw [finSum_zero_seq]
  exact Q'.eqv_refl 0

private theorem signedPowerEval_binomialRow
    (degree exponent : Nat) (w : Q') (hexponent : exponent ≤ degree) :
    signedPowerEval degree
        (fun index => Int.ofNat (binom exponent index)) w ≈
      (w + 1) ^ exponent := by
  unfold signedPowerEval
  have hlength : degree + 1 = (exponent + 1) + (degree - exponent) := by
    omega
  rw [hlength]
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.finSum_split
      (fun index => Q'.ofInt (Int.ofNat (binom exponent index)) * w ^ index)
      (exponent + 1) (degree - exponent)) ?_
  have hprefix :
      finSum
          (fun index => Q'.ofInt (Int.ofNat (binom exponent index)) *
            w ^ index) (exponent + 1) ≈
        finSum (BernsteinVariance.S0seq exponent w 1) (exponent + 1) := by
    refine finSum_eqv_congr_lt _ _ (exponent + 1) ?_
    intro index hindex
    change Q'.ofNat (binom exponent index) * w ^ index ≈
      Q'.ofNat (binom exponent index) *
        (w ^ index * (1 : Q') ^ (exponent - index))
    have hone : (1 : Q') ^ (exponent - index) ≈ 1 :=
      BernsteinVariance.eqv_one_pow 1 (Q'.eqv_refl 1) _
    refine Q'.mul_eqv_congr_left (Q'.ofNat (binom exponent index)) _ _ ?_
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (w ^ index) _ _ hone)
      (Q'.mul_one_eqv (w ^ index)))
  have hsuffix :
      finSum
          (fun offset =>
            Q'.ofInt (Int.ofNat
              (binom exponent (exponent + 1 + offset))) *
                w ^ (exponent + 1 + offset))
          (degree - exponent) ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt _ (fun _ => (0 : Q')) (degree - exponent)
        (fun offset _ => ?_)) ?_
    · rw [binom_eq_zero_of_lt exponent (exponent + 1 + offset) (by omega)]
      exact Q'.zero_mul_eqv _
    · rw [finSum_zero_seq]
      exact Q'.eqv_refl 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hprefix) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hsuffix) ?_
  rw [Q'.add_zero']
  exact BinomialTheorem.binomialTheorem exponent w 1

private theorem signedPowerEval_upperPrefix (degree : Nat)
    (coefficients : Nat → Int) (w : Q') :
    ∀ count, count ≤ degree + 1 →
      signedPowerEval degree
          (upperBinomialPrefix coefficients count) w ≈
        finSum (fun exponent =>
          Q'.ofInt (coefficients exponent) * (w + 1) ^ exponent) count
  | 0, _ => signedPowerEval_zero degree w
  | count + 1, hcount => by
      have hcountDegree : count ≤ degree := by omega
      have ih := signedPowerEval_upperPrefix degree coefficients w count (by omega)
      let binomialRow : Nat → Int := fun index =>
        Int.ofNat (binom count index)
      have hbinomial :
          signedPowerEval degree binomialRow w ≈ (w + 1) ^ count :=
        signedPowerEval_binomialRow degree count w hcountDegree
      unfold upperBinomialPrefix
      refine Q'.eqv_trans _ _ _
        (signedPowerEval_add degree
          (upperBinomialPrefix coefficients count)
          (rowScale (coefficients count) binomialRow) w) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (signedPowerEval_scale degree (coefficients count) binomialRow w)) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofInt (coefficients count)) _ _ hbinomial)

/-- Upper-binomial coefficient transform reconstructs the shift `w ↦ w+1`. -/
theorem signedPowerEval_upperBinomialTransform
    (degree : Nat) (coefficients : Nat → Int) (w : Q') :
    signedPowerEval degree
        (fun index => upperBinomialTransform degree coefficients index) w ≈
      finSum (fun exponent =>
        Q'.ofInt (coefficients exponent) * (w + 1) ^ exponent)
        (degree + 1) := by
  unfold upperBinomialTransform
  exact signedPowerEval_upperPrefix degree coefficients w (degree + 1)
    (Nat.le_refl _)

/-! ## Tensor reconstruction -/

def tensorBernsteinEval (degreeX degreeY : Nat)
    (weighted : Nat → Nat → Int) (x y : Q') : Q' :=
  finSum (fun i => bernsteinBasis degreeX x i *
    signedBernsteinEval degreeY (weighted i) y) (degreeX + 1)

def tensorPowerEval (degreeX degreeY : Nat)
    (power : Nat → Nat → Int) (x y : Q') : Q' :=
  finSum (fun exponentY =>
    signedPowerEval degreeX (fun exponentX => power exponentX exponentY) x *
      y ^ exponentY) (degreeY + 1)

private theorem tensor_reorder (a b c : Q') :
    a * (b * c) ≈ (b * a) * c := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  exact Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)

/-- Two coefficient-level Pascal passes reconstruct a tensor power table. -/
theorem tensorBernsteinEval_eqv_powerEval
    (degreeX degreeY : Nat) (power weighted : Nat → Nat → Int)
    (x y : Q')
    (htransform : ∀ i, i < degreeX + 1 → ∀ j, j < degreeY + 1 →
      weighted i j = tensorPascalTransform degreeX degreeY power i j) :
    tensorBernsteinEval degreeX degreeY weighted x y ≈
      tensorPowerEval degreeX degreeY power x y := by
  unfold tensorBernsteinEval
  let mid : Nat → Nat → Int := tensorPascalMid degreeX power
  have hinner : ∀ i, i < degreeX + 1 →
      signedBernsteinEval degreeY (weighted i) y ≈
        signedPowerEval degreeY (mid i) y := by
    intro i hi
    have hrow : signedBernsteinEval degreeY (weighted i) y ≈
        signedBernsteinEval degreeY
          (fun j => tensorPascalTransform degreeX degreeY power i j) y := by
      unfold signedBernsteinEval
      exact finSum_eqv_congr_lt _ _ (degreeY + 1) (fun j hj => by
        rw [htransform i hi j hj]
        exact Q'.eqv_refl _)
    exact Q'.eqv_trans _ _ _ hrow
      (signedBernsteinEval_pascalTransformRow degreeY (mid i) y)
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun i hi =>
      Q'.mul_eqv_congr_left (bernsteinBasis degreeX x i) _ _
        (hinner i hi))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun i _ =>
      const_mul_finSum
        (fun b => Q'.ofInt (mid i b) * y ^ b)
        (bernsteinBasis degreeX x i) (degreeY + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_swap
      (fun i b => bernsteinBasis degreeX x i *
        (Q'.ofInt (mid i b) * y ^ b))
      (degreeX + 1) (degreeY + 1)) ?_
  unfold tensorPowerEval
  refine finSum_eqv_congr_lt _ _ (degreeY + 1) ?_
  intro b hb
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun i _ =>
      tensor_reorder (bernsteinBasis degreeX x i)
        (Q'.ofInt (mid i b)) (y ^ b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finSum_mul_const
        (fun i => Q'.ofInt (mid i b) * bernsteinBasis degreeX x i)
        (y ^ b) (degreeX + 1))) ?_
  exact Q'.mul_eqv_congr_right _ _ (y ^ b)
    (signedBernsteinEval_pascalTransformRow degreeX
      (fun a => power a b) x)

/-! ## Projective raw-chart reconstruction -/

def diagonalPowerEval (degreeA degreeY totalDegree : Nat)
    (raw : Nat → Nat → Int) (den target : Q') : Q' :=
  finSum (fun a =>
    finSum (fun j => Q'.ofInt (raw a j) *
      (target ^ j * den ^ (totalDegree - a - j))) (degreeY + 1))
    (degreeA + 1)

private theorem pow_add_eqv (value : Q') (a : Nat) : ∀ b,
    value ^ (a + b) ≈ value ^ a * value ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (value ^ a))
  | b + 1 => by
      have ih := pow_add_eqv value a b
      show value * value ^ (a + b) ≈ value ^ a * (value * value ^ b)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left value _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv value (value ^ a) (value ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (value ^ b)
          (Q'.mul_comm_eqv value (value ^ a))) ?_
      exact Q'.mul_assoc_eqv (value ^ a) value (value ^ b)

private theorem pow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ exponent : Nat,
    a ^ exponent ≈ b ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := pow_eqv_congr h exponent
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a ^ exponent) h)
        (Q'.mul_eqv_congr_left b _ _ ih)

private theorem rearrange4 (a b c d : Q') :
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

private theorem mul_pow_eqv (a b : Q') : ∀ exponent : Nat,
    (a * b) ^ exponent ≈ a ^ exponent * b ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have ih := mul_pow_eqv a b exponent
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      exact rearrange4 a b (a ^ exponent) (b ^ exponent)

private theorem ofNat_pow_eqv (value : Nat) : ∀ exponent,
    (Q'.ofNat value) ^ exponent ≈ Q'.ofNat (value ^ exponent)
  | 0 => by
      change (1 : Q') ≈ Q'.ofNat 1
      decide
  | exponent + 1 => by
      have ih := ofNat_pow_eqv value exponent
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat value) _ _ ih) ?_
      have hmul := YMGap.Continuum.RingNormaliser.ofInt_mul
        (Int.ofNat value) (Int.ofNat (value ^ exponent))
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hmul) ?_
      show (Int.ofNat value * Int.ofNat (value ^ exponent)) * (1 : Int) =
        Int.ofNat (value ^ (exponent + 1)) * (1 : Int)
      simp only [Int.mul_one, Int.ofNat_eq_natCast, ← Int.natCast_mul,
        Nat.pow_succ, Nat.mul_comm]

private theorem tensorPowerEval_by_x
    (degreeX degreeY : Nat) (power : Nat → Nat → Int) (x y : Q') :
    tensorPowerEval degreeX degreeY power x y ≈
      finSum (fun a => x ^ a * signedPowerEval degreeY (power a) y)
        (degreeX + 1) := by
  unfold tensorPowerEval signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeY + 1) (fun b _ =>
      finSum_mul_const
        (fun a => Q'.ofInt (power a b) * x ^ a)
        (y ^ b) (degreeX + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_swap
      (fun b a => (Q'.ofInt (power a b) * x ^ a) * y ^ b)
      (degreeY + 1) (degreeX + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degreeX + 1) ?_
  intro a ha
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun b => (Q'.ofInt (power a b) * x ^ a) * y ^ b)
      (fun b => x ^ a * (Q'.ofInt (power a b) * y ^ b))
      (degreeY + 1) (fun b _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofInt (power a b)) (x ^ a) (y ^ b)) ?_
    refine Q'.eqv_trans _ _ _
      (tensor_reorder (Q'.ofInt (power a b)) (x ^ a) (y ^ b)) ?_
    exact Q'.mul_assoc_eqv (x ^ a) (Q'.ofInt (power a b)) (y ^ b)
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun b => Q'.ofInt (power a b) * y ^ b)
        (x ^ a) (degreeY + 1))

private theorem scale_signedPowerEval
    (degree constant exponent : Nat) (coefficients : Nat → Int) (w : Q') :
    Q'.ofNat constant ^ exponent * signedPowerEval degree coefficients w ≈
      signedPowerEval degree
        (fun index => coefficients index * Int.ofNat (constant ^ exponent)) w := by
  unfold signedPowerEval
  refine Q'.eqv_trans _ _ _
    (const_mul_finSum
      (fun index => Q'.ofInt (coefficients index) * w ^ index)
      (Q'.ofNat constant ^ exponent) (degree + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
  intro index hindex
  have hpow := ofNat_pow_eqv constant exponent
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hpow) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (constant ^ exponent))
        (Q'.ofInt (coefficients index)) (w ^ index))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (w ^ index)
      (Q'.mul_comm_eqv (Q'.ofNat (constant ^ exponent))
        (Q'.ofInt (coefficients index)))) ?_
  refine Q'.mul_eqv_congr_right _ _ (w ^ index) ?_
  exact Q'.eqv_symm
    (YMGap.Continuum.RingNormaliser.ofInt_mul
      (coefficients index) (Int.ofNat (constant ^ exponent)))

/-- Clear a common projective denominator after the raw upper-binomial
chart transform.  The only coefficient checks are the supplied pointwise
integer relations and diagonal support bound. -/
theorem tensorPowerEval_mul_den_pow_eqv_diagonal
    (degreeX degreeY totalDegree constant : Nat)
    (power raw : Nat → Nat → Int) (x y den target : Q')
    (hdegree : degreeX ≤ totalDegree)
    (hxden : x * den ≈ Q'.ofNat constant)
    (hyden : (y + 1) * den ≈ target)
    (hshift : ∀ a, a < degreeX + 1 → ∀ b, b < degreeY + 1 →
      power a b * Int.ofNat (constant ^ a) =
        upperBinomialTransform degreeY (raw a) b)
    (hsupport : ∀ a, a < degreeX + 1 → ∀ j, j < degreeY + 1 →
      raw a j ≠ 0 → a + j ≤ totalDegree) :
    tensorPowerEval degreeX degreeY power x y * den ^ totalDegree ≈
      diagonalPowerEval degreeX degreeY totalDegree raw den target := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (den ^ totalDegree)
      (tensorPowerEval_by_x degreeX degreeY power x y)) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_mul_const
      (fun a => x ^ a * signedPowerEval degreeY (power a) y)
      (den ^ totalDegree) (degreeX + 1)) ?_
  unfold diagonalPowerEval
  refine finSum_eqv_congr_lt _ _ (degreeX + 1) ?_
  intro a ha
  have haTotal : a ≤ totalDegree := Nat.le_trans (by omega) hdegree
  have hdenSplit : den ^ totalDegree ≈ den ^ a * den ^ (totalDegree - a) := by
    have hshape : totalDegree = a + (totalDegree - a) := by omega
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg (fun exponent => den ^ exponent) hshape))
      (pow_add_eqv den a (totalDegree - a))
  have hxa : x ^ a * den ^ a ≈ Q'.ofNat constant ^ a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_pow_eqv x den a))
      (pow_eqv_congr hxden a)
  have hscaled :
      Q'.ofNat constant ^ a * signedPowerEval degreeY (power a) y ≈
        signedPowerEval degreeY
          (fun b => upperBinomialTransform degreeY (raw a) b) y := by
    refine Q'.eqv_trans _ _ _
      (scale_signedPowerEval degreeY constant a (power a) y) ?_
    unfold signedPowerEval
    exact finSum_eqv_congr_lt _ _ (degreeY + 1) (fun b hb => by
      change Q'.ofInt (power a b * Int.ofNat (constant ^ a)) * y ^ b ≈
        Q'.ofInt (upperBinomialTransform degreeY (raw a) b) * y ^ b
      rw [hshift a ha b hb]
      exact Q'.eqv_refl _)
  have hshiftEval := signedPowerEval_upperBinomialTransform
    degreeY (raw a) y
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (x ^ a * signedPowerEval degreeY (power a) y)
      _ _ hdenSplit) ?_
  refine Q'.eqv_trans _ _ _
    (rearrange4 (x ^ a) (signedPowerEval degreeY (power a) y)
      (den ^ a) (den ^ (totalDegree - a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (signedPowerEval degreeY (power a) y *
      den ^ (totalDegree - a)) hxa) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat constant ^ a)
        (signedPowerEval degreeY (power a) y)
        (den ^ (totalDegree - a)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (den ^ (totalDegree - a)) hscaled) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (den ^ (totalDegree - a)) hshiftEval) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_mul_const
      (fun j => Q'.ofInt (raw a j) * (y + 1) ^ j)
      (den ^ (totalDegree - a)) (degreeY + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degreeY + 1) ?_
  intro j hj
  by_cases hvalid : a + j ≤ totalDegree
  · have hrestShape : totalDegree - a = j + (totalDegree - a - j) := by
      omega
    have hrest : den ^ (totalDegree - a) ≈
        den ^ j * den ^ (totalDegree - a - j) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg (fun exponent => den ^ exponent) hrestShape))
        (pow_add_eqv den j (totalDegree - a - j))
    have hyj : (y + 1) ^ j * den ^ j ≈ target ^ j :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_pow_eqv (y + 1) den j))
        (pow_eqv_congr hyden j)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofInt (raw a j) * (y + 1) ^ j) _ _ hrest) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofInt (raw a j)) ((y + 1) ^ j)
        (den ^ j * den ^ (totalDegree - a - j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofInt (raw a j)) _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv ((y + 1) ^ j) (den ^ j)
            (den ^ (totalDegree - a - j))))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofInt (raw a j)) _ _
      (Q'.mul_eqv_congr_right _ _ (den ^ (totalDegree - a - j)) hyj)
  · have hzero : raw a j = 0 := by
      by_cases hz : raw a j = 0
      · exact hz
      · exact False.elim (hvalid (hsupport a ha j hj hz))
    rw [hzero]
    change ((0 : Q') * (y + 1) ^ j) * den ^ (totalDegree - a) ≈
      (0 : Q') * (target ^ j * den ^ (totalDegree - a - j))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (den ^ (totalDegree - a))
        (Q'.zero_mul_eqv ((y + 1) ^ j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.zero_mul_eqv (den ^ (totalDegree - a))) ?_
    exact Q'.eqv_symm
      (Q'.zero_mul_eqv (target ^ j * den ^ (totalDegree - a - j)))

/-- Integer scaling commutes with diagonal power evaluation. -/
theorem diagonalPowerEval_scale
    (degreeA degreeY totalDegree : Nat) (scale : Int)
    (raw : Nat → Nat → Int) (den target : Q') :
    diagonalPowerEval degreeA degreeY totalDegree
        (fun a j => scale * raw a j) den target ≈
      Q'.ofInt scale *
        diagonalPowerEval degreeA degreeY totalDegree raw den target := by
  unfold diagonalPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun a => finSum (fun j =>
        Q'.ofInt (scale * raw a j) *
          (target ^ j * den ^ (totalDegree - a - j))) (degreeY + 1))
      (fun a => Q'.ofInt scale * finSum (fun j =>
        Q'.ofInt (raw a j) *
          (target ^ j * den ^ (totalDegree - a - j))) (degreeY + 1))
      (degreeA + 1) (fun a _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt
        (fun j => Q'.ofInt (scale * raw a j) *
          (target ^ j * den ^ (totalDegree - a - j)))
        (fun j => Q'.ofInt scale *
          (Q'.ofInt (raw a j) *
            (target ^ j * den ^ (totalDegree - a - j))))
        (degreeY + 1) (fun j _ => ?_)) ?_
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (YMGap.Continuum.RingNormaliser.ofInt_mul scale (raw a j))) ?_
      exact Q'.mul_assoc_eqv (Q'.ofInt scale) (Q'.ofInt (raw a j))
        (target ^ j * den ^ (totalDegree - a - j))
    · exact Q'.eqv_symm
        (const_mul_finSum
          (fun j => Q'.ofInt (raw a j) *
            (target ^ j * den ^ (totalDegree - a - j)))
          (Q'.ofInt scale) (degreeY + 1))
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun a => finSum (fun j => Q'.ofInt (raw a j) *
          (target ^ j * den ^ (totalDegree - a - j))) (degreeY + 1))
        (Q'.ofInt scale) (degreeA + 1))

private theorem ofInt_nonnegative {coefficient : Int}
    (hcoefficient : (0 : Int) ≤ coefficient) :
    (0 : Q') ≤ Q'.ofInt coefficient := by
  change (0 : Int) * (1 : Int) ≤ coefficient * (1 : Int)
  simpa using hcoefficient

private theorem finSum_nonnegative_bounded (f : Nat → Q') :
    ∀ count, (∀ i, i < count → (0 : Q') ≤ f i) →
      (0 : Q') ≤ finSum f count
  | 0, _ => Q'.le_refl' 0
  | count + 1, h =>
      Q'.zero_le_add _ _
        (finSum_nonnegative_bounded f count
          (fun i hi => h i (by omega)))
        (h count (by omega))

/-- A nonnegative weighted tensor table is nonnegative on `[0,1]²`. -/
theorem tensorBernsteinEval_nonnegative
    (degreeX degreeY : Nat) (weighted : Nat → Nat → Int)
    (x y : Q')
    (hx : (0 : Q') ≤ x) (hxc : (0 : Q') ≤ 1 - x)
    (hy : (0 : Q') ≤ y) (hyc : (0 : Q') ≤ 1 - y)
    (hweighted : ∀ i, i < degreeX + 1 → ∀ j, j < degreeY + 1 →
      (0 : Int) ≤ weighted i j) :
    (0 : Q') ≤ tensorBernsteinEval degreeX degreeY weighted x y := by
  unfold tensorBernsteinEval signedBernsteinEval
  apply finSum_nonnegative_bounded
  intro i hi
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _ (Q'.pow_nonneg x hx i)
      (Q'.pow_nonneg (1 - x) hxc (degreeX - i))
  · apply finSum_nonnegative_bounded
    intro j hj
    apply Q'.mul_nonneg
    · exact ofInt_nonnegative (hweighted i hi j hj)
    · exact Q'.mul_nonneg _ _ (Q'.pow_nonneg y hy j)
        (Q'.pow_nonneg (1 - y) hyc (degreeY - j))

#print axioms pascalTransformRow_congr
#print axioms gridRelation_true_at
#print axioms gridNonnegative_true_at
#print axioms signedBernsteinEval_pascalTransformRow
#print axioms signedPowerEval_upperBinomialTransform
#print axioms tensorBernsteinEval_eqv_powerEval
#print axioms tensorPowerEval_mul_den_pow_eqv_diagonal
#print axioms diagonalPowerEval_scale
#print axioms tensorBernsteinEval_nonnegative

end YMGap.Continuum.TensorBernsteinSeparableReconstruction
