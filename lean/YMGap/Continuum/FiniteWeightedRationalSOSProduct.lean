/-
# Constructive finite products of rational weighted SOS values

The direct active-quadratic route builds a nonnegative density face by face.
This leaf records the exact algebra needed to multiply two finite rational
sum-of-squares presentations without extracting square roots.

If

`A(x) = Σ_{i<a} w_i (f_i(x) f_i(x))`

and

`B(x) = Σ_{j<b} v_j (g_j(x) g_j(x))`,

their product is the packed SOS with `b*a` terms.  Packed index `p` represents
`(p / b, p % b)`, has weight `w_(p/b) v_(p%b)`, and feature
`f_(p/b) g_(p%b)`.  The proof uses `finSum_flatten`, so it is valid unchanged
when `b = 0`; no positive-divisor hypothesis or partial division is introduced.

Everything is explicit `Type`-level data over `Q'`.  There is no choice,
excluded middle, square-root extraction, or hidden existence claim.
-/

import YMGap.Continuum.SchurHadamardTransfer

namespace YMGap.Continuum.FiniteWeightedRationalSOSProduct

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SchurHadamardTransfer

local infix:50 " ≈ " => Q'.eqv

universe u v w

/-! ## 1. Finite weighted rational SOS data -/

/-- A finite rational sum-of-squares presentation on inputs of type `Input`.
The nonnegative weights are carried as data; no square roots of them are
chosen.  Values of `weight` and `feature` beyond `termCount` are harmless and
make packed mixed-radix indexing total. -/
structure FiniteWeightedRationalSOS (Input : Type u) : Type u where
  termCount : Nat
  weight : Nat → Q'
  weight_nonnegative : ∀ term, (0 : Q') ≤ weight term
  feature : Nat → Input → Q'

/-- Evaluation of a finite weighted rational SOS at one input. -/
def value {Input : Type u}
    (data : FiniteWeightedRationalSOS Input) (input : Input) : Q' :=
  finSum (fun term =>
    data.weight term *
      (data.feature term input * data.feature term input))
    data.termCount

/-- Every finite weighted rational SOS evaluates nonnegatively.  The proof is
fully constructive: each feature square is nonnegative, multiplication by its
stored nonnegative weight preserves nonnegativity, and the finite sum is
closed by induction. -/
theorem value_nonnegative {Input : Type u}
    (data : FiniteWeightedRationalSOS Input) (input : Input) :
    (0 : Q') ≤ value data input := by
  unfold value
  induction data.termCount with
  | zero =>
      change (0 : Q') ≤ 0
      exact Q'.le_refl' 0
  | succ termCount ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih
        (Q'.mul_nonneg _ _
          (data.weight_nonnegative termCount)
          (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
            (data.feature termCount input)))

/-! ## 2. Pullback along an input map -/

/-- Pull a finite weighted SOS presentation back along a map of input types.
The finite carrier and every weight are unchanged; only the feature functions
are precomposed with `map`. -/
def pullback {Input : Type u} {Source : Type v}
    (map : Source → Input)
    (data : FiniteWeightedRationalSOS Input) :
    FiniteWeightedRationalSOS Source where
  termCount := data.termCount
  weight := data.weight
  weight_nonnegative := data.weight_nonnegative
  feature := fun term source => data.feature term (map source)

/-- Pullback preserves every stored nonnegative weight exactly. -/
theorem pullback_weight_nonnegative
    {Input : Type u} {Source : Type v}
    (map : Source → Input)
    (data : FiniteWeightedRationalSOS Input) (term : Nat) :
    (0 : Q') ≤ (pullback map data).weight term :=
  (pullback map data).weight_nonnegative term

/-- Evaluation of a pulled-back presentation is evaluation of the original
presentation after applying the input map. -/
theorem value_pullback
    {Input : Type u} {Source : Type v}
    (map : Source → Input)
    (data : FiniteWeightedRationalSOS Input) (source : Source) :
    value (pullback map data) source ≈ value data (map source) :=
  Q'.eqv_refl _

/-- Pullback along the identity map is definitionally the original finite
weighted SOS presentation. -/
theorem pullback_id {Input : Type u}
    (data : FiniteWeightedRationalSOS Input) :
    pullback (fun input : Input => input) data = data := by
  cases data
  rfl

/-- Successive pullbacks compose definitionally. -/
theorem pullback_comp
    {Input : Type u} {Middle : Type v} {Source : Type w}
    (map : Middle → Input) (next : Source → Middle)
    (data : FiniteWeightedRationalSOS Input) :
    pullback next (pullback map data) =
      pullback (fun source => map (next source)) data := rfl

/-! ## 3. Packed multiplication -/

/-- The constructive product of two finite weighted SOS presentations.

The right factor supplies the least-significant mixed-radix coordinate.  Thus
the packed carrier has size `right.termCount * left.termCount`, including the
degenerate `right.termCount = 0` case. -/
def multiply {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) :
    FiniteWeightedRationalSOS Input where
  termCount := right.termCount * left.termCount
  weight := fun packed =>
    left.weight (packed / right.termCount) *
      right.weight (packed % right.termCount)
  weight_nonnegative := fun packed =>
    Q'.mul_nonneg _ _
      (left.weight_nonnegative (packed / right.termCount))
      (right.weight_nonnegative (packed % right.termCount))
  feature := fun packed input =>
    left.feature (packed / right.termCount) input *
      right.feature (packed % right.termCount) input

/-- Every packed product weight is nonnegative.  This is a named projection of
the constructive witness stored by `multiply`, useful to downstream SOS
nonnegativity consumers. -/
theorem multiply_weight_nonnegative {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) (packed : Nat) :
    (0 : Q') ≤ (multiply left right).weight packed :=
  (multiply left right).weight_nonnegative packed

/-- **Finite weighted SOS values are closed under multiplication.**

The first equivalence flattens the packed carrier into the double sum, the
second regroups each six-factor term, and the last folds the double sum into
the product of the two original sums.  Since `finSum_flatten` proves the zero
radix case constructively, this theorem requires no assumption that the right
term count is positive. -/
theorem value_multiply {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) (input : Input) :
    value (multiply left right) input ≈ value left input * value right input := by
  unfold value multiply
  refine Q'.eqv_trans _ _ _
    (finSum_flatten
      (fun i j =>
        (left.weight i * right.weight j) *
          ((left.feature i input * right.feature j input) *
            (left.feature i input * right.feature j input)))
      right.termCount left.termCount) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun i => finSum (fun j =>
        (left.weight i * right.weight j) *
          ((left.feature i input * right.feature j input) *
            (left.feature i input * right.feature j input)))
        right.termCount)
      (fun i => finSum (fun j =>
        (left.weight i *
            (left.feature i input * left.feature i input)) *
          (right.weight j *
            (right.feature j input * right.feature j input)))
        right.termCount)
      (fun i => finSum_eqv_congr _ _ (fun j =>
        Q'.eqv_symm
          (mul6_schur
            (left.weight i)
            (left.feature i input) (left.feature i input)
            (right.weight j)
            (right.feature j input) (right.feature j input)))
        right.termCount)
      left.termCount) ?_
  exact Q'.eqv_symm
    (finSum_mul_finSum
      (fun i => left.weight i *
        (left.feature i input * left.feature i input))
      (fun j => right.weight j *
        (right.feature j input * right.feature j input))
      left.termCount right.termCount)

/-! ## 4. Finite-list product interface -/

/-- The one-term SOS representing the constant value `1`. -/
def one (Input : Type u) : FiniteWeightedRationalSOS Input where
  termCount := 1
  weight := fun _ => 1
  weight_nonnegative := fun _ => by decide
  feature := fun _ _ => 1

/-- The constant-one SOS evaluates to `1`. -/
theorem value_one {Input : Type u} (input : Input) :
    value (one Input) input ≈ 1 := by
  change (((0 : Q') + (1 * (1 * 1))).eqv 1)
  decide

/-- Iterated constructive product of a finite list of SOS presentations. -/
def multiplyList {Input : Type u} :
    List (FiniteWeightedRationalSOS Input) → FiniteWeightedRationalSOS Input
  | [] => one Input
  | head :: tail => multiply head (multiplyList tail)

/-- The corresponding pointwise product of the presented SOS values. -/
def valueList {Input : Type u} :
    List (FiniteWeightedRationalSOS Input) → Input → Q'
  | [], _ => 1
  | head :: tail, input => value head input * valueList tail input

/-- Evaluation commutes with the finite-list product construction. -/
theorem value_multiplyList {Input : Type u}
    (data : List (FiniteWeightedRationalSOS Input)) (input : Input) :
    value (multiplyList data) input ≈ valueList data input := by
  induction data with
  | nil => exact value_one input
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (value_multiply head (multiplyList tail) input)
        (Q'.mul_eqv_congr_left (value head input)
          (value (multiplyList tail) input) (valueList tail input) ih)

/-! ## 5. Nonnegative scaling and finite sums -/

/-- The rank-zero SOS presentation of the constant value `0`. -/
def zero (Input : Type u) : FiniteWeightedRationalSOS Input where
  termCount := 0
  weight := fun _ => 0
  weight_nonnegative := fun _ => by decide
  feature := fun _ _ => 0

/-- Every (inactive) weight of the rank-zero presentation is nonnegative. -/
theorem zero_weight_nonnegative {Input : Type u} (term : Nat) :
    (0 : Q') ≤ (zero Input).weight term :=
  (zero Input).weight_nonnegative term

/-- The rank-zero SOS evaluates to `0`. -/
theorem value_zero {Input : Type u} (input : Input) :
    value (zero Input) input ≈ 0 := by
  exact Q'.eqv_refl _

/-- The one-term SOS presentation of a nonnegative rational constant.

The coefficient is kept as a weight and the feature is `1`, so no square root
of the constant is selected. -/
def constant (Input : Type u) (q : Q') (hq : (0 : Q') ≤ q) :
    FiniteWeightedRationalSOS Input where
  termCount := 1
  weight := fun _ => q
  weight_nonnegative := fun _ => hq
  feature := fun _ _ => 1

/-- Every weight of a constant SOS presentation is nonnegative. -/
theorem constant_weight_nonnegative {Input : Type u}
    (q : Q') (hq : (0 : Q') ≤ q) (term : Nat) :
    (0 : Q') ≤ (constant Input q hq).weight term :=
  (constant Input q hq).weight_nonnegative term

/-- Evaluation of the constant presentation gives exactly its coefficient. -/
theorem value_constant {Input : Type u}
    (q : Q') (hq : (0 : Q') ≤ q) (input : Input) :
    value (constant Input q hq) input ≈ q := by
  change ((0 : Q') + q * ((1 : Q') * (1 : Q'))) ≈ q
  rw [Q'.zero_add']
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q _ _ (Q'.mul_one_eqv (1 : Q')))
    (Q'.mul_one_eqv q)

/-- Scale a finite weighted SOS by a nonnegative rational, absorbing the
coefficient into its weights. -/
def scale {Input : Type u}
    (q : Q') (hq : (0 : Q') ≤ q)
    (data : FiniteWeightedRationalSOS Input) :
    FiniteWeightedRationalSOS Input where
  termCount := data.termCount
  weight := fun term => q * data.weight term
  weight_nonnegative := fun term =>
    Q'.mul_nonneg _ _ hq (data.weight_nonnegative term)
  feature := data.feature

/-- Every weight remains nonnegative after nonnegative scaling. -/
theorem scale_weight_nonnegative {Input : Type u}
    (q : Q') (hq : (0 : Q') ≤ q)
    (data : FiniteWeightedRationalSOS Input) (term : Nat) :
    (0 : Q') ≤ (scale q hq data).weight term :=
  (scale q hq data).weight_nonnegative term

/-- Evaluation commutes exactly with nonnegative rational scaling. -/
theorem value_scale {Input : Type u}
    (q : Q') (hq : (0 : Q') ≤ q)
    (data : FiniteWeightedRationalSOS Input) (input : Input) :
    value (scale q hq data) input ≈ q * value data input := by
  unfold value scale
  refine Q'.eqv_trans _
    (finSum (fun term =>
      q * (data.weight term *
        (data.feature term input * data.feature term input)))
      data.termCount) _ ?_ ?_
  · exact finSum_eqv_congr _ _ (fun term =>
      Q'.mul_assoc_eqv q (data.weight term)
        (data.feature term input * data.feature term input)) data.termCount
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun term => data.weight term *
          (data.feature term input * data.feature term input))
        q data.termCount)

/-- Constructive direct sum of two finite weighted SOS presentations.

Indices below `left.termCount` address the left block.  Every remaining index
uses the total offset coordinate `term - left.termCount` in the right block.
This definition is total even outside the active range. -/
def add {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) :
    FiniteWeightedRationalSOS Input where
  termCount := left.termCount + right.termCount
  weight := fun term =>
    if term < left.termCount then left.weight term
    else right.weight (term - left.termCount)
  weight_nonnegative := fun term => by
    show (0 : Q') ≤
      (if term < left.termCount then left.weight term
       else right.weight (term - left.termCount))
    split
    · exact left.weight_nonnegative term
    · exact right.weight_nonnegative _
  feature := fun term input =>
    if term < left.termCount then left.feature term input
    else right.feature (term - left.termCount) input

/-- Every offset-packed direct-sum weight is nonnegative. -/
theorem add_weight_nonnegative {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) (term : Nat) :
    (0 : Q') ≤ (add left right).weight term :=
  (add left right).weight_nonnegative term

/-- Evaluation of the offset-packed direct sum is exactly the sum of the two
presented values. -/
theorem value_add {Input : Type u}
    (left right : FiniteWeightedRationalSOS Input) (input : Input) :
    value (add left right) input ≈ value left input + value right input := by
  unfold value add
  refine Q'.eqv_trans _ _ _
    (finSum_add_range _ left.termCount right.termCount) ?_
  have hleft :
      (finSum (fun term =>
        (if term < left.termCount then left.weight term
         else right.weight (term - left.termCount)) *
          ((if term < left.termCount then left.feature term input
            else right.feature (term - left.termCount) input) *
           (if term < left.termCount then left.feature term input
            else right.feature (term - left.termCount) input)))
        left.termCount).eqv
      (finSum (fun term =>
        left.weight term *
          (left.feature term input * left.feature term input))
        left.termCount) :=
    finSum_congr_lt _ _ left.termCount (fun term hterm => by
      simp only [if_pos hterm]
      exact Q'.eqv_refl _)
  have hright :
      (finSum (fun offset =>
        (if left.termCount + offset < left.termCount
           then left.weight (left.termCount + offset)
           else right.weight ((left.termCount + offset) - left.termCount)) *
          ((if left.termCount + offset < left.termCount
             then left.feature (left.termCount + offset) input
             else right.feature ((left.termCount + offset) - left.termCount) input) *
           (if left.termCount + offset < left.termCount
             then left.feature (left.termCount + offset) input
             else right.feature ((left.termCount + offset) - left.termCount) input)))
        right.termCount).eqv
      (finSum (fun offset =>
        right.weight offset *
          (right.feature offset input * right.feature offset input))
        right.termCount) :=
    finSum_congr_lt _ _ right.termCount (fun offset _ => by
      have hnlt : ¬ (left.termCount + offset < left.termCount) :=
        Nat.not_lt.mpr (Nat.le_add_right left.termCount offset)
      simp only [if_neg hnlt, Nat.add_sub_cancel_left]
      exact Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hleft)
    (Q'.add_eqv_congr_left _ _ _ hright)

/-- Iterated constructive direct sum of a finite list of SOS presentations.
The empty list is represented by the rank-zero presentation. -/
def addList {Input : Type u} :
    List (FiniteWeightedRationalSOS Input) → FiniteWeightedRationalSOS Input
  | [] => zero Input
  | head :: tail => add head (addList tail)

/-- Every weight in an iterated finite direct sum is nonnegative. -/
theorem addList_weight_nonnegative {Input : Type u}
    (data : List (FiniteWeightedRationalSOS Input)) (term : Nat) :
    (0 : Q') ≤ (addList data).weight term :=
  (addList data).weight_nonnegative term

/-- Evaluation commutes with the finite-list direct sum.  The right side is
the structurally recursive list fold of the exact presented values. -/
theorem value_addList {Input : Type u}
    (data : List (FiniteWeightedRationalSOS Input)) (input : Input) :
    value (addList data) input ≈
      data.foldr (fun datum total => value datum input + total) (0 : Q') := by
  induction data with
  | nil =>
      exact value_zero input
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (value_add head (addList tail) input)
        (Q'.add_eqv_congr_left (value head input)
          (value (addList tail) input)
          (tail.foldr (fun datum total => value datum input + total) (0 : Q')) ih)

#print axioms multiply_weight_nonnegative
#print axioms value_nonnegative
#print axioms pullback_weight_nonnegative
#print axioms value_pullback
#print axioms pullback_id
#print axioms pullback_comp
#print axioms value_multiply
#print axioms value_one
#print axioms value_multiplyList
#print axioms zero_weight_nonnegative
#print axioms value_zero
#print axioms constant_weight_nonnegative
#print axioms value_constant
#print axioms scale_weight_nonnegative
#print axioms value_scale
#print axioms add_weight_nonnegative
#print axioms value_add
#print axioms addList_weight_nonnegative
#print axioms value_addList

end YMGap.Continuum.FiniteWeightedRationalSOSProduct
