/-
# Exact reconstruction of elevated monomials from Pascal coefficients

This module proves the semantic half of the Pascal/Bernstein certificate.
The coefficient row

  `j ↦ if e ≤ j then C(D-e,j-e) else 0`

really evaluates to `w^e` in the unnormalised Bernstein basis
`w^j (1-w)^(D-j)`.  The proof is constructive: split off the zero prefix,
reindex the supported suffix, factor `w^e`, and use the proved binomial
theorem over `Q'`.
-/

import YMGap.Continuum.BinomialTheorem
import YMGap.Constructive.CornerBound
import YMGap.Constructive.CharacterTail
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BernsteinMonomialReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BinomialTheorem

local infix:50 " ≈ " => Q'.eqv

private theorem rearrange4 (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num * (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num * (((a * b) * (c * d)).den : Int)
  rw [Q'.mul_den_cast (a * c) (b * d), Q'.mul_den_cast a c,
    Q'.mul_den_cast b d, Q'.mul_den_cast (a * b) (c * d),
    Q'.mul_den_cast a b, Q'.mul_den_cast c d]
  show (a.num * b.num) * (c.num * d.num) *
      (((a.den : Int) * c.den) * ((b.den : Int) * d.den)) =
    (a.num * c.num) * (b.num * d.num) *
      (((a.den : Int) * b.den) * ((c.den : Int) * d.den))
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

/-- The unnormalised degree-`D` Bernstein basis element. -/
def bernsteinBasis (D : Nat) (w : Q') (j : Nat) : Q' :=
  w ^ j * (1 - w) ^ (D - j)

/-- Pascal elevation coefficient of `w^e` at degree `D`. -/
def elevatedMonoCoeff (D e j : Nat) : Nat :=
  if e ≤ j then binom (D - e) (j - e) else 0

/-- Evaluation of the complete elevated coefficient row. -/
def elevatedMonoEval (D e : Nat) (w : Q') : Q' :=
  finSum (fun j => Q'.ofNat (elevatedMonoCoeff D e j) *
    bernsteinBasis D w j) (D + 1)

/-- Evaluation of an arbitrary signed coefficient row in increasing
Bernstein index. -/
def signedBernsteinEval (D : Nat) (c : Nat → Int) (w : Q') : Q' :=
  finSum (fun j => Q'.ofInt (c j) * bernsteinBasis D w j) (D + 1)

/-- The same row in deficit order `r=D-j`, after clearing the common
projective denominator.  At the harmonic point this is exactly
`sum_r c(D-r) (k+1)^(D-r)`. -/
def projectiveDeficitEval (D : Nat) (c : Nat → Int) (t : Q') : Q' :=
  finSum (fun r => Q'.ofInt (c (D - r)) * t ^ (D - r)) (D + 1)

/-- The four exceptional top-coordinate contributions, in deficit order. -/
def projectiveBoundaryFour (D : Nat) (c : Nat → Int) (t : Q') : Q' :=
  finSum (fun r => Q'.ofInt (c (D - r)) * t ^ (D - r)) 4

/-- The bulk following the four exceptional top coordinates. -/
def projectiveBulkAfterFour (D : Nat) (c : Nat → Int) (t : Q') : Q' :=
  finSum (fun s => Q'.ofInt (c (D - (4 + s))) * t ^ (D - (4 + s)))
    (D + 1 - 4)

private theorem pow_add_eqv (w : Q') (a : Nat) : ∀ b,
    w ^ (a + b) ≈ w ^ a * w ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (w ^ a))
  | b + 1 => by
      have ih := pow_add_eqv w a b
      show w * w ^ (a + b) ≈ w ^ a * (w * w ^ b)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left w _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv w (w ^ a) (w ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (w ^ b)
          (Q'.mul_comm_eqv w (w ^ a))) ?_
      exact Q'.mul_assoc_eqv (w ^ a) w (w ^ b)

private theorem pow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ (n : Nat),
    a ^ n ≈ b ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := pow_eqv_congr h n
      show a * a ^ n ≈ b * b ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right a b (a ^ n) h) ?_
      exact Q'.mul_eqv_congr_left b _ _ ih

private theorem mul_pow_eqv (a b : Q') : ∀ (n : Nat),
    (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n + 1 => by
      have ih := mul_pow_eqv a b n
      show (a * b) * (a * b) ^ n ≈
        (a * a ^ n) * (b * b ^ n)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      exact rearrange4 a b (a ^ n) (b ^ n)

private theorem finSum_reverse (g : QSeq) : ∀ n,
    finSum g n ≈ finSum (fun r => g (n - 1 - r)) n
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      have hpeel := RationalTail.finSum_peel_left (fun r => g (n - r)) n
      have hrefl : (fun r => g (n + 1 - 1 - r)) =
          (fun r => g (n - r)) := by
        funext r
        congr 1 <;> omega
      have htail : (fun r => g (n - (r + 1))) =
          (fun r => g (n - 1 - r)) := by
        funext r
        congr 1 <;> omega
      have hih : finSum (fun r => g (n - 1 - r)) n ≈ finSum g n :=
        Q'.eqv_symm (finSum_reverse g n)
      rw [hrefl]
      show finSum g n + g n ≈ finSum (fun r => g (n - r)) (n + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (finSum g n) (g n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (g n) _ _ (Q'.eqv_symm hih)) ?_
      rw [← htail]
      exact Q'.eqv_symm hpeel

private theorem basis_mul_den_pow (D j : Nat) (w den t : Q')
    (hj : j ≤ D) (hwt : w * den ≈ t)
    (hud : (1 - w) * den ≈ 1) :
    bernsteinBasis D w j * den ^ D ≈ t ^ j := by
  have hD : D = j + (D - j) := by omega
  have hsplit : den ^ D ≈ den ^ j * den ^ (D - j) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg (fun n : Nat => den ^ n) hD))
      (pow_add_eqv den j (D - j))
  unfold bernsteinBasis
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (w ^ j * (1 - w) ^ (D - j)) _ _ hsplit) ?_
  refine Q'.eqv_trans _ _ _
    (rearrange4 (w ^ j) ((1 - w) ^ (D - j))
      (den ^ j) (den ^ (D - j))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (mul_pow_eqv w den j))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ((w * den) ^ j) _ _
      (Q'.eqv_symm (mul_pow_eqv (1 - w) den (D - j)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (pow_eqv_congr hwt j)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (t ^ j) _ _
      (pow_eqv_congr hud (D - j))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (t ^ j) _ _
      (eqv_one_pow 1 (Q'.eqv_refl 1) (D - j))) ?_
  exact Q'.mul_one_eqv (t ^ j)

/-- **Projective clearing identity for an arbitrary signed row.**  If
`w·den=t` and `(1-w)·den=1`, multiplying the Bernstein evaluation by
the positive common denominator `den^D` gives the deficit polynomial
`sum_r c(D-r)t^(D-r)`.  This is the exact weighted reconstruction needed
when the top coefficients have mixed signs. -/
theorem signedBernsteinEval_mul_den_pow_eqv_projectiveDeficitEval
    (D : Nat) (c : Nat → Int) (w den t : Q')
    (hwt : w * den ≈ t) (hud : (1 - w) * den ≈ 1) :
    signedBernsteinEval D c w * den ^ D ≈
      projectiveDeficitEval D c t := by
  unfold signedBernsteinEval projectiveDeficitEval
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const
      (fun j => Q'.ofInt (c j) * bernsteinBasis D w j)
      (den ^ D) (D + 1)) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _
      (fun j => Q'.ofInt (c j) * t ^ j) (D + 1) ?_) ?_
  · intro j hj
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofInt (c j)) (bernsteinBasis D w j)
        (den ^ D)) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofInt (c j)) _ _
      (basis_mul_den_pow D j w den t (by omega) hwt hud)
  · exact finSum_reverse (fun j => Q'.ofInt (c j) * t ^ j) (D + 1)

/-- Exact four-coordinate/bulk split of the projective deficit polynomial. -/
theorem projectiveDeficitEval_split_four (D : Nat) (c : Nat → Int)
    (t : Q') (hD : 3 ≤ D) :
    projectiveDeficitEval D c t ≈
      projectiveBoundaryFour D c t + projectiveBulkAfterFour D c t := by
  unfold projectiveDeficitEval projectiveBoundaryFour projectiveBulkAfterFour
  have hlen : D + 1 = 4 + (D + 1 - 4) := by omega
  let f : QSeq := fun r => Q'.ofInt (c (D - r)) * t ^ (D - r)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (congrArg (finSum f) hlen))
    (YMGap.Constructive.finSum_split f 4 (D + 1 - 4))

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem finSum_nonnegative (f : QSeq) : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ f i) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      show (0 : Q') ≤ finSum f N + f N
      exact Q'.zero_le_add _ _
        (finSum_nonnegative f N (fun i hi => h i (by omega)))
        (h N (by omega))

/-- Quantitative boundary-payment consumer.  A nonnegative weighted sum of
the four exceptional coefficients, together with coefficientwise
nonnegativity only in the genuine bulk, makes the entire projective row
nonnegative. -/
theorem projectiveDeficitEval_nonnegative_of_boundary_bulk
    (D : Nat) (c : Nat → Int) (t : Q')
    (hD : 3 ≤ D) (ht : (0 : Q') ≤ t)
    (hboundary : (0 : Q') ≤ projectiveBoundaryFour D c t)
    (hbulk : ∀ r, 4 ≤ r → r ≤ D → (0 : Int) ≤ c (D - r)) :
    (0 : Q') ≤ projectiveDeficitEval D c t := by
  have hbulkSum : (0 : Q') ≤ projectiveBulkAfterFour D c t := by
    unfold projectiveBulkAfterFour
    apply finSum_nonnegative
    intro s hs
    have hr4 : 4 ≤ 4 + s := by omega
    have hrD : 4 + s ≤ D := by omega
    exact Q'.mul_nonneg _ _
      (ofInt_nonnegative (hbulk (4 + s) hr4 hrD))
      (Q'.pow_nonneg t ht (D - (4 + s)))
  exact Q'.le_trans' _ _ _
    (Q'.zero_le_add _ _ hboundary hbulkSum)
    (Q'.ge_of_eqv (projectiveDeficitEval_split_four D c t hD))

private theorem coeff_factor_reorder (C A B Z : Q') :
    C * ((A * B) * Z) ≈ A * (C * (B * Z)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left C _ _ (Q'.mul_assoc_eqv A B Z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv C A (B * Z))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (B * Z) (Q'.mul_comm_eqv C A)) ?_
  exact Q'.mul_assoc_eqv A C (B * Z)

private theorem supported_term (D e k : Nat) (w : Q')
    (heD : e ≤ D) (hk : k < D - e + 1) :
    Q'.ofNat (elevatedMonoCoeff D e (e + k)) *
        bernsteinBasis D w (e + k) ≈
      w ^ e * S0seq (D - e) w (1 - w) k := by
  have hek : e ≤ e + k := Nat.le_add_right e k
  have hsub : e + k - e = k := by omega
  have hExp : D - (e + k) = (D - e) - k := by omega
  rw [elevatedMonoCoeff, if_pos hek, hsub]
  unfold bernsteinBasis S0seq bmono
  rw [hExp]
  have hp := pow_add_eqv w e k
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (binom (D - e) k)) _ _
      (Q'.mul_eqv_congr_right _ _ _ hp)) ?_
  exact coeff_factor_reorder _ _ _ _

private theorem unsupported_prefix (D e : Nat) (w : Q') :
    finSum (fun j => Q'.ofNat (elevatedMonoCoeff D e j) *
      bernsteinBasis D w j) e ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ (fun _ => (0 : Q')) e ?_) ?_
  · intro j hj
    have hnot : ¬ e ≤ j := by omega
    rw [elevatedMonoCoeff, if_neg hnot]
    change (0 : Q') * bernsteinBasis D w j ≈ 0
    exact Q'.zero_mul_eqv _
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

private theorem supported_suffix (D e : Nat) (w : Q') (heD : e ≤ D) :
    finSum
        (fun k =>
          Q'.ofNat (elevatedMonoCoeff D e (e + k)) *
            bernsteinBasis D w (e + k))
        (D - e + 1) ≈
      w ^ e * finSum (S0seq (D - e) w (1 - w)) (D - e + 1) := by
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _
      (fun k => w ^ e * S0seq (D - e) w (1 - w) k)
      (D - e + 1) (fun k hk => supported_term D e k w heD hk)) ?_
  exact Q'.eqv_symm
    (const_mul_finSum (S0seq (D - e) w (1 - w)) (w ^ e) (D - e + 1))

/-- **Exact coefficient-to-evaluation reconstruction.**  Every elevated
monomial row evaluates to the original monomial on all constructive
rationals. -/
theorem elevatedMonoEval_eqv_pow (D e : Nat) (w : Q') (heD : e ≤ D) :
    elevatedMonoEval D e w ≈ w ^ e := by
  unfold elevatedMonoEval
  have hlen : D + 1 = e + (D - e + 1) := by omega
  rw [hlen]
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.finSum_split
      (fun j => Q'.ofNat (elevatedMonoCoeff D e j) *
        bernsteinBasis D w j) e (D - e + 1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (unsupported_prefix D e w)) ?_
  rw [Q'.zero_add']
  refine Q'.eqv_trans _ _ _ (supported_suffix D e w heD) ?_
  have hbin := binomialTheorem (D - e) w (1 - w)
  have hone := add_one_sub_eqv_one w
  have hpow : (w + (1 - w)) ^ (D - e) ≈ 1 :=
    eqv_one_pow (w + (1 - w)) hone (D - e)
  have hsum : finSum (S0seq (D - e) w (1 - w)) (D - e + 1) ≈ 1 :=
    Q'.eqv_trans _ _ _ hbin hpow
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (w ^ e) _ _ hsum) ?_
  exact Q'.mul_one_eqv (w ^ e)

#print axioms elevatedMonoEval_eqv_pow
#print axioms signedBernsteinEval_mul_den_pow_eqv_projectiveDeficitEval
#print axioms projectiveDeficitEval_split_four
#print axioms projectiveDeficitEval_nonnegative_of_boundary_bulk

end YMGap.Continuum.BernsteinMonomialReconstruction
