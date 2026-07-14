/-
# Physical normalization of the first five-channel near-stretched family

For `n=u+8`, the all-order-two channel

  `(n,4,n; 2n-4; n,n)`

lies in a five-dimensional right-channel block.  This file proves its exact
denominator-free transvectant recoupling row, identifies the signed inverse
Schur coefficient, and closes the collapsed factorial Racah square.
-/

import YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm
import YMGap.Continuum.SU2OrderedRacahNearStretchedCrossNormalization
import YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
import YMGap.Continuum.RingNormaliserStream

namespace YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization

set_option maxHeartbeats 9000000
set_option maxRecDepth 28000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAdjacentDifference
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTerm
open YMGap.Continuum.SU2OrderedRacahCasimirCapstone
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.add_zero, Int.zero_add] <;> ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem add_eqv_zero_of_zero {a b : Q'}
    (ha : a ≈ 0) (hb : b ≈ 0) : a + b ≈ 0 := by
  exact Q'.eqv_trans _ (0 + 0) _
    (Q'.add_eqv_congr' ha hb) (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem five_scaled_zeros (a b c d e : Q') :
    ((((a * 0 + b * 0) + c * 0) + d * 0) + e * 0) ≈ 0 := by
  exact add_eqv_zero_of_zero
    (add_eqv_zero_of_zero
      (add_eqv_zero_of_zero
        (add_eqv_zero_of_zero (Q'.mul_zero_eqv a) (Q'.mul_zero_eqv b))
        (Q'.mul_zero_eqv c))
      (Q'.mul_zero_eqv d))
    (Q'.mul_zero_eqv e)

private theorem five_scaled_center (a b c d x : Q') :
    ((((a * 0 + b * 0) + x) + c * 0) + d * 0) ≈ x := by
  have hab : a * 0 + b * 0 ≈ 0 :=
    add_eqv_zero_of_zero (Q'.mul_zero_eqv a) (Q'.mul_zero_eqv b)
  have hx : (a * 0 + b * 0) + x ≈ x :=
    Q'.eqv_trans _ (0 + x) _
      (Q'.add_eqv_congr_right _ _ _ hab)
      (Q'.eqv_of_eq (Q'.zero_add' x))
  have hc : ((a * 0 + b * 0) + x) + c * 0 ≈ x :=
    Q'.eqv_trans _ (x + 0) _
      (Q'.add_eqv_congr' hx (Q'.mul_zero_eqv c))
      (Q'.eqv_of_eq (Q'.add_zero' x))
  exact Q'.eqv_trans _ (x + 0) _
    (Q'.add_eqv_congr' hc (Q'.mul_zero_eqv d))
    (Q'.eqv_of_eq (Q'.add_zero' x))

/-! ## A uniform symbolic factorial row -/

/-- Falling factorial over `Q'`, written as a genuine polynomial. -/
def qFall : Q' → Nat → Q'
  | _, 0 => 1
  | X, r + 1 => qFall X r * qSub X (Q'.ofNat r)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  ac_rfl

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = qSub (Q'.ofNat a) (Q'.ofNat b) := by
  unfold qSub
  change Q'.ofNat (a - b) = Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofNat b))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private theorem ofNat_add_eq (a b : Nat) :
    Q'.ofNat (a + b) = Q'.ofNat a + Q'.ofNat b := by
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem tvFallingNat_zero_of_lt (N : Nat) : ∀ r, N < r →
    tvFallingNat N r = 0
  | 0, h => by omega
  | r + 1, h => by
      simp only [tvFallingNat]
      by_cases hr : r ≤ N
      · have hrN : r = N := by omega
        rw [hrN, Nat.sub_self, Nat.mul_zero]
      · rw [tvFallingNat_zero_of_lt N r (by omega), Nat.zero_mul]

private theorem qFall_ofNat (N : Nat) : ∀ r,
    qFall (Q'.ofNat N) r ≈ Q'.ofNat (tvFallingNat N r)
  | 0 => by
      unfold qFall tvFallingNat
      exact Q'.eqv_refl _
  | r + 1 => by
      unfold qFall tvFallingNat
      by_cases hr : r ≤ N
      · have hsub := ofNat_sub_eq N r hr
        rw [← hsub]
        exact Q'.eqv_trans _
          (Q'.ofNat (tvFallingNat N r) * Q'.ofNat (N - r)) _
          (Q'.mul_eqv_congr_right _ _ _ (qFall_ofNat N r))
          (ofNat_mul_eqv _ _)
      · have hz : tvFallingNat N r = 0 :=
          tvFallingNat_zero_of_lt N r (by omega)
        rw [hz, Nat.zero_mul]
        have hq0 : qFall (Q'.ofNat N) r ≈ Q'.ofNat 0 := by
          simpa only [hz] using qFall_ofNat N r
        refine Q'.eqv_trans _ (Q'.ofNat 0 * qSub (Q'.ofNat N) (Q'.ofNat r)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ hq0
        · exact Q'.eqv_trans _ (0 * qSub (Q'.ofNat N) (Q'.ofNat r)) _
            (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
            (Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
              (Q'.eqv_symm Q'.ofNat_zero_eqv))

theorem tvFallQ_symbolic (N r : Nat) :
    tvFallQ N r ≈ qFall (Q'.ofNat N) r := by
  by_cases hr : r ≤ N
  · exact Q'.eqv_trans _ (Q'.ofNat (tvFallingNat N r)) _
      (tvFallQ_eqv_fallingNat N r hr) (Q'.eqv_symm (qFall_ofNat N r))
  · have hz : tvFallingNat N r = 0 :=
      tvFallingNat_zero_of_lt N r (by omega)
    have hq := qFall_ofNat N r
    rw [hz] at hq
    unfold tvFallQ
    rw [if_neg hr]
    exact Q'.eqv_trans _ (Q'.ofNat 0) _
      (Q'.eqv_symm Q'.ofNat_zero_eqv) (Q'.eqv_symm hq)

private def signedChoose (k r : Nat) : Int :=
  if r % 2 = 0 then Int.ofNat (PNPaths.choose k r)
  else -Int.ofNat (PNPaths.choose k r)

private theorem phase_binom_symbolic (k r : Nat) :
    tvPhase r * tvBinomQ k r ≈ Q'.ofInt (signedChoose k r) := by
  have hb := tvBinomQ_eqv_choose_all k r
  refine Q'.eqv_trans _
    (tvPhase r * Q'.ofNat (PNPaths.choose k r)) _
    (Q'.mul_eqv_congr_left _ _ _ hb) ?_
  unfold tvPhase signedChoose
  by_cases hpar : r % 2 = 0
  · rw [if_pos hpar, if_pos hpar]
    exact Q'.one_mul_eqv _
  · rw [if_neg hpar, if_neg hpar]
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast]
    change ((-1 : Int) * Int.ofNat (PNPaths.choose k r)) * 1 =
      (-Int.ofNat (PNPaths.choose k r)) * ((1 : Int) * 1)
    simp

private def hahnRowTermSymbolic (k r : Nat) (M N X Y : Q') : Q' :=
  Q'.ofInt (signedChoose k r) *
    qFall X (k - r) * qFall (qSub M X) r *
      qFall Y r * qFall (qSub N Y) (k - r)

private def hahnRowSumSymbolic (k : Nat) (M N X Y : Q') : Nat → Q'
  | 0 => 0
  | r + 1 => hahnRowSumSymbolic k M N X Y r +
      hahnRowTermSymbolic k r M N X Y

/-- The order-`k` factorial Hahn row as a polynomial over `Q'`. -/
def hahnRowSymbolic (k : Nat) (M N X Y : Q') : Q' :=
  finSum (fun r => hahnRowTermSymbolic k r M N X Y) (k + 1)

theorem transvectFactorialCoeff_symbolic (m n k i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    transvectFactorialCoeff m n k i j ≈
      hahnRowSymbolic k (Q'.ofNat m) (Q'.ofNat n)
        (Q'.ofNat i) (Q'.ofNat j) := by
  have hmi := ofNat_sub_eq m i hi
  have hnj := ofNat_sub_eq n j hj
  unfold transvectFactorialCoeff hahnRowSymbolic
  apply finSum_eqv_congr
  intro r
  unfold hahnRowTermSymbolic
  rw [← hmi, ← hnj]
  exact mul_eqv_congr
    (mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr (phase_binom_symbolic k r)
          (tvFallQ_symbolic i (k - r)))
        (tvFallQ_symbolic (m - i) r))
      (tvFallQ_symbolic j r))
    (tvFallQ_symbolic (n - j) (k - r))

private theorem qFall_zero_of_lt (N r : Nat) (h : N < r) :
    qFall (Q'.ofNat N) r ≈ 0 := by
  have hq := qFall_ofNat N r
  rw [tvFallingNat_zero_of_lt N r h] at hq
  exact Q'.eqv_trans _ (Q'.ofNat 0) _ hq Q'.ofNat_zero_eqv

private theorem finSum_all_zero_local (f : Nat → Q') : ∀ N,
    (∀ i, i < N → f i ≈ 0) → finSum f N ≈ 0
  | 0, _ => Q'.eqv_refl 0
  | N + 1, h => by
      change finSum f N + f N ≈ 0
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (finSum_all_zero_local f N (fun i hi => h i (by omega)))
          (h N (by omega))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem mul_zero_second_chain (a b c d : Q') :
    a * 0 * b * c * d ≈ 0 := by
  have h0 : a * 0 ≈ 0 := Q'.mul_zero_eqv a
  have h1 : a * 0 * b ≈ 0 := Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv b)
  have h2 : a * 0 * b * c ≈ 0 := Q'.eqv_trans _ (0 * c) _
    (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv c)
  exact Q'.eqv_trans _ (0 * d) _
    (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.zero_mul_eqv d)

private theorem mul_zero_fourth_chain (a b c d : Q') :
    a * b * c * 0 * d ≈ 0 := by
  have h0 : a * b * c * 0 ≈ 0 := Q'.mul_zero_eqv _
  exact Q'.eqv_trans _ (0 * d) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv d)

theorem hahnRowSymbolic_zero_below (m n k i j : Nat)
    (_hi : i ≤ m) (_hj : j ≤ n) (hbelow : i + j < k) :
    hahnRowSymbolic k (Q'.ofNat m) (Q'.ofNat n)
        (Q'.ofNat i) (Q'.ofNat j) ≈ 0 := by
  unfold hahnRowSymbolic
  apply finSum_all_zero_local
  intro R hR
  have hRk : R ≤ k := by omega
  have hor : i < k - R ∨ j < R := by omega
  unfold hahnRowTermSymbolic
  rcases hor with hleft | hright
  · have hz := qFall_zero_of_lt i (k - R) hleft
    refine Q'.eqv_trans _
      (Q'.ofInt (signedChoose k R) * 0 *
        qFall (qSub (Q'.ofNat m) (Q'.ofNat i)) R *
          qFall (Q'.ofNat j) R *
            qFall (qSub (Q'.ofNat n) (Q'.ofNat j)) (k - R)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hz)))
    · exact mul_zero_second_chain _ _ _ _
  · have hz := qFall_zero_of_lt j R hright
    refine Q'.eqv_trans _
      (Q'.ofInt (signedChoose k R) * qFall (Q'.ofNat i) (k - R) *
        qFall (qSub (Q'.ofNat m) (Q'.ofNat i)) R * 0 *
          qFall (qSub (Q'.ofNat n) (Q'.ofNat j)) (k - R)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hz)
    · exact mul_zero_fourth_chain _ _ _ _

private theorem mul_zero_third_chain (a b c d : Q') :
    a * b * 0 * c * d ≈ 0 := by
  have h0 : a * b * 0 ≈ 0 := Q'.mul_zero_eqv _
  have h1 : a * b * 0 * c ≈ 0 := Q'.eqv_trans _ (0 * c) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv c)
  exact Q'.eqv_trans _ (0 * d) _
    (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv d)

/-- A factorial Hahn row vanishes above its physical total-degree support. -/
theorem hahnRowSymbolic_zero_above (m n k i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) (habove : m + n < i + j + k) :
    hahnRowSymbolic k (Q'.ofNat m) (Q'.ofNat n)
        (Q'.ofNat i) (Q'.ofNat j) ≈ 0 := by
  unfold hahnRowSymbolic
  apply finSum_all_zero_local
  intro R hR
  have hRk : R ≤ k := by omega
  have hor : m - i < R ∨ n - j < k - R := by omega
  have hmi := ofNat_sub_eq m i hi
  have hnj := ofNat_sub_eq n j hj
  unfold hahnRowTermSymbolic
  rw [← hmi, ← hnj]
  rcases hor with hleft | hright
  · have hz := qFall_zero_of_lt (m - i) R hleft
    refine Q'.eqv_trans _
      (Q'.ofInt (signedChoose k R) * qFall (Q'.ofNat i) (k - R) * 0 *
        qFall (Q'.ofNat j) R * qFall (Q'.ofNat (n - j)) (k - R)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hz))
    · exact mul_zero_third_chain _ _ _ _
  · have hz := qFall_zero_of_lt (n - j) (k - R) hright
    refine Q'.eqv_trans _
      (Q'.ofInt (signedChoose k R) * qFall (Q'.ofNat i) (k - R) *
        qFall (Q'.ofNat (m - i)) R * qFall (Q'.ofNat j) R * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hz
    · exact Q'.mul_zero_eqv _

/-! ## The five-channel polynomial row -/

def threeLeftPayloadQ (U I J L : Q') : Q' :=
  let N := U + 8
  hahnRowSymbolic 2 N 4 I J *
    hahnRowSymbolic 2 N N (qSub (I + J) 2) L

def threeRightPayloadQ (p : Nat) (U I J L : Q') : Q' :=
  let N := U + 8
  hahnRowSymbolic p 4 N J L *
    hahnRowSymbolic (4 - p) N
      (qSub (N + 4) (Q'.ofNat (2 * p))) I
      (qSub (J + L) (Q'.ofNat p))

def threeRowScaleQ (U : Q') : Q' :=
  (U + 6) * (U + 8) * (U + 9) * (U + 10) * (U + 11) * (U + 12)

def threeRowCoeffQ (p : Nat) (U : Q') : Q' :=
  match p with
  | 0 => 12 * (U + 6) * (U + 7) * ((U + 8) * (U + 8))
  | 1 => -(6 * (U + 6) * (U + 7) * (U + 11) *
      (U * U + 7 * U + (-4)))
  | 2 => (U + 6) * (U + 9) * (U + 12) *
      (U * U * U + -(U * U) + -(124 * U) + (-452))
  | 3 => 2 * (U + 2) * ((U + 7) * (U + 7)) * (2 * U + 15) *
      (U + 11) * (U + 12)
  | _ => 2 * (U + 7) * (2 * U + 15) * (U + 8) * (U + 10) *
      (U + 11) * (U + 12)

private abbrev PE := PolyExpr
private def peAdd (x y : PE) : PE := .add x y
private def peMul (x y : PE) : PE := .mul x y
private def peNeg (x : PE) : PE := .neg x
private def peConst (z : Int) : PE := .const z
private def peSub (x y : PE) : PE := peAdd x (peNeg y)

private def fallExpr (X : PE) : Nat → PE
  | 0 => peConst 1
  | r + 1 => peMul (fallExpr X r) (peSub X (peConst (Int.ofNat r)))

private def rowTermExpr (k r : Nat) (M N X Y : PE) : PE :=
  peMul (peMul (peMul (peMul
    (peConst (signedChoose k r)) (fallExpr X (k - r)))
    (fallExpr (peSub M X) r)) (fallExpr Y r))
    (fallExpr (peSub N Y) (k - r))

private def rowSumExpr (k : Nat) (M N X Y : PE) : Nat → PE
  | 0 => peConst 0
  | r + 1 => peAdd (rowSumExpr k M N X Y r) (rowTermExpr k r M N X Y)

private def rowExpr (k : Nat) (M N X Y : PE) : PE :=
  rowSumExpr k M N X Y (k + 1)

private def pU : PE := .var 0
private def pI : PE := .var 1
private def pJ : PE := .var 2
private def pL : PE := .var 3
private def pN : PE := peAdd pU (peConst 8)

private def leftPayloadExpr (J : PE) : PE :=
  peMul (rowExpr 2 pN (peConst 4) pI J)
    (rowExpr 2 pN pN (peSub (peAdd pI J) (peConst 2)) pL)

private def rightPayloadExpr (p : Nat) (J : PE) : PE :=
  peMul (rowExpr p (peConst 4) pN J pL)
    (rowExpr (4 - p) pN
      (peSub (peAdd pN (peConst 4)) (peConst (Int.ofNat (2 * p)))) pI
      (peSub (peAdd J pL) (peConst (Int.ofNat p))))

private def rowScaleExpr : PE :=
  peMul (peMul (peMul (peMul (peMul
    (peAdd pU (peConst 6)) (peAdd pU (peConst 8)))
    (peAdd pU (peConst 9))) (peAdd pU (peConst 10)))
    (peAdd pU (peConst 11))) (peAdd pU (peConst 12))

private def coeffExpr : Nat → PE
  | 0 => peMul (peMul (peMul (peConst 12) (peAdd pU (peConst 6)))
      (peAdd pU (peConst 7)))
      (peMul (peAdd pU (peConst 8)) (peAdd pU (peConst 8)))
  | 1 => peNeg (peMul (peMul (peMul (peMul (peConst 6)
      (peAdd pU (peConst 6))) (peAdd pU (peConst 7)))
      (peAdd pU (peConst 11)))
      (peAdd (peAdd (peMul pU pU) (peMul (peConst 7) pU)) (peConst (-4))))
  | 2 => peMul (peMul (peMul (peAdd pU (peConst 6))
      (peAdd pU (peConst 9))) (peAdd pU (peConst 12)))
      (peAdd (peAdd (peAdd (peMul (peMul pU pU) pU)
        (peNeg (peMul pU pU))) (peNeg (peMul (peConst 124) pU)))
        (peConst (-452)))
  | 3 => peMul (peMul (peMul (peMul (peMul (peConst 2)
      (peAdd pU (peConst 2)))
      (peMul (peAdd pU (peConst 7)) (peAdd pU (peConst 7))))
      (peAdd (peMul (peConst 2) pU) (peConst 15)))
      (peAdd pU (peConst 11))) (peAdd pU (peConst 12))
  | _ => peMul (peMul (peMul (peMul (peMul (peConst 2)
      (peAdd pU (peConst 7)))
      (peAdd (peMul (peConst 2) pU) (peConst 15)))
      (peAdd pU (peConst 8))) (peAdd pU (peConst 10)))
      (peMul (peAdd pU (peConst 11)) (peAdd pU (peConst 12)))

private def rowLHSExpr (J : PE) : PE := peMul rowScaleExpr (leftPayloadExpr J)

private def rowRHSExpr (J : PE) : PE :=
  peAdd (peAdd (peAdd (peAdd
    (peMul (coeffExpr 0) (rightPayloadExpr 0 J))
    (peMul (coeffExpr 1) (rightPayloadExpr 1 J)))
    (peMul (coeffExpr 2) (rightPayloadExpr 2 J)))
    (peMul (coeffExpr 3) (rightPayloadExpr 3 J)))
    (peMul (coeffExpr 4) (rightPayloadExpr 4 J))

private def rowResidualExpr (j : Nat) : PE :=
  peAdd (rowLHSExpr (peConst (Int.ofNat j)))
    (peNeg (rowRHSExpr (peConst (Int.ofNat j))))

/-! ### A three-variable deterministic root certificate -/

private def env3 (x y z : Q') : Nat → Q' := fun i =>
  if i = 0 then x else if i = 1 then y else if i = 3 then z else 0

private theorem update0_env3 (x y z : Q') :
    (fun i => if i = 0 then x else env3 0 y z i) = env3 x y z := by
  funext i
  by_cases h0 : i = 0 <;> simp [env3, h0]

private theorem update1_env3 (x y z : Q') :
    (fun i => if i = 1 then y else env3 x 0 z i) = env3 x y z := by
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [env3]
  · by_cases h1 : i = 1 <;> simp [env3, h0, h1]

private theorem update2_env3 (x y z : Q') :
    (fun i => if i = 3 then z else env3 x y 0 i) = env3 x y z := by
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [env3]
  · by_cases h1 : i = 1
    · subst i
      simp [env3]
    · by_cases h3 : i = 3 <;> simp [env3, h0, h1, h3]

private def degreeAt (v : Nat) : PE → Nat
  | .const _ => 0
  | .var i => if i = v then 1 else 0
  | .add a b => max (degreeAt v a) (degreeAt v b)
  | .mul a b => degreeAt v a + degreeAt v b
  | .neg a => degreeAt v a
  | .pow a n => n * degreeAt v a + n

private theorem length_coeffAt_le_degreeAt (v : Nat) : ∀ (e : PE) (rho : Nat → Q'),
    (YMGap.Continuum.RingNormaliserStream.coeffAt v e rho).length ≤
      degreeAt v e + 1
  | .const _, rho => by
      simp [YMGap.Continuum.RingNormaliserStream.coeffAt, degreeAt]
  | .var i, rho => by
      show (if i = v then
          ([0, 1] : YMGap.Constructive.QPoly.Poly) else [rho i]).length ≤
        degreeAt v (.var i) + 1
      by_cases h : i = v <;> simp [degreeAt, h]
  | .add a b, rho => by
      have ha := length_coeffAt_le_degreeAt v a rho
      have hb := length_coeffAt_le_degreeAt v b rho
      show (YMGap.Constructive.QPoly.padd
          (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho)
          (YMGap.Continuum.RingNormaliserStream.coeffAt v b rho)).length ≤
        max (degreeAt v a) (degreeAt v b) + 1
      rw [YMGap.Continuum.RingNormaliserStream.length_padd]
      omega
  | .mul a b, rho => by
      have ha := length_coeffAt_le_degreeAt v a rho
      have hb := length_coeffAt_le_degreeAt v b rho
      have hm := YMGap.Continuum.RingNormaliserStream.length_pmul_le_of_pos
        (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho)
        (YMGap.Continuum.RingNormaliserStream.coeffAt v b rho)
        (YMGap.Continuum.RingNormaliserStream.length_coeffAt_pos v a rho)
        (YMGap.Continuum.RingNormaliserStream.length_coeffAt_pos v b rho)
      show (YMGap.Constructive.QPoly.pmul
          (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho)
          (YMGap.Continuum.RingNormaliserStream.coeffAt v b rho)).length ≤
        degreeAt v a + degreeAt v b + 1
      omega
  | .neg a, rho => by
      have ha := length_coeffAt_le_degreeAt v a rho
      show (YMGap.Constructive.QPoly.pneg
          (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho)).length ≤
        degreeAt v a + 1
      rw [YMGap.Continuum.RingNormaliserStream.length_pneg]
      exact ha
  | .pow a n, rho => by
      have ha := length_coeffAt_le_degreeAt v a rho
      have hp := YMGap.Continuum.RingNormaliserStream.length_ppow_le
        (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho) n
      show (YMGap.Continuum.RingNormaliserStream.ppow
          (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho) n).length ≤
        n * degreeAt v a + n + 1
      have hmul : n *
          (YMGap.Continuum.RingNormaliserStream.coeffAt v a rho).length ≤
          n * degreeAt v a + n := by
        have h := Nat.mul_le_mul_left n ha
        rw [Nat.mul_add, Nat.mul_one] at h
        exact h
      omega

private theorem poly_identity_of_grid3 (F : PE) (d0 d1 d2 : Nat)
    (hdeg0 : degreeAt 0 F ≤ d0)
    (hdeg1 : degreeAt 1 F ≤ d1)
    (hdeg2 : degreeAt 3 F ≤ d2)
    (hgrid : ∀ i j l, i ≤ d0 → j ≤ d1 → l ≤ d2 →
      RingNormaliser.eval (env3 (Q'.ofNat i) (Q'.ofNat j) (Q'.ofNat l)) F ≈ 0) :
    ∀ x y z, RingNormaliser.eval (env3 x y z) F ≈ 0 := by
  have step0 : ∀ j l, j ≤ d1 → l ≤ d2 → ∀ x,
      RingNormaliser.eval (env3 x (Q'.ofNat j) (Q'.ofNat l)) F ≈ 0 := by
    intro j l hj hl
    have heval : ∀ x,
        RingNormaliser.eval (env3 x (Q'.ofNat j) (Q'.ofNat l)) F ≈
          YMGap.Constructive.QPoly.eval
            (YMGap.Continuum.RingNormaliserStream.coeffAt 0 F
              (env3 0 (Q'.ofNat j) (Q'.ofNat l))) x := by
      intro x
      have h := YMGap.Continuum.RingNormaliserStream.eval_coeffAt 0 F
        (env3 0 (Q'.ofNat j) (Q'.ofNat l)) x
      rw [update0_env3] at h
      exact h
    have hlen :
        (YMGap.Continuum.RingNormaliserStream.coeffAt 0 F
          (env3 0 (Q'.ofNat j) (Q'.ofNat l))).length ≤
        (YMGap.Continuum.RingNormaliserStream.gridList (d0 + 1)).length := by
      have h := length_coeffAt_le_degreeAt 0 F
        (env3 0 (Q'.ofNat j) (Q'.ofNat l))
      rw [YMGap.Continuum.RingNormaliserStream.length_gridList]
      omega
    have hroots : ∀ q ∈ YMGap.Continuum.RingNormaliserStream.gridList (d0 + 1),
        YMGap.Constructive.QPoly.eval
          (YMGap.Continuum.RingNormaliserStream.coeffAt 0 F
            (env3 0 (Q'.ofNat j) (Q'.ofNat l))) q ≈ 0 := by
      intro q hq
      rcases YMGap.Continuum.RingNormaliserStream.mem_gridList (d0 + 1) q hq with
        ⟨i, hi, rfl⟩
      exact Q'.eqv_trans _
        (RingNormaliser.eval
          (env3 (Q'.ofNat i) (Q'.ofNat j) (Q'.ofNat l)) F) _
        (Q'.eqv_symm (heval (Q'.ofNat i)))
        (hgrid i j l (by omega) hj hl)
    have hz := YMGap.Continuum.RingNormaliserStream.roots_zero
      (YMGap.Continuum.RingNormaliserStream.gridList (d0 + 1))
      (YMGap.Continuum.RingNormaliserStream.qdistinct_gridList (d0 + 1))
      (YMGap.Continuum.RingNormaliserStream.coeffAt 0 F
        (env3 0 (Q'.ofNat j) (Q'.ofNat l))) hlen hroots
    intro x
    exact Q'.eqv_trans _
      (YMGap.Constructive.QPoly.eval
        (YMGap.Continuum.RingNormaliserStream.coeffAt 0 F
          (env3 0 (Q'.ofNat j) (Q'.ofNat l))) x) _ (heval x) (hz x)
  have step1 : ∀ l, l ≤ d2 → ∀ x y,
      RingNormaliser.eval (env3 x y (Q'.ofNat l)) F ≈ 0 := by
    intro l hl x
    have heval : ∀ y,
        RingNormaliser.eval (env3 x y (Q'.ofNat l)) F ≈
          YMGap.Constructive.QPoly.eval
            (YMGap.Continuum.RingNormaliserStream.coeffAt 1 F
              (env3 x 0 (Q'.ofNat l))) y := by
      intro y
      have h := YMGap.Continuum.RingNormaliserStream.eval_coeffAt 1 F
        (env3 x 0 (Q'.ofNat l)) y
      rw [update1_env3] at h
      exact h
    have hlen :
        (YMGap.Continuum.RingNormaliserStream.coeffAt 1 F
          (env3 x 0 (Q'.ofNat l))).length ≤
        (YMGap.Continuum.RingNormaliserStream.gridList (d1 + 1)).length := by
      have h := length_coeffAt_le_degreeAt 1 F
        (env3 x 0 (Q'.ofNat l))
      rw [YMGap.Continuum.RingNormaliserStream.length_gridList]
      omega
    have hroots : ∀ q ∈ YMGap.Continuum.RingNormaliserStream.gridList (d1 + 1),
        YMGap.Constructive.QPoly.eval
          (YMGap.Continuum.RingNormaliserStream.coeffAt 1 F
            (env3 x 0 (Q'.ofNat l))) q ≈ 0 := by
      intro q hq
      rcases YMGap.Continuum.RingNormaliserStream.mem_gridList (d1 + 1) q hq with
        ⟨j, hj, rfl⟩
      exact Q'.eqv_trans _
        (RingNormaliser.eval (env3 x (Q'.ofNat j) (Q'.ofNat l)) F) _
        (Q'.eqv_symm (heval (Q'.ofNat j)))
        (step0 j l (by omega) hl x)
    have hz := YMGap.Continuum.RingNormaliserStream.roots_zero
      (YMGap.Continuum.RingNormaliserStream.gridList (d1 + 1))
      (YMGap.Continuum.RingNormaliserStream.qdistinct_gridList (d1 + 1))
      (YMGap.Continuum.RingNormaliserStream.coeffAt 1 F
        (env3 x 0 (Q'.ofNat l))) hlen hroots
    intro y
    exact Q'.eqv_trans _
      (YMGap.Constructive.QPoly.eval
        (YMGap.Continuum.RingNormaliserStream.coeffAt 1 F
          (env3 x 0 (Q'.ofNat l))) y) _ (heval y) (hz y)
  intro x y
  have heval : ∀ z, RingNormaliser.eval (env3 x y z) F ≈
      YMGap.Constructive.QPoly.eval
        (YMGap.Continuum.RingNormaliserStream.coeffAt 3 F (env3 x y 0)) z := by
    intro z
    have h := YMGap.Continuum.RingNormaliserStream.eval_coeffAt 3 F
      (env3 x y 0) z
    rw [update2_env3] at h
    exact h
  have hlen :
      (YMGap.Continuum.RingNormaliserStream.coeffAt 3 F
        (env3 x y 0)).length ≤
      (YMGap.Continuum.RingNormaliserStream.gridList (d2 + 1)).length := by
    have h := length_coeffAt_le_degreeAt 3 F
      (env3 x y 0)
    rw [YMGap.Continuum.RingNormaliserStream.length_gridList]
    omega
  have hroots : ∀ q ∈ YMGap.Continuum.RingNormaliserStream.gridList (d2 + 1),
      YMGap.Constructive.QPoly.eval
        (YMGap.Continuum.RingNormaliserStream.coeffAt 3 F (env3 x y 0)) q ≈ 0 := by
    intro q hq
    rcases YMGap.Continuum.RingNormaliserStream.mem_gridList (d2 + 1) q hq with
      ⟨l, hl, rfl⟩
    exact Q'.eqv_trans _
      (RingNormaliser.eval (env3 x y (Q'.ofNat l)) F) _
      (Q'.eqv_symm (heval (Q'.ofNat l))) (step1 l (by omega) x y)
  have hz := YMGap.Continuum.RingNormaliserStream.roots_zero
    (YMGap.Continuum.RingNormaliserStream.gridList (d2 + 1))
    (YMGap.Continuum.RingNormaliserStream.qdistinct_gridList (d2 + 1))
    (YMGap.Continuum.RingNormaliserStream.coeffAt 3 F (env3 x y 0))
    hlen hroots
  intro z
  exact Q'.eqv_trans _
    (YMGap.Constructive.QPoly.eval
      (YMGap.Continuum.RingNormaliserStream.coeffAt 3 F (env3 x y 0)) z) _
    (heval z) (hz z)

private def gridCheck3B (F : PE) (d0 d1 d2 : Nat) : Bool :=
  (List.range (d0 + 1)).all (fun i =>
    (List.range (d1 + 1)).all (fun j =>
      (List.range (d2 + 1)).all (fun l =>
        decide (RingNormaliser.eval
          (env3 (Q'.ofNat i) (Q'.ofNat j) (Q'.ofNat l)) F ≈ 0))))

private theorem grid3_of_check (F : PE) (d0 d1 d2 : Nat)
    (h : gridCheck3B F d0 d1 d2 = true) :
    ∀ i j l, i ≤ d0 → j ≤ d1 → l ≤ d2 →
      RingNormaliser.eval
        (env3 (Q'.ofNat i) (Q'.ofNat j) (Q'.ofNat l)) F ≈ 0 := by
  intro i j l hi hj hl
  have hi' : i ∈ List.range (d0 + 1) := List.mem_range.mpr (by omega)
  have hj' : j ∈ List.range (d1 + 1) := List.mem_range.mpr (by omega)
  have hl' : l ∈ List.range (d2 + 1) := List.mem_range.mpr (by omega)
  have h1 := (List.all_eq_true.mp h) i hi'
  have h2 := (List.all_eq_true.mp h1) j hj'
  have h3 := (List.all_eq_true.mp h2) l hl'
  exact of_decide_eq_true h3

private theorem fiveChannel_zero_0 (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (rowResidualExpr 0) ≈ 0 := by
  exact poly_identity_of_grid3 (rowResidualExpr 0) 12 4 4
    (by decide) (by decide) (by decide)
    (grid3_of_check _ 12 4 4 (by decide)) U I L

private theorem fiveChannel_zero_1 (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (rowResidualExpr 1) ≈ 0 := by
  exact poly_identity_of_grid3 (rowResidualExpr 1) 12 4 4
    (by decide) (by decide) (by decide)
    (grid3_of_check _ 12 4 4 (by decide)) U I L

private theorem fiveChannel_zero_2 (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (rowResidualExpr 2) ≈ 0 := by
  exact poly_identity_of_grid3 (rowResidualExpr 2) 12 4 4
    (by decide) (by decide) (by decide)
    (grid3_of_check _ 12 4 4 (by decide)) U I L

private theorem fiveChannel_zero_3 (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (rowResidualExpr 3) ≈ 0 := by
  exact poly_identity_of_grid3 (rowResidualExpr 3) 12 4 4
    (by decide) (by decide) (by decide)
    (grid3_of_check _ 12 4 4 (by decide)) U I L

private theorem fiveChannel_zero_4 (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (rowResidualExpr 4) ≈ 0 := by
  exact poly_identity_of_grid3 (rowResidualExpr 4) 12 4 4
    (by decide) (by decide) (by decide)
    (grid3_of_check _ 12 4 4 (by decide)) U I L

private theorem fallExpr_eval (rho : Nat → Q') (X : PE) : ∀ r,
    RingNormaliser.eval rho (fallExpr X r) ≈
      qFall (RingNormaliser.eval rho X) r
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      change RingNormaliser.eval rho (fallExpr X r) *
          (RingNormaliser.eval rho X + -Q'.ofInt (Int.ofNat r)) ≈
        qFall (RingNormaliser.eval rho X) r *
          qSub (RingNormaliser.eval rho X) (Q'.ofNat r)
      exact mul_eqv_congr (fallExpr_eval rho X r) (Q'.eqv_refl _)

private theorem rowTermExpr_eval (rho : Nat → Q') (k r : Nat)
    (M N X Y : PE) :
    RingNormaliser.eval rho (rowTermExpr k r M N X Y) ≈
      hahnRowTermSymbolic k r (RingNormaliser.eval rho M)
        (RingNormaliser.eval rho N) (RingNormaliser.eval rho X)
        (RingNormaliser.eval rho Y) := by
  unfold rowTermExpr hahnRowTermSymbolic peMul peConst peSub peNeg
  exact mul_eqv_congr
    (mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr (Q'.eqv_refl _) (fallExpr_eval rho X (k - r)))
        (fallExpr_eval rho (.add M (.neg X)) r))
      (fallExpr_eval rho Y r))
    (fallExpr_eval rho (.add N (.neg Y)) (k - r))

private theorem rowSumExpr_eval (rho : Nat → Q') (k : Nat)
    (M N X Y : PE) : ∀ R,
    RingNormaliser.eval rho (rowSumExpr k M N X Y R) ≈
      finSum (fun r => hahnRowTermSymbolic k r
        (RingNormaliser.eval rho M) (RingNormaliser.eval rho N)
        (RingNormaliser.eval rho X) (RingNormaliser.eval rho Y)) R
  | 0 => Q'.eqv_of_eq RingNormaliser.ofInt_zero
  | R + 1 => by
      change RingNormaliser.eval rho (rowSumExpr k M N X Y R) +
          RingNormaliser.eval rho (rowTermExpr k R M N X Y) ≈
        finSum (fun r => hahnRowTermSymbolic k r
          (RingNormaliser.eval rho M) (RingNormaliser.eval rho N)
          (RingNormaliser.eval rho X) (RingNormaliser.eval rho Y)) R +
          hahnRowTermSymbolic k R (RingNormaliser.eval rho M)
            (RingNormaliser.eval rho N) (RingNormaliser.eval rho X)
            (RingNormaliser.eval rho Y)
      exact Q'.add_eqv_congr'
        (rowSumExpr_eval rho k M N X Y R)
        (rowTermExpr_eval rho k R M N X Y)

private theorem rowExpr_eval (rho : Nat → Q') (k : Nat) (M N X Y : PE) :
    RingNormaliser.eval rho (rowExpr k M N X Y) ≈
      hahnRowSymbolic k (RingNormaliser.eval rho M)
        (RingNormaliser.eval rho N) (RingNormaliser.eval rho X)
        (RingNormaliser.eval rho Y) := by
  exact rowSumExpr_eval rho k M N X Y (k + 1)

private theorem leftPayloadExpr_eval (U I L : Q') (j : Nat) :
    RingNormaliser.eval (env3 U I L)
        (leftPayloadExpr (peConst (Int.ofNat j))) ≈
      threeLeftPayloadQ U I (Q'.ofNat j) L := by
  have h := mul_eqv_congr
    (rowExpr_eval (env3 U I L) 2 pN (peConst 4) pI
      (peConst (Int.ofNat j)))
    (rowExpr_eval (env3 U I L) 2 pN pN
      (peSub (peAdd pI (peConst (Int.ofNat j))) (peConst 2)) pL)
  simpa only [leftPayloadExpr, threeLeftPayloadQ, pN, pU, pI, pL,
    peAdd, peSub, peNeg, peConst, env3, RingNormaliser.eval] using h

private theorem rightPayloadExpr_eval (p j : Nat) (U I L : Q') :
    RingNormaliser.eval (env3 U I L)
        (rightPayloadExpr p (peConst (Int.ofNat j))) ≈
      threeRightPayloadQ p U I (Q'.ofNat j) L := by
  have h := mul_eqv_congr
    (rowExpr_eval (env3 U I L) p (peConst 4) pN
      (peConst (Int.ofNat j)) pL)
    (rowExpr_eval (env3 U I L) (4 - p) pN
      (peSub (peAdd pN (peConst 4)) (peConst (Int.ofNat (2 * p)))) pI
      (peSub (peAdd (peConst (Int.ofNat j)) pL)
        (peConst (Int.ofNat p))))
  simpa only [rightPayloadExpr, threeRightPayloadQ, pN, pU, pI, pL,
    peAdd, peSub, peNeg, peConst, env3, RingNormaliser.eval] using h

private theorem rowScaleExpr_eval (U I L : Q') :
    RingNormaliser.eval (env3 U I L) rowScaleExpr ≈ threeRowScaleQ U := by
  exact Q'.eqv_refl _

private theorem coeffExpr_eval (p : Nat) (hp : p ≤ 4) (U I L : Q') :
    RingNormaliser.eval (env3 U I L) (coeffExpr p) ≈ threeRowCoeffQ p U := by
  have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact Q'.eqv_refl _
  · exact Q'.eqv_refl _
  · exact Q'.eqv_refl _
  · exact Q'.eqv_refl _
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem payload_identity_of_zero (j : Nat) (U I L : Q')
    (hzero : RingNormaliser.eval (env3 U I L) (rowResidualExpr j) ≈ 0) :
    threeRowScaleQ U * threeLeftPayloadQ U I (Q'.ofNat j) L ≈
      threeRowCoeffQ 0 U * threeRightPayloadQ 0 U I (Q'.ofNat j) L +
      threeRowCoeffQ 1 U * threeRightPayloadQ 1 U I (Q'.ofNat j) L +
      threeRowCoeffQ 2 U * threeRightPayloadQ 2 U I (Q'.ofNat j) L +
      threeRowCoeffQ 3 U * threeRightPayloadQ 3 U I (Q'.ofNat j) L +
      threeRowCoeffQ 4 U * threeRightPayloadQ 4 U I (Q'.ofNat j) L := by
  have hsub :
      RingNormaliser.eval (env3 U I L)
          (rowLHSExpr (peConst (Int.ofNat j))) +
        -RingNormaliser.eval (env3 U I L)
          (rowRHSExpr (peConst (Int.ofNat j))) ≈ 0 := by
    simpa only [rowResidualExpr, peAdd, peNeg, RingNormaliser.eval] using hzero
  have heq := YMGap.Constructive.QPoly.q_eqv_of_sub_zero hsub
  have hL : RingNormaliser.eval (env3 U I L)
        (rowLHSExpr (peConst (Int.ofNat j))) ≈
      threeRowScaleQ U * threeLeftPayloadQ U I (Q'.ofNat j) L := by
    exact mul_eqv_congr (rowScaleExpr_eval U I L)
      (leftPayloadExpr_eval U I L j)
  have h0 := mul_eqv_congr (coeffExpr_eval 0 (by decide) U I L)
    (rightPayloadExpr_eval 0 j U I L)
  have h1 := mul_eqv_congr (coeffExpr_eval 1 (by decide) U I L)
    (rightPayloadExpr_eval 1 j U I L)
  have h2 := mul_eqv_congr (coeffExpr_eval 2 (by decide) U I L)
    (rightPayloadExpr_eval 2 j U I L)
  have h3 := mul_eqv_congr (coeffExpr_eval 3 (by decide) U I L)
    (rightPayloadExpr_eval 3 j U I L)
  have h4 := mul_eqv_congr (coeffExpr_eval 4 (by decide) U I L)
    (rightPayloadExpr_eval 4 j U I L)
  have hR : RingNormaliser.eval (env3 U I L)
        (rowRHSExpr (peConst (Int.ofNat j))) ≈
      threeRowCoeffQ 0 U * threeRightPayloadQ 0 U I (Q'.ofNat j) L +
      threeRowCoeffQ 1 U * threeRightPayloadQ 1 U I (Q'.ofNat j) L +
      threeRowCoeffQ 2 U * threeRightPayloadQ 2 U I (Q'.ofNat j) L +
      threeRowCoeffQ 3 U * threeRightPayloadQ 3 U I (Q'.ofNat j) L +
      threeRowCoeffQ 4 U * threeRightPayloadQ 4 U I (Q'.ofNat j) L := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' h0 h1) h2) h3) h4
  exact Q'.eqv_trans _
    (RingNormaliser.eval (env3 U I L)
      (rowLHSExpr (peConst (Int.ofNat j)))) _
    (Q'.eqv_symm hL) (Q'.eqv_trans _ _ _ heq hR)

/-- Exact denominator-free five-channel polynomial recoupling row. -/
theorem three_payload_scaled_recoupling (U I L : Q') (j : Nat) (hj : j ≤ 4) :
    threeRowScaleQ U * threeLeftPayloadQ U I (Q'.ofNat j) L ≈
      threeRowCoeffQ 0 U * threeRightPayloadQ 0 U I (Q'.ofNat j) L +
      threeRowCoeffQ 1 U * threeRightPayloadQ 1 U I (Q'.ofNat j) L +
      threeRowCoeffQ 2 U * threeRightPayloadQ 2 U I (Q'.ofNat j) L +
      threeRowCoeffQ 3 U * threeRightPayloadQ 3 U I (Q'.ofNat j) L +
      threeRowCoeffQ 4 U * threeRightPayloadQ 4 U I (Q'.ofNat j) L := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact payload_identity_of_zero 0 U I L (fiveChannel_zero_0 U I L)
  · exact payload_identity_of_zero 1 U I L (fiveChannel_zero_1 U I L)
  · exact payload_identity_of_zero 2 U I L (fiveChannel_zero_2 U I L)
  · exact payload_identity_of_zero 3 U I L (fiveChannel_zero_3 U I L)
  · exact payload_identity_of_zero 4 U I L (fiveChannel_zero_4 U I L)

/-! ## Physical five-channel block -/

def threeRightChannelAt (u p : Nat) (hp : p ≤ 4) :
    FixedRightCGChannel (threeN u) 4 (threeN u) (threeD u) where
  p := p
  p_le := hp
  r := 4 - p
  r_le := by unfold threeN; omega
  degree_eq := by unfold threeN threeD; omega

theorem three_rightAt_intermediate (u p : Nat) (hp : p ≤ 4) :
    (threeRightChannelAt u p hp).intermediate = threeN u + 4 - 2 * p := by
  change 4 + threeN u - 2 * p = threeN u + 4 - 2 * p
  omega

private theorem threeN_cast (u : Nat) :
    Q'.ofNat (threeN u) = Q'.ofNat u + 8 := by
  unfold threeN
  simpa using ofNat_add_eq u 8

private theorem mul_eqv_zero_of_left {a b : Q'} (ha : a ≈ 0) : a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv _)

private theorem three_left_payload_eq_symbolic_core (u i j l : Nat)
    (hi : i ≤ threeN u) (hj : j ≤ 4) (hl : l ≤ threeN u)
    (hlo : 2 ≤ i + j) (hhi : i + j - 2 ≤ threeN u) :
    leftFactorialPayload (threeLeftChannel u) i j l ≈
      threeLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hinner := transvectFactorialCoeff_symbolic
    (threeN u) 4 2 i j hi hj
  have houter := transvectFactorialCoeff_symbolic
    (threeN u) (threeN u) 2 (i + j - 2) l hhi hl
  have ht : i + j - i = j := by omega
  unfold leftFactorialPayload threeLeftChannel
  simp only [hahnEntry, FixedLeftCGChannel.intermediate]
  rw [ht]
  refine Q'.eqv_trans _
    (hahnRowSymbolic 2 (Q'.ofNat (threeN u)) 4
        (Q'.ofNat i) (Q'.ofNat j) *
      hahnRowSymbolic 2 (Q'.ofNat (threeN u)) (Q'.ofNat (threeN u))
        (Q'.ofNat (i + j - 2)) (Q'.ofNat l)) _
    (mul_eqv_congr hinner houter) ?_
  unfold threeLeftPayloadQ
  rw [← threeN_cast u, ← ofNat_add_eq i j, ofNat_sub_eq (i + j) 2 hlo]
  exact Q'.eqv_refl _

theorem three_left_payload_eq_symbolic_all (u i j l : Nat)
    (hi : i ≤ threeN u) (hj : j ≤ 4) (hl : l ≤ threeN u) :
    leftFactorialPayload (threeLeftChannel u) i j l ≈
      threeLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  by_cases hlo : 2 ≤ i + j
  · by_cases hhi : i + j - 2 ≤ threeN u
    · exact three_left_payload_eq_symbolic_core u i j l hi hj hl hlo hhi
    · have hz := hahnRowSymbolic_zero_above (threeN u) 4 2 i j hi hj
          (by omega)
      have hinner := transvectFactorialCoeff_symbolic
        (threeN u) 4 2 i j hi hj
      have hphysical : leftFactorialPayload (threeLeftChannel u) i j l ≈ 0 := by
        unfold leftFactorialPayload threeLeftChannel
        simp only [hahnEntry, FixedLeftCGChannel.intermediate,
          show i + j - i = j by omega]
        exact mul_eqv_zero_of_left (Q'.eqv_trans _ _ _ hinner hz)
      refine Q'.eqv_trans _ 0 _ hphysical ?_
      unfold threeLeftPayloadQ
      rw [← threeN_cast u]
      exact Q'.eqv_symm (mul_eqv_zero_of_left hz)
  · have hz := hahnRowSymbolic_zero_below (threeN u) 4 2 i j hi hj
        (by omega)
    have hinner := transvectFactorialCoeff_symbolic
      (threeN u) 4 2 i j hi hj
    have hphysical : leftFactorialPayload (threeLeftChannel u) i j l ≈ 0 := by
      unfold leftFactorialPayload threeLeftChannel
      simp only [hahnEntry, FixedLeftCGChannel.intermediate,
        show i + j - i = j by omega]
      exact mul_eqv_zero_of_left (Q'.eqv_trans _ _ _ hinner hz)
    refine Q'.eqv_trans _ 0 _ hphysical ?_
    unfold threeLeftPayloadQ
    rw [← threeN_cast u]
    exact Q'.eqv_symm (mul_eqv_zero_of_left hz)

private theorem three_right_payload_eq_symbolic_core (u p : Nat) (hp : p ≤ 4)
    (i j l : Nat) (hi : i ≤ threeN u) (hj : j ≤ 4)
    (hl : l ≤ threeN u) (hlo : p ≤ j + l)
    (hhi : j + l - p ≤ threeN u + 4 - 2 * p) :
    rightFactorialPayload (threeRightChannelAt u p hp) i j l ≈
      threeRightPayloadQ p (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  have hinner := transvectFactorialCoeff_symbolic 4 (threeN u) p j l hj hl
  have houter := transvectFactorialCoeff_symbolic
    (threeN u) (threeN u + 4 - 2 * p) (4 - p) i (j + l - p) hi hhi
  have ht : j + l - j = l := by omega
  have h2p : 2 * p ≤ threeN u + 4 := by unfold threeN; omega
  have hm : 4 + threeN u - 2 * p = threeN u + 4 - 2 * p := by omega
  unfold rightFactorialPayload threeRightChannelAt
  simp only [hahnEntry, FixedRightCGChannel.intermediate]
  rw [ht, hm]
  refine Q'.eqv_trans _
    (hahnRowSymbolic p 4 (Q'.ofNat (threeN u))
        (Q'.ofNat j) (Q'.ofNat l) *
      hahnRowSymbolic (4 - p) (Q'.ofNat (threeN u))
        (Q'.ofNat (threeN u + 4 - 2 * p))
        (Q'.ofNat i) (Q'.ofNat (j + l - p))) _
    (mul_eqv_congr hinner houter) ?_
  unfold threeRightPayloadQ
  rw [← threeN_cast u,
    ofNat_sub_eq (threeN u + 4) (2 * p) h2p,
    ofNat_add_eq (threeN u) 4,
    ← ofNat_add_eq j l, ofNat_sub_eq (j + l) p hlo]
  exact Q'.eqv_refl _

theorem three_right_payload_eq_symbolic_all (u p : Nat) (hp : p ≤ 4)
    (i j l : Nat) (hi : i ≤ threeN u) (hj : j ≤ 4)
    (hl : l ≤ threeN u) :
    rightFactorialPayload (threeRightChannelAt u p hp) i j l ≈
      threeRightPayloadQ p (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l) := by
  by_cases hlo : p ≤ j + l
  · by_cases hhi : j + l - p ≤ threeN u + 4 - 2 * p
    · exact three_right_payload_eq_symbolic_core u p hp i j l hi hj hl hlo hhi
    · have hz := hahnRowSymbolic_zero_above 4 (threeN u) p j l hj hl
          (by omega)
      have hinner := transvectFactorialCoeff_symbolic 4 (threeN u) p j l hj hl
      have hphysical :
          rightFactorialPayload (threeRightChannelAt u p hp) i j l ≈ 0 := by
        unfold rightFactorialPayload threeRightChannelAt
        simp only [hahnEntry, FixedRightCGChannel.intermediate,
          show j + l - j = l by omega]
        exact mul_eqv_zero_of_left (Q'.eqv_trans _ _ _ hinner hz)
      refine Q'.eqv_trans _ 0 _ hphysical ?_
      unfold threeRightPayloadQ
      rw [← threeN_cast u]
      exact Q'.eqv_symm (mul_eqv_zero_of_left hz)
  · have hz := hahnRowSymbolic_zero_below 4 (threeN u) p j l hj hl
        (by omega)
    have hinner := transvectFactorialCoeff_symbolic 4 (threeN u) p j l hj hl
    have hphysical :
        rightFactorialPayload (threeRightChannelAt u p hp) i j l ≈ 0 := by
      unfold rightFactorialPayload threeRightChannelAt
      simp only [hahnEntry, FixedRightCGChannel.intermediate,
        show j + l - j = l by omega]
      exact mul_eqv_zero_of_left (Q'.eqv_trans _ _ _ hinner hz)
    refine Q'.eqv_trans _ 0 _ hphysical ?_
    unfold threeRightPayloadQ
    rw [← threeN_cast u]
    exact Q'.eqv_symm (mul_eqv_zero_of_left hz)

theorem three_physical_payload_scaled_recoupling (u i j l : Nat)
    (hi : i ≤ threeN u) (hj : j ≤ 4) (hl : l ≤ threeN u) :
    threeRowScaleQ (Q'.ofNat u) *
        leftFactorialPayload (threeLeftChannel u) i j l ≈
      threeRowCoeffQ 0 (Q'.ofNat u) *
          rightFactorialPayload (threeRightChannelAt u 0 (by decide)) i j l +
      threeRowCoeffQ 1 (Q'.ofNat u) *
          rightFactorialPayload (threeRightChannelAt u 1 (by decide)) i j l +
      threeRowCoeffQ 2 (Q'.ofNat u) *
          rightFactorialPayload (threeRightChannelAt u 2 (by decide)) i j l +
      threeRowCoeffQ 3 (Q'.ofNat u) *
          rightFactorialPayload (threeRightChannelAt u 3 (by decide)) i j l +
      threeRowCoeffQ 4 (Q'.ofNat u) *
          rightFactorialPayload (threeRightChannelAt u 4 (by decide)) i j l := by
  have hL := three_left_payload_eq_symbolic_all u i j l hi hj hl
  have h0 := three_right_payload_eq_symbolic_all u 0 (by decide) i j l hi hj hl
  have h1 := three_right_payload_eq_symbolic_all u 1 (by decide) i j l hi hj hl
  have h2 := three_right_payload_eq_symbolic_all u 2 (by decide) i j l hi hj hl
  have h3 := three_right_payload_eq_symbolic_all u 3 (by decide) i j l hi hj hl
  have h4 := three_right_payload_eq_symbolic_all u 4 (by decide) i j l hi hj hl
  have hp := three_payload_scaled_recoupling (Q'.ofNat u)
    (Q'.ofNat i) (Q'.ofNat l) j hj
  refine Q'.eqv_trans _
    (threeRowScaleQ (Q'.ofNat u) *
      threeLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
        (Q'.ofNat l)) _ (Q'.mul_eqv_congr_left _ _ _ hL) ?_
  refine Q'.eqv_trans _ _ _ hp ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h0))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h1)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h2)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h3)))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h4))

private theorem three_left_payload_zero_below (u i j l : Nat)
    (hi : i ≤ threeN u) (hj : j ≤ 4) (hl : l ≤ threeN u)
    (hbelow : i + j < 2) :
    leftFactorialPayload (threeLeftChannel u) i j l ≈ 0 := by
  have hbridge := three_left_payload_eq_symbolic_all u i j l hi hj hl
  have hz := hahnRowSymbolic_zero_below (threeN u) 4 2 i j hi hj hbelow
  refine Q'.eqv_trans _
    (threeLeftPayloadQ (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
      (Q'.ofNat l)) _ hbridge ?_
  unfold threeLeftPayloadQ
  rw [← threeN_cast u]
  exact mul_eqv_zero_of_left hz

private theorem three_right_payload_zero_below (u p : Nat) (hp : p ≤ 4)
    (i j l : Nat) (hi : i ≤ threeN u) (hj : j ≤ 4)
    (hl : l ≤ threeN u) (hbelow : j + l < p) :
    rightFactorialPayload (threeRightChannelAt u p hp) i j l ≈ 0 := by
  have hbridge := three_right_payload_eq_symbolic_all u p hp i j l hi hj hl
  have hz := hahnRowSymbolic_zero_below 4 (threeN u) p j l hj hl hbelow
  refine Q'.eqv_trans _
    (threeRightPayloadQ p (Q'.ofNat u) (Q'.ofNat i) (Q'.ofNat j)
      (Q'.ofNat l)) _ hbridge ?_
  unfold threeRightPayloadQ
  rw [← threeN_cast u]
  exact mul_eqv_zero_of_left hz

private theorem three_guardedLeft_eq_shellPayload (u i j l s : Nat)
    (hi : i ≤ threeN u) (hj : j ≤ 4) (hl : l ≤ threeN u) :
    guardedLeftFactorialCoefficient (threeLeftChannel u) i j l s ≈
      if s + 4 = i + j + l then
        leftFactorialPayload (threeLeftChannel u) i j l else 0 := by
  unfold guardedLeftFactorialCoefficient leftFactorialPayload
  simp only [threeLeftChannel, FixedLeftCGChannel.intermediate]
  by_cases hinner : 2 ≤ i + j
  · rw [if_pos hinner]
    by_cases hs : s + 4 = i + j + l
    · rw [if_pos hs, if_pos]
      · exact Q'.eqv_refl _
      · omega
    · rw [if_neg hs, if_neg]
      · exact Q'.mul_zero_eqv _
      · intro h
        apply hs
        omega
  · rw [if_neg hinner]
    have hz := three_left_payload_zero_below u i j l hi hj hl (by omega)
    by_cases hs : s + 4 = i + j + l
    · rw [if_pos hs]
      exact Q'.eqv_symm hz
    · rw [if_neg hs]
      exact Q'.eqv_refl 0

private theorem three_guardedRight_eq_shellPayload (u p : Nat) (hp : p ≤ 4)
    (i j l s : Nat) (hi : i ≤ threeN u) (hj : j ≤ 4)
    (hl : l ≤ threeN u) :
    guardedRightFactorialCoefficient (threeRightChannelAt u p hp) i j l s ≈
      if s + 4 = i + j + l then
        rightFactorialPayload (threeRightChannelAt u p hp) i j l else 0 := by
  unfold guardedRightFactorialCoefficient rightFactorialPayload
  simp only [threeRightChannelAt, FixedRightCGChannel.intermediate]
  by_cases hinner : p ≤ j + l
  · rw [if_pos hinner]
    by_cases hs : s + 4 = i + j + l
    · rw [if_pos hs, if_pos]
      · exact Q'.eqv_refl _
      · omega
    · rw [if_neg hs, if_neg]
      · exact Q'.mul_zero_eqv _
      · intro h
        apply hs
        omega
  · rw [if_neg hinner]
    have hz := three_right_payload_zero_below u p hp i j l hi hj hl (by omega)
    by_cases hs : s + 4 = i + j + l
    · rw [if_pos hs]
      exact Q'.eqv_symm hz
    · rw [if_neg hs]
      exact Q'.eqv_refl 0

private def threeRightMapAt (u p : Nat) (hp : p ≤ 4) :=
  triRight (threeN u) 4 (threeN u) (threeD u)
    (threeRightChannelAt u p hp).intermediate

private def threeRightCombination (u : Nat) (x y z : BForm) : BForm :=
  addForm
    (addForm
      (addForm
        (addForm
          (scaleForm (threeRowCoeffQ 0 (Q'.ofNat u))
            (threeRightMapAt u 0 (by decide) x y z))
          (scaleForm (threeRowCoeffQ 1 (Q'.ofNat u))
            (threeRightMapAt u 1 (by decide) x y z)))
        (scaleForm (threeRowCoeffQ 2 (Q'.ofNat u))
          (threeRightMapAt u 2 (by decide) x y z)))
      (scaleForm (threeRowCoeffQ 3 (Q'.ofNat u))
        (threeRightMapAt u 3 (by decide) x y z)))
    (scaleForm (threeRowCoeffQ 4 (Q'.ofNat u))
      (threeRightMapAt u 4 (by decide) x y z))

/-- The denominator-free polynomial row is the physical five-channel
transvectant recoupling on the complete monomial box. -/
theorem three_triMap_scaled_recoupling (u : Nat) :
    TriMapEqv (threeN u) 4 (threeN u) (threeD u)
      (fun x y z => scaleForm (threeRowScaleQ (Q'.ofNat u))
        (triLeft (threeN u) 4 (threeN u) (threeD u) (threeN u) x y z))
      (threeRightCombination u) := by
  intro i hi j hj l hl s hsout
  have hi' : i ≤ threeN u := by omega
  have hj' : j ≤ 4 := by omega
  have hl' : l ≤ threeN u := by omega
  have hL := Q'.eqv_trans _ _ _
    (triLeft_monomial_eq_guardedHahn (threeLeftChannel u) i j l s)
    (guardedLeftHahnCoefficient_eq_factorial (threeLeftChannel u) i j l s)
  have h0 := Q'.eqv_trans _ _ _
    (triRight_monomial_eq_guardedHahn
      (threeRightChannelAt u 0 (by decide)) i j l s)
    (guardedRightHahnCoefficient_eq_factorial
      (threeRightChannelAt u 0 (by decide)) i j l s)
  have h1 := Q'.eqv_trans _ _ _
    (triRight_monomial_eq_guardedHahn
      (threeRightChannelAt u 1 (by decide)) i j l s)
    (guardedRightHahnCoefficient_eq_factorial
      (threeRightChannelAt u 1 (by decide)) i j l s)
  have h2 := Q'.eqv_trans _ _ _
    (triRight_monomial_eq_guardedHahn
      (threeRightChannelAt u 2 (by decide)) i j l s)
    (guardedRightHahnCoefficient_eq_factorial
      (threeRightChannelAt u 2 (by decide)) i j l s)
  have h3 := Q'.eqv_trans _ _ _
    (triRight_monomial_eq_guardedHahn
      (threeRightChannelAt u 3 (by decide)) i j l s)
    (guardedRightHahnCoefficient_eq_factorial
      (threeRightChannelAt u 3 (by decide)) i j l s)
  have h4 := Q'.eqv_trans _ _ _
    (triRight_monomial_eq_guardedHahn
      (threeRightChannelAt u 4 (by decide)) i j l s)
    (guardedRightHahnCoefficient_eq_factorial
      (threeRightChannelAt u 4 (by decide)) i j l s)
  have hgL := three_guardedLeft_eq_shellPayload u i j l s hi' hj' hl'
  have hg0 := three_guardedRight_eq_shellPayload u 0 (by decide)
    i j l s hi' hj' hl'
  have hg1 := three_guardedRight_eq_shellPayload u 1 (by decide)
    i j l s hi' hj' hl'
  have hg2 := three_guardedRight_eq_shellPayload u 2 (by decide)
    i j l s hi' hj' hl'
  have hg3 := three_guardedRight_eq_shellPayload u 3 (by decide)
    i j l s hi' hj' hl'
  have hg4 := three_guardedRight_eq_shellPayload u 4 (by decide)
    i j l s hi' hj' hl'
  by_cases hshell : s + 4 = i + j + l
  · rw [if_pos hshell] at hgL hg0 hg1 hg2 hg3 hg4
    have hcL := Q'.eqv_trans _ _ _ hL hgL
    have hc0 := Q'.eqv_trans _ _ _ h0 hg0
    have hc1 := Q'.eqv_trans _ _ _ h1 hg1
    have hc2 := Q'.eqv_trans _ _ _ h2 hg2
    have hc3 := Q'.eqv_trans _ _ _ h3 hg3
    have hc4 := Q'.eqv_trans _ _ _ h4 hg4
    have hp := three_physical_payload_scaled_recoupling u i j l hi' hj' hl'
    unfold threeRightCombination threeRightMapAt
    simp only [scaleForm, addForm]
    refine Q'.eqv_trans _
      (threeRowScaleQ (Q'.ofNat u) *
        leftFactorialPayload (threeLeftChannel u) i j l) _
      (Q'.mul_eqv_congr_left _ _ _ hcL) ?_
    refine Q'.eqv_trans _ _ _ hp ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hc0))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hc1)))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hc2)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hc3)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hc4))
  · rw [if_neg hshell] at hgL hg0 hg1 hg2 hg3 hg4
    have hcL := Q'.eqv_trans _ _ _ hL hgL
    have hc0 := Q'.eqv_trans _ _ _ h0 hg0
    have hc1 := Q'.eqv_trans _ _ _ h1 hg1
    have hc2 := Q'.eqv_trans _ _ _ h2 hg2
    have hc3 := Q'.eqv_trans _ _ _ h3 hg3
    have hc4 := Q'.eqv_trans _ _ _ h4 hg4
    unfold threeRightCombination threeRightMapAt
    simp only [scaleForm, addForm]
    refine Q'.eqv_trans _ (threeRowScaleQ (Q'.ofNat u) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hcL) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
    refine Q'.eqv_symm (Q'.eqv_trans _
      ((((threeRowCoeffQ 0 (Q'.ofNat u) * 0 +
        threeRowCoeffQ 1 (Q'.ofNat u) * 0) +
        threeRowCoeffQ 2 (Q'.ofNat u) * 0) +
        threeRowCoeffQ 3 (Q'.ofNat u) * 0) +
        threeRowCoeffQ 4 (Q'.ofNat u) * 0) _ ?_ ?_)
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ hc0)
              (Q'.mul_eqv_congr_left _ _ _ hc1))
            (Q'.mul_eqv_congr_left _ _ _ hc2))
          (Q'.mul_eqv_congr_left _ _ _ hc3))
        (Q'.mul_eqv_congr_left _ _ _ hc4)
    · exact five_scaled_zeros
        (threeRowCoeffQ 0 (Q'.ofNat u))
        (threeRowCoeffQ 1 (Q'.ofNat u))
        (threeRowCoeffQ 2 (Q'.ofNat u))
        (threeRowCoeffQ 3 (Q'.ofNat u))
        (threeRowCoeffQ 4 (Q'.ofNat u))

theorem three_rightAt_middle (u : Nat) :
    (threeRightChannelAt u 2 (by decide)).intermediate = threeN u := by
  change 4 + threeN u - 2 * 2 = threeN u
  omega

theorem three_rightAt_two_eq (u : Nat) :
    threeRightChannelAt u 2 (by decide) = threeRightChannel u := by
  apply fixedRightChannel_eq_of_p_eq
  rfl

/-- Pairing the five-channel row against its middle channel kills the other
four summands by right-channel Gram orthogonality. -/
theorem three_scaled_cross_gram (u : Nat) :
    threeRowScaleQ (Q'.ofNat u) *
        triCrossChannelWeight (threeLeftChannel u)
          (threeRightChannelAt u 2 (by decide)) ≈
      threeRowCoeffQ 2 (Q'.ofNat u) *
        triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u) := by
  let L := triLeft (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let R0 := threeRightMapAt u 0 (by decide)
  let R1 := threeRightMapAt u 1 (by decide)
  let R2 := threeRightMapAt u 2 (by decide)
  let R3 := threeRightMapAt u 3 (by decide)
  let R4 := threeRightMapAt u 4 (by decide)
  let C0 := threeRowCoeffQ 0 (Q'.ofNat u)
  let C1 := threeRowCoeffQ 1 (Q'.ofNat u)
  let C2 := threeRowCoeffQ 2 (Q'.ofNat u)
  let C3 := threeRowCoeffQ 3 (Q'.ofNat u)
  let C4 := threeRowCoeffQ 4 (Q'.ofNat u)
  let M := threeRightCombination u
  have hrow : TriMapEqv (threeN u) 4 (threeN u) (threeD u)
      (fun x y z => scaleForm (threeRowScaleQ (Q'.ofNat u)) (L x y z)) M := by
    simpa only [L, M] using three_triMap_scaled_recoupling u
  have hpair := triMapInner_congr_left (R := R2) hrow
  have hleft := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u)
    (threeRowScaleQ (Q'.ofNat u)) L R2
  have hgram0 := rightChannel_gram_all
    (threeRightChannelAt u 0 (by decide)) (threeRightChannelAt u 2 (by decide))
  have hgram1 := rightChannel_gram_all
    (threeRightChannelAt u 1 (by decide)) (threeRightChannelAt u 2 (by decide))
  have hgram3 := rightChannel_gram_all
    (threeRightChannelAt u 3 (by decide)) (threeRightChannelAt u 2 (by decide))
  have hgram4 := rightChannel_gram_all
    (threeRightChannelAt u 4 (by decide)) (threeRightChannelAt u 2 (by decide))
  have hg0 : triMapInner (threeN u) 4 (threeN u) (threeD u) R0 R2 ≈ 0 := by
    simpa only [R0, R2, show (0 : Nat) ≠ 2 by decide, if_false] using hgram0
  have hg1 : triMapInner (threeN u) 4 (threeN u) (threeD u) R1 R2 ≈ 0 := by
    simpa only [R1, R2, show (1 : Nat) ≠ 2 by decide, if_false] using hgram1
  have hg2 : triMapInner (threeN u) 4 (threeN u) (threeD u) R2 R2 ≈
      triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u) := by
    unfold R2 threeRightMapAt triRightChannelWeight
    rw [three_rightAt_middle u]
    exact Q'.eqv_refl _
  have hg3 : triMapInner (threeN u) 4 (threeN u) (threeD u) R3 R2 ≈ 0 := by
    simpa only [R3, R2, show (3 : Nat) ≠ 2 by decide, if_false] using hgram3
  have hg4 : triMapInner (threeN u) 4 (threeN u) (threeD u) R4 R2 ≈ 0 := by
    simpa only [R4, R2, show (4 : Nat) ≠ 2 by decide, if_false] using hgram4
  have hs0 := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u) C0 R0 R2
  have hs1 := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u) C1 R1 R2
  have hs2 := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u) C2 R2 R2
  have hs3 := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u) C3 R3 R2
  have hs4 := triMapInner_scale_left (threeN u) 4 (threeN u) (threeD u) C4 R4 R2
  have ha0 := triMapInner_add_left (threeN u) 4 (threeN u) (threeD u)
    (fun x y z => addForm
      (addForm
        (addForm (scaleForm C0 (R0 x y z)) (scaleForm C1 (R1 x y z)))
        (scaleForm C2 (R2 x y z)))
      (scaleForm C3 (R3 x y z)))
    (fun x y z => scaleForm C4 (R4 x y z)) R2
  have ha1 := triMapInner_add_left (threeN u) 4 (threeN u) (threeD u)
    (fun x y z => addForm
      (addForm (scaleForm C0 (R0 x y z)) (scaleForm C1 (R1 x y z)))
      (scaleForm C2 (R2 x y z)))
    (fun x y z => scaleForm C3 (R3 x y z)) R2
  have ha2 := triMapInner_add_left (threeN u) 4 (threeN u) (threeD u)
    (fun x y z => addForm (scaleForm C0 (R0 x y z)) (scaleForm C1 (R1 x y z)))
    (fun x y z => scaleForm C2 (R2 x y z)) R2
  have ha3 := triMapInner_add_left (threeN u) 4 (threeN u) (threeD u)
    (fun x y z => scaleForm C0 (R0 x y z))
    (fun x y z => scaleForm C1 (R1 x y z)) R2
  have hright : triMapInner (threeN u) 4 (threeN u) (threeD u) M R2 ≈
      C2 * triRightChannelWeight (threeN u) 4 (threeN u) (threeD u)
        (threeN u) := by
    refine Q'.eqv_trans _
      (((((C0 * triMapInner (threeN u) 4 (threeN u) (threeD u) R0 R2) +
          C1 * triMapInner (threeN u) 4 (threeN u) (threeD u) R1 R2) +
          C2 * triMapInner (threeN u) 4 (threeN u) (threeD u) R2 R2) +
          C3 * triMapInner (threeN u) 4 (threeN u) (threeD u) R3 R2) +
          C4 * triMapInner (threeN u) 4 (threeN u) (threeD u) R4 R2) _ ?_ ?_
    · refine Q'.eqv_trans _
        (triMapInner (threeN u) 4 (threeN u) (threeD u)
          (fun x y z => addForm
            (addForm
              (addForm (scaleForm C0 (R0 x y z)) (scaleForm C1 (R1 x y z)))
              (scaleForm C2 (R2 x y z)))
            (scaleForm C3 (R3 x y z))) R2 +
          triMapInner (threeN u) 4 (threeN u) (threeD u)
            (fun x y z => scaleForm C4 (R4 x y z)) R2) _
        (by simpa only [M, threeRightCombination, C0, C1, C2, C3, C4,
          R0, R1, R2, R3, R4] using ha0) ?_
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ ha1
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ ha2
              (Q'.add_eqv_congr'
                (Q'.eqv_trans _ _ _ ha3 (Q'.add_eqv_congr' hs0 hs1)) hs2)) hs3)) hs4
    · refine Q'.eqv_trans _
        ((((C0 * 0 + C1 * 0) + C2 *
          triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u)) +
          C3 * 0) + C4 * 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left _ _ _ hg0)
                (Q'.mul_eqv_congr_left _ _ _ hg1))
              (Q'.mul_eqv_congr_left _ _ _ hg2))
            (Q'.mul_eqv_congr_left _ _ _ hg3))
          (Q'.mul_eqv_congr_left _ _ _ hg4)
      · exact five_scaled_center C0 C1 C3 C4
          (C2 * triRightChannelWeight (threeN u) 4 (threeN u)
            (threeD u) (threeN u))
  refine Q'.eqv_trans _
    (triMapInner (threeN u) 4 (threeN u) (threeD u)
      (fun x y z => scaleForm (threeRowScaleQ (Q'.ofNat u)) (L x y z)) R2) _
    (Q'.eqv_symm hleft) ?_
  refine Q'.eqv_trans _ (triMapInner (threeN u) 4 (threeN u) (threeD u) M R2) _
    hpair ?_
  simpa only [L, R2, C2, triCrossChannelWeight, three_rightAt_middle u] using hright

def threeCoeffPolyQ (U : Q') : Q' :=
  U * U * U + -(U * U) + -(124 * U) + (-452)

def threeDenQ (U : Q') : Q' := (U + 8) * (U + 10) * (U + 11)

private theorem ofNat_add_ofNat_pos_right (u k : Nat) (hk : 0 < k) :
    (0 : Q') < Q'.ofNat u + Q'.ofNat k := by
  show (0 : Int) * (((Q'.ofNat u + Q'.ofNat k).den : Nat) : Int) <
    (Q'.ofNat u + Q'.ofNat k).num * (1 : Int)
  simp only [Int.zero_mul, Int.mul_one, Q'.add_num_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  have hu : (0 : Int) ≤ Int.ofNat u := Int.natCast_nonneg u
  have hk' : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk
  omega

/-- After cancelling the positive common factor, only the physical cubic and
the three expected denominator factors remain. -/
theorem three_collapsed_cross_scale (u : Nat) :
    threeDenQ (Q'.ofNat u) *
        collapsedFactorialCrossSum (threeLeftChannel u) (threeRightChannel u) ≈
      threeCoeffPolyQ (Q'.ofNat u) *
        triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u) := by
  let U := Q'.ofNat u
  let C := triCrossChannelWeight (threeLeftChannel u)
    (threeRightChannelAt u 2 (by decide))
  let W := triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let F := (U + 6) * (U + 9) * (U + 12)
  have hs := three_scaled_cross_gram u
  have hfactor : F * (threeDenQ U * C) ≈ F * (threeCoeffPolyQ U * W) := by
    refine Q'.eqv_trans _ (threeRowScaleQ U * C) _ (by
      simp only [F, threeDenQ, threeRowScaleQ]
      ring_qeqv) ?_
    refine Q'.eqv_trans _ (threeRowCoeffQ 2 U * W) _
      (by simpa only [U, C, W] using hs) (by
        simp only [F, threeCoeffPolyQ, threeRowCoeffQ]
        ring_qeqv)
  have hFpos : (0 : Q') < F := by
    exact Q'.mul_pos
      (Q'.mul_pos
        (ofNat_add_ofNat_pos_right u 6 (by omega))
        (ofNat_add_ofNat_pos_right u 9 (by omega)))
      (ofNat_add_ofNat_pos_right u 12 (by omega))
  have hc := Q'.mul_left_cancel_of_pos hFpos hfactor
  have hcarrier := triCrossChannelWeight_eq_collapsedFactorialCrossSum
    (threeLeftChannel u) (threeRightChannelAt u 2 (by decide))
  rw [three_rightAt_two_eq u] at hcarrier
  refine Q'.eqv_trans _ (threeDenQ U * C) _ ?_ hc
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (Q'.eqv_symm hcarrier) (by
      unfold C
      rw [three_rightAt_two_eq u]
      exact Q'.eqv_refl _))

theorem threeInverseCoeffClosed_scale (u : Nat) :
    threeDenQ (Q'.ofNat u) * threeInverseCoeffClosed u ≈
      threeCoeffPolyQ (Q'.ofNat u) := by
  let D := (u + 8) * (u + 10) * (u + 11)
  have hpos : 0 < (u + 8) * (u + 10) * (u + 11) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hden : D - 1 + 1 = D :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))
  have hD : threeDenQ (Q'.ofNat u) ≈ Q'.ofNat D := by
    unfold threeDenQ D
    change ((Q'.ofNat u + Q'.ofNat 8) *
      (Q'.ofNat u + Q'.ofNat 10)) *
        (Q'.ofNat u + Q'.ofNat 11) ≈
      Q'.ofNat ((u + 8) * (u + 10) * (u + 11))
    rw [← ofNat_add_eq u 8, ← ofNat_add_eq u 10,
      ← ofNat_add_eq u 11]
    exact Q'.eqv_trans _
      (Q'.ofNat ((u + 8) * (u + 10)) * Q'.ofNat (u + 11)) _
      (Q'.mul_eqv_congr_right _ _ _
        (ofNat_mul_eqv (u + 8) (u + 10)))
      (ofNat_mul_eqv ((u + 8) * (u + 10)) (u + 11))
  have hraw : Q'.ofNat D * threeInverseCoeffClosed u ≈
      Q'.ofInt (threeCoeffNum u) := by
    unfold threeInverseCoeffClosed Q'.ofInt
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast]
    simp only [Q'.den]
    rw [hden]
    ac_rfl
  have hnum : Q'.ofInt (threeCoeffNum u) ≈
      threeCoeffPolyQ (Q'.ofNat u) := by
    unfold Q'.eqv threeCoeffNum threeCoeffPolyQ Q'.ofInt Q'.ofNat
    simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
      Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.den,
      Int.add_mul, Int.mul_add, Int.neg_mul,
      Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
      Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add,
      Nat.add_sub_cancel]
    rw [show (124 : Q').num = (124 : Int) by rfl,
      show (452 : Q').num = (452 : Int) by rfl]
    simp only [Int.sub_eq_add_neg]
    ac_rfl
  exact Q'.eqv_trans _ (Q'.ofNat D * threeInverseCoeffClosed u) _
    (Q'.mul_eqv_congr_right _ _ _ hD) (Q'.eqv_trans _ _ _ hraw hnum)

/-- The physical inverse Schur coefficient is the signed cubic divided by
`(u+8)(u+10)(u+11)`. -/
theorem three_inverseSchurCoeff_closed (u : Nat) :
    fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0 ≈
      threeInverseCoeffClosed u := by
  let U := Q'.ofNat u
  let W := triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let K := fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0
  have hcross := three_collapsed_cross_scale u
  have hcap := collapsed_cross_inverse_normalization_arbitrary
    (threeLeftChannel u) (threeRightChannel u)
  have hcap' : collapsedFactorialCrossSum (threeLeftChannel u) (threeRightChannel u) ≈
      W * K := by
    simpa only [W, K, (three_intermediates u).2] using hcap
  have hscaled : W * (threeDenQ U * K) ≈ W * threeCoeffPolyQ U := by
    refine Q'.eqv_trans _ (threeDenQ U * (W * K)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (threeDenQ U * collapsedFactorialCrossSum
        (threeLeftChannel u) (threeRightChannel u)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcap')) ?_
    refine Q'.eqv_trans _ (threeCoeffPolyQ U * W) _
      (by simpa only [U, W] using hcross) (by ring_qeqv)
  have hWpos : (0 : Q') < W := by
    simpa only [W, (three_intermediates u).2] using
      right_channel_weight_pos_all (threeRightChannel u)
  have hKscale : threeDenQ U * K ≈ threeCoeffPolyQ U :=
    Q'.mul_left_cancel_of_pos hWpos hscaled
  have hclosed : threeDenQ U * threeInverseCoeffClosed u ≈ threeCoeffPolyQ U := by
    simpa only [U] using threeInverseCoeffClosed_scale u
  have hdenPos : (0 : Q') < threeDenQ U := by
    unfold threeDenQ U
    exact Q'.mul_pos
      (Q'.mul_pos
        (ofNat_add_ofNat_pos_right u 8 (by omega))
        (ofNat_add_ofNat_pos_right u 10 (by omega)))
      (ofNat_add_ofNat_pos_right u 11 (by omega))
  exact Q'.mul_left_cancel_of_pos hdenPos
    (Q'.eqv_trans _ _ _ hKscale (Q'.eqv_symm hclosed))

/-! ## Reversal symmetry and the collapsed square -/

private theorem three_tprod_transpose (x y : BForm) :
    BForm2Eqv (transpose2 (tprod x y)) (tprod y x) := by
  intro i j
  unfold transpose2 tprod
  exact Q'.mul_comm_eqv _ _

private theorem three_tprod_congr_left (x : BForm) {y z : BForm}
    (h : BFormEqv y z) : BForm2Eqv (tprod x y) (tprod x z) := by
  intro i j
  exact Q'.mul_eqv_congr_left (x i) _ _ (h j)

theorem three_triLeft_reverse (u : Nat) (x y z : BForm) :
    BFormEqv
      (triLeft (threeN u) 4 (threeN u) (threeD u) (threeN u) x y z)
      (triRight (threeN u) 4 (threeN u) (threeD u) (threeN u) z y x) := by
  have hinnerOrder : couplingOrder (threeN u) 4 (threeN u) = 2 := by
    unfold couplingOrder threeN
    omega
  have hrightInnerOrder : couplingOrder 4 (threeN u) (threeN u) = 2 := by
    unfold couplingOrder threeN
    omega
  have houterOrder : couplingOrder (threeN u) (threeN u) (threeD u) = 2 := by
    unfold couplingOrder threeN threeD
    omega
  let A := transvect (threeN u) 4 2 (tprod x y)
  let B := transvect 4 (threeN u) 2 (tprod y x)
  have hphase (q : Q') : swapPhase 2 * q ≈ q := by
    unfold swapPhase
    exact Q'.one_mul_eqv q
  have hinner : BFormEqv B A := by
    have hswap := transvect_transpose (threeN u) 4 2 (tprod x y)
    have hcongr := transvect_congr 4 (threeN u) 2 (three_tprod_transpose x y)
    intro s
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s))
      (Q'.eqv_trans _ _ _ (by simpa only [A, B] using hswap s) (hphase _))
  have htensor := three_tprod_congr_left z hinner
  have hright : BFormEqv
      (transvect (threeN u) (threeN u) 2 (tprod z B))
      (transvect (threeN u) (threeN u) 2 (tprod z A)) :=
    transvect_congr (threeN u) (threeN u) 2 htensor
  have houter : BFormEqv
      (transvect (threeN u) (threeN u) 2 (tprod z A))
      (transvect (threeN u) (threeN u) 2 (tprod A z)) := by
    have hswap := transvect_transpose (threeN u) (threeN u) 2 (tprod A z)
    have hcongr := transvect_congr (threeN u) (threeN u) 2
      (three_tprod_transpose A z)
    intro s
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hcongr s))
      (Q'.eqv_trans _ _ _ (hswap s) (hphase _))
  intro s
  unfold triLeft triRight
  rw [hinnerOrder, hrightInnerOrder, houterOrder]
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (hright s) (houter s))

theorem three_channel_weights_eq (u : Nat) :
    triLeftChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u) ≈
      triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u) := by
  let L := triLeft (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let R := triRight (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let A : Nat → Nat → Nat → Nat → Q' := fun i j l s =>
    tvBinomQ (threeN u) i * tvBinomQ 4 j * tvBinomQ (threeN u) l *
      symMonomialNormSq (threeD u) s *
        (R (mono i) (mono j) (mono l) s * R (mono i) (mono j) (mono l) s)
  have hterm : ∀ i j l s,
      tvBinomQ (threeN u) i * tvBinomQ 4 j * tvBinomQ (threeN u) l *
          symMonomialNormSq (threeD u) s *
            (L (mono i) (mono j) (mono l) s * L (mono i) (mono j) (mono l) s) ≈
        A l j i s := by
    intro i j l s
    have hrev := three_triLeft_reverse u (mono i) (mono j) (mono l) s
    unfold A R
    have hsq := Q'.eqv_trans _
      (triRight (threeN u) 4 (threeN u) (threeD u) (threeN u)
          (mono l) (mono j) (mono i) s * L (mono i) (mono j) (mono l) s) _
      (Q'.mul_eqv_congr_right _ _ _ hrev)
      (Q'.mul_eqv_congr_left _ _ _ hrev)
    refine Q'.eqv_trans _
      (tvBinomQ (threeN u) i * tvBinomQ 4 j * tvBinomQ (threeN u) l *
        symMonomialNormSq (threeD u) s *
          (triRight (threeN u) 4 (threeN u) (threeD u) (threeN u)
              (mono l) (mono j) (mono i) s *
            triRight (threeN u) 4 (threeN u) (threeD u) (threeN u)
              (mono l) (mono j) (mono i) s)) _
      (Q'.mul_eqv_congr_left _ _ _ hsq) (by ring_qeqv)
  unfold triLeftChannelWeight triRightChannelWeight triMapInner
  refine Q'.eqv_trans _
    (finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
      A l j i s) (threeD u + 1)) (threeN u + 1)) 5) (threeN u + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (threeN u + 1) (fun i hi => ?_)
    refine finSum_eqv_congr_lt _ _ 5 (fun j hj => ?_)
    refine finSum_eqv_congr_lt _ _ (threeN u + 1) (fun l hl => ?_)
    refine finSum_eqv_congr_lt _ _ (threeD u + 1) (fun s hs => ?_)
    exact hterm i j l s
  · let S : Nat → Nat → Nat → Q' := fun i j l =>
      finSum (fun s => A i j l s) (threeD u + 1)
    have hswapIJ := finSum_swap
      (fun i j => finSum (fun l => S l j i) (threeN u + 1))
      (threeN u + 1) 5
    have hswapIL : finSum
        (fun j => finSum (fun i => finSum (fun l => S l j i)
          (threeN u + 1)) (threeN u + 1)) 5 ≈
        finSum (fun j => finSum (fun l => finSum (fun i => S l j i)
          (threeN u + 1)) (threeN u + 1)) 5 := by
      refine finSum_eqv_congr_lt _ _ 5 (fun j hj => ?_)
      exact finSum_swap (fun i l => S l j i) (threeN u + 1) (threeN u + 1)
    have hswapJL := finSum_swap
      (fun j l => finSum (fun i => S l j i) (threeN u + 1))
      5 (threeN u + 1)
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun i => finSum (fun l => S l j i)
        (threeN u + 1)) (threeN u + 1)) 5) _ ?_ ?_
    · simpa only [S] using hswapIJ
    refine Q'.eqv_trans _
      (finSum (fun j => finSum (fun l => finSum (fun i => S l j i)
        (threeN u + 1)) (threeN u + 1)) 5) _ hswapIL ?_
    simpa only [S, A, L, R] using hswapJL

theorem threeInverseCoeffClosed_square (u : Nat) :
    threeInverseCoeffClosed u * threeInverseCoeffClosed u ≈ threeKernelClosed u := by
  exact Q'.eqv_refl _

theorem three_collapsedRacahSquare_iff_inverseCoeffSquare (u : Nat) :
    CollapsedRacahSquareAt (threeLeftChannel u) (threeRightChannel u) ↔
      threeKernelClosed u ≈
        fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0 *
          fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0 := by
  let W := triRightChannelWeight (threeN u) 4 (threeN u) (threeD u) (threeN u)
  let K := fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0
  have hcap := collapsedRacahSquare_iff_explicit_inverse_kernel_identity
    (threeLeftChannel u) (threeRightChannel u)
  have hW := three_channel_weights_eq u
  have hP := three_racahKernel_closed u
  have hpos : (0 : Q') < W := by
    simpa only [W, (three_intermediates u).2] using
      right_channel_weight_pos_all (threeRightChannel u)
  have hleft :
      triLeftChannelWeight (threeN u) 4 (threeN u) (threeD u)
          (threeLeftChannel u).intermediate *
        racahKernel6 (threeN u) 4 (threeN u) (threeD u)
          (threeLeftChannel u).intermediate (threeRightChannel u).intermediate ≈
      W * threeKernelClosed u := by
    rw [(three_intermediates u).1, (three_intermediates u).2]
    exact Q'.eqv_trans _
      (W * racahKernel6 (threeN u) 4 (threeN u) (threeD u)
        (threeN u) (threeN u)) _
      (Q'.mul_eqv_congr_right _ _ _ hW)
      (Q'.mul_eqv_congr_left W _ _ hP)
  constructor
  · intro hsquare
    have hbridge := hcap.mp hsquare
    have hscaled : W * threeKernelClosed u ≈ W * (K * K) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
        (by simpa only [W, K, (three_intermediates u).2] using hbridge)
    exact Q'.mul_left_cancel_of_pos hpos hscaled
  · intro hscalar
    apply hcap.mpr
    refine Q'.eqv_trans _ (W * threeKernelClosed u) _ hleft ?_
    exact Q'.eqv_trans _ (W * (K * K)) _
      (Q'.mul_eqv_congr_left W _ _ hscalar)
      (by rw [(three_intermediates u).2]; exact Q'.eqv_refl _)

/-- The physical collapsed Racah square for `(u+8,4,u+8;2u+12;u+8,u+8)`. -/
theorem three_collapsedRacahSquare (u : Nat) :
    CollapsedRacahSquareAt (threeLeftChannel u) (threeRightChannel u) := by
  apply (three_collapsedRacahSquare_iff_inverseCoeffSquare u).2
  let K := fixedLeftRightDiagonalCoeff (threeLeftChannel u) (threeRightChannel u) 0
  have hK : K ≈ threeInverseCoeffClosed u := by
    simpa only [K] using three_inverseSchurCoeff_closed u
  exact Q'.eqv_trans _
    (threeInverseCoeffClosed u * threeInverseCoeffClosed u) _
    (Q'.eqv_symm (threeInverseCoeffClosed_square u))
    (mul_eqv_congr (Q'.eqv_symm hK) (Q'.eqv_symm hK))

end YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization

#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.transvectFactorialCoeff_symbolic
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.hahnRowSymbolic_zero_below
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_payload_scaled_recoupling
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_triMap_scaled_recoupling
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_scaled_cross_gram
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.threeInverseCoeffClosed_scale
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_inverseSchurCoeff_closed
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_triLeft_reverse
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_channel_weights_eq
#print axioms YMGap.Continuum.SU2OrderedRacahNearStretchedThreeTermCrossNormalization.three_collapsedRacahSquare
