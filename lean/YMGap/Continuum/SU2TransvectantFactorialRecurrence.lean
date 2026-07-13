/-
# Falling-factorial recurrence for arbitrary-order Cayley coefficients

This module develops the exact factorial identities needed to match the
two-branch monomial recurrence with Pascal's recurrence.  It works directly
with the project's unnormalised constructive rationals `Q'` and treats every
truncating-natural boundary explicitly.
-/

import YMGap.Continuum.SU2TransvectantOrderTwo
import YMGap.Continuum.ThetaResidualPascalTelescope

namespace YMGap.Continuum.SU2TransvectantFactorialRecurrence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.RingNormaliser

/-- Multiplication by the leading label advances a falling factorial:
`n · (n-1)_r = (n)_(r+1)`, including `n=0` and the out-of-support region. -/
theorem tvFallQ_leading_shift (n r : Nat) :
    (Q'.ofNat n * tvFallQ (n - 1) r).eqv (tvFallQ n (r + 1)) := by
  cases n with
  | zero =>
      unfold tvFallQ
      rw [if_neg (by omega : ¬ r + 1 ≤ 0)]
      change ((0 : Q') *
        (if r ≤ 0 then Q'.mkN (tvFact 0) (tvFact (0 - r) - 1) else 0)).eqv 0
      exact Q'.zero_mul_eqv _
  | succ n =>
      unfold tvFallQ
      rw [show n + 1 - 1 = n by omega]
      by_cases hr : r ≤ n
      · rw [if_pos hr, if_pos (by omega : r + 1 ≤ n + 1)]
        have hsub : n + 1 - (r + 1) = n - r := by omega
        rw [hsub]
        show (Q'.ofNat (n + 1) * Q'.mkN (tvFact n) (tvFact (n - r) - 1)).eqv
          (Q'.mkN (tvFact (n + 1)) (tvFact (n - r) - 1))
        unfold Q'.eqv
        simp only [Q'.mul_num_cast, Q'.mul_den_cast,
          Q'.ofNat_num_cast, Q'.ofNat_den_cast]
        change
          (((n + 1 : Nat) : Int) * (tvFact n : Int)) *
              (((tvFact (n - r) - 1) + 1 : Nat) : Int) =
            (tvFact (n + 1) : Int) *
              ((((1 : Nat) * ((tvFact (n - r) - 1) + 1) - 1) + 1 : Nat) : Int)
        have hd : tvFact (n - r) - 1 + 1 = tvFact (n - r) := by
          have hp := tvFact_pos (n - r)
          omega
        rw [hd]
        simp only [Nat.one_mul]
        rw [show tvFact (n - r) - 1 + 1 = tvFact (n - r) from hd]
        simp only [tvFact]
        push_cast
        rfl
      · have hrs : ¬ r + 1 ≤ n + 1 := by omega
        rw [if_neg hr, if_neg hrs]
        change (Q'.ofNat (n + 1) * (0 : Q')).eqv 0
        exact Q'.mul_zero_eqv _

/-- The left edge of every binomial row is one. -/
theorem tvBinomQ_zero (k : Nat) : (tvBinomQ k 0).eqv 1 := by
  unfold tvBinomQ
  rw [if_pos (Nat.zero_le k), Nat.sub_zero]
  simp only [tvFact, Nat.one_mul]
  exact mkN_self_pred_eqv_one (tvFact k) (tvFact_pos k)

/-- The right edge of every binomial row is one. -/
theorem tvBinomQ_self (k : Nat) : (tvBinomQ k k).eqv 1 := by
  unfold tvBinomQ
  rw [if_pos (Nat.le_refl k), Nat.sub_self]
  simp only [tvFact, Nat.mul_one]
  exact mkN_self_pred_eqv_one (tvFact k) (tvFact_pos k)

/-! ## The factorial carrier equals the constructive Pascal carrier -/

/-- Natural falling factorial, used only as an exact bridge to the recursively
defined Pascal coefficient. -/
def tvFallingNat (n : Nat) : Nat → Nat
  | 0 => 1
  | r + 1 => tvFallingNat n r * (n - r)

/-- `r! * C(n,r) = (n)_r`, proved from the subtraction-free adjacent-binomial
identity already available for the constructive Pascal carrier. -/
theorem tvFact_mul_choose_eq_falling : ∀ r n : Nat, r ≤ n →
    tvFact r * PNPaths.choose n r = tvFallingNat n r
  | 0, n, _ => by simp [tvFact, tvFallingNat, PNPaths.choose]
  | r + 1, n, hrn => by
      have hrlt : r < n := by omega
      have hadj :=
        YMGap.Continuum.ThetaResidualPascalTelescope.choose_adjacent_cross
          n r hrlt
      have ih := tvFact_mul_choose_eq_falling r n (by omega)
      simp only [tvFact, tvFallingNat]
      calc
        (r + 1) * tvFact r * PNPaths.choose n (r + 1) =
            tvFact r * ((r + 1) * PNPaths.choose n (r + 1)) := by ac_rfl
        _ = tvFact r * ((n - r) * PNPaths.choose n r) := by rw [hadj]
        _ = (tvFact r * PNPaths.choose n r) * (n - r) := by ac_rfl
        _ = tvFallingNat n r * (n - r) := by rw [ih]

/-- Multiplying `(n)_r` by the omitted tail factorial reconstructs `n!`. -/
theorem tvFallingNat_mul_tailFact : ∀ r n : Nat, r ≤ n →
    tvFallingNat n r * tvFact (n - r) = tvFact n
  | 0, n, _ => by simp [tvFallingNat]
  | r + 1, n, hrn => by
      have ih := tvFallingNat_mul_tailFact r n (by omega)
      have hsub : n - (r + 1) = n - r - 1 := by omega
      have hfact : (n - r) * tvFact (n - (r + 1)) = tvFact (n - r) := by
        rw [hsub]
        cases hnr : n - r with
        | zero => omega
        | succ q =>
            simp only [Nat.add_sub_cancel]
            rfl
      simp only [tvFallingNat]
      calc
        (tvFallingNat n r * (n - r)) * tvFact (n - (r + 1)) =
            tvFallingNat n r * ((n - r) * tvFact (n - (r + 1))) := by ac_rfl
        _ = tvFallingNat n r * tvFact (n - r) := by rw [hfact]
        _ = tvFact n := ih

/-- Cleared factorial formula for the Pascal coefficient. -/
theorem choose_mul_factorial_den (n r : Nat) (hrn : r ≤ n) :
    PNPaths.choose n r * (tvFact r * tvFact (n - r)) = tvFact n := by
  calc
    PNPaths.choose n r * (tvFact r * tvFact (n - r)) =
        (tvFact r * PNPaths.choose n r) * tvFact (n - r) := by ac_rfl
    _ = tvFallingNat n r * tvFact (n - r) := by
      rw [tvFact_mul_choose_eq_falling r n hrn]
    _ = tvFact n := tvFallingNat_mul_tailFact r n hrn

/-- The factorial-ratio binomial used by the transvectant is exactly the
constructive Pascal coefficient at every in-range index. -/
theorem tvBinomQ_eqv_choose (n r : Nat) (hrn : r ≤ n) :
    (tvBinomQ n r).eqv (Q'.ofNat (PNPaths.choose n r)) := by
  unfold tvBinomQ
  rw [if_pos hrn]
  let D := tvFact r * tvFact (n - r)
  have hDpos : 0 < D := Nat.mul_pos (tvFact_pos r) (tvFact_pos (n - r))
  have hpred : D - 1 + 1 = D := by omega
  show (Q'.mkN (tvFact n) (D - 1)).eqv
    (Q'.ofNat (PNPaths.choose n r))
  show (tvFact n : Int) * (1 : Int) =
    (PNPaths.choose n r : Int) * (((D - 1) + 1 : Nat) : Int)
  rw [hpred, Int.mul_one]
  have hnat := choose_mul_factorial_den n r hrn
  have hint := congrArg Int.ofNat hnat
  push_cast at hint
  exact hint.symm

/-- Pascal coefficients vanish strictly beyond the row. -/
theorem choose_zero_of_lt : ∀ n r : Nat, n < r → PNPaths.choose n r = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, r + 1, h => by
      simp only [PNPaths.choose]
      rw [choose_zero_of_lt n r (by omega)]
      rw [choose_zero_of_lt n (r + 1) (by omega)]

/-- Factorial-ratio and Pascal binomials agree at every index, including the
zero region beyond the row. -/
theorem tvBinomQ_eqv_choose_all (n r : Nat) :
    (tvBinomQ n r).eqv (Q'.ofNat (PNPaths.choose n r)) := by
  by_cases hrn : r ≤ n
  · exact tvBinomQ_eqv_choose n r hrn
  · have hzero : PNPaths.choose n r = 0 := choose_zero_of_lt n r (by omega)
    unfold tvBinomQ
    rw [if_neg hrn, hzero]
    exact Q'.eqv_symm Q'.ofNat_zero_eqv

private theorem ofNat_add_eqv (a b : Nat) :
    (Q'.ofNat (a + b)).eqv (Q'.ofNat a + Q'.ofNat b) := by
  show (Q'.ofNat (a + b)).num * ((Q'.ofNat a + Q'.ofNat b).den : Int) =
    (Q'.ofNat a + Q'.ofNat b).num * ((Q'.ofNat (a + b)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- **Pascal recurrence for the exact rational factorial carrier.** -/
theorem tvBinomQ_pascal (k r : Nat) :
    (tvBinomQ (k + 1) (r + 1)).eqv
      (tvBinomQ k r + tvBinomQ k (r + 1)) := by
  have hleft := tvBinomQ_eqv_choose_all (k + 1) (r + 1)
  have h0 := tvBinomQ_eqv_choose_all k r
  have h1 := tvBinomQ_eqv_choose_all k (r + 1)
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose k r + PNPaths.choose k (r + 1))) _
    (by simpa only [PNPaths.choose] using hleft) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose k r) + Q'.ofNat (PNPaths.choose k (r + 1))) _
    (ofNat_add_eqv _ _) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm h0) (Q'.eqv_symm h1)

/-! ## Phase and paired falling-factor shifts -/

/-- Advancing the negative-branch counter flips the Cayley phase. -/
theorem tvPhase_succ (r : Nat) : (tvPhase (r + 1)).eqv (-(tvPhase r)) := by
  have hpar : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hpar with heven | hodd
  · have hsucc : (r + 1) % 2 = 1 := by omega
    unfold tvPhase
    rw [if_neg (by omega : ¬ (r + 1) % 2 = 0), if_pos heven]
    exact Q'.eqv_refl _
  · have hsucc : (r + 1) % 2 = 0 := by omega
    unfold tvPhase
    rw [if_pos hsucc, if_neg (by omega : ¬ r % 2 = 0)]
    exact Q'.eqv_symm (Q'.neg_neg_eqv 1)

private theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem mul_four_regroup (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

/-- Two leading labels simultaneously advance two falling factorials. -/
theorem tvFallQ_double_leading_shift (a b r : Nat) :
    (Q'.ofNat (a * b) *
      (tvFallQ (a - 1) r * tvFallQ (b - 1) r)).eqv
      (tvFallQ a (r + 1) * tvFallQ b (r + 1)) := by
  have hab := Q'.eqv_symm (ofNat_mul_eqv a b)
  have hregroup := mul_four_regroup
    (Q'.ofNat a) (Q'.ofNat b) (tvFallQ (a - 1) r) (tvFallQ (b - 1) r)
  have ha := tvFallQ_leading_shift a r
  have hb := tvFallQ_leading_shift b r
  refine Q'.eqv_trans _
    ((Q'.ofNat a * Q'.ofNat b) *
      (tvFallQ (a - 1) r * tvFallQ (b - 1) r)) _
    (Q'.mul_eqv_congr_right _ _ _ hab) ?_
  refine Q'.eqv_trans _ _ _ hregroup ?_
  refine Q'.eqv_trans _
    (tvFallQ a (r + 1) * (Q'.ofNat b * tvFallQ (b - 1) r)) _
    (Q'.mul_eqv_congr_right _ _ _ ha) ?_
  exact Q'.mul_eqv_congr_left (tvFallQ a (r + 1)) _ _ hb

/-! ## Termwise positive-branch shift -/

/-- One summand of the closed factorial coefficient. -/
def tvCoeffTerm (m n k i j r : Nat) : Q' :=
  tvPhase r * tvBinomQ k r * tvFallQ i (k - r) * tvFallQ (m - i) r *
    tvFallQ j r * tvFallQ (n - j) (k - r)

private def scaledPairLHS : PolyExpr :=
  .mul (.var 0)
    (.mul
      (.mul
        (.mul
          (.mul (.mul (.var 1) (.var 2)) (.var 3))
          (.var 4))
        (.var 5))
      (.var 6))

private def scaledPairMid : PolyExpr :=
  .mul
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 4) (.var 5)))
    (.mul (.var 0) (.mul (.var 3) (.var 6)))

private theorem scaledPair_normal_eq :
    normalize scaledPairLHS = normalize scaledPairMid := by decide

private def unscaledPairLHS : PolyExpr :=
  .mul
    (.mul
      (.mul
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.var 3))
      (.var 4))
    (.var 5)

private def unscaledPairMid : PolyExpr :=
  .mul
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 4)))
    (.mul (.var 2) (.var 5))

private theorem unscaledPair_normal_eq :
    normalize unscaledPairLHS = normalize unscaledPairMid := by decide

private theorem scaled_pair_regroup
    (a p b x y z w : Q') :
    (a * (((((p * b) * x) * y) * z) * w)).eqv
      ((((p * b) * (y * z)) * (a * (x * w)))) := by
  let ρ : Nat → Q' := fun t =>
    if t = 0 then a else if t = 1 then p else if t = 2 then b else
    if t = 3 then x else if t = 4 then y else if t = 5 then z else w
  have h := poly_identity_of_normal_eq scaledPairLHS scaledPairMid
    scaledPair_normal_eq ρ
  simpa [scaledPairLHS, scaledPairMid, eval, ρ] using h

private theorem unscaled_pair_regroup
    (p b x y z w : Q') :
    (((((p * b) * x) * y) * z) * w).eqv
      ((((p * b) * (y * z)) * (x * w))) := by
  let ρ : Nat → Q' := fun t =>
    if t = 0 then p else if t = 1 then b else if t = 2 then x else
    if t = 3 then y else if t = 4 then z else w
  have h := poly_identity_of_normal_eq unscaledPairLHS unscaledPairMid
    unscaledPair_normal_eq ρ
  simpa [unscaledPairLHS, unscaledPairMid, eval, ρ] using h

/-- A scalar which advances the two separated falling factors can be inserted
back into their original six-factor coefficient term. -/
theorem scaled_six_factor_pair_shift
    (a p b x y z w X W : Q')
    (hpair : (a * (x * w)).eqv (X * W)) :
    (a * (((((p * b) * x) * y) * z) * w)).eqv
      (((((p * b) * X) * y) * z) * W) := by
  refine Q'.eqv_trans _ (((p * b) * (y * z)) * (a * (x * w))) _
    (scaled_pair_regroup a p b x y z w) ?_
  refine Q'.eqv_trans _ (((p * b) * (y * z)) * (X * W)) _
    (Q'.mul_eqv_congr_left ((p * b) * (y * z)) _ _ hpair) ?_
  exact Q'.eqv_symm (unscaled_pair_regroup p b X y z W)

/-- The positive derivative branch advances the two positive-side falling
factors in each coefficient summand. -/
theorem positive_branch_term_shift
    (m n k i j r : Nat) (hi : 0 < i) :
    (Q'.ofNat (i * (n - j)) *
      tvCoeffTerm (m - 1) (n - 1) k (i - 1) j r).eqv
      (tvPhase r * tvBinomQ k r * tvFallQ i (k - r + 1) *
        tvFallQ (m - i) r * tvFallQ j r *
        tvFallQ (n - j) (k - r + 1)) := by
  have hm : (m - 1) - (i - 1) = m - i := by omega
  have hn : (n - 1) - j = n - j - 1 := by omega
  have hpair := tvFallQ_double_leading_shift i (n - j) (k - r)
  unfold tvCoeffTerm
  rw [hm, hn]
  exact scaled_six_factor_pair_shift _ _ _ _ _ _ _ _ _ hpair

private def negativeMiddleLHS : PolyExpr :=
  .mul (.neg (.var 0))
    (.mul
      (.mul
        (.mul
          (.mul (.mul (.var 1) (.var 2)) (.var 3))
          (.var 4))
        (.var 5))
      (.var 6))

private def negativeMiddleMid : PolyExpr :=
  .mul
    (.mul
      (.mul (.mul (.neg (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.var 4) (.var 5))))
    (.var 6)

private theorem negativeMiddle_normal_eq :
    normalize negativeMiddleLHS = normalize negativeMiddleMid := by decide

private theorem negative_middle_regroup
    (a p b x y z w : Q') :
    ((-a) * (((((p * b) * x) * y) * z) * w)).eqv
      (((((-p) * b) * x) * (a * (y * z))) * w) := by
  let ρ : Nat → Q' := fun t =>
    if t = 0 then a else if t = 1 then p else if t = 2 then b else
    if t = 3 then x else if t = 4 then y else if t = 5 then z else w
  have h := poly_identity_of_normal_eq negativeMiddleLHS negativeMiddleMid
    negativeMiddle_normal_eq ρ
  simpa [negativeMiddleLHS, negativeMiddleMid, eval, ρ] using h

/-- The negative derivative branch advances the two negative-side falling
factors, shifts the summation index, and flips the Cayley phase. -/
theorem negative_branch_term_shift
    (m n k i j r : Nat) (hj : 0 < j) :
    ((-(Q'.ofNat ((m - i) * j))) *
      tvCoeffTerm (m - 1) (n - 1) k i (j - 1) r).eqv
      (tvPhase (r + 1) * tvBinomQ k r * tvFallQ i (k - r) *
        tvFallQ (m - i) (r + 1) * tvFallQ j (r + 1) *
        tvFallQ (n - j) (k - r)) := by
  have hm : (m - 1) - i = m - i - 1 := by omega
  have hn : (n - 1) - (j - 1) = n - j := by omega
  let p := tvPhase r
  let b := tvBinomQ k r
  let x := tvFallQ i (k - r)
  let y := tvFallQ (m - i - 1) r
  let z := tvFallQ (j - 1) r
  let w := tvFallQ (n - j) (k - r)
  let Y := tvFallQ (m - i) (r + 1)
  let Z := tvFallQ j (r + 1)
  have hpair :
      (Q'.ofNat ((m - i) * j) * (y * z)).eqv (Y * Z) := by
    simpa only [y, z, Y, Z] using
      tvFallQ_double_leading_shift (m - i) j r
  have hphase : (tvPhase (r + 1)).eqv (-p) := by
    simpa only [p] using tvPhase_succ r
  unfold tvCoeffTerm
  rw [hm, hn]
  change ((-(Q'.ofNat ((m - i) * j))) *
      (((((p * b) * x) * y) * z) * w)).eqv _
  refine Q'.eqv_trans _
    (((((-p) * b) * x) * (Q'.ofNat ((m - i) * j) * (y * z))) * w) _
    (negative_middle_regroup _ p b x y z w) ?_
  refine Q'.eqv_trans _ (((((-p) * b) * x) * (Y * Z)) * w) _
    (Q'.mul_eqv_congr_right _ _ w
      (Q'.mul_eqv_congr_left (((-p) * b) * x) _ _ hpair)) ?_
  refine Q'.eqv_trans _ ((((((-p) * b) * x) * Y) * Z) * w) _
    (Q'.mul_eqv_congr_right _ _ w
      (Q'.eqv_symm (Q'.mul_assoc_eqv (((-p) * b) * x) Y Z))) ?_
  have hp0 : ((-p) * b).eqv (tvPhase (r + 1) * b) :=
    Q'.mul_eqv_congr_right _ _ b (Q'.eqv_symm hphase)
  have hp1 : (((-p) * b) * x).eqv ((tvPhase (r + 1) * b) * x) :=
    Q'.mul_eqv_congr_right _ _ x hp0
  have hp2 : ((((-p) * b) * x) * Y).eqv
      (((tvPhase (r + 1) * b) * x) * Y) :=
    Q'.mul_eqv_congr_right _ _ Y hp1
  have hp3 : (((((-p) * b) * x) * Y) * Z).eqv
      ((((tvPhase (r + 1) * b) * x) * Y) * Z) :=
    Q'.mul_eqv_congr_right _ _ Z hp2
  exact Q'.mul_eqv_congr_right _ _ w hp3

/-! ## Pascal combination at a fixed shifted index -/

/-- Positive-branch contribution written on the order-`k+1` falling shape. -/
def positivePascalTerm (m n k i j r : Nat) : Q' :=
  tvPhase r * tvBinomQ k r * tvFallQ i (k + 1 - r) *
    tvFallQ (m - i) r * tvFallQ j r * tvFallQ (n - j) (k + 1 - r)

/-- Negative-branch contribution after shifting its old index by one. -/
def negativePascalTerm (m n k i j : Nat) : Nat → Q'
  | 0 => 0
  | r + 1 =>
      tvPhase (r + 1) * tvBinomQ k r * tvFallQ i (k - r) *
        tvFallQ (m - i) (r + 1) * tvFallQ j (r + 1) *
        tvFallQ (n - j) (k - r)

private def binomFactorLHS : PolyExpr :=
  .add
    (.mul
      (.mul
        (.mul
          (.mul (.mul (.var 0) (.var 1)) (.var 3))
          (.var 4))
        (.var 5))
      (.var 6))
    (.mul
      (.mul
        (.mul
          (.mul (.mul (.var 0) (.var 2)) (.var 3))
          (.var 4))
        (.var 5))
      (.var 6))

private def binomFactorRHS : PolyExpr :=
  .mul
    (.mul
      (.mul
        (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
        (.var 4))
      (.var 5))
    (.var 6)

private theorem binomFactor_normal_eq :
    normalize binomFactorLHS = normalize binomFactorRHS := by decide

private theorem six_term_binom_congr
    (p b B x y z w : Q') (hb : b.eqv B) :
    (((((p * b) * x) * y) * z) * w).eqv
      (((((p * B) * x) * y) * z) * w) := by
  have h0 : (p * b).eqv (p * B) := Q'.mul_eqv_congr_left p _ _ hb
  have h1 := Q'.mul_eqv_congr_right _ _ x h0
  have h2 := Q'.mul_eqv_congr_right _ _ y h1
  have h3 := Q'.mul_eqv_congr_right _ _ z h2
  exact Q'.mul_eqv_congr_right _ _ w h3

private theorem six_term_add_binom
    (p b0 b1 B x y z w : Q') (hB : B.eqv (b0 + b1)) :
    (((((p * b0) * x) * y) * z) * w +
      ((((p * b1) * x) * y) * z) * w).eqv
      (((((p * B) * x) * y) * z) * w) := by
  let ρ : Nat → Q' := fun t =>
    if t = 0 then p else if t = 1 then b0 else if t = 2 then b1 else
    if t = 3 then x else if t = 4 then y else if t = 5 then z else w
  have hfactor := poly_identity_of_normal_eq binomFactorLHS binomFactorRHS
    binomFactor_normal_eq ρ
  refine Q'.eqv_trans _
    (((((p * (b0 + b1)) * x) * y) * z) * w) _
    (by simpa [binomFactorLHS, binomFactorRHS, eval, ρ] using hfactor) ?_
  exact six_term_binom_congr p (b0 + b1) B x y z w (Q'.eqv_symm hB)

/-- At every new index, the positive and shifted negative summands combine by
Pascal's recurrence to the order-`k+1` factorial summand. -/
theorem pascal_term_decomposition (m n k i j r : Nat) :
    (positivePascalTerm m n k i j r + negativePascalTerm m n k i j r).eqv
      (tvCoeffTerm m n (k + 1) i j r) := by
  cases r with
  | zero =>
      unfold positivePascalTerm negativePascalTerm tvCoeffTerm
      simp only [Nat.sub_zero]
      have hB : (tvBinomQ (k + 1) 0).eqv (tvBinomQ k 0) :=
        Q'.eqv_trans _ 1 _ (tvBinomQ_zero (k + 1))
          (Q'.eqv_symm (tvBinomQ_zero k))
      refine Q'.eqv_trans _ (positivePascalTerm m n k i j 0) _ ?_ ?_
      · change (positivePascalTerm m n k i j 0 + 0).eqv
          (positivePascalTerm m n k i j 0)
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      · unfold positivePascalTerm
        simp only [Nat.sub_zero]
        exact six_term_binom_congr _ _ _ _ _ _ _ (Q'.eqv_symm hB)
  | succ r =>
      unfold positivePascalTerm negativePascalTerm tvCoeffTerm
      have hsub : k + 1 - (r + 1) = k - r := by omega
      rw [hsub]
      have hpascal := tvBinomQ_pascal k r
      have hB : (tvBinomQ (k + 1) (r + 1)).eqv
          (tvBinomQ k (r + 1) + tvBinomQ k r) :=
        Q'.eqv_trans _ _ _ hpascal
          (Q'.add_comm_eqv (tvBinomQ k r) (tvBinomQ k (r + 1)))
      exact six_term_add_binom _ _ _ _ _ _ _ _ hB

/-! ## Exact finite-sum reindexing substrate -/

/-- Termwise semantic equality lifts through an arbitrary finite sum. -/
theorem finSum_congr (f g : Nat → Q') (h : ∀ r, (f r).eqv (g r)) :
    ∀ K, (finSum f K).eqv (finSum g K)
  | 0 => Q'.eqv_refl 0
  | K + 1 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (f K) (finSum_congr f g h K))
      (Q'.add_eqv_congr_left (finSum g K) (f K) (g K) (h K))

/-- Finite sums distribute over pointwise addition. -/
theorem finSum_add (f g : Nat → Q') :
    ∀ K, (finSum (fun r => f r + g r) K).eqv
      (finSum f K + finSum g K)
  | 0 => by
      show (0 : Q').eqv (0 + 0)
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | K + 1 => by
      show (finSum (fun r => f r + g r) K + (f K + g K)).eqv
        ((finSum f K + f K) + (finSum g K + g K))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f K + g K) (finSum_add f g K)) ?_
      exact Q'.add_swap_inner (finSum f K) (finSum g K) (f K) (g K)

/-- Peel index zero and reindex the remaining terms by successor. -/
theorem finSum_shift (f : Nat → Q') : ∀ K,
    (finSum f (K + 1)).eqv
      (f 0 + finSum (fun r => f (r + 1)) K)
  | 0 => by
      show ((0 : Q') + f 0).eqv (f 0 + 0)
      refine Q'.eqv_trans _ (f 0) _
        (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
  | K + 1 => by
      show (finSum f (K + 1) + f (K + 1)).eqv
        (f 0 + (finSum (fun r => f (r + 1)) K + f (K + 1)))
      refine Q'.eqv_trans _
        ((f 0 + finSum (fun r => f (r + 1)) K) + f (K + 1)) _
        (Q'.add_eqv_congr_right _ _ _ (finSum_shift f K)) ?_
      exact Q'.add_assoc_eqv _ _ _

/-- Pull a constant scalar into a finite sum. -/
theorem finSum_const_mul (c : Q') (f : Nat → Q') : ∀ K,
    (c * finSum f K).eqv (finSum (fun r => c * f r) K)
  | 0 => Q'.mul_zero_eqv c
  | K + 1 => by
      show (c * (finSum f K + f K)).eqv
        (finSum (fun r => c * f r) K + c * f K)
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (finSum f K) (f K)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (finSum_const_mul c f K)

private theorem six_term_zero_of_binom
    (p b x y z w : Q') (hb : b.eqv 0) :
    (((((p * b) * x) * y) * z) * w).eqv 0 := by
  have h0 : (p * b).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left p _ _ hb) (Q'.mul_zero_eqv p)
  have h1 : ((p * b) * x).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x h0) (Q'.zero_mul_eqv x)
  have h2 : (((p * b) * x) * y).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y h1) (Q'.zero_mul_eqv y)
  have h3 : ((((p * b) * x) * y) * z).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z h2) (Q'.zero_mul_eqv z)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w h3) (Q'.zero_mul_eqv w)

private theorem six_term_zero_of_first_fall
    (p b x y z w : Q') (hx : x.eqv 0) :
    (((((p * b) * x) * y) * z) * w).eqv 0 := by
  have h0 : ((p * b) * x).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (p * b) _ _ hx)
      (Q'.mul_zero_eqv (p * b))
  have h1 : (((p * b) * x) * y).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y h0) (Q'.zero_mul_eqv y)
  have h2 : ((((p * b) * x) * y) * z).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z h1) (Q'.zero_mul_eqv z)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w h2) (Q'.zero_mul_eqv w)

private theorem six_term_zero_of_third_fall
    (p b x y z w : Q') (hz : z.eqv 0) :
    (((((p * b) * x) * y) * z) * w).eqv 0 := by
  have h0 : ((((p * b) * x) * y) * z).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (((p * b) * x) * y) _ _ hz)
      (Q'.mul_zero_eqv (((p * b) * x) * y))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w h0) (Q'.zero_mul_eqv w)

private theorem tvFallQ_zero_of_pos (r : Nat) (hr : 0 < r) :
    (tvFallQ 0 r).eqv 0 := by
  unfold tvFallQ
  rw [if_neg (by omega : ¬ r ≤ 0)]
  exact Q'.eqv_refl 0

theorem positivePascalTerm_last_zero (m n k i j : Nat) :
    (positivePascalTerm m n k i j (k + 1)).eqv 0 := by
  have hchoose := tvBinomQ_eqv_choose_all k (k + 1)
  have hzero : PNPaths.choose k (k + 1) = 0 :=
    choose_zero_of_lt k (k + 1) (by omega)
  have hbin : (tvBinomQ k (k + 1)).eqv 0 := by
    rw [hzero] at hchoose
    exact Q'.eqv_trans _ _ _ hchoose Q'.ofNat_zero_eqv
  unfold positivePascalTerm
  exact six_term_zero_of_binom _ _ _ _ _ _ hbin

/-- The positive branch may be extended by its zero final Pascal cell. -/
theorem positivePascal_sum_extend (m n k i j : Nat) :
    (finSum (positivePascalTerm m n k i j) (k + 1)).eqv
      (finSum (positivePascalTerm m n k i j) (k + 2)) := by
  have hlast := positivePascalTerm_last_zero m n k i j
  refine Q'.eqv_symm ?_
  show (finSum (positivePascalTerm m n k i j) (k + 1) +
      positivePascalTerm m n k i j (k + 1)).eqv
    (finSum (positivePascalTerm m n k i j) (k + 1))
  refine Q'.eqv_trans _
    (finSum (positivePascalTerm m n k i j) (k + 1) + 0) _
    (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- With `i=0`, the entire positive Pascal branch vanishes. -/
theorem positivePascal_sum_zero_left (m n k j : Nat) :
    (finSum (positivePascalTerm m n k 0 j) (k + 2)).eqv 0 := by
  refine Q'.eqv_trans _ (finSum (fun _ => (0 : Q')) (k + 2)) _ ?_ ?_
  · apply RationalTail.finSum_eqv_congr_lt
    intro r hr
    by_cases hrk : r ≤ k
    · have hpos : 0 < k + 1 - r := by omega
      unfold positivePascalTerm
      exact six_term_zero_of_first_fall _ _ _ _ _ _
        (tvFallQ_zero_of_pos _ hpos)
    · have hre : r = k + 1 := by omega
      subst r
      exact positivePascalTerm_last_zero m n k 0 j
  · rw [RationalTail.finSum_zero_seq]
    exact Q'.eqv_refl 0

/-- With `j=0`, the entire shifted negative Pascal branch vanishes. -/
theorem negativePascal_sum_zero_right (m n k i : Nat) :
    (finSum (negativePascalTerm m n k i 0) (k + 2)).eqv 0 := by
  refine Q'.eqv_trans _ (finSum (fun _ => (0 : Q')) (k + 2)) _ ?_ ?_
  · apply RationalTail.finSum_eqv_congr_lt
    intro r _
    cases r with
    | zero => exact Q'.eqv_refl 0
    | succ r =>
        unfold negativePascalTerm
        exact six_term_zero_of_third_fall _ _ _ _ _ _
          (tvFallQ_zero_of_pos (r + 1) (by omega))
  · rw [RationalTail.finSum_zero_seq]
    exact Q'.eqv_refl 0

theorem positive_branch_sum_shift
    (m n k i j : Nat) (hi : 0 < i) :
    (finSum (fun r => Q'.ofNat (i * (n - j)) *
      tvCoeffTerm (m - 1) (n - 1) k (i - 1) j r) (k + 1)).eqv
      (finSum (positivePascalTerm m n k i j) (k + 2)) := by
  have hterms :
      (finSum (fun r => Q'.ofNat (i * (n - j)) *
        tvCoeffTerm (m - 1) (n - 1) k (i - 1) j r) (k + 1)).eqv
        (finSum (positivePascalTerm m n k i j) (k + 1)) := by
    apply RationalTail.finSum_eqv_congr_lt
    intro r hr
    have hsub : k + 1 - r = k - r + 1 := by omega
    simpa only [positivePascalTerm, hsub] using
      positive_branch_term_shift m n k i j r hi
  exact Q'.eqv_trans _ _ _ hterms (positivePascal_sum_extend m n k i j)

theorem negative_branch_sum_shift
    (m n k i j : Nat) (hj : 0 < j) :
    (finSum (fun r => (-(Q'.ofNat ((m - i) * j))) *
      tvCoeffTerm (m - 1) (n - 1) k i (j - 1) r) (k + 1)).eqv
      (finSum (negativePascalTerm m n k i j) (k + 2)) := by
  have hterms :
      (finSum (fun r => (-(Q'.ofNat ((m - i) * j))) *
        tvCoeffTerm (m - 1) (n - 1) k i (j - 1) r) (k + 1)).eqv
        (finSum (fun r => negativePascalTerm m n k i j (r + 1)) (k + 1)) := by
    apply finSum_congr
    intro r
    simpa only [negativePascalTerm] using
      negative_branch_term_shift m n k i j r hj
  have hshift := finSum_shift (negativePascalTerm m n k i j) (k + 1)
  have hshift0 :
      (finSum (negativePascalTerm m n k i j) (k + 2)).eqv
        (finSum (fun r => negativePascalTerm m n k i j (r + 1)) (k + 1)) := by
    refine Q'.eqv_trans _ _ _ hshift ?_
    change ((0 : Q') +
      finSum (fun r => negativePascalTerm m n k i j (r + 1)) (k + 1)).eqv _
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  exact Q'.eqv_trans _ _ _ hterms (Q'.eqv_symm hshift0)

/-- Summing the pointwise Pascal decomposition reconstructs the next
factorial coefficient row. -/
theorem pascal_sum_decomposition (m n k i j : Nat) :
    (finSum (positivePascalTerm m n k i j) (k + 2) +
      finSum (negativePascalTerm m n k i j) (k + 2)).eqv
      (finSum (tvCoeffTerm m n (k + 1) i j) (k + 2)) := by
  refine Q'.eqv_trans _
    (finSum (fun r => positivePascalTerm m n k i j r +
      negativePascalTerm m n k i j r) (k + 2)) _
    (Q'.eqv_symm (finSum_add _ _ (k + 2))) ?_
  exact finSum_congr _ _
    (fun r => pascal_term_decomposition m n k i j r) (k + 2)

/-- **Interior factorial-coefficient recurrence.**  The exact closed
coefficient obeys the same two-branch recurrence as the actual Cayley
transvectant for all positive monomial indices. -/
theorem transvectFactorialCoeff_succ_interior
    (m n k i j : Nat) (hi : 0 < i) (hj : 0 < j) :
    (Q'.ofNat (i * (n - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
      (-(Q'.ofNat ((m - i) * j))) *
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1)).eqv
      (transvectFactorialCoeff m n (k + 1) i j) := by
  unfold transvectFactorialCoeff
  have hpull0 := finSum_const_mul (Q'.ofNat (i * (n - j)))
    (tvCoeffTerm (m - 1) (n - 1) k (i - 1) j) (k + 1)
  have hpull1 := finSum_const_mul (-(Q'.ofNat ((m - i) * j)))
    (tvCoeffTerm (m - 1) (n - 1) k i (j - 1)) (k + 1)
  refine Q'.eqv_trans _
    (finSum (fun r => Q'.ofNat (i * (n - j)) *
        tvCoeffTerm (m - 1) (n - 1) k (i - 1) j r) (k + 1) +
      finSum (fun r => (-(Q'.ofNat ((m - i) * j))) *
        tvCoeffTerm (m - 1) (n - 1) k i (j - 1) r) (k + 1)) _
    (Q'.add_eqv_congr' hpull0 hpull1) ?_
  refine Q'.eqv_trans _
    (finSum (positivePascalTerm m n k i j) (k + 2) +
      finSum (negativePascalTerm m n k i j) (k + 2)) _
    (Q'.add_eqv_congr'
      (positive_branch_sum_shift m n k i j hi)
      (negative_branch_sum_shift m n k i j hj)) ?_
  exact pascal_sum_decomposition m n k i j

/-- Left zero-index boundary of the factorial recurrence. -/
theorem transvectFactorialCoeff_succ_left
    (m n k j : Nat) (hj : 0 < j) :
    ((-(Q'.ofNat (m * j))) *
      transvectFactorialCoeff (m - 1) (n - 1) k 0 (j - 1)).eqv
      (transvectFactorialCoeff m n (k + 1) 0 j) := by
  unfold transvectFactorialCoeff
  change ((-(Q'.ofNat (m * j))) *
      finSum (tvCoeffTerm (m - 1) (n - 1) k 0 (j - 1)) (k + 1)).eqv
    (finSum (tvCoeffTerm m n (k + 1) 0 j) (k + 2))
  have hpull := finSum_const_mul (-(Q'.ofNat (m * j)))
    (tvCoeffTerm (m - 1) (n - 1) k 0 (j - 1)) (k + 1)
  have hneg := negative_branch_sum_shift m n k 0 j hj
  have hP := positivePascal_sum_zero_left m n k j
  have hdrop :
      (finSum (positivePascalTerm m n k 0 j) (k + 2) +
        finSum (negativePascalTerm m n k 0 j) (k + 2)).eqv
        (finSum (negativePascalTerm m n k 0 j) (k + 2)) := by
    refine Q'.eqv_trans _
      ((0 : Q') + finSum (negativePascalTerm m n k 0 j) (k + 2)) _
      (Q'.add_eqv_congr_right _ _ _ hP) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  refine Q'.eqv_trans _ _ _ hpull ?_
  refine Q'.eqv_trans _ _ _ (by simpa only [Nat.zero_sub] using hneg) ?_
  refine Q'.eqv_trans _
    (finSum (positivePascalTerm m n k 0 j) (k + 2) +
      finSum (negativePascalTerm m n k 0 j) (k + 2)) _
    (Q'.eqv_symm hdrop) ?_
  exact pascal_sum_decomposition m n k 0 j

/-- Right zero-index boundary of the factorial recurrence. -/
theorem transvectFactorialCoeff_succ_right
    (m n k i : Nat) (hi : 0 < i) :
    (Q'.ofNat (i * n) *
      transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) 0).eqv
      (transvectFactorialCoeff m n (k + 1) i 0) := by
  unfold transvectFactorialCoeff
  change (Q'.ofNat (i * n) *
      finSum (tvCoeffTerm (m - 1) (n - 1) k (i - 1) 0) (k + 1)).eqv
    (finSum (tvCoeffTerm m n (k + 1) i 0) (k + 2))
  have hpull := finSum_const_mul (Q'.ofNat (i * n))
    (tvCoeffTerm (m - 1) (n - 1) k (i - 1) 0) (k + 1)
  have hpos := positive_branch_sum_shift m n k i 0 hi
  have hN := negativePascal_sum_zero_right m n k i
  have hdrop :
      (finSum (positivePascalTerm m n k i 0) (k + 2) +
        finSum (negativePascalTerm m n k i 0) (k + 2)).eqv
        (finSum (positivePascalTerm m n k i 0) (k + 2)) := by
    refine Q'.eqv_trans _
      (finSum (positivePascalTerm m n k i 0) (k + 2) + 0) _
      (Q'.add_eqv_congr_left _ _ _ hN) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  refine Q'.eqv_trans _ _ _ hpull ?_
  refine Q'.eqv_trans _ _ _ (by simpa only [Nat.sub_zero] using hpos) ?_
  refine Q'.eqv_trans _
    (finSum (positivePascalTerm m n k i 0) (k + 2) +
      finSum (negativePascalTerm m n k i 0) (k + 2)) _
    (Q'.eqv_symm hdrop) ?_
  exact pascal_sum_decomposition m n k i 0

private theorem transvectFactorialCoeff_succ_zero_zero (m n k : Nat) :
    (transvectFactorialCoeff m n (k + 1) 0 0).eqv 0 := by
  unfold transvectFactorialCoeff
  change (finSum (tvCoeffTerm m n (k + 1) 0 0) (k + 2)).eqv 0
  have hpas := pascal_sum_decomposition m n k 0 0
  have hP := positivePascal_sum_zero_left m n k 0
  have hN := negativePascal_sum_zero_right m n k 0
  refine Q'.eqv_trans _
    (finSum (positivePascalTerm m n k 0 0) (k + 2) +
      finSum (negativePascalTerm m n k 0 0) (k + 2)) _
    (Q'.eqv_symm hpas) ?_
  refine Q'.eqv_trans _ ((0 : Q') + 0) _
    (Q'.add_eqv_congr' hP hN) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- **Universal factorial-coefficient recurrence.**  The closed coefficient
obeys the Cayley two-branch recurrence also on both coordinate boundaries.
This removes the positivity side conditions from the interior formula and is
the induction interface needed to compare every order with the actual
transvectant. -/
theorem transvectFactorialCoeff_succ (m n k i j : Nat) :
    (Q'.ofNat (i * (n - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) k (i - 1) j +
      (-(Q'.ofNat ((m - i) * j))) *
        transvectFactorialCoeff (m - 1) (n - 1) k i (j - 1)).eqv
      (transvectFactorialCoeff m n (k + 1) i j) := by
  cases i with
  | zero =>
      cases j with
      | zero =>
          refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
          · apply Q'.add_eqv_congr'
            · simp only [Nat.zero_mul, Nat.zero_sub]
              change ((0 : Q') *
                transvectFactorialCoeff (m - 1) (n - 1) k 0 0).eqv 0
              exact Q'.zero_mul_eqv _
            · exact Q'.zero_mul_eqv _
          · refine Q'.eqv_trans _ 0 _ (Q'.eqv_of_eq (Q'.zero_add' 0)) ?_
            exact Q'.eqv_symm (transvectFactorialCoeff_succ_zero_zero m n k)
      | succ j =>
          refine Q'.eqv_trans _
            ((0 : Q') + (-(Q'.ofNat (m * (j + 1)))) *
              transvectFactorialCoeff (m - 1) (n - 1) k 0 j) _ ?_ ?_
          · apply Q'.add_eqv_congr'
            · simp only [Nat.zero_mul, Nat.zero_sub]
              change ((0 : Q') *
                transvectFactorialCoeff (m - 1) (n - 1) k 0 (j + 1)).eqv 0
              exact Q'.zero_mul_eqv _
            · exact Q'.eqv_refl _
          · refine Q'.eqv_trans _ _ _
              (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
            simpa only [Nat.zero_sub] using
              transvectFactorialCoeff_succ_left m n k (j + 1) (by omega)
  | succ i =>
      cases j with
      | zero =>
          refine Q'.eqv_trans _
            (Q'.ofNat ((i + 1) * n) *
              transvectFactorialCoeff (m - 1) (n - 1) k i 0 + 0) _ ?_ ?_
          · apply Q'.add_eqv_congr'
            · exact Q'.eqv_refl _
            · exact Q'.zero_mul_eqv _
          · refine Q'.eqv_trans _ _ _
              (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
            simpa only [Nat.sub_zero] using
              transvectFactorialCoeff_succ_right m n k (i + 1) (by omega)
      | succ j =>
          exact transvectFactorialCoeff_succ_interior m n k (i + 1) (j + 1)
            (by omega) (by omega)

end YMGap.Continuum.SU2TransvectantFactorialRecurrence

#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvFallQ_leading_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvBinomQ_zero
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvBinomQ_self
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvFact_mul_choose_eq_falling
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvFallingNat_mul_tailFact
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.choose_mul_factorial_den
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvBinomQ_eqv_choose
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.choose_zero_of_lt
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvBinomQ_eqv_choose_all
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvBinomQ_pascal
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvPhase_succ
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.tvFallQ_double_leading_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.scaled_six_factor_pair_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.positive_branch_term_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.negative_branch_term_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.pascal_term_decomposition
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.finSum_congr
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.finSum_add
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.finSum_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.finSum_const_mul
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.positive_branch_sum_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.negative_branch_sum_shift
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.pascal_sum_decomposition
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.transvectFactorialCoeff_succ_interior
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.transvectFactorialCoeff_succ_left
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.transvectFactorialCoeff_succ_right
#print axioms YMGap.Continuum.SU2TransvectantFactorialRecurrence.transvectFactorialCoeff_succ
