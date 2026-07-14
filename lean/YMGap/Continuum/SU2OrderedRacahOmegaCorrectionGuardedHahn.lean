/-
# Guarded Hahn discharge of the one-Omega correction

The raw correction has already been reduced exactly to guarded factorial Hahn
coefficients.  This module attacks that residual.  The first step closes the
complete off-output-shell region, leaving only the common physical output
shell for the genuine contiguous calculation.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
import YMGap.Continuum.IntRingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl
private theorem ofInt_num (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem ofInt_den (z : Int) : ((Q'.ofInt z).den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl]; ac_rfl))

local macro "ring_zero_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl]; ac_rfl))

private def firstBulkCasInt (x : Int) : Int := x * (x + 2)

private def firstBulkDiagInt (A B C D F : Int) : Int :=
  (firstBulkCasInt D - firstBulkCasInt A - firstBulkCasInt F) *
      (firstBulkCasInt F + firstBulkCasInt B - firstBulkCasInt C) -
    4 * A * B * firstBulkCasInt F

private def firstBulkScalarInt
    (A B C F P R I J L : Int) : Int :=
  (F + 2) * (J * (B - P) - L * (C - P)) *
      ((I - R) * (F - R) - R * (A - I + 1)) -
    F * (F + 2) * (I * L + (A - I) * J) -
    F * (J * (B - P + 1) - L * (C - P + 1)) *
      ((I - R) * (F - R + 1) - (R + 1) * (A - I))

/-- Exact rational scalar left after the first-bulk Hahn rows are factored. -/
def firstBulkScalarQ
    (a b c f p r i j l : Nat) : Q' :=
  let F := Q'.ofNat f
  let R := Q'.ofNat r
  let I := Q'.ofNat i
  let J := Q'.ofNat j
  let L := Q'.ofNat l
  ((F + Q'.ofNat 2) *
      (J * Q'.ofNat (b - p) + -(L * Q'.ofNat (c - p))) *
      (Q'.ofNat (i - r) * Q'.ofNat (f - r) +
        -(R * Q'.ofNat (a - i + 1))) +
    -(F * (F + Q'.ofNat 2) *
      (I * L + Q'.ofNat (a - i) * J))) +
    -(F *
      (J * Q'.ofNat (b - p + 1) + -(L * Q'.ofNat (c - p + 1))) *
      (Q'.ofNat (i - r) * Q'.ofNat (f - r + 1) +
        -(Q'.ofNat (r + 1) * Q'.ofNat (a - i))))

private abbrev FBPE := YMGap.Continuum.RingNormaliser.PolyExpr
private def fbv (n : Nat) : FBPE := .var n
private def fbc (z : Int) : FBPE := .const z
private def fba (x y : FBPE) : FBPE := .add x y
private def fbm (x y : FBPE) : FBPE := .mul x y
private def fbn (x : FBPE) : FBPE := .neg x
private def fbs (x y : FBPE) : FBPE := fba x (fbn y)
private def fbA : FBPE := fbv 0
private def fbB : FBPE := fbv 1
private def fbF : FBPE := fbv 2
private def fbP : FBPE := fbv 3
private def fbR : FBPE := fbv 4
private def fbI : FBPE := fbv 5
private def fbJ : FBPE := fbv 6
private def fbC : FBPE := fbs (fba (fbm (fbc 2) fbP) fbF) fbB
private def fbD : FBPE := fbs (fba fbA fbF) (fbm (fbc 2) fbR)
private def fbL : FBPE := fbs fbP fbJ
private def fbCas (x : FBPE) : FBPE := fbm x (fba x (fbc 2))
private def fbDiag (A B C D F : FBPE) : FBPE :=
  fbs (fbm (fbs (fbs (fbCas D) (fbCas A)) (fbCas F))
    (fbs (fba (fbCas F) (fbCas B)) (fbCas C)))
    (fbm (fbm (fbm (fbc 4) A) B) (fbCas F))
private def fbScalar : FBPE :=
  fbs
    (fbs
      (fbm (fbm (fba fbF (fbc 2))
        (fbs (fbm fbJ (fbs fbB fbP)) (fbm fbL (fbs fbC fbP))))
        (fbs (fbm (fbs fbI fbR) (fbs fbF fbR))
          (fbm fbR (fba (fbs fbA fbI) (fbc 1)))))
      (fbm (fbm fbF (fba fbF (fbc 2)))
        (fba (fbm fbI fbL) (fbm (fbs fbA fbI) fbJ))))
    (fbm (fbm fbF
      (fbs (fbm fbJ (fba (fbs fbB fbP) (fbc 1)))
        (fbm fbL (fba (fbs fbC fbP) (fbc 1)))))
      (fbs (fbm (fbs fbI fbR) (fba (fbs fbF fbR) (fbc 1)))
        (fbm (fba fbR (fbc 1)) (fbs fbA fbI))))
private def fbDiagLHS : FBPE :=
  fbm fbP (fbs (fbDiag fbA fbB fbC fbD fbF)
    (fbDiag fbA (fbs fbB (fbc 1)) (fbs fbC (fbc 1)) fbD fbF))
private def fbDiagRHS : FBPE := fbm (fbc 8) fbScalar

private theorem fbDiag_normal :
    YMGap.Continuum.RingNormaliser.normalize fbDiagLHS =
      YMGap.Continuum.RingNormaliser.normalize fbDiagRHS := by decide

private theorem firstBulk_diagonal_polynomial
    (A B F P R I J : Int) :
    let C := 2 * P + F - B
    let D := A + F - 2 * R
    let L := P - J
    P * (firstBulkDiagInt A B C D F -
      firstBulkDiagInt A (B - 1) (C - 1) D F) =
        8 * firstBulkScalarInt A B C F P R I J L := by
  have h := YMGap.Continuum.IntRingNormaliser.poly_identity_of_normal_eq
    fbDiagLHS fbDiagRHS fbDiag_normal
    (fun n => if n = 0 then A else if n = 1 then B else
      if n = 2 then F else if n = 3 then P else if n = 4 then R else
      if n = 5 then I else J)
  simpa [fbDiagLHS, fbDiagRHS, fbScalar, fbDiag, fbCas, fbA, fbB, fbC,
    fbD, fbF, fbP, fbR, fbI, fbJ, fbL, fbv, fbc, fba, fbm, fbn, fbs,
    YMGap.Continuum.IntRingNormaliser.eval, firstBulkDiagInt,
    firstBulkCasInt, firstBulkScalarInt, Int.sub_eq_add_neg] using h

private theorem mul_eqv_congr {a b c d : Q'}
    (ha : a ≈ c) (hb : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

private theorem unit_six_collapse (A B : Q') :
    (1 : Q') * 1 * A * 1 * 1 * B ≈ A * B := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.one_mul, Int.mul_one]

private theorem finSum_eqv_first_two (f : Nat → Q') : ∀ M,
    (∀ r, r < M + 2 → 2 ≤ r → f r ≈ 0) →
      RationalTail.finSum f (M + 2) ≈ f 0 + f 1
  | 0, _ => by
      change ((0 : Q') + f 0) + f 1 ≈ f 0 + f 1
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' (f 0)))
  | M + 1, hzero => by
      change RationalTail.finSum f (M + 2) + f (M + 2) ≈ f 0 + f 1
      refine Q'.eqv_trans _ ((f 0 + f 1) + 0) _
        (Q'.add_eqv_congr'
          (finSum_eqv_first_two f M (fun r hr h2 =>
            hzero r (by omega) h2))
          (hzero (M + 2) (by omega) (by omega))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (f 0 + f 1))

private theorem finSum_eqv_two (f : Nat → Q') : ∀ N u v,
    u < v → v < N →
      (∀ r, r < N → r ≠ u → r ≠ v → f r ≈ 0) →
      RationalTail.finSum f N ≈ f u + f v
  | 0, _, _, _, hv, _ => by omega
  | N + 1, u, v, huv, hv, hzero => by
      by_cases hvtop : v = N
      · subst v
        change RationalTail.finSum f N + f N ≈ f u + f N
        exact Q'.add_eqv_congr_right _ _ _
          (finSum_eqv_single f N u (by omega)
            (fun r hr hru => hzero r (by omega) hru (by omega)))
      · change RationalTail.finSum f N + f N ≈ f u + f v
        refine Q'.eqv_trans _ ((f u + f v) + 0) _
          (Q'.add_eqv_congr'
            (finSum_eqv_two f N u v huv (by omega)
              (fun r hr hru hrv => hzero r (by omega) hru hrv))
            (hzero N (by omega) (by omega) (by omega))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' (f u + f v))

private theorem pnChoose_one : ∀ n : Nat, PNPaths.choose n 1 = n
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose, pnChoose_one]
      omega

private theorem tvBinomQ_one (k : Nat) :
    tvBinomQ k 1 ≈ Q'.ofNat k := by
  simpa only [pnChoose_one] using tvBinomQ_eqv_choose_all k 1

private theorem second_one_term_zero_above
    (m n k i r : Nat) (hr : 2 ≤ r) :
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
        tvFallQ (m - i) r * tvFallQ 1 r *
        tvFallQ (n - 1) (k - r) ≈ 0 := by
  have hz := tvFallQ_eqv_zero_of_lt 1 r (by omega)
  let A := tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
    tvFallQ (m - i) r
  have h0 : A * tvFallQ 1 r ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  exact Q'.eqv_trans _ (0 * tvFallQ (n - 1) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)

private theorem second_one_term_zero_closed (m n k i : Nat) :
    tvPhase 0 * tvBinomQ k 0 * tvFallQ i k *
        tvFallQ (m - i) 0 * tvFallQ 1 0 * tvFallQ (n - 1) k ≈
      tvFallQ i k * tvFallQ (n - 1) k := by
  have hp : tvPhase 0 ≈ 1 := by decide
  have hb := tvBinomQ_zero k
  have hm := tvFallQ_zero (m - i)
  have h1 := tvFallQ_zero 1
  exact Q'.eqv_trans _
    ((1 : Q') * 1 * tvFallQ i k * 1 * 1 * tvFallQ (n - 1) k) _
    (mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (mul_eqv_congr hp hb) (Q'.eqv_refl _)) hm) h1)
      (Q'.eqv_refl _))
    (unit_six_collapse _ _)

private theorem second_one_term_one_closed (m n k i : Nat) :
    tvPhase 1 * tvBinomQ k 1 * tvFallQ i (k - 1) *
        tvFallQ (m - i) 1 * tvFallQ 1 1 *
        tvFallQ (n - 1) (k - 1) ≈
      -(Q'.ofNat k * tvFallQ i (k - 1) * Q'.ofNat (m - i) *
        tvFallQ (n - 1) (k - 1)) := by
  have hp : tvPhase 1 ≈ -(1 : Q') := by decide
  have hb := tvBinomQ_one k
  have hm := tvFallQ_one (m - i)
  have h1 := tvFallQ_one 1
  let X := tvFallQ i (k - 1)
  let Y := tvFallQ (n - 1) (k - 1)
  have hprod :
      tvPhase 1 * tvBinomQ k 1 * X * tvFallQ (m - i) 1 *
          tvFallQ 1 1 * Y ≈
        (-(1 : Q')) * Q'.ofNat k * X * Q'.ofNat (m - i) *
          Q'.ofNat 1 * Y :=
    mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (mul_eqv_congr hp hb) (Q'.eqv_refl X)) hm) h1)
      (Q'.eqv_refl Y)
  refine Q'.eqv_trans _
    ((-(1 : Q')) * Q'.ofNat k * tvFallQ i (k - 1) *
      Q'.ofNat (m - i) * Q'.ofNat 1 * tvFallQ (n - 1) (k - 1)) _
    (by simpa only [X, Y] using hprod) ?_
  ring_qeqv

/-- Closed two-term row with second monomial index one. -/
theorem transvectFactorialCoeff_second_one_closed
    (m n k i : Nat) :
    transvectFactorialCoeff m n k i 1 ≈
      tvFallQ i k * tvFallQ (n - 1) k +
        -(Q'.ofNat k * tvFallQ i (k - 1) * Q'.ofNat (m - i) *
          tvFallQ (n - 1) (k - 1)) := by
  cases k with
  | zero =>
      have hcoeff := transvectFactorialCoeff_zero m n i 1
      have hi0 := tvFallQ_zero i
      have hn0 := tvFallQ_zero (n - 1)
      have hmain : tvFallQ i 0 * tvFallQ (n - 1) 0 ≈ (1 : Q') * 1 :=
        mul_eqv_congr hi0 hn0
      have hz0 : Q'.ofNat 0 * tvFallQ i 0 ≈ 0 :=
        Q'.eqv_trans _ ((0 : Q') * tvFallQ i 0) _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv _)
      have hz1 : (Q'.ofNat 0 * tvFallQ i 0) * Q'.ofNat (m - i) ≈ 0 :=
        Q'.eqv_trans _ (0 * Q'.ofNat (m - i)) _
          (Q'.mul_eqv_congr_right _ _ _ hz0) (Q'.zero_mul_eqv _)
      have hz2 : Q'.ofNat 0 * tvFallQ i 0 * Q'.ofNat (m - i) *
          tvFallQ (n - 1) 0 ≈ 0 :=
        Q'.eqv_trans _ (0 * tvFallQ (n - 1) 0) _
          (Q'.mul_eqv_congr_right _ _ _ hz1) (Q'.zero_mul_eqv _)
      refine Q'.eqv_trans _ 1 _ hcoeff (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _ ((1 : Q') * 1 + -(0 : Q')) _ ?_ ?_
      · exact Q'.add_eqv_congr' hmain (Q'.neg_eqv_congr _ _ hz2)
      · ring_zero_qeqv
  | succ k =>
      unfold transvectFactorialCoeff
      have hsum := finSum_eqv_first_two
        (fun r => tvPhase r * tvBinomQ (k + 1) r *
          tvFallQ i (k + 1 - r) * tvFallQ (m - i) r * tvFallQ 1 r *
          tvFallQ (n - 1) (k + 1 - r)) k
        (fun r hr h2 => second_one_term_zero_above m n (k + 1) i r h2)
      have hterms := Q'.add_eqv_congr'
        (second_one_term_zero_closed m n (k + 1) i)
        (second_one_term_one_closed m n (k + 1) i)
      simpa only [Nat.sub_zero, show k + 1 - 1 = k by omega] using
        Q'.eqv_trans _ _ _ hsum hterms

/-- Multiplication by the omitted trailing factor advances a supported
falling factorial. -/
theorem tvFallQ_trailing_shift (n r : Nat) (hr : r + 1 ≤ n) :
    tvFallQ n r * Q'.ofNat (n - r) ≈ tvFallQ n (r + 1) := by
  have h0 := tvFallQ_eqv_fallingNat n r (by omega)
  have h1 := tvFallQ_eqv_fallingNat n (r + 1) hr
  refine Q'.eqv_trans _
    (Q'.ofNat (tvFallingNat n r) * Q'.ofNat (n - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (tvFallingNat n r * (n - r))) _
    (ofNat_mul_eqv _ _) ?_
  change Q'.ofNat (tvFallingNat n (r + 1)) ≈ _
  exact Q'.eqv_symm h1

private theorem tvFallQ_pred_endpoint (n : Nat) (hn : 0 < n) :
    tvFallQ n (n - 1) ≈
      Q'.ofNat n * tvFallQ (n - 1) (n - 1) := by
  have ht := tvFallQ_trailing_shift n (n - 1) (by omega)
  have ht' : tvFallQ n (n - 1) * Q'.ofNat 1 ≈ tvFallQ n n := by
    simpa only [show n - (n - 1) = 1 by omega,
      show n - 1 + 1 = n by omega] using ht
  have hlead := tvFallQ_leading_shift n (n - 1)
  refine Q'.eqv_trans _ (tvFallQ n (n - 1) * Q'.ofNat 1) _ ?_ ?_
  · refine Q'.eqv_trans _ (tvFallQ n (n - 1) * 1) _
      (Q'.eqv_symm (Q'.mul_one_eqv _)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_trans _ _ _ ht' (Q'.eqv_symm (by
      simpa only [show n - 1 + 1 = n by omega] using hlead))

/-- Factored second-index-one row in the strict supported interior. -/
theorem transvectFactorialCoeff_second_one_factored
    (m n k i : Nat) (hk : 0 < k) (hki : k ≤ i) (hkn : k < n) :
    transvectFactorialCoeff m n k i 1 ≈
      (tvFallQ i (k - 1) * tvFallQ (n - 1) (k - 1)) *
        (Q'.ofNat (i - k + 1) * Q'.ofNat (n - k) +
          -(Q'.ofNat k * Q'.ofNat (m - i))) := by
  have hclosed := transvectFactorialCoeff_second_one_closed m n k i
  have hishift := tvFallQ_trailing_shift i (k - 1) (by omega)
  have hishift' :
      tvFallQ i (k - 1) * Q'.ofNat (i - k + 1) ≈ tvFallQ i k := by
    simpa only [show i - (k - 1) = i - k + 1 by omega,
      show k - 1 + 1 = k by omega] using hishift
  have hnshift := tvFallQ_trailing_shift (n - 1) (k - 1) (by omega)
  have hnshift' :
      tvFallQ (n - 1) (k - 1) * Q'.ofNat (n - k) ≈
        tvFallQ (n - 1) k := by
    simpa only [show n - 1 - (k - 1) = n - k by omega,
      show k - 1 + 1 = k by omega] using hnshift
  refine Q'.eqv_trans _ _ _ hclosed ?_
  refine Q'.eqv_trans _
    ((tvFallQ i (k - 1) * Q'.ofNat (i - k + 1)) *
        (tvFallQ (n - 1) (k - 1) * Q'.ofNat (n - k)) +
      -(Q'.ofNat k * tvFallQ i (k - 1) * Q'.ofNat (m - i) *
        tvFallQ (n - 1) (k - 1))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_eqv_congr (Q'.eqv_symm hishift') (Q'.eqv_symm hnshift'))
      (Q'.eqv_refl _)
  · ring_qeqv

private theorem tvFallQ_label_shift (n r : Nat) (hr : r + 1 ≤ n) :
    Q'.ofNat n * tvFallQ (n - 1) r ≈
      Q'.ofNat (n - r) * tvFallQ n r := by
  refine Q'.eqv_trans _ (tvFallQ n (r + 1)) _
    (tvFallQ_leading_shift n r) ?_
  refine Q'.eqv_trans _ (tvFallQ n r * Q'.ofNat (n - r)) _
    (Q'.eqv_symm (tvFallQ_trailing_shift n r hr)) ?_
  exact Q'.mul_comm_eqv _ _

private theorem pair_scale_rearrange (A B P X Y : Q') :
    (A * B) * (P * X * Y) ≈ P * (A * X) * (B * Y) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

private theorem two_by_two_rearrange (A B X Y : Q') :
    (A * B) * (X * Y) ≈ (A * X) * (B * Y) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

private theorem lowest_term_zero_above
    (m n k j l r : Nat) (hlr : l < r) :
    tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
        tvFallQ (m - j) r * tvFallQ l r * tvFallQ (n - l) (k - r) ≈
      0 := by
  have hz := tvFallQ_eqv_zero_of_lt l r hlr
  let A := tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
    tvFallQ (m - j) r
  have h0 : A * tvFallQ l r ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  exact Q'.eqv_trans _ (0 * tvFallQ (n - l) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)

private theorem lowest_term_zero_below
    (m n k j l r : Nat) (hsum : j + l = k) (hrl : r < l) :
    tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
        tvFallQ (m - j) r * tvFallQ l r * tvFallQ (n - l) (k - r) ≈
      0 := by
  have hz : tvFallQ j (k - r) ≈ 0 :=
    tvFallQ_eqv_zero_of_lt j (k - r) (by omega)
  let A := tvPhase r * tvBinomQ k r
  have h0 : A * tvFallQ j (k - r) ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  have h1 : (A * tvFallQ j (k - r)) * tvFallQ (m - j) r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (m - j) r) _
      (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
  have h2 :
      ((A * tvFallQ j (k - r)) * tvFallQ (m - j) r) *
          tvFallQ l r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ l r) _
      (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ (0 * tvFallQ (n - l) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.zero_mul_eqv _)

private theorem one_above_lowest_term_zero_below
    (m n k j l r : Nat) (hsum : j + l = k + 1)
    (hrl : r < l - 1) :
    tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
        tvFallQ (m - j) r * tvFallQ l r *
        tvFallQ (n - l) (k - r) ≈ 0 := by
  have hz : tvFallQ j (k - r) ≈ 0 :=
    tvFallQ_eqv_zero_of_lt j (k - r) (by omega)
  let A := tvPhase r * tvBinomQ k r
  have h0 : A * tvFallQ j (k - r) ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  have h1 : (A * tvFallQ j (k - r)) * tvFallQ (m - j) r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (m - j) r) _
      (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
  have h2 :
      ((A * tvFallQ j (k - r)) * tvFallQ (m - j) r) *
          tvFallQ l r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ l r) _
      (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ (0 * tvFallQ (n - l) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.zero_mul_eqv _)

/-- A row one shell above its lowest support has exactly the two summands
at indices `l-1` and `l`. -/
theorem transvectFactorialCoeff_one_above_lowest_two_term
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) :
    transvectFactorialCoeff m n k j l ≈
      (tvPhase (l - 1) * tvBinomQ k (l - 1) *
          tvFallQ j (k - (l - 1)) * tvFallQ (m - j) (l - 1) *
          tvFallQ l (l - 1) * tvFallQ (n - l) (k - (l - 1))) +
        (tvPhase l * tvBinomQ k l * tvFallQ j (k - l) *
          tvFallQ (m - j) l * tvFallQ l l *
          tvFallQ (n - l) (k - l)) := by
  unfold transvectFactorialCoeff
  apply finSum_eqv_two _ (k + 1) (l - 1) l (by omega) (by omega)
  intro r hr hru hrv
  by_cases hbelow : r < l - 1
  · exact one_above_lowest_term_zero_below m n k j l r hsum hbelow
  · exact lowest_term_zero_above m n k j l r (by omega)

private theorem one_above_lowest_first_term_closed
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) (hkn : k + 1 ≤ n) :
    tvPhase (l - 1) * tvBinomQ k (l - 1) *
        tvFallQ j (k - (l - 1)) * tvFallQ (m - j) (l - 1) *
        tvFallQ l (l - 1) * tvFallQ (n - l) (k - (l - 1)) ≈
      (tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k)) := by
  have hcomp : k - (l - 1) = j := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k (l - 1) (by omega)
  have hcancel' :
      tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
          tvFallQ j j ≈ Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hlend := tvFallQ_pred_endpoint l hl
  have hnshift := tvFallQ_trailing_shift (n - l) (j - 1) (by omega)
  have hnshift' :
      tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k) ≈
        tvFallQ (n - l) j := by
    simpa only [show n - l - (j - 1) = n - k by omega,
      show j - 1 + 1 = j by omega] using hnshift
  rw [hcomp]
  refine Q'.eqv_trans _
    (tvPhase (l - 1) * tvBinomQ k (l - 1) * tvFallQ j j *
      tvFallQ (m - j) (l - 1) *
      (Q'.ofNat l * tvFallQ (l - 1) (l - 1)) *
      (tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k))) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr (Q'.eqv_refl _) hlend)
      (Q'.eqv_symm hnshift')
  · refine Q'.eqv_trans _
      ((tvPhase (l - 1) *
          (tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
            tvFallQ j j) * tvFallQ (m - j) (l - 1) *
          tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k))) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hcancel')))

private theorem one_above_lowest_second_term_closed
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) (hkm : k + 1 ≤ m) :
    tvPhase l * tvBinomQ k l * tvFallQ j (k - l) *
        tvFallQ (m - j) l * tvFallQ l l *
        tvFallQ (n - l) (k - l) ≈
      -((tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat j * Q'.ofNat (m - k))) := by
  have hcomp : k - l = j - 1 := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k l (by omega)
  have hcancel' :
      tvBinomQ k l * tvFallQ l l * tvFallQ (j - 1) (j - 1) ≈
        Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hphase := tvPhase_succ (l - 1)
  have hphase' : tvPhase l ≈ -(tvPhase (l - 1)) := by
    simpa only [show l - 1 + 1 = l by omega] using hphase
  have hjend := tvFallQ_pred_endpoint j hj
  have hmshift := tvFallQ_trailing_shift (m - j) (l - 1) (by omega)
  have hmshift' :
      tvFallQ (m - j) (l - 1) * Q'.ofNat (m - k) ≈
        tvFallQ (m - j) l := by
    simpa only [show m - j - (l - 1) = m - k by omega,
      show l - 1 + 1 = l by omega] using hmshift
  rw [hcomp]
  refine Q'.eqv_trans _
    (-(tvPhase (l - 1)) * tvBinomQ k l *
      (Q'.ofNat j * tvFallQ (j - 1) (j - 1)) *
      (tvFallQ (m - j) (l - 1) * Q'.ofNat (m - k)) *
      tvFallQ l l * tvFallQ (n - l) (j - 1)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr hphase' (Q'.eqv_refl _)) hjend)
          (Q'.eqv_symm hmshift'))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (-((tvPhase (l - 1) *
          (tvBinomQ k l * tvFallQ l l *
            tvFallQ (j - 1) (j - 1)) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat j * Q'.ofNat (m - k)))) _ (by ring_qeqv) ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hcancel'))))

/-- Closed row one shell above lowest support.  The two surviving summands
factor into the common lowest-row product and one signed linear factor. -/
theorem transvectFactorialCoeff_one_above_lowest_closed
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) (hkm : k + 1 ≤ m) (hkn : k + 1 ≤ n) :
    transvectFactorialCoeff m n k j l ≈
      (tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k) +
          -(Q'.ofNat j * Q'.ofNat (m - k))) := by
  have htwo := transvectFactorialCoeff_one_above_lowest_two_term
    m n k j l hj hl hsum
  have hfirst := one_above_lowest_first_term_closed
    m n k j l hj hl hsum hkn
  have hsecond := one_above_lowest_second_term_closed
    m n k j l hj hl hsum hkm
  refine Q'.eqv_trans _ _ _ htwo ?_
  refine Q'.eqv_trans _
    ((tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k)) +
      -((tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat j * Q'.ofNat (m - k)))) _
    (Q'.add_eqv_congr' hfirst hsecond) ?_
  ring_qeqv

private theorem lowest_six_factor_reorder (p x A Y B Z : Q') :
    p * x * A * Y * B * Z ≈ p * (x * B * A) * Y * Z := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Closed lowest-output Hahn row.  This is the complement of the existing
highest-row formula and is the exact row exposed at the lower support face of
the Omega correction. -/
theorem transvectFactorialCoeff_lowest_row_closed
    (m n k j l : Nat) (hsum : j + l = k) :
    transvectFactorialCoeff m n k j l ≈
      tvPhase l * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
        tvFallQ (n - l) j := by
  unfold transvectFactorialCoeff
  have hsingle := finSum_eqv_single
    (fun r => tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
      tvFallQ (m - j) r * tvFallQ l r *
      tvFallQ (n - l) (k - r))
    (k + 1) l (by omega)
    (fun r hr hne => by
      rcases Nat.lt_or_gt_of_ne hne with hrl | hlr
      · exact lowest_term_zero_below m n k j l r hsum hrl
      · exact lowest_term_zero_above m n k j l r hlr)
  have hreorder := lowest_six_factor_reorder
    (tvPhase l) (tvBinomQ k l) (tvFallQ j (k - l))
    (tvFallQ (m - j) l) (tvFallQ l l) (tvFallQ (n - l) (k - l))
  have hcancel := tvBinomQ_mul_endpoint_factorials k l (by omega)
  have hcancel' :
      tvBinomQ k l * tvFallQ l l * tvFallQ j j ≈
        Q'.ofNat (tvFact k) := by
    simpa only [show k - l = j by omega] using hcancel
  have hclosed :
      tvPhase l * (tvBinomQ k l * tvFallQ l l * tvFallQ j j) *
          tvFallQ (m - j) l * tvFallQ (n - l) j ≈
        tvPhase l * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
          tvFallQ (n - l) j :=
    Q'.mul_eqv_congr_right _ _ (tvFallQ (n - l) j)
      (Q'.mul_eqv_congr_right _ _ (tvFallQ (m - j) l)
        (Q'.mul_eqv_congr_left (tvPhase l) _ _ hcancel'))
  refine Q'.eqv_trans _ _ _ hsingle ?_
  change tvPhase l * tvBinomQ k l * tvFallQ j (k - l) *
      tvFallQ (m - j) l * tvFallQ l l * tvFallQ (n - l) (k - l) ≈ _
  have hreorder' := hreorder
  rw [show k - l = j by omega] at hreorder' ⊢
  exact Q'.eqv_trans _ _ _ hreorder' hclosed

/-- First predecessor on a lowest row, with all factorial scaling cleared. -/
theorem lowest_row_first_predecessor_scaled
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k) (hkm : k ≤ m) (hkn : k ≤ n) :
    (Q'.ofNat k * Q'.ofNat (m - j)) *
        transvectFactorialCoeff (m - 1) (n - 1) (k - 1) j (l - 1) ≈
      -(transvectFactorialCoeff m n k j l) := by
  have hred := transvectFactorialCoeff_lowest_row_closed
    (m - 1) (n - 1) (k - 1) j (l - 1) (by omega)
  have hfull := transvectFactorialCoeff_lowest_row_closed m n k j l hsum
  have hphase := tvPhase_succ (l - 1)
  have hphase' : tvPhase l ≈ -(tvPhase (l - 1)) := by
    simpa only [show l - 1 + 1 = l by omega] using hphase
  have hphaseBack : tvPhase (l - 1) ≈ -(tvPhase l) := by
    have hneg := Q'.neg_eqv_congr _ _ hphase'
    exact Q'.eqv_symm (Q'.eqv_trans _ (-(-(tvPhase (l - 1)))) _ hneg
      (Q'.neg_neg_eqv _))
  have hfact : Q'.ofNat k * Q'.ofNat (tvFact (k - 1)) ≈
      Q'.ofNat (tvFact k) := by
    rw [show tvFact k = k * tvFact (k - 1) by
      cases k <;> simp_all [tvFact]]
    exact ofNat_mul_eqv k (tvFact (k - 1))
  have hmshift := tvFallQ_leading_shift (m - j) (l - 1)
  have hmshift' :
      Q'.ofNat (m - j) * tvFallQ ((m - 1) - j) (l - 1) ≈
        tvFallQ (m - j) l := by
    simpa only [show (m - 1) - j = m - j - 1 by omega,
      show l - 1 + 1 = l by omega] using hmshift
  refine Q'.eqv_trans _
    ((Q'.ofNat k * Q'.ofNat (m - j)) *
      (tvPhase (l - 1) * Q'.ofNat (tvFact (k - 1)) *
        tvFallQ ((m - 1) - j) (l - 1) *
        tvFallQ ((n - 1) - (l - 1)) j)) _
    (Q'.mul_eqv_congr_left _ _ _ hred) ?_
  refine Q'.eqv_trans _
    (-(tvPhase l) * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
      tvFallQ (n - l) j) _ ?_ ?_
  · rw [show (n - 1) - (l - 1) = n - l by omega]
    refine Q'.eqv_trans _
      ((Q'.ofNat k * Q'.ofNat (m - j)) *
        (-(tvPhase l) * Q'.ofNat (tvFact (k - 1)) *
          tvFallQ ((m - 1) - j) (l - 1) * tvFallQ (n - l) j)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hphaseBack)))) ?_
    refine Q'.eqv_trans _
      (-(tvPhase l) *
        (Q'.ofNat k * Q'.ofNat (tvFact (k - 1))) *
        (Q'.ofNat (m - j) * tvFallQ ((m - 1) - j) (l - 1)) *
        tvFallQ (n - l) j) _ (by ring_qeqv) ?_
    exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr (Q'.eqv_refl _) hfact) hmshift')
      (Q'.eqv_refl _)
  · have hassoc :
        -(tvPhase l) * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
            tvFallQ (n - l) j ≈
          -(tvPhase l * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
            tvFallQ (n - l) j) := by
        refine Q'.eqv_trans _
          (-(tvPhase l * Q'.ofNat (tvFact k)) * tvFallQ (m - j) l *
            tvFallQ (n - l) j) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.neg_mul_eqv _ _))
        · refine Q'.eqv_trans _
            (-(tvPhase l * Q'.ofNat (tvFact k) * tvFallQ (m - j) l) *
              tvFallQ (n - l) j) _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_mul_eqv _ _)) ?_
          exact Q'.neg_mul_eqv _ _
    exact Q'.eqv_trans _ _ _ hassoc
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hfull))

/-- Second predecessor on a lowest row, with all factorial scaling cleared. -/
theorem lowest_row_second_predecessor_scaled
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k) (hkm : k ≤ m) (hkn : k ≤ n) :
    (Q'.ofNat k * Q'.ofNat (n - l)) *
        transvectFactorialCoeff (m - 1) (n - 1) (k - 1) (j - 1) l ≈
      transvectFactorialCoeff m n k j l := by
  have hred := transvectFactorialCoeff_lowest_row_closed
    (m - 1) (n - 1) (k - 1) (j - 1) l (by omega)
  have hfull := transvectFactorialCoeff_lowest_row_closed m n k j l hsum
  have hfact : Q'.ofNat k * Q'.ofNat (tvFact (k - 1)) ≈
      Q'.ofNat (tvFact k) := by
    rw [show tvFact k = k * tvFact (k - 1) by
      cases k <;> simp_all [tvFact]]
    exact ofNat_mul_eqv k (tvFact (k - 1))
  have hnshift := tvFallQ_leading_shift (n - l) (j - 1)
  have hnshift' :
      Q'.ofNat (n - l) * tvFallQ ((n - 1) - l) (j - 1) ≈
        tvFallQ (n - l) j := by
    simpa only [show (n - 1) - l = n - l - 1 by omega,
      show j - 1 + 1 = j by omega] using hnshift
  refine Q'.eqv_trans _
    ((Q'.ofNat k * Q'.ofNat (n - l)) *
      (tvPhase l * Q'.ofNat (tvFact (k - 1)) *
        tvFallQ ((m - 1) - (j - 1)) l *
        tvFallQ ((n - 1) - l) (j - 1))) _
    (Q'.mul_eqv_congr_left _ _ _ hred) ?_
  refine Q'.eqv_trans _
    (tvPhase l * (Q'.ofNat k * Q'.ofNat (tvFact (k - 1))) *
      tvFallQ (m - j) l *
      (Q'.ofNat (n - l) * tvFallQ ((n - 1) - l) (j - 1))) _ ?_ ?_
  · rw [show (m - 1) - (j - 1) = m - j by omega]
    ring_qeqv
  · exact Q'.eqv_trans _
      (tvPhase l * Q'.ofNat (tvFact k) * tvFallQ (m - j) l *
        tvFallQ (n - l) j) _
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (Q'.eqv_refl _) hfact) (Q'.eqv_refl _)) hnshift')
      (Q'.eqv_symm hfull)

/-- Division-free bridge from the row one shell above lowest support to the
adjacent lowest row. -/
theorem one_above_lowest_scaled_to_lowest
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) (hkm : k + 1 ≤ m) (hkn : k + 1 ≤ n) :
    (Q'.ofNat (k + 1) * (Q'.ofNat (m - k) * Q'.ofNat (n - k))) *
        transvectFactorialCoeff m n k j l ≈
      (Q'.ofNat j * Q'.ofNat (m - k) +
          -(Q'.ofNat l * Q'.ofNat (n - k))) *
        transvectFactorialCoeff m n (k + 1) j l := by
  let P := Q'.ofNat (k + 1)
  let U := Q'.ofNat (m - k)
  let V := Q'.ofNat (n - k)
  let J := Q'.ofNat j
  let L := Q'.ofNat l
  let A := tvFallQ (m - j) (l - 1)
  let B := tvFallQ (n - l) (j - 1)
  let R := tvPhase (l - 1) * Q'.ofNat (tvFact k) * A * B
  have habove := transvectFactorialCoeff_one_above_lowest_closed
    m n k j l hj hl hsum hkm hkn
  have habove' : transvectFactorialCoeff m n k j l ≈
      R * (L * V + -(J * U)) := by
    simpa only [P, U, V, J, L, A, B, R] using habove
  have hlow := transvectFactorialCoeff_lowest_row_closed
    m n (k + 1) j l hsum
  have hphase := tvPhase_succ (l - 1)
  have hphase' : tvPhase l ≈ -(tvPhase (l - 1)) := by
    simpa only [show l - 1 + 1 = l by omega] using hphase
  have hfact : Q'.ofNat (tvFact (k + 1)) ≈
      P * Q'.ofNat (tvFact k) := by
    rw [show tvFact (k + 1) = (k + 1) * tvFact k by rfl]
    have hmul := ofNat_mul_eqv (k + 1) (tvFact k)
    exact Q'.eqv_symm (by simpa only [P] using hmul)
  have hmshift := tvFallQ_trailing_shift (m - j) (l - 1) (by omega)
  have hmshift' : A * U ≈ tvFallQ (m - j) l := by
    simpa only [A, U, show m - j - (l - 1) = m - k by omega,
      show l - 1 + 1 = l by omega] using hmshift
  have hnshift := tvFallQ_trailing_shift (n - l) (j - 1) (by omega)
  have hnshift' : B * V ≈ tvFallQ (n - l) j := by
    simpa only [B, V, show n - l - (j - 1) = n - k by omega,
      show j - 1 + 1 = j by omega] using hnshift
  have hlow' : transvectFactorialCoeff m n (k + 1) j l ≈
      -(R * (P * (U * V))) := by
    refine Q'.eqv_trans _ _ _ hlow ?_
    refine Q'.eqv_trans _
      (-(tvPhase (l - 1)) * (P * Q'.ofNat (tvFact k)) *
        (A * U) * (B * V)) _ ?_ ?_
    · exact mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr hphase' hfact) (Q'.eqv_symm hmshift'))
        (Q'.eqv_symm hnshift')
    · simp only [R]
      ring_qeqv
  refine Q'.eqv_trans _
    (P * (U * V) * (R * (L * V + -(J * U)))) _
    (Q'.mul_eqv_congr_left _ _ _ habove') ?_
  refine Q'.eqv_trans _
    ((J * U + -(L * V)) * (-(R * (P * (U * V))))) _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hlow')

/-- Lowest-row label shift used by the lower adjacent carrier. -/
theorem lowest_row_double_label_shift
    (b c k j l : Nat) (hsum : j + l = k)
    (hkb : k + 1 ≤ b) (hkc : k + 1 ≤ c) :
    (Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
        transvectFactorialCoeff (b - 1) (c - 1) k j l ≈
      (Q'.ofNat (b - k) * Q'.ofNat (c - k)) *
        transvectFactorialCoeff b c k j l := by
  have hred := transvectFactorialCoeff_lowest_row_closed
    (b - 1) (c - 1) k j l hsum
  have hfull := transvectFactorialCoeff_lowest_row_closed b c k j l hsum
  have hbsub : (b - 1) - j = b - j - 1 := by omega
  have hcsub : (c - 1) - l = c - l - 1 := by omega
  have hbshift := tvFallQ_label_shift (b - j) l (by omega)
  have hcshift := tvFallQ_label_shift (c - l) j (by omega)
  have hbscale :
      Q'.ofNat (b - j) * tvFallQ ((b - 1) - j) l ≈
        Q'.ofNat (b - k) * tvFallQ (b - j) l := by
    rw [hbsub]
    simpa only [show b - j - l = b - k by omega] using hbshift
  have hcscale :
      Q'.ofNat (c - l) * tvFallQ ((c - 1) - l) j ≈
        Q'.ofNat (c - k) * tvFallQ (c - l) j := by
    rw [hcsub]
    simpa only [show c - l - j = c - k by omega] using hcshift
  let P := tvPhase l * Q'.ofNat (tvFact k)
  refine Q'.eqv_trans _
    (Q'.ofNat (b - j) * Q'.ofNat (c - l) *
      (P * tvFallQ ((b - 1) - j) l *
        tvFallQ ((c - 1) - l) j)) _
    (Q'.mul_eqv_congr_left _ _ _ (by simpa only [P] using hred)) ?_
  refine Q'.eqv_trans _
    (P * (Q'.ofNat (b - j) * tvFallQ ((b - 1) - j) l) *
      (Q'.ofNat (c - l) * tvFallQ ((c - 1) - l) j)) _
    (pair_scale_rearrange _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    (P * (Q'.ofNat (b - k) * tvFallQ (b - j) l) *
      (Q'.ofNat (c - k) * tvFallQ (c - l) j)) _
    (mul_eqv_congr
      (Q'.mul_eqv_congr_left P _ _ hbscale) hcscale) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (b - k) * Q'.ofNat (c - k)) *
      (P * tvFallQ (b - j) l * tvFallQ (c - l) j)) _
    (Q'.eqv_symm (pair_scale_rearrange _ _ _ _ _)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (by simpa only [P] using (Q'.eqv_symm hfull))

private theorem zero_second_term_zero
    (m n k i r : Nat) (hr : 0 < r) :
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
        tvFallQ (m - i) r * tvFallQ 0 r * tvFallQ n (k - r) ≈ 0 := by
  have hz := tvFallQ_eqv_zero_of_lt 0 r hr
  let A := tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
    tvFallQ (m - i) r
  have h0 : A * tvFallQ 0 r ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  exact Q'.eqv_trans _ (0 * tvFallQ n (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)

/-- Every zero-second-index coefficient is the product of the two positive
falling-factorial branches. -/
theorem transvectFactorialCoeff_zero_second_closed
    (m n k i : Nat) :
    transvectFactorialCoeff m n k i 0 ≈ tvFallQ i k * tvFallQ n k := by
  unfold transvectFactorialCoeff
  have hsingle := finSum_eqv_single
    (fun r => tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ (m - i) r * tvFallQ 0 r * tvFallQ n (k - r))
    (k + 1) 0 (by omega)
    (fun r hr hne => zero_second_term_zero m n k i r (by omega))
  refine Q'.eqv_trans _ _ _ hsingle ?_
  change tvPhase 0 * tvBinomQ k 0 * tvFallQ i (k - 0) *
      tvFallQ (m - i) 0 * tvFallQ 0 0 * tvFallQ n (k - 0) ≈ _
  have hp : tvPhase 0 ≈ 1 := by decide
  have hb := tvBinomQ_zero k
  have hm := tvFallQ_zero (m - i)
  have hz := tvFallQ_zero 0
  have hprod :
      tvPhase 0 * tvBinomQ k 0 * tvFallQ i k *
          tvFallQ (m - i) 0 * tvFallQ 0 0 * tvFallQ n k ≈
        (1 : Q') * 1 * tvFallQ i k * 1 * 1 * tvFallQ n k := by
    exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr hp hb) (Q'.eqv_refl _)) hm) hz)
      (Q'.eqv_refl _)
  simpa only [Nat.sub_zero] using
    Q'.eqv_trans _ _ _ hprod (unit_six_collapse _ _)

/-- A strict supported second-index-one row scaled by its two leading labels
is the signed linear factor times the adjacent zero-second row. -/
theorem second_one_scaled_to_zero_next
    (m n k x : Nat) (hk : 0 < k) (hkx : k ≤ x) (hkn : k < n) :
    (Q'.ofNat (x + 1) * Q'.ofNat n) *
        transvectFactorialCoeff m n k x 1 ≈
      (Q'.ofNat (x - k + 1) * Q'.ofNat (n - k) +
          -(Q'.ofNat k * Q'.ofNat (m - x))) *
        transvectFactorialCoeff m n k (x + 1) 0 := by
  have h1 := transvectFactorialCoeff_second_one_factored
    m n k x hk hkx hkn
  have h0 := transvectFactorialCoeff_zero_second_closed m n k (x + 1)
  have hx := tvFallQ_leading_shift (x + 1) (k - 1)
  have hx' : Q'.ofNat (x + 1) * tvFallQ x (k - 1) ≈
      tvFallQ (x + 1) k := by
    simpa only [show x + 1 - 1 = x by omega,
      show k - 1 + 1 = k by omega] using hx
  have hn := tvFallQ_leading_shift n (k - 1)
  have hn' : Q'.ofNat n * tvFallQ (n - 1) (k - 1) ≈
      tvFallQ n k := by
    simpa only [show k - 1 + 1 = k by omega] using hn
  let F := Q'.ofNat (x - k + 1) * Q'.ofNat (n - k) +
    -(Q'.ofNat k * Q'.ofNat (m - x))
  refine Q'.eqv_trans _
    ((Q'.ofNat (x + 1) * Q'.ofNat n) *
      ((tvFallQ x (k - 1) * tvFallQ (n - 1) (k - 1)) * F)) _
    (Q'.mul_eqv_congr_left _ _ _ (by simpa only [F] using h1)) ?_
  refine Q'.eqv_trans _
    (F * ((Q'.ofNat (x + 1) * tvFallQ x (k - 1)) *
      (Q'.ofNat n * tvFallQ (n - 1) (k - 1)))) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (F * (tvFallQ (x + 1) k * tvFallQ n k)) _
    (Q'.mul_eqv_congr_left F _ _ (mul_eqv_congr hx' hn')) ?_
  exact Q'.mul_eqv_congr_left F _ _ (Q'.eqv_symm h0)

/-- The upper adjacent second-index-one row, scaled by its omitted trailing
factor, reduces to the base zero-second row. -/
theorem upper_second_one_scaled_to_base_zero
    (a f r i : Nat) (hrf : r ≤ f) (hri : r < i) :
    Q'.ofNat (f - r + 1) *
        transvectFactorialCoeff a (f + 2) (r + 1) i 1 ≈
      Q'.ofNat (f + 1) *
        (Q'.ofNat (i - r) * Q'.ofNat (f - r + 1) +
          -(Q'.ofNat (r + 1) * Q'.ofNat (a - i))) *
        transvectFactorialCoeff a f r i 0 := by
  have h1 := transvectFactorialCoeff_second_one_factored
    a (f + 2) (r + 1) i (by omega) (by omega) (by omega)
  have h0 := transvectFactorialCoeff_zero_second_closed a f r i
  have hlabel := tvFallQ_label_shift (f + 1) r (by omega)
  have hlabel' :
      Q'.ofNat (f + 1) * tvFallQ f r ≈
        Q'.ofNat (f - r + 1) * tvFallQ (f + 1) r := by
    simpa only [show f + 1 - r = f - r + 1 by omega] using hlabel
  let F := Q'.ofNat (i - r) * Q'.ofNat (f - r + 1) +
    -(Q'.ofNat (r + 1) * Q'.ofNat (a - i))
  refine Q'.eqv_trans _
    (Q'.ofNat (f - r + 1) *
      ((tvFallQ i r * tvFallQ (f + 1) r) * F)) _
    (Q'.mul_eqv_congr_left _ _ _ (by
      simpa only [F, show r + 1 - 1 = r by omega,
        show i - (r + 1) + 1 = i - r by omega,
        show f + 2 - 1 = f + 1 by omega,
        show f + 2 - (r + 1) = f - r + 1 by omega] using h1)) ?_
  refine Q'.eqv_trans _
    (F * (tvFallQ i r *
      (Q'.ofNat (f - r + 1) * tvFallQ (f + 1) r))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (F * (tvFallQ i r * (Q'.ofNat (f + 1) * tvFallQ f r))) _
    (Q'.mul_eqv_congr_left F _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hlabel'))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (f + 1) * F * (tvFallQ i r * tvFallQ f r)) _
    (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h0)

/-- Integer polynomial form of the diagonal correction on the first bulk
shell.  Strict inner support removes the removable `f=0` branch. -/
theorem omegaCorrectionDiagonalNumerator_first_bulk_int
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hpb : q.p < b) (hpc : q.p < c)
    (hsum : j + l = q.p) :
    (q.p : Int) *
        omegaCorrectionDiagonalNumerator a b c d q.intermediate =
      8 * firstBulkScalarInt (a : Int) (b : Int) (c : Int)
        (q.intermediate : Int) (q.p : Int) (q.r : Int)
        (i : Int) (j : Int) (l : Int) := by
  have hfpos : 0 < q.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hbc : b + c = 2 * q.p + q.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have had : a + q.intermediate = d + 2 * q.r := by
    have hdeg := q.degree_eq
    have hqr := Nat.le_min.mp q.r_le
    have hle : 2 * q.r ≤ a + q.intermediate := by
      unfold FixedRightCGChannel.intermediate
      omega
    unfold FixedRightCGChannel.intermediate at hdeg hle ⊢
    omega
  have hC :
      2 * (q.p : Int) + (q.intermediate : Int) - (b : Int) = (c : Int) := by
    have h := congrArg Int.ofNat hbc
    push_cast at h
    omega
  have hD :
      (a : Int) + (q.intermediate : Int) - 2 * (q.r : Int) = (d : Int) := by
    have h := congrArg Int.ofNat had
    push_cast at h
    omega
  have hL : (q.p : Int) - (j : Int) = (l : Int) := by
    have h := congrArg Int.ofNat hsum
    push_cast at h
    omega
  have hpoly := firstBulk_diagonal_polynomial
    (a : Int) (b : Int) (q.intermediate : Int) (q.p : Int)
      (q.r : Int) (i : Int) (j : Int)
  rw [hC, hD, hL] at hpoly
  dsimp only at hpoly
  have hbsub : ((b - 1 : Nat) : Int) = (b : Int) - 1 := by omega
  have hcsub : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
  have hdiag0 :
      firstBulkDiagInt (a : Int) (b : Int) (c : Int) (d : Int)
          (q.intermediate : Int) =
        diagonalNum a b c d q.intermediate := by
    unfold firstBulkDiagInt firstBulkCasInt diagonalNum casimir4
    push_cast
    rfl
  have hdiag1 :
      firstBulkDiagInt (a : Int) ((b : Int) - 1) ((c : Int) - 1) (d : Int)
          (q.intermediate : Int) =
        diagonalNum a (b - 1) (c - 1) d q.intermediate := by
    rw [← hbsub, ← hcsub]
    unfold firstBulkDiagInt firstBulkCasInt diagonalNum casimir4
    push_cast
    rfl
  rw [hdiag0, hdiag1] at hpoly
  simpa only [omegaCorrectionDiagonalNumerator, if_neg (Nat.ne_of_gt hfpos)]
    using hpoly

theorem firstBulkScalarQ_eq_int
    (a b c f p r i j l : Nat) (hpb : p ≤ b) (hpc : p ≤ c)
    (hrf : r ≤ f) (hri : r ≤ i) (hia : i ≤ a) :
    firstBulkScalarQ a b c f p r i j l ≈
      Q'.ofInt (firstBulkScalarInt (a : Int) (b : Int) (c : Int)
        (f : Int) (p : Int) (r : Int) (i : Int) (j : Int) (l : Int)) := by
  have hbp : ((b - p : Nat) : Int) = (b : Int) - (p : Int) := by omega
  have hcp : ((c - p : Nat) : Int) = (c : Int) - (p : Int) := by omega
  have hfr : ((f - r : Nat) : Int) = (f : Int) - (r : Int) := by omega
  have hir : ((i - r : Nat) : Int) = (i : Int) - (r : Int) := by omega
  have hai : ((a - i : Nat) : Int) = (a : Int) - (i : Int) := by omega
  unfold Q'.eqv firstBulkScalarQ firstBulkScalarInt
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, ofInt_num, ofInt_den]
  push_cast
  rw [hbp, hcp, hfr, hir, hai]
  simp only [Int.mul_one, Int.sub_eq_add_neg]

/-- The closed diagonal correction, scaled by its denominator and the inner
order, is exactly the reflected first-bulk scalar polynomial. -/
theorem omegaCorrectionDiagonalCoefficient_first_bulk_scaled
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l : Nat) (hpb : q.p < b) (hpc : q.p < c)
    (hsum : j + l = q.p) :
    Q'.ofNat q.p *
        (Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
          omegaCorrectionDiagonalCoefficient a b c d q.p) ≈
      Q'.ofNat 8 * Q'.ofInt
        (firstBulkScalarInt (a : Int) (b : Int) (c : Int)
          (q.intermediate : Int) (q.p : Int) (q.r : Int)
          (i : Int) (j : Int) (l : Int)) := by
  have hcoeff := omegaCorrectionDiagonalCoefficient_closed q hp
  have hnum := omegaCorrectionDiagonalNumerator_first_bulk_int
    q i j l hpb hpc hsum
  let N := omegaCorrectionDiagonalNumerator a b c d q.intermediate
  let S := firstBulkScalarInt (a : Int) (b : Int) (c : Int)
    (q.intermediate : Int) (q.p : Int) (q.r : Int)
    (i : Int) (j : Int) (l : Int)
  refine Q'.eqv_trans _ (Q'.ofNat q.p * Q'.ofInt N) _
    (Q'.mul_eqv_congr_left _ _ _ (by simpa only [N] using hcoeff)) ?_
  refine Q'.eqv_trans _ (Q'.ofInt ((q.p : Int) * N)) _
    (Q'.eqv_symm (by simpa only [N] using
      YMGap.Continuum.RingNormaliser.ofInt_mul (q.p : Int) N)) ?_
  refine Q'.eqv_trans _ (Q'.ofInt (8 * S)) _ ?_ ?_
  · exact Q'.eqv_of_eq (congrArg Q'.ofInt (by simpa only [N, S] using hnum))
  · simpa only [S] using
      YMGap.Continuum.RingNormaliser.ofInt_mul 8 S

/-- On the strict first bulk shell, the diagonal coefficient has exactly the
scalar normalization used by the adjacent Hahn rows. -/
theorem omegaCorrectionDiagonalCoefficient_first_bulk_scalar
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l : Nat) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r ≤ i) (hia : i ≤ a) (hsum : j + l = q.p) :
    Q'.ofNat q.p *
        ((Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2)) *
          omegaCorrectionDiagonalCoefficient a b c d q.p) ≈
      firstBulkScalarQ a b c q.intermediate q.p q.r i j l := by
  have hqr := Nat.le_min.mp q.r_le
  have hscaled := omegaCorrectionDiagonalCoefficient_first_bulk_scaled
    q hp i j l hpb hpc hsum
  have hscalar := firstBulkScalarQ_eq_int
    a b c q.intermediate q.p q.r i j l
      (by omega) (by omega) hqr.2 hri hia
  let P := Q'.ofNat q.p
  let F := Q'.ofNat q.intermediate
  let G := Q'.ofNat (q.intermediate + 2)
  let E := Q'.ofNat 8
  let C := omegaCorrectionDiagonalCoefficient a b c d q.p
  let S := firstBulkScalarQ a b c q.intermediate q.p q.r i j l
  have hD : Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) ≈
      E * (F * G) := by
    have hf : q.intermediate ≠ 0 := by
      unfold FixedRightCGChannel.intermediate
      omega
    simp only [omegaCorrectionDiagonalDenominator, hf, diagonalDen,
      casimir4, E, F, G]
    refine Q'.eqv_trans _
      (Q'.ofNat 8 * Q'.ofNat
        (q.intermediate * (q.intermediate + 2))) _
      (Q'.eqv_symm (ofNat_mul_eqv 8
        (q.intermediate * (q.intermediate + 2)))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (ofNat_mul_eqv q.intermediate
        (q.intermediate + 2)))
  have hleft : E * (P * ((F * G) * C)) ≈
      P * (Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) * C) := by
    refine Q'.eqv_trans _ (P * ((E * (F * G)) * C)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left P _ _
      (Q'.mul_eqv_congr_right _ _ C (Q'.eqv_symm hD))
  have hright : E * Q'.ofInt
        (firstBulkScalarInt (a : Int) (b : Int) (c : Int)
          (q.intermediate : Int) (q.p : Int) (q.r : Int)
          (i : Int) (j : Int) (l : Int)) ≈ E * S :=
    Q'.mul_eqv_congr_left E _ _ (Q'.eqv_symm (by
      simpa only [S] using hscalar))
  have hfactor : E * (P * ((F * G) * C)) ≈ E * S :=
    Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ (by simpa only [P, C, E] using hscaled) hright)
  simpa only [P, F, G, C, S] using
    Q'.mul_left_cancel_of_pos (ofNat_pos_of_pos 8 (by omega)) hfactor

/-- The unique one-above-lowest reduced inner row on the first bulk shell,
with the two visible exchange labels included, collapses to the base row. -/
theorem first_bulk_inner_above_reduced
    (b c p j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = p) (hpb : p < b) (hpc : p < c) :
    Q'.ofNat p *
        ((Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
          transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l) ≈
      (Q'.ofNat j * Q'.ofNat (b - p) +
          -(Q'.ofNat l * Q'.ofNat (c - p))) *
        transvectFactorialCoeff b c p j l := by
  let P := Q'.ofNat p
  let U := Q'.ofNat (b - p)
  let V := Q'.ofNat (c - p)
  let B := Q'.ofNat (b - j)
  let C := Q'.ofNat (c - l)
  let A := Q'.ofNat j * U + -(Q'.ofNat l * V)
  let H0 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l
  let Hr := transvectFactorialCoeff (b - 1) (c - 1) p j l
  let H := transvectFactorialCoeff b c p j l
  have habove := one_above_lowest_scaled_to_lowest
    (b - 1) (c - 1) (p - 1) j l hj hl (by omega) (by omega) (by omega)
  have habove' : (P * (U * V)) * H0 ≈ A * Hr := by
    simpa only [P, U, V, A, H0, Hr,
      show p - 1 + 1 = p by omega,
      show b - 1 - (p - 1) = b - p by omega,
      show c - 1 - (p - 1) = c - p by omega] using habove
  have hshift := lowest_row_double_label_shift
    b c p j l hsum (by omega) (by omega)
  have hshift' : (B * C) * Hr ≈ (U * V) * H := by
    simpa only [B, C, U, V, Hr, H] using hshift
  have hfactor : (U * V) * (P * ((B * C) * H0)) ≈
      (U * V) * (A * H) := by
    refine Q'.eqv_trans _ ((B * C) * ((P * (U * V)) * H0)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((B * C) * (A * Hr)) _
      (Q'.mul_eqv_congr_left (B * C) _ _ habove') ?_
    refine Q'.eqv_trans _ (A * ((B * C) * Hr)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _ (A * ((U * V) * H)) _
      (Q'.mul_eqv_congr_left A _ _ hshift') ?_
    ring_qeqv
  have hUV : (0 : Q') < U * V := Q'.mul_pos
    (ofNat_pos_of_pos (b - p) (by omega))
    (ofNat_pos_of_pos (c - p) (by omega))
  simpa only [P, U, V, B, C, A, H0, H] using
    Q'.mul_left_cancel_of_pos hUV hfactor

/-- The lower adjacent carrier on the strict first bulk shell, after the
common `p·f·(f+2)` scaling, is a single base-row scalar. -/
theorem first_bulk_lower_carrier_scaled
    {a b c d : Nat} (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r < i) :
    (Q'.ofNat q.p *
        (Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2))) *
        (omegaCorrectionLowerCoefficient a b c d q.p *
          (transvectFactorialCoeff b c qm.p j l *
            transvectFactorialCoeff a qm.intermediate qm.r i 1)) ≈
      Q'.ofNat q.intermediate *
        ((Q'.ofNat j * Q'.ofNat (b - q.p + 1) +
            -(Q'.ofNat l * Q'.ofNat (c - q.p + 1))) *
          (Q'.ofNat (i - q.r) *
              Q'.ofNat (q.intermediate - q.r + 1) +
            -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i)))) *
        (transvectFactorialCoeff b c q.p j l *
          transvectFactorialCoeff a q.intermediate q.r i 0) := by
  have hqr := Nat.le_min.mp q.r_le
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrm : qm.r = q.r + 1 := by
    have hqm := Nat.le_min.mp qm.r_le
    have hq := Nat.le_min.mp q.r_le
    have hqp := Nat.le_min.mp q.p_le
    have hdegm := qm.degree_eq
    have hdeg := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hqm hq hdegm hdeg
    omega
  let P := Q'.ofNat q.p
  let F := Q'.ofNat q.intermediate
  let G := Q'.ofNat (q.intermediate + 2)
  let G1 := Q'.ofNat (q.intermediate + 1)
  let U := Q'.ofNat (b - q.p + 1)
  let V := Q'.ofNat (c - q.p + 1)
  let R := Q'.ofNat (q.intermediate - q.r + 1)
  let A := Q'.ofNat j * U + -(Q'.ofNat l * V)
  let C := Q'.ofNat (i - q.r) * R +
    -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i))
  let L := omegaCorrectionLowerCoefficient a b c d q.p
  let Hm := transvectFactorialCoeff b c qm.p j l
  let Om := transvectFactorialCoeff a qm.intermediate qm.r i 1
  let H := transvectFactorialCoeff b c q.p j l
  let O := transvectFactorialCoeff a q.intermediate q.r i 0
  have hcoeff0 := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  have hnum : Q'.ofNat
        ((b - q.p + 1) * (c - q.p + 1) *
          (q.intermediate - q.r + 1)) ≈ (U * V) * R := by
    refine Q'.eqv_trans _
      (Q'.ofNat ((b - q.p + 1) * (c - q.p + 1)) *
        Q'.ofNat (q.intermediate - q.r + 1)) _
      (Q'.eqv_symm (ofNat_mul_eqv
        ((b - q.p + 1) * (c - q.p + 1))
        (q.intermediate - q.r + 1))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (ofNat_mul_eqv
        (b - q.p + 1) (c - q.p + 1)))
  have hcoeff : (G * G1) * L ≈ (U * V) * R :=
    Q'.eqv_trans _ _ _ (by simpa only [G, G1, L] using hcoeff0) hnum
  have hinner0 := one_above_lowest_scaled_to_lowest
    b c (q.p - 1) j l hj hl (by omega) (by omega) (by omega)
  have hinner : (P * (U * V)) * Hm ≈ A * H := by
    simpa only [P, U, V, A, Hm, H,
      show q.p - 1 + 1 = q.p by omega,
      show b - (q.p - 1) = b - q.p + 1 by omega,
      show c - (q.p - 1) = c - q.p + 1 by omega,
      show qm.p = q.p - 1 by omega] using hinner0
  have houter0 := upper_second_one_scaled_to_base_zero
    a q.intermediate q.r i hqr.2 hri
  have houter : R * Om ≈ (G1 * C) * O := by
    simpa only [R, Om, G1, C, O, hf, hrm] using houter0
  have hfactor :
      G1 * ((P * (F * G)) * (L * (Hm * Om))) ≈
        G1 * (F * (A * C) * (H * O)) := by
    refine Q'.eqv_trans _
      (F * (((G * G1) * L) * ((P * Hm) * Om))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (F * (((U * V) * R) * ((P * Hm) * Om))) _
      (Q'.mul_eqv_congr_left F _ _
        (Q'.mul_eqv_congr_right _ _ _ hcoeff)) ?_
    refine Q'.eqv_trans _
      (F * (((P * (U * V)) * Hm) * (R * Om))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (F * ((A * H) * ((G1 * C) * O))) _
      (Q'.mul_eqv_congr_left F _ _ (mul_eqv_congr hinner houter)) ?_
    ring_qeqv
  simpa only [P, F, G, G1, A, C, L, Hm, Om, H, O] using
    Q'.mul_left_cancel_of_pos
      (ofNat_pos_of_pos (q.intermediate + 1) (by omega)) hfactor

private theorem firstBulk_three_term_scale
    (P F G X Y Z : Q') :
    (P * (F * G)) * ((X + Y) + Z) ≈
      G * ((((P * F) * X + (P * F) * Y) + (P * F) * Z)) := by
  ring_qeqv

private theorem firstBulk_exchange_collect
    (G F A B I L AI J H O : Q') :
    G * (((A * B) * (H * O) +
        -(F * (I * L)) * (H * O)) +
      -(F * (AI * J)) * (H * O)) ≈
      G * ((A * B + -(F * (I * L + AI * J))) * (H * O)) := by
  ring_qeqv

private theorem firstBulk_neg_factor_reassoc (X H O : Q') :
    X * ((-H) * O) ≈ (-X) * (H * O) := by
  have hleft : X * ((-H) * O) ≈ -((X * H) * O) := by
    refine Q'.eqv_trans _ ((X * (-H)) * O) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv X (-H) O)) ?_
    refine Q'.eqv_trans _ (-(X * H) * O) _
      (Q'.mul_eqv_congr_right _ _ O (Q'.mul_neg_eqv X H)) ?_
    exact Q'.neg_mul_eqv (X * H) O
  have hright : (-X) * (H * O) ≈ -((X * H) * O) := by
    refine Q'.eqv_trans _ (((-X) * H) * O) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (-X) H O)) ?_
    refine Q'.eqv_trans _ (-(X * H) * O) _
      (Q'.mul_eqv_congr_right _ _ O (Q'.neg_mul_eqv X H)) ?_
    exact Q'.neg_mul_eqv (X * H) O
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- The three live exchange terms on the strict first bulk shell reduce to
the first two scalar blocks in `firstBulkScalarQ`. -/
theorem first_bulk_exchange_rows_scaled
    (a b c f p r i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = p)
    (hpb : p < b) (hpc : p < c)
    (hr : 0 < r) (hrf : r < f) (hri : r < i) (hia : i ≤ a) :
    (Q'.ofNat p * (Q'.ofNat f * Q'.ofNat (f + 2))) *
        ((Q'.ofNat i * Q'.ofNat (b - j)) *
            (Q'.ofNat (c - l) *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l *
                transvectFactorialCoeff a f r (i - 1) 1)) +
          (Q'.ofNat i * Q'.ofNat (b - j)) *
            (Q'.ofNat l *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j (l - 1) *
                transvectFactorialCoeff a f r i 0)) +
          -((Q'.ofNat (a - i) * Q'.ofNat j) *
            (Q'.ofNat (c - l) *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) (j - 1) l *
                transvectFactorialCoeff a f r i 0)))) ≈
      Q'.ofNat (f + 2) *
        (((Q'.ofNat j * Q'.ofNat (b - p) +
              -(Q'.ofNat l * Q'.ofNat (c - p))) *
            (Q'.ofNat (i - r) * Q'.ofNat (f - r) +
              -(Q'.ofNat r * Q'.ofNat (a - i + 1))) +
          -(Q'.ofNat f *
            (Q'.ofNat i * Q'.ofNat l +
              Q'.ofNat (a - i) * Q'.ofNat j))) *
        (transvectFactorialCoeff b c p j l *
          transvectFactorialCoeff a f r i 0)) := by
  let P := Q'.ofNat p
  let F := Q'.ofNat f
  let G := Q'.ofNat (f + 2)
  let I := Q'.ofNat i
  let J := Q'.ofNat j
  let L := Q'.ofNat l
  let Bj := Q'.ofNat (b - j)
  let Cl := Q'.ofNat (c - l)
  let Ai := Q'.ofNat (a - i)
  let A := J * Q'.ofNat (b - p) + -(L * Q'.ofNat (c - p))
  let B := Q'.ofNat (i - r) * Q'.ofNat (f - r) +
    -(Q'.ofNat r * Q'.ofNat (a - i + 1))
  let M := I * L + Ai * J
  let H0 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l
  let H1 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j (l - 1)
  let H2 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) (j - 1) l
  let H := transvectFactorialCoeff b c p j l
  let O1 := transvectFactorialCoeff a f r (i - 1) 1
  let O := transvectFactorialCoeff a f r i 0
  have hinner0 := first_bulk_inner_above_reduced
    b c p j l hj hl hsum hpb hpc
  have hinner0' : P * ((Bj * Cl) * H0) ≈ A * H := by
    simpa only [P, Bj, Cl, H0, A, J, L, H] using hinner0
  have hinner1 := lowest_row_first_predecessor_scaled
    b c p j l hj hl hsum (by omega) (by omega)
  have hinner1' : (P * Bj) * H1 ≈ -H := by
    simpa only [P, Bj, H1, H] using hinner1
  have hinner2 := lowest_row_second_predecessor_scaled
    b c p j l hj hl hsum (by omega) (by omega)
  have hinner2' : (P * Cl) * H2 ≈ H := by
    simpa only [P, Cl, H2, H] using hinner2
  have houter0 := second_one_scaled_to_zero_next
    a f r (i - 1) hr (by omega) hrf
  have houter : (I * F) * O1 ≈ B * O := by
    simpa only [I, F, O1, B, O,
      show i - 1 + 1 = i by omega,
      show i - 1 - r + 1 = i - r by omega,
      show a - (i - 1) = a - i + 1 by omega] using houter0
  have hterm0 : (P * F) * ((I * Bj) * (Cl * (H0 * O1))) ≈
      (A * B) * (H * O) := by
    refine Q'.eqv_trans _
      (P * ((Bj * Cl) * H0) * ((I * F) * O1)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((A * H) * (B * O)) _
      (mul_eqv_congr hinner0' houter) ?_
    ring_qeqv
  have hterm1 : (P * F) * ((I * Bj) * (L * (H1 * O))) ≈
      -(F * (I * L)) * (H * O) := by
    refine Q'.eqv_trans _
      (F * (I * L) * (((P * Bj) * H1) * O)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ (F * (I * L) * ((-H) * O)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ O hinner1')) ?_
    exact firstBulk_neg_factor_reassoc (F * (I * L)) H O
  have hterm2 : (P * F) * (-((Ai * J) * (Cl * (H2 * O)))) ≈
      -(F * (Ai * J)) * (H * O) := by
    refine Q'.eqv_trans _
      (-(F * (Ai * J)) * (((P * Cl) * H2) * O)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ O hinner2')
  refine Q'.eqv_trans _
    (G * (((P * F) * ((I * Bj) * (Cl * (H0 * O1))) +
      (P * F) * ((I * Bj) * (L * (H1 * O)))) +
      (P * F) * (-((Ai * J) * (Cl * (H2 * O)))))) _
    (firstBulk_three_term_scale P F G
      ((I * Bj) * (Cl * (H0 * O1)))
      ((I * Bj) * (L * (H1 * O)))
      (-((Ai * J) * (Cl * (H2 * O))))) ?_
  refine Q'.eqv_trans _
    (G * (((A * B) * (H * O) +
      -(F * (I * L)) * (H * O)) +
      -(F * (Ai * J)) * (H * O))) _
    (Q'.mul_eqv_congr_left G _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hterm0 hterm1) hterm2)) ?_
  simpa only [P, F, G, I, J, L, Bj, Cl, Ai, A, B, M,
    H0, H1, H2, H, O1, O] using
      firstBulk_exchange_collect G F A B I L Ai J H O

private theorem firstBulk_scalar_partition_q
    (F G A B M N C : Q') :
    G * (A * B + -(F * M)) ≈
      F * (N * C) +
        (((G * A) * B + -((F * G) * M)) + -((F * N) * C)) := by
  let X := (G * A) * B + -((F * G) * M)
  let Z := (F * N) * C
  have hleft : G * (A * B + -(F * M)) ≈ X := by
    simp only [X]
    ring_qeqv
  have hcancel := Q'.add_sub_cancel_eqv X Z
  refine Q'.eqv_trans _ X _ hleft ?_
  refine Q'.eqv_trans _ (Z + (X + -Z)) _ hcancel ?_
  exact Q'.add_eqv_congr_right Z (F * (N * C)) (X + -Z)
    (Q'.mul_assoc_eqv F N C)

/-- Exact scalar partition matching the exchange, lower-adjacent, and
diagonal first-bulk contributions. -/
theorem firstBulkScalarQ_split (a b c f p r i j l : Nat) :
    Q'.ofNat (f + 2) *
        ((Q'.ofNat j * Q'.ofNat (b - p) +
            -(Q'.ofNat l * Q'.ofNat (c - p))) *
          (Q'.ofNat (i - r) * Q'.ofNat (f - r) +
            -(Q'.ofNat r * Q'.ofNat (a - i + 1))) +
        -(Q'.ofNat f *
          (Q'.ofNat i * Q'.ofNat l +
            Q'.ofNat (a - i) * Q'.ofNat j))) ≈
      Q'.ofNat f *
          ((Q'.ofNat j * Q'.ofNat (b - p + 1) +
              -(Q'.ofNat l * Q'.ofNat (c - p + 1))) *
            (Q'.ofNat (i - r) * Q'.ofNat (f - r + 1) +
              -(Q'.ofNat (r + 1) * Q'.ofNat (a - i)))) +
        firstBulkScalarQ a b c f p r i j l := by
  let F := Q'.ofNat f
  let G := F + Q'.ofNat 2
  let A := Q'.ofNat j * Q'.ofNat (b - p) +
    -(Q'.ofNat l * Q'.ofNat (c - p))
  let B := Q'.ofNat (i - r) * Q'.ofNat (f - r) +
    -(Q'.ofNat r * Q'.ofNat (a - i + 1))
  let M := Q'.ofNat i * Q'.ofNat l +
    Q'.ofNat (a - i) * Q'.ofNat j
  let N := Q'.ofNat j * Q'.ofNat (b - p + 1) +
    -(Q'.ofNat l * Q'.ofNat (c - p + 1))
  let C := Q'.ofNat (i - r) * Q'.ofNat (f - r + 1) +
    -(Q'.ofNat (r + 1) * Q'.ofNat (a - i))
  refine Q'.eqv_trans _ (G * (A * B + -(F * M))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by
      simpa only [F, G] using Q'.ofNat_add_eqv f 2)
  · simpa only [F, G, A, B, M, N, C, firstBulkScalarQ] using
      firstBulk_scalar_partition_q F G A B M N C

private theorem triple_swap (C A B : Q') :
    C * (A * B) ≈ A * (C * B) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Int.mul_assoc, Int.mul_left_comm]

theorem outer_falling_double_shift (f r : Nat) (hr : r ≤ f) :
    Q'.ofNat ((f + 2) * (f + 1)) * tvFallQ f r ≈
      Q'.ofNat (f - r + 1) * tvFallQ (f + 2) (r + 1) := by
  have h1 := tvFallQ_leading_shift (f + 1) r
  have h2 := tvFallQ_leading_shift (f + 2) (r + 1)
  have ht := tvFallQ_trailing_shift (f + 2) (r + 1) (by omega)
  refine Q'.eqv_trans _
    ((Q'.ofNat (f + 2) * Q'.ofNat (f + 1)) * tvFallQ f r) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm
      (ofNat_mul_eqv (f + 2) (f + 1)))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (f + 2) * (Q'.ofNat (f + 1) * tvFallQ f r)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (f + 2) * tvFallQ (f + 1) (r + 1)) _
    (Q'.mul_eqv_congr_left _ _ _ h1) ?_
  refine Q'.eqv_trans _ (tvFallQ (f + 2) (r + 2)) _ h2 ?_
  refine Q'.eqv_trans _
    (tvFallQ (f + 2) (r + 1) * Q'.ofNat ((f + 2) - (r + 1))) _
    (Q'.eqv_symm ht) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat ((f + 2) - (r + 1)) * tvFallQ (f + 2) (r + 1)) _
    (Q'.mul_comm_eqv _ _) ?_
  rw [show (f + 2) - (r + 1) = f - r + 1 by omega]
  exact Q'.eqv_refl _

/-- Zero-second-index outer row shift between the lower adjacent channel and
the peeled channel. -/
theorem zero_second_outer_adjacent_shift
    (a f r i : Nat) (hr : r ≤ f) :
    Q'.ofNat (f - r + 1) *
        transvectFactorialCoeff a (f + 2) (r + 1) i 0 ≈
      (Q'.ofNat i * Q'.ofNat ((f + 2) * (f + 1))) *
        transvectFactorialCoeff a f r (i - 1) 0 := by
  have hu := transvectFactorialCoeff_zero_second_closed
    a (f + 2) (r + 1) i
  have hd := transvectFactorialCoeff_zero_second_closed a f r (i - 1)
  have hiShift := tvFallQ_leading_shift i r
  have hfShift := outer_falling_double_shift f r hr
  let A := tvFallQ i (r + 1)
  let B := tvFallQ (f + 2) (r + 1)
  let X := tvFallQ (i - 1) r
  let Y := tvFallQ f r
  let C := Q'.ofNat (f - r + 1)
  let I := Q'.ofNat i
  let D := Q'.ofNat ((f + 2) * (f + 1))
  have hI : I * X ≈ A := by simpa only [I, X, A] using hiShift
  have hD : D * Y ≈ C * B := by simpa only [D, Y, C, B] using hfShift
  have hleft :
      Q'.ofNat (f - r + 1) *
          transvectFactorialCoeff a (f + 2) (r + 1) i 0 ≈
        A * (C * B) := by
    refine Q'.eqv_trans _ (C * (A * B)) _
      (Q'.mul_eqv_congr_left C _ _ (by simpa only [A, B] using hu)) ?_
    exact triple_swap C A B
  have hright :
      (Q'.ofNat i * Q'.ofNat ((f + 2) * (f + 1))) *
          transvectFactorialCoeff a f r (i - 1) 0 ≈
        A * (C * B) := by
    refine Q'.eqv_trans _ ((I * D) * (X * Y)) _
      (Q'.mul_eqv_congr_left (I * D) _ _ (by simpa only [X, Y] using hd)) ?_
    refine Q'.eqv_trans _ ((I * X) * (D * Y)) _
      (two_by_two_rearrange I D X Y) ?_
    exact mul_eqv_congr hI hD
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

private theorem lower_boundary_core {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hsum : j + l = qm.p) :
    (Q'.ofNat i * Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
        (transvectFactorialCoeff (b - 1) (c - 1) qm.p j l *
          transvectFactorialCoeff a q.intermediate q.r (i - 1) 0) ≈
      omegaCorrectionLowerCoefficient a b c d q.p *
        (transvectFactorialCoeff b c qm.p j l *
          transvectFactorialCoeff a (q.intermediate + 2) (q.r + 1) i 0) := by
  have hqmin := Nat.le_min.mp q.p_le
  have hqr := Nat.le_min.mp q.r_le
  have hinner := lowest_row_double_label_shift b c qm.p j l hsum
    (by omega) (by omega)
  have houter := zero_second_outer_adjacent_shift
    a q.intermediate q.r i hqr.2
  have hcoeff := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  let U := b - q.p + 1
  let V := c - q.p + 1
  let F := q.intermediate - q.r + 1
  let D := (q.intermediate + 2) * (q.intermediate + 1)
  let I := Q'.ofNat i
  let B := Q'.ofNat (b - j)
  let C := Q'.ofNat (c - l)
  let Uq := Q'.ofNat U
  let Vq := Q'.ofNat V
  let Fq := Q'.ofNat F
  let Dq := Q'.ofNat D
  let L := omegaCorrectionLowerCoefficient a b c d q.p
  let Hred := transvectFactorialCoeff (b - 1) (c - 1) qm.p j l
  let Ored := transvectFactorialCoeff a q.intermediate q.r (i - 1) 0
  let Hfull := transvectFactorialCoeff b c qm.p j l
  let Ofull := transvectFactorialCoeff a (q.intermediate + 2)
    (q.r + 1) i 0
  have hsplit : Q'.ofNat (U * V * F) ≈ (Uq * Vq) * Fq := by
    refine Q'.eqv_trans _ (Q'.ofNat (U * V) * Q'.ofNat F) _
      (Q'.eqv_symm (ofNat_mul_eqv (U * V) F)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (ofNat_mul_eqv U V))
  have hcoeff' : Dq * L ≈ (Uq * Vq) * Fq :=
    Q'.eqv_trans _ _ _ (by simpa only [Dq, D, L, U, V, F] using hcoeff)
      hsplit
  have hinner' : (B * C) * Hred ≈ (Uq * Vq) * Hfull := by
    simpa only [B, C, Hred, Uq, Vq, Hfull, U, V,
      show b - qm.p = b - q.p + 1 by omega,
      show c - qm.p = c - q.p + 1 by omega] using hinner
  have houter' : Fq * Ofull ≈ (I * Dq) * Ored := by
    simpa only [Fq, F, Ofull, I, Dq, D, Ored] using houter
  have hDnat : 0 < D := by
    dsimp only [D]
    exact Nat.mul_pos (by omega) (by omega)
  have hscaled :
      Dq * (L * (Hfull * Ofull)) ≈
        Dq * ((I * B * C) * (Hred * Ored)) := by
    refine Q'.eqv_trans _ ((Dq * L) * (Hfull * Ofull)) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv Dq L (Hfull * Ofull))) ?_
    refine Q'.eqv_trans _ (((Uq * Vq) * Fq) * (Hfull * Ofull)) _
      (Q'.mul_eqv_congr_right _ _ _ hcoeff') ?_
    refine Q'.eqv_trans _
      (((Uq * Vq) * Hfull) * (Fq * Ofull)) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (((B * C) * Hred) * ((I * Dq) * Ored)) _
      (mul_eqv_congr (Q'.eqv_symm hinner') houter') ?_
    ring_qeqv
  have hcancel := Q'.mul_left_cancel_of_pos
    (ofNat_pos_of_pos D hDnat) hscaled
  exact Q'.eqv_symm (by
    simpa only [I, B, C, Hred, Ored, L, Hfull, Ofull] using hcancel)

/-- A guarded right factorial coefficient vanishes unless its source total,
inner contraction order, outer contraction order, and output index obey the
single total-shell equation. -/
private theorem guardedRightFactorialCoefficient_zero_off_total_shell
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (i j l s : Nat) (hoff : s + q.r + q.p ≠ i + j + l) :
    guardedRightFactorialCoefficient q i j l s ≈ 0 := by
  unfold guardedRightFactorialCoefficient
  by_cases hinner : q.p ≤ j + l
  · rw [if_pos hinner]
    have houter : ¬ s + q.r = i + (j + l - q.p) := by
      intro h
      apply hoff
      omega
    rw [if_neg houter]
    exact Q'.mul_zero_eqv _
  · rw [if_neg hinner]
    exact Q'.eqv_refl 0

private theorem lower_outer_order {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1) : qm.r = q.r + 1 := by
  have hqm := Nat.le_min.mp qm.r_le
  have hq := Nat.le_min.mp q.r_le
  have hp := Nat.le_min.mp q.p_le
  have hdm := qm.degree_eq
  have hd := q.degree_eq
  unfold FixedRightCGChannel.intermediate at hqm hq hdm hd
  omega

private theorem upper_outer_order {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d)
    (hnext : qp.p = q.p + 1) : qp.r + 1 = q.r := by
  have hq := Nat.le_min.mp q.r_le
  have hqp := Nat.le_min.mp qp.r_le
  have hp := Nat.le_min.mp qp.p_le
  have hd := q.degree_eq
  have hdp := qp.degree_eq
  unfold FixedRightCGChannel.intermediate at hq hqp hd hdp
  omega

private theorem factorial_correction_zero_off_total_shell
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hoff : s + q.r + q.p ≠ i + j + l) :
    omegaExchangeCorrection a b c
        (fun u v w => guardedRightFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w s) i j l ≈ 0 := by
  let qr := reducePositiveInnerRightChannel q hp
  have hqrp : qr.p = q.p - 1 := rfl
  have hqrr : qr.r = q.r := rfl
  have h0 : guardedRightFactorialCoefficient qr (i - 1) j l s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qr _ _ _ _ (by
      rw [hqrp, hqrr]
      intro hshell
      apply hoff
      omega)
  have h1 : guardedRightFactorialCoefficient qr i j (l - 1) s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qr _ _ _ _ (by
      rw [hqrp, hqrr]
      intro hshell
      apply hoff
      omega)
  have h2 : guardedRightFactorialCoefficient qr i (j - 1) l s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qr _ _ _ _ (by
      rw [hqrp, hqrr]
      intro hshell
      apply hoff
      omega)
  have h3 : guardedRightFactorialCoefficient qr (i + 1) (j - 1)
      (l - 1) s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qr _ _ _ _ (by
      rw [hqrp, hqrr]
      intro hshell
      apply hoff
      omega)
  unfold omegaExchangeCorrection
  refine Q'.eqv_trans _
    ((Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h0)
          (Q'.mul_eqv_congr_left _ _ _ h1)))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ h2)
            (Q'.mul_eqv_congr_left _ _ _ h3))))
  · have hz0 : Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0 ≈ 0 := by
      refine Q'.eqv_trans _ ((0 : Q') + 0) _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) (Q'.mul_zero_eqv _))
        (by decide)
    refine Q'.eqv_trans _
      ((Q'.ofNat i * Q'.ofNat (b - j)) * 0 +
        -((Q'.ofNat (a - i) * Q'.ofNat j) * 0)) _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hz0)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ hz0))) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -0) _
      (Q'.add_eqv_congr'
        (Q'.mul_zero_eqv _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _)))
      (by decide)

/-- The guarded factorial residual is completely discharged off the common
physical output shell.  Only positivity of the three shifted source indices
is needed; upper coordinate faces are already encoded by the guards. -/
theorem omegaCorrectionFactorialAt_off_total_shell {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hoff : s + q.r + q.p ≠ i + j + l) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  have hrm := lower_outer_order qm q hprev
  have hrp := upper_outer_order q qp hnext
  have hcorr := factorial_correction_zero_off_total_shell
    q hp i j l s hi hj hl hoff
  have hqm : guardedRightFactorialCoefficient qm i j l s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qm _ _ _ _ (by
      intro hshell
      apply hoff
      omega)
  have hq : guardedRightFactorialCoefficient q i j l s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell q _ _ _ _ hoff
  have hqp : guardedRightFactorialCoefficient qp i j l s ≈ 0 :=
    guardedRightFactorialCoefficient_zero_off_total_shell qp _ _ _ _ (by
      intro hshell
      apply hoff
      omega)
  unfold OmegaCorrectionFactorialAt
  refine Q'.eqv_trans _ 0 _ hcorr (Q'.eqv_symm ?_)
  refine Q'.eqv_trans _
    (omegaCorrectionLowerCoefficient a b c d q.p * 0 +
      omegaCorrectionDiagonalCoefficient a b c d q.p * 0 +
      omegaCorrectionUpperCoefficient a b c d q.p * 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hqm)
        (Q'.mul_eqv_congr_left _ _ _ hq))
      (Q'.mul_eqv_congr_left _ _ _ hqp)
  · refine Q'.eqv_trans _ (((0 : Q') + 0) + 0) _ ?_ (by decide)
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_zero_eqv _)
        (Q'.mul_zero_eqv _))
      (Q'.mul_zero_eqv _)

/-- Raw three-carrier consequence of the guarded off-shell calculation. -/
theorem omegaCorrectionThreeCarrierAt_off_total_shell {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hoff : s + q.r + q.p ≠ i + j + l) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_off_total_shell qm q qp hp hprev hnext
      i j l s hi hj hl hoff)

/-- Output-shell coefficient with only the genuine inner-support guard left.
The final output index disappears after imposing total-shell conservation. -/
def rightShellFactorialCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  if q.p ≤ j + l then
    hahnEntry b c (j + l) q.p j *
      transvectFactorialCoeff a q.intermediate q.r i (j + l - q.p)
  else 0

private theorem guardedRightFactorialCoefficient_eq_shell
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l) :
    guardedRightFactorialCoefficient q i j l s ≈
      rightShellFactorialCoefficient q i j l := by
  unfold guardedRightFactorialCoefficient rightShellFactorialCoefficient
  by_cases hinner : q.p ≤ j + l
  · rw [if_pos hinner, if_pos hinner]
    have houter : s + q.r = i + (j + l - q.p) := by omega
    rw [if_pos houter]
    exact Q'.eqv_refl _
  · rw [if_neg hinner, if_neg hinner]
    exact Q'.eqv_refl 0

/-- The exact remaining on-shell Hahn product identity. -/
def OmegaCorrectionShellAt {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) : Prop :=
  omegaExchangeCorrection a b c
      (fun u v w => rightShellFactorialCoefficient
        (reducePositiveInnerRightChannel q hp) u v w) i j l ≈
    omegaCorrectionLowerCoefficient a b c d q.p *
        rightShellFactorialCoefficient qm i j l +
      omegaCorrectionDiagonalCoefficient a b c d q.p *
        rightShellFactorialCoefficient q i j l +
      omegaCorrectionUpperCoefficient a b c d q.p *
        rightShellFactorialCoefficient qp i j l

/-- The complete lower support face of the on-shell Hahn residual. -/
theorem omegaCorrectionShellAt_lower_boundary {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = qm.p) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  have hqmin := Nat.le_min.mp q.p_le
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrm := lower_outer_order qm q hprev
  let qr := reducePositiveInnerRightChannel q hp
  have hqrp : qr.p = qm.p := by
    change q.p - 1 = qm.p
    omega
  have hqrr : qr.r = q.r := rfl
  have hqrf : qr.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  let Hred := transvectFactorialCoeff (b - 1) (c - 1) qm.p j l
  let Ored := transvectFactorialCoeff a q.intermediate q.r (i - 1) 0
  let Hfull := transvectFactorialCoeff b c qm.p j l
  let Ofull := transvectFactorialCoeff a (q.intermediate + 2)
    (q.r + 1) i 0
  have hx0 : rightShellFactorialCoefficient qr (i - 1) j l ≈
      Hred * Ored := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega, hqrp,
      show j + l - qm.p = 0 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx1 : rightShellFactorialCoefficient qr i j (l - 1) ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qr.p ≤ j + (l - 1))]
    exact Q'.eqv_refl 0
  have hx2 : rightShellFactorialCoefficient qr i (j - 1) l ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qr.p ≤ j - 1 + l)]
    exact Q'.eqv_refl 0
  have hx3 : rightShellFactorialCoefficient qr (i + 1) (j - 1) (l - 1) ≈
      0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qr.p ≤ j - 1 + (l - 1))]
    exact Q'.eqv_refl 0
  have hqm : rightShellFactorialCoefficient qm i j l ≈
      Hfull * Ofull := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qm.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega,
      show j + l - qm.p = 0 by omega, hf, hrm]
    exact Q'.eqv_refl _
  have hq : rightShellFactorialCoefficient q i j l ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ q.p ≤ j + l)]
    exact Q'.eqv_refl 0
  have hqp : rightShellFactorialCoefficient qp i j l ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qp.p ≤ j + l)]
    exact Q'.eqv_refl 0
  have hleft :
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
        (Q'.ofNat i * Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
          (Hred * Ored) := by
    unfold omegaExchangeCorrection
    refine Q'.eqv_trans _
      ((Q'.ofNat i * Q'.ofNat (b - j)) *
          (Q'.ofNat (c - l) * (Hred * Ored) + Q'.ofNat l * 0) +
        -((Q'.ofNat (a - i) * Q'.ofNat j) *
          (Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ hx0)
            (Q'.mul_eqv_congr_left _ _ _ hx1)))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ hx2)
              (Q'.mul_eqv_congr_left _ _ _ hx3))))
    · ring_zero_qeqv
  have hright :
      omegaCorrectionLowerCoefficient a b c d q.p *
            rightShellFactorialCoefficient qm i j l +
          omegaCorrectionDiagonalCoefficient a b c d q.p *
            rightShellFactorialCoefficient q i j l +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l ≈
        omegaCorrectionLowerCoefficient a b c d q.p *
          (Hfull * Ofull) := by
    refine Q'.eqv_trans _
      (omegaCorrectionLowerCoefficient a b c d q.p * (Hfull * Ofull) +
        omegaCorrectionDiagonalCoefficient a b c d q.p * 0 +
        omegaCorrectionUpperCoefficient a b c d q.p * 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hqm)
          (Q'.mul_eqv_congr_left _ _ _ hq))
        (Q'.mul_eqv_congr_left _ _ _ hqp)
    · ring_zero_qeqv
  unfold OmegaCorrectionShellAt
  refine Q'.eqv_trans _ _ _ (by simpa only [qr] using hleft) ?_
  refine Q'.eqv_trans _
    (omegaCorrectionLowerCoefficient a b c d q.p * (Hfull * Ofull)) _ ?_ ?_
  · simpa only [Hred, Ored, Hfull, Ofull] using
      lower_boundary_core qm q hp hprev i j l hsum
  · exact Q'.eqv_symm hright

private theorem firstBulk_scale_row_reassoc
    (P F G C W : Q') :
    (P * (F * G)) * (C * W) ≈ (P * ((F * G) * C)) * W := by
  ring_qeqv

/-- The complete strict first-bulk face of the on-shell Hahn residual.  All
inner and outer support factors are positive, so the common division-free
scale may be cancelled constructively. -/
theorem omegaCorrectionShellAt_first_bulk_strict {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = q.p)
    (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r < q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrm := lower_outer_order qm q hprev
  let qr := reducePositiveInnerRightChannel q hp
  have hqrp : qr.p = q.p - 1 := rfl
  have hqrr : qr.r = q.r := rfl
  have hqrf : qr.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  let H0 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) j l
  let H1 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) j (l - 1)
  let H2 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) (j - 1) l
  let H := transvectFactorialCoeff b c q.p j l
  let Hm := transvectFactorialCoeff b c qm.p j l
  let O1 := transvectFactorialCoeff
    a q.intermediate q.r (i - 1) 1
  let O := transvectFactorialCoeff a q.intermediate q.r i 0
  let Om := transvectFactorialCoeff a qm.intermediate qm.r i 1
  have hx0 : rightShellFactorialCoefficient qr (i - 1) j l ≈
      H0 * O1 := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega, hqrp,
      show j + l - (q.p - 1) = 1 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx1 : rightShellFactorialCoefficient qr i j (l - 1) ≈
      H1 * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j + (l - 1))]
    unfold hahnEntry
    rw [show j + (l - 1) - j = l - 1 by omega, hqrp,
      show j + (l - 1) - (q.p - 1) = 0 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx2 : rightShellFactorialCoefficient qr i (j - 1) l ≈
      H2 * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j - 1 + l)]
    unfold hahnEntry
    rw [show j - 1 + l - (j - 1) = l by omega, hqrp,
      show j - 1 + l - (q.p - 1) = 0 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx3 : rightShellFactorialCoefficient qr
      (i + 1) (j - 1) (l - 1) ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qr.p ≤ j - 1 + (l - 1))]
    exact Q'.eqv_refl 0
  have hqm : rightShellFactorialCoefficient qm i j l ≈ Hm * Om := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qm.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega,
      show j + l - qm.p = 1 by omega]
    exact Q'.eqv_refl _
  have hq : rightShellFactorialCoefficient q i j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : q.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega,
      show j + l - q.p = 0 by omega]
    exact Q'.eqv_refl _
  have hqp : rightShellFactorialCoefficient qp i j l ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qp.p ≤ j + l)]
    exact Q'.eqv_refl 0
  let E :=
    (Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) * (H0 * O1)) +
      (Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat l * (H1 * O)) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * (H2 * O)))
  have hleft :
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
        E := by
    unfold omegaExchangeCorrection
    refine Q'.eqv_trans _
      ((Q'.ofNat i * Q'.ofNat (b - j)) *
          (Q'.ofNat (c - l) * (H0 * O1) +
            Q'.ofNat l * (H1 * O)) +
        -((Q'.ofNat (a - i) * Q'.ofNat j) *
          (Q'.ofNat (c - l) * (H2 * O) + Q'.ofNat l * 0))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ hx0)
            (Q'.mul_eqv_congr_left _ _ _ hx1)))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ hx2)
              (Q'.mul_eqv_congr_left _ _ _ hx3))))
    · simp only [E]
      ring_zero_qeqv
  let K := Q'.ofNat q.p *
    (Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2))
  let W := H * O
  let X0 :=
    ((Q'.ofNat j * Q'.ofNat (b - q.p) +
          -(Q'.ofNat l * Q'.ofNat (c - q.p))) *
        (Q'.ofNat (i - q.r) *
            Q'.ofNat (q.intermediate - q.r) +
          -(Q'.ofNat q.r * Q'.ofNat (a - i + 1))) +
      -(Q'.ofNat q.intermediate *
        (Q'.ofNat i * Q'.ofNat l +
          Q'.ofNat (a - i) * Q'.ofNat j)))
  let X := Q'.ofNat (q.intermediate + 2) * X0
  let Y := Q'.ofNat q.intermediate *
    ((Q'.ofNat j * Q'.ofNat (b - q.p + 1) +
          -(Q'.ofNat l * Q'.ofNat (c - q.p + 1))) *
      (Q'.ofNat (i - q.r) *
          Q'.ofNat (q.intermediate - q.r + 1) +
        -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i))))
  let S := firstBulkScalarQ a b c q.intermediate q.p q.r i j l
  have hleftScaled : K *
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
        X * W := by
    refine Q'.eqv_trans _ (K * E) _
      (Q'.mul_eqv_congr_left K _ _ hleft) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (q.intermediate + 2) * (X0 * W)) _ ?_ ?_
    · simpa only [K, E, X0, W, H0, H1, H2, H, O1, O] using
        first_bulk_exchange_rows_scaled
          a b c q.intermediate q.p q.r i j l
            hj hl hsum hpb hpc hr hrf hri hia
    · simpa only [X] using Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat (q.intermediate + 2)) X0 W)
  let Lc := omegaCorrectionLowerCoefficient a b c d q.p
  let Dc := omegaCorrectionDiagonalCoefficient a b c d q.p
  have hright :
      omegaCorrectionLowerCoefficient a b c d q.p *
            rightShellFactorialCoefficient qm i j l +
          omegaCorrectionDiagonalCoefficient a b c d q.p *
            rightShellFactorialCoefficient q i j l +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l ≈
        Lc * (Hm * Om) + Dc * W := by
    refine Q'.eqv_trans _
      (Lc * (Hm * Om) + Dc * (H * O) +
        omegaCorrectionUpperCoefficient a b c d q.p * 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hqm)
          (Q'.mul_eqv_congr_left _ _ _ hq))
        (Q'.mul_eqv_congr_left _ _ _ hqp)
    · simp only [Lc, Dc, W]
      ring_zero_qeqv
  have hlower : K * (Lc * (Hm * Om)) ≈ Y * W := by
    simpa only [K, Lc, Y, W, Hm, Om, H, O] using
      first_bulk_lower_carrier_scaled
        qm q hp hprev i j l hj hl hsum hpb hpc hri
  have hdiag0 := omegaCorrectionDiagonalCoefficient_first_bulk_scalar
    q hp i j l hpb hpc (by omega) hia hsum
  have hdiag : K * (Dc * W) ≈ S * W := by
    refine Q'.eqv_trans _
      ((Q'.ofNat q.p *
        ((Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2)) * Dc)) * W) _
      (by
        simpa only [K] using (firstBulk_scale_row_reassoc
          (Q'.ofNat q.p) (Q'.ofNat q.intermediate)
            (Q'.ofNat (q.intermediate + 2)) Dc W)) ?_
    exact Q'.mul_eqv_congr_right _ _ W (by
      simpa only [Dc, S] using hdiag0)
  have hrightScaled : K *
      (omegaCorrectionLowerCoefficient a b c d q.p *
            rightShellFactorialCoefficient qm i j l +
          omegaCorrectionDiagonalCoefficient a b c d q.p *
            rightShellFactorialCoefficient q i j l +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l) ≈
        (Y + S) * W := by
    refine Q'.eqv_trans _ (K * (Lc * (Hm * Om) + Dc * W)) _
      (Q'.mul_eqv_congr_left K _ _ hright) ?_
    refine Q'.eqv_trans _
      (K * (Lc * (Hm * Om)) + K * (Dc * W)) _
      (Q'.mul_add_eqv K _ _) ?_
    refine Q'.eqv_trans _ (Y * W + S * W) _
      (Q'.add_eqv_congr' hlower hdiag) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv Y S W)
  have hsplit : X ≈ Y + S := by
    simpa only [X, X0, Y, S] using
      firstBulkScalarQ_split
        a b c q.intermediate q.p q.r i j l
  have hscaled : K *
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
      K *
        (omegaCorrectionLowerCoefficient a b c d q.p *
              rightShellFactorialCoefficient qm i j l +
            omegaCorrectionDiagonalCoefficient a b c d q.p *
              rightShellFactorialCoefficient q i j l +
            omegaCorrectionUpperCoefficient a b c d q.p *
              rightShellFactorialCoefficient qp i j l) :=
    Q'.eqv_trans _ _ _ hleftScaled
      (Q'.eqv_trans _ ((Y + S) * W) _
        (Q'.mul_eqv_congr_right _ _ W hsplit)
        (Q'.eqv_symm hrightScaled))
  have hK : (0 : Q') < K := Q'.mul_pos
    (ofNat_pos_of_pos q.p hp)
    (Q'.mul_pos
      (ofNat_pos_of_pos q.intermediate (by omega))
      (ofNat_pos_of_pos (q.intermediate + 2) (by omega)))
  unfold OmegaCorrectionShellAt
  simpa only [qr] using Q'.mul_left_cancel_of_pos hK hscaled

private theorem factorialCorrection_eq_shellCorrection
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l) :
    omegaExchangeCorrection a b c
        (fun u v w => guardedRightFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w s) i j l ≈
      omegaExchangeCorrection a b c
        (fun u v w => rightShellFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w) i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  have hqrp : qr.p = q.p - 1 := rfl
  have hqrr : qr.r = q.r := rfl
  have hs0 : s + qr.r + qr.p = (i - 1) + j + l := by
    rw [hqrp, hqrr]
    omega
  have hs1 : s + qr.r + qr.p = i + j + (l - 1) := by
    rw [hqrp, hqrr]
    omega
  have hs2 : s + qr.r + qr.p = i + (j - 1) + l := by
    rw [hqrp, hqrr]
    omega
  have hs3 : s + qr.r + qr.p = (i + 1) + (j - 1) + (l - 1) := by
    rw [hqrp, hqrr]
    omega
  have h0 := guardedRightFactorialCoefficient_eq_shell
    qr (i - 1) j l s hs0
  have h1 := guardedRightFactorialCoefficient_eq_shell
    qr i j (l - 1) s hs1
  have h2 := guardedRightFactorialCoefficient_eq_shell
    qr i (j - 1) l s hs2
  have h3 := guardedRightFactorialCoefficient_eq_shell
    qr (i + 1) (j - 1) (l - 1) s hs3
  unfold omegaExchangeCorrection
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ h0)
        (Q'.mul_eqv_congr_left _ _ _ h1)))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h2)
          (Q'.mul_eqv_congr_left _ _ _ h3))))

private theorem factorialRHS_eq_shellRHS {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l) :
    omegaCorrectionLowerCoefficient a b c d q.p *
          guardedRightFactorialCoefficient qm i j l s +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          guardedRightFactorialCoefficient q i j l s +
        omegaCorrectionUpperCoefficient a b c d q.p *
          guardedRightFactorialCoefficient qp i j l s ≈
      omegaCorrectionLowerCoefficient a b c d q.p *
          rightShellFactorialCoefficient qm i j l +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          rightShellFactorialCoefficient q i j l +
        omegaCorrectionUpperCoefficient a b c d q.p *
          rightShellFactorialCoefficient qp i j l := by
  have hrm := lower_outer_order qm q hprev
  have hrp := upper_outer_order q qp hnext
  have hsm : s + qm.r + qm.p = i + j + l := by omega
  have hsp : s + qp.r + qp.p = i + j + l := by omega
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (guardedRightFactorialCoefficient_eq_shell qm i j l s hsm))
      (Q'.mul_eqv_congr_left _ _ _
        (guardedRightFactorialCoefficient_eq_shell q i j l s hshell)))
    (Q'.mul_eqv_congr_left _ _ _
      (guardedRightFactorialCoefficient_eq_shell qp i j l s hsp))

/-- On the common output shell, the guarded residual is exactly the
three-product Hahn identity `OmegaCorrectionShellAt`, independent of `s`. -/
theorem omegaCorrectionFactorialAt_on_shell_iff_shell {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s ↔
      OmegaCorrectionShellAt qm q qp hp i j l := by
  have hleft := factorialCorrection_eq_shellCorrection
    q hp i j l s hi hj hl hshell
  have hright := factorialRHS_eq_shellRHS
    qm q qp hprev hnext i j l s hshell
  constructor
  · intro h
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
      (Q'.eqv_trans _ _ _ h hright)
  · intro h
    exact Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ h (Q'.eqv_symm hright))

/-- Guarded factorial correction on the first genuine inner-support face. -/
theorem omegaCorrectionFactorialAt_lower_boundary_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = qm.p) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s hi hj hl hshell).2
  exact omegaCorrectionShellAt_lower_boundary
    qm q qp hp hprev hnext i j l hj hl hsum

/-- Raw three-carrier correction on the first genuine inner-support face. -/
theorem omegaCorrectionThreeCarrierAt_lower_boundary_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = qm.p) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_lower_boundary_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum)

/-- Guarded factorial correction on the strict first-bulk face. -/
theorem omegaCorrectionFactorialAt_first_bulk_strict_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r < q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s hi hj hl hshell).2
  exact omegaCorrectionShellAt_first_bulk_strict
    qm q qp hp hprev hnext i j l hj hl hsum hpb hpc hr hrf hri hia

/-- Raw three-carrier correction on the strict first-bulk face. -/
theorem omegaCorrectionThreeCarrierAt_first_bulk_strict_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r < q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_first_bulk_strict_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc
        hr hrf hri hia)

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionFactorialAt_off_total_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionThreeCarrierAt_off_total_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionFactorialAt_on_shell_iff_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_lowest_row_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.lowest_row_double_label_shift
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_zero_second_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.zero_second_outer_adjacent_shift
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionShellAt_lower_boundary
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionFactorialAt_lower_boundary_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionThreeCarrierAt_lower_boundary_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_second_one_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_second_one_factored
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_one_above_lowest_two_term
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.transvectFactorialCoeff_one_above_lowest_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.lowest_row_first_predecessor_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.lowest_row_second_predecessor_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.one_above_lowest_scaled_to_lowest
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.second_one_scaled_to_zero_next
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.upper_second_one_scaled_to_base_zero
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionDiagonalNumerator_first_bulk_int
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.firstBulkScalarQ_eq_int
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionDiagonalCoefficient_first_bulk_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionDiagonalCoefficient_first_bulk_scalar
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.first_bulk_inner_above_reduced
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.first_bulk_lower_carrier_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.first_bulk_exchange_rows_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.firstBulkScalarQ_split
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionShellAt_first_bulk_strict
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionFactorialAt_first_bulk_strict_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn.omegaCorrectionThreeCarrierAt_first_bulk_strict_on_shell
