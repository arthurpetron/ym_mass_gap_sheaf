/-
# Exact degree-split transport for the ordered Racah outer shifts

The first/second and first/third physical channel shifts both lower the total
source degree by two.  Their inner Hahn factors are related to the unshifted
factor by the two Euler splits proved below.  These identities are uniform in
the contraction order and use the closed factorial coefficients, not finite
enumeration.
-/

import YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell
import YMGap.Continuum.SU2TransvectantRowNormRecurrence
import YMGap.Continuum.SU2TransvectantHighestWeightRowFormula

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Q'.ofInt]; ac_rfl))

private theorem scale_zero_left (a x : Q') (hx : x ≈ 0) : a * x ≈ 0 :=
  Q'.eqv_trans _ (a * 0) _ (Q'.mul_eqv_congr_left a _ _ hx)
    (Q'.mul_zero_eqv a)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- Universal one-label Euler split for a falling factorial.  It includes the
endpoint and the out-of-support range, where both sides vanish. -/
theorem tvFallQ_degree_split (n r : Nat) :
    Q'.ofNat n * tvFallQ (n - 1) r ≈
      Q'.ofNat (n - r) * tvFallQ n r := by
  by_cases hr : r < n
  · have hlead := tvFallQ_leading_shift n r
    have htrail := tvFallQ_trailing_shift n r (by omega)
    exact Q'.eqv_trans _ _ _ hlead
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm htrail)
        (Q'.mul_comm_eqv _ _))
  · by_cases hn : n = 0
    · subst n
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (by
          simpa only [Nat.zero_sub] using Q'.zero_mul_eqv (tvFallQ 0 r)))
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hleftFall : tvFallQ (n - 1) r ≈ 0 :=
        tvFallQ_eqv_zero_of_lt (n - 1) r (by omega)
      have hleft : Q'.ofNat n * tvFallQ (n - 1) r ≈ 0 :=
        scale_zero_left _ _ hleftFall
      by_cases hre : r = n
      · subst r
        exact Q'.eqv_trans _ 0 _ hleft
          (Q'.eqv_symm (by
            simpa only [Nat.sub_self] using Q'.zero_mul_eqv (tvFallQ n n)))
      · have hrightFall : tvFallQ n r ≈ 0 :=
          tvFallQ_eqv_zero_of_lt n r (by omega)
        exact Q'.eqv_trans _ 0 _ hleft
          (Q'.eqv_symm (scale_zero_left _ _ hrightFall))

private theorem raising_term_split
    (m n k i j r : Nat) (hi0 : 0 < i) (hj0 : 0 < j)
    (hi : i ≤ m) (hj : j ≤ n) (hr : r < k + 1) :
    Q'.ofNat i *
          (tvPhase r * tvBinomQ k r * tvFallQ (i - 1) (k - r) *
            tvFallQ ((m - 1) - (i - 1)) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) +
        Q'.ofNat j *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ (j - 1) r *
            tvFallQ ((n - 1) - (j - 1)) (k - r)) ≈
      Q'.ofNat (i + j - k) *
        (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
          tvFallQ (m - i) r * tvFallQ j r *
          tvFallQ (n - j) (k - r)) := by
  have hm : (m - 1) - (i - 1) = m - i := by omega
  have hn : (n - 1) - (j - 1) = n - j := by omega
  rw [hm, hn]
  by_cases hui : k - r ≤ i
  · by_cases hrj : r ≤ j
    · have hfi := tvFallQ_degree_split i (k - r)
      have hfj := tvFallQ_degree_split j r
      have hnat : (i - (k - r)) + (j - r) = i + j - k := by omega
      refine Q'.eqv_trans _
        (Q'.ofNat (i - (k - r)) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) +
          Q'.ofNat (j - r) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (by
            refine Q'.eqv_trans _
              ((Q'.ofNat i * tvFallQ (i - 1) (k - r)) *
                (tvPhase r * tvBinomQ k r * tvFallQ (m - i) r *
                  tvFallQ j r * tvFallQ (n - j) (k - r))) _
                (by ring_qeqv) ?_
            refine Q'.eqv_trans _
              ((Q'.ofNat (i - (k - r)) * tvFallQ i (k - r)) *
                (tvPhase r * tvBinomQ k r * tvFallQ (m - i) r *
                  tvFallQ j r * tvFallQ (n - j) (k - r))) _
              (Q'.mul_eqv_congr_right _ _ _ hfi) (by ring_qeqv))
          (by
            refine Q'.eqv_trans _
              ((Q'.ofNat j * tvFallQ (j - 1) r) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ (m - i) r * tvFallQ (n - j) (k - r))) _
                (by ring_qeqv) ?_
            refine Q'.eqv_trans _
              ((Q'.ofNat (j - r) * tvFallQ j r) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ (m - i) r * tvFallQ (n - j) (k - r))) _
              (Q'.mul_eqv_congr_right _ _ _ hfj) (by ring_qeqv))
      · rw [← hnat]
        have hadd := Q'.ofNat_add_eqv (i - (k - r)) (j - r)
        refine Q'.eqv_trans _
          ((Q'.ofNat (i - (k - r)) + Q'.ofNat (j - r)) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r))) _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hadd)
    · have hz := tvFallQ_eqv_zero_of_lt j r (by omega)
      have hz' := tvFallQ_eqv_zero_of_lt (j - 1) r (by omega)
      have hzero0 :
          Q'.ofNat i *
            (tvPhase r * tvBinomQ k r * tvFallQ (i - 1) (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat i * tvPhase r * tvBinomQ k r *
            tvFallQ (i - 1) (k - r) * tvFallQ (m - i) r *
            tvFallQ (n - j) (k - r)) * tvFallQ j r) _
          (by ring_qeqv) (scale_zero_left _ _ hz)
      have hzero1 :
          Q'.ofNat j *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ (j - 1) r *
              tvFallQ (n - j) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat j * tvPhase r * tvBinomQ k r *
            tvFallQ i (k - r) * tvFallQ (m - i) r *
            tvFallQ (n - j) (k - r)) * tvFallQ (j - 1) r) _
          (by ring_qeqv) (scale_zero_left _ _ hz')
      have hzeroT :
          Q'.ofNat (i + j - k) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (i + j - k) * tvPhase r * tvBinomQ k r *
            tvFallQ i (k - r) * tvFallQ (m - i) r *
            tvFallQ (n - j) (k - r)) * tvFallQ j r) _
          (by ring_qeqv) (scale_zero_left _ _ hz)
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr' hzero0 hzero1
      · exact Q'.eqv_trans _ 0 _ (by decide) (Q'.eqv_symm hzeroT)
  · have hz := tvFallQ_eqv_zero_of_lt i (k - r) (by omega)
    have hz' := tvFallQ_eqv_zero_of_lt (i - 1) (k - r) (by omega)
    have hzero0 :
        Q'.ofNat i *
          (tvPhase r * tvBinomQ k r * tvFallQ (i - 1) (k - r) *
            tvFallQ (m - i) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat i * tvPhase r * tvBinomQ k r * tvFallQ (m - i) r *
          tvFallQ j r * tvFallQ (n - j) (k - r)) *
          tvFallQ (i - 1) (k - r)) _
        (by ring_qeqv) (scale_zero_left _ _ hz')
    have hzero1 :
        Q'.ofNat j *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ (j - 1) r *
            tvFallQ (n - j) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat j * tvPhase r * tvBinomQ k r * tvFallQ (m - i) r *
          tvFallQ (j - 1) r * tvFallQ (n - j) (k - r)) *
          tvFallQ i (k - r)) _
        (by ring_qeqv) (scale_zero_left _ _ hz)
    have hzeroT :
        Q'.ofNat (i + j - k) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat (i + j - k) * tvPhase r * tvBinomQ k r *
          tvFallQ (m - i) r * tvFallQ j r *
          tvFallQ (n - j) (k - r)) * tvFallQ i (k - r)) _
        (by ring_qeqv) (scale_zero_left _ _ hz)
    refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr' hzero0 hzero1
    · exact Q'.eqv_trans _ 0 _ (by decide) (Q'.eqv_symm hzeroT)

/-- Coordinate-degree Euler split.  The current Hahn row is reconstructed
from the two one-label-lowered rows, with the exact positive coordinate
factor `i+j-k`. -/
theorem transvectFactorialCoeff_coordinate_degree_split
    (m n k i j : Nat) (hi0 : 0 < i) (hj0 : 0 < j)
    (hi : i ≤ m) (hj : j ≤ n) :
    Q'.ofNat i * transvectFactorialCoeff (m - 1) n k (i - 1) j +
        Q'.ofNat j * transvectFactorialCoeff m (n - 1) k i (j - 1) ≈
      Q'.ofNat (i + j - k) * transvectFactorialCoeff m n k i j := by
  unfold transvectFactorialCoeff
  let f : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ (i - 1) (k - r) *
      tvFallQ ((m - 1) - (i - 1)) r * tvFallQ j r *
      tvFallQ (n - j) (k - r)
  let g : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ (m - i) r * tvFallQ (j - 1) r *
      tvFallQ ((n - 1) - (j - 1)) (k - r)
  let h : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ (m - i) r * tvFallQ j r *
      tvFallQ (n - j) (k - r)
  refine Q'.eqv_trans _
    (finSum (fun r => Q'.ofNat i * f r) (k + 1) +
      finSum (fun r => Q'.ofNat j * g r) (k + 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (by simpa only [f] using const_mul_finSum f (Q'.ofNat i) (k + 1))
      (by simpa only [g] using const_mul_finSum g (Q'.ofNat j) (k + 1))
  · refine Q'.eqv_trans _
      (finSum (fun r => Q'.ofNat i * f r + Q'.ofNat j * g r)
      (k + 1)) _
      (Q'.eqv_symm (RationalTail.finSum_add _ _ (k + 1))) ?_
    refine Q'.eqv_trans _
      (finSum (fun r => Q'.ofNat (i + j - k) * h r) (k + 1)) _
      (finSum_eqv_congr_lt _ _ (k + 1) (fun r hr => by
        simpa only [f, g, h] using
          raising_term_split m n k i j r hi0 hj0 hi hj hr)) ?_
    exact Q'.eqv_symm
      (by simpa only [h] using
        const_mul_finSum h (Q'.ofNat (i + j - k)) (k + 1))

private theorem complement_term_split
    (m n k i j r : Nat) (hi : i < m) (hj : j < n)
    (hr : r < k + 1) :
    Q'.ofNat (m - i) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ ((m - 1) - i) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) +
        Q'.ofNat (n - j) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ j r *
            tvFallQ ((n - 1) - j) (k - r)) ≈
      Q'.ofNat (m + n - i - j - k) *
        (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
          tvFallQ (m - i) r * tvFallQ j r *
          tvFallQ (n - j) (k - r)) := by
  have hm : (m - 1) - i = (m - i) - 1 := by omega
  have hn : (n - 1) - j = (n - j) - 1 := by omega
  rw [hm, hn]
  by_cases hrm : r ≤ m - i
  · by_cases huk : k - r ≤ n - j
    · have hfm := tvFallQ_degree_split (m - i) r
      have hfn := tvFallQ_degree_split (n - j) (k - r)
      have hnat : ((m - i) - r) + ((n - j) - (k - r)) =
          m + n - i - j - k := by omega
      refine Q'.eqv_trans _
        (Q'.ofNat ((m - i) - r) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) +
          Q'.ofNat ((n - j) - (k - r)) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (by
            refine Q'.eqv_trans _
              ((Q'.ofNat (m - i) * tvFallQ ((m - i) - 1) r) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ j r * tvFallQ (n - j) (k - r))) _
                (by ring_qeqv) ?_
            refine Q'.eqv_trans _
              ((Q'.ofNat ((m - i) - r) * tvFallQ (m - i) r) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ j r * tvFallQ (n - j) (k - r))) _
              (Q'.mul_eqv_congr_right _ _ _ hfm) (by ring_qeqv))
          (by
            refine Q'.eqv_trans _
              ((Q'.ofNat (n - j) *
                  tvFallQ ((n - j) - 1) (k - r)) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ (m - i) r * tvFallQ j r)) _
                (by ring_qeqv) ?_
            refine Q'.eqv_trans _
              ((Q'.ofNat ((n - j) - (k - r)) *
                  tvFallQ (n - j) (k - r)) *
                (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
                  tvFallQ (m - i) r * tvFallQ j r)) _
              (Q'.mul_eqv_congr_right _ _ _ hfn) (by ring_qeqv))
      · rw [← hnat]
        have hadd := Q'.ofNat_add_eqv ((m - i) - r)
          ((n - j) - (k - r))
        refine Q'.eqv_trans _
          ((Q'.ofNat ((m - i) - r) +
              Q'.ofNat ((n - j) - (k - r))) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r))) _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hadd)
    · have hz := tvFallQ_eqv_zero_of_lt (n - j) (k - r) (by omega)
      have hz' := tvFallQ_eqv_zero_of_lt ((n - j) - 1) (k - r) (by omega)
      have hzero0 :
          Q'.ofNat (m - i) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ ((m - i) - 1) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (m - i) * tvPhase r * tvBinomQ k r *
            tvFallQ i (k - r) * tvFallQ ((m - i) - 1) r *
            tvFallQ j r) * tvFallQ (n - j) (k - r)) _
          (by ring_qeqv) (scale_zero_left _ _ hz)
      have hzero1 :
          Q'.ofNat (n - j) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ ((n - j) - 1) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (n - j) * tvPhase r * tvBinomQ k r *
            tvFallQ i (k - r) * tvFallQ (m - i) r * tvFallQ j r) *
            tvFallQ ((n - j) - 1) (k - r)) _
          (by ring_qeqv) (scale_zero_left _ _ hz')
      have hzeroT :
          Q'.ofNat (m + n - i - j - k) *
            (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
              tvFallQ (m - i) r * tvFallQ j r *
              tvFallQ (n - j) (k - r)) ≈ 0 := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (m + n - i - j - k) * tvPhase r * tvBinomQ k r *
            tvFallQ i (k - r) * tvFallQ (m - i) r * tvFallQ j r) *
            tvFallQ (n - j) (k - r)) _
          (by ring_qeqv) (scale_zero_left _ _ hz)
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr' hzero0 hzero1
      · exact Q'.eqv_trans _ 0 _ (by decide) (Q'.eqv_symm hzeroT)
  · have hz := tvFallQ_eqv_zero_of_lt (m - i) r (by omega)
    have hz' := tvFallQ_eqv_zero_of_lt ((m - i) - 1) r (by omega)
    have hzero0 :
        Q'.ofNat (m - i) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ ((m - i) - 1) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat (m - i) * tvPhase r * tvBinomQ k r *
          tvFallQ i (k - r) * tvFallQ j r *
          tvFallQ (n - j) (k - r)) * tvFallQ ((m - i) - 1) r) _
        (by ring_qeqv) (scale_zero_left _ _ hz')
    have hzero1 :
        Q'.ofNat (n - j) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ j r *
            tvFallQ ((n - j) - 1) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat (n - j) * tvPhase r * tvBinomQ k r *
          tvFallQ i (k - r) * tvFallQ j r *
          tvFallQ ((n - j) - 1) (k - r)) * tvFallQ (m - i) r) _
        (by ring_qeqv) (scale_zero_left _ _ hz)
    have hzeroT :
        Q'.ofNat (m + n - i - j - k) *
          (tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
            tvFallQ (m - i) r * tvFallQ j r *
            tvFallQ (n - j) (k - r)) ≈ 0 := by
      refine Q'.eqv_trans _
        ((Q'.ofNat (m + n - i - j - k) * tvPhase r * tvBinomQ k r *
          tvFallQ i (k - r) * tvFallQ j r *
          tvFallQ (n - j) (k - r)) * tvFallQ (m - i) r) _
        (by ring_qeqv) (scale_zero_left _ _ hz)
    refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr' hzero0 hzero1
    · exact Q'.eqv_trans _ 0 _ (by decide) (Q'.eqv_symm hzeroT)

/-- Complementary-degree Euler split.  The omitted-coordinate factor is the
sum of the first/second and first/third one-label-lowered rows. -/
theorem transvectFactorialCoeff_complement_degree_split
    (m n k i j : Nat) (hi : i < m) (hj : j < n) :
    Q'.ofNat (m - i) * transvectFactorialCoeff (m - 1) n k i j +
        Q'.ofNat (n - j) * transvectFactorialCoeff m (n - 1) k i j ≈
      Q'.ofNat (m + n - i - j - k) *
        transvectFactorialCoeff m n k i j := by
  unfold transvectFactorialCoeff
  let f : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ ((m - 1) - i) r * tvFallQ j r *
      tvFallQ (n - j) (k - r)
  let g : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ (m - i) r * tvFallQ j r *
      tvFallQ ((n - 1) - j) (k - r)
  let h : Nat → Q' := fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
      tvFallQ (m - i) r * tvFallQ j r *
      tvFallQ (n - j) (k - r)
  refine Q'.eqv_trans _
    (finSum (fun r => Q'.ofNat (m - i) * f r) (k + 1) +
      finSum (fun r => Q'.ofNat (n - j) * g r) (k + 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (by simpa only [f] using
        const_mul_finSum f (Q'.ofNat (m - i)) (k + 1))
      (by simpa only [g] using
        const_mul_finSum g (Q'.ofNat (n - j)) (k + 1))
  · refine Q'.eqv_trans _
      (finSum
        (fun r => Q'.ofNat (m - i) * f r + Q'.ofNat (n - j) * g r)
        (k + 1)) _
      (Q'.eqv_symm (RationalTail.finSum_add _ _ (k + 1))) ?_
    refine Q'.eqv_trans _
      (finSum (fun r => Q'.ofNat (m + n - i - j - k) * h r)
        (k + 1)) _
      (finSum_eqv_congr_lt _ _ (k + 1) (fun r hr => by
        simpa only [f, g, h] using
          complement_term_split m n k i j r hi hj hr)) ?_
    exact Q'.eqv_symm
      (by simpa only [h] using
        const_mul_finSum h (Q'.ofNat (m + n - i - j - k)) (k + 1))

/-- The product of an inner Hahn row and its outer Hahn row is reconstructed
from the two physical degree-lowering directions.  This is the exact carrier
identity underlying the first/second and first/third `N-2` channel maps. -/
theorem nestedFactorialCarrier_two_direction_transport
    (a b c p r i j l : Nat)
    (hr : 0 < r) (hj : 0 < j) (hl : 0 < l)
    (hjb : j < b) (hlc : l < c)
    (hpjl : p < j + l) (hdegree : j + l + p ≤ b + c) :
    Q'.ofNat i *
          (Q'.ofNat (b - j) *
              (transvectFactorialCoeff (b - 1) c p j l *
                transvectFactorialCoeff (a - 1) (b + c - 2 * p - 1)
                  (r - 1) (i - 1) (j + l - p)) +
            Q'.ofNat (c - l) *
              (transvectFactorialCoeff b (c - 1) p j l *
                transvectFactorialCoeff (a - 1) (b + c - 2 * p - 1)
                  (r - 1) (i - 1) (j + l - p))) +
        -(Q'.ofNat (a - i) *
          (Q'.ofNat j *
              (transvectFactorialCoeff (b - 1) c p (j - 1) l *
                transvectFactorialCoeff (a - 1) (b + c - 2 * p - 1)
                  (r - 1) i (j + l - p - 1)) +
            Q'.ofNat l *
              (transvectFactorialCoeff b (c - 1) p j (l - 1) *
                transvectFactorialCoeff (a - 1) (b + c - 2 * p - 1)
                  (r - 1) i (j + l - p - 1)))) ≈
      transvectFactorialCoeff b c p j l *
        transvectFactorialCoeff a (b + c - 2 * p) r i (j + l - p) := by
  let H := transvectFactorialCoeff b c p j l
  let HB := transvectFactorialCoeff (b - 1) c p j l
  let HC := transvectFactorialCoeff b (c - 1) p j l
  let HBp := transvectFactorialCoeff (b - 1) c p (j - 1) l
  let HCp := transvectFactorialCoeff b (c - 1) p j (l - 1)
  let f := b + c - 2 * p
  let h := j + l - p
  let O0 := transvectFactorialCoeff (a - 1) (f - 1)
    (r - 1) (i - 1) h
  let O1 := transvectFactorialCoeff (a - 1) (f - 1)
    (r - 1) i (h - 1)
  let O := transvectFactorialCoeff a f r i h
  have hf : 0 < f := by
    dsimp only [f]
    omega
  have hh : 0 < h := by
    dsimp only [h]
    omega
  have hfh : f - h = b + c - j - l - p := by
    dsimp only [f, h]
    omega
  have hinner0 := transvectFactorialCoeff_complement_degree_split
    b c p j l hjb hlc
  have hinner0' :
      Q'.ofNat (b - j) * HB + Q'.ofNat (c - l) * HC ≈
        Q'.ofNat (f - h) * H := by
    simpa only [H, HB, HC, f, h, hfh] using hinner0
  have hinner1 := transvectFactorialCoeff_coordinate_degree_split
    b c p j l hj hl (by omega) (by omega)
  have hinner1' :
      Q'.ofNat j * HBp + Q'.ofNat l * HCp ≈
        Q'.ofNat h * H := by
    simpa only [H, HBp, HCp, h] using hinner1
  have houter0 := transvectFactorialCoeff_succ a f (r - 1) i h
  have houter :
      (Q'.ofNat i * Q'.ofNat (f - h)) * O0 +
          -((Q'.ofNat (a - i) * Q'.ofNat h) * O1) ≈ O := by
    have hmul0 := ofNat_mul_eqv i (f - h)
    have hmul1 := ofNat_mul_eqv (a - i) h
    have hr' : r - 1 + 1 = r := by omega
    rw [hr'] at houter0
    refine Q'.eqv_trans _
      (Q'.ofNat (i * (f - h)) * O0 +
        (-(Q'.ofNat ((a - i) * h))) * O1) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ O0 hmul0)
        (Q'.eqv_trans _ ((-(Q'.ofNat (a - i) * Q'.ofNat h)) * O1) _
          (Q'.eqv_symm (Q'.neg_mul_eqv _ _))
          (Q'.mul_eqv_congr_right _ _ O1
            (Q'.neg_eqv_congr _ _ hmul1)))
    · simpa only [O0, O1, O] using houter0
  change
    Q'.ofNat i *
          (Q'.ofNat (b - j) * (HB * O0) +
            Q'.ofNat (c - l) * (HC * O0)) +
        -(Q'.ofNat (a - i) *
          (Q'.ofNat j * (HBp * O1) + Q'.ofNat l * (HCp * O1))) ≈
      H * O
  refine Q'.eqv_trans _
    (Q'.ofNat i * ((Q'.ofNat (b - j) * HB +
        Q'.ofNat (c - l) * HC) * O0) +
      -(Q'.ofNat (a - i) *
        ((Q'.ofNat j * HBp + Q'.ofNat l * HCp) * O1))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat i * ((Q'.ofNat (f - h) * H) * O0) +
      -(Q'.ofNat (a - i) * ((Q'.ofNat h * H) * O1))) _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ O0 hinner0'))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ O1 hinner1')))) ?_
  refine Q'.eqv_trans _
    (H * (((Q'.ofNat i * Q'.ofNat (f - h)) * O0) +
      -((Q'.ofNat (a - i) * Q'.ofNat h) * O1))) _
    (by ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left H _ _ houter

/-- Four-term reconstruction functional on the two `N-2` shifted channel
families.  Its coefficients are the literal source-coordinate Euler factors. -/
def outerShiftReconstruction
    {a b c d : Nat}
    (qs : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (i j l : Nat) : Q' :=
  Q'.ofNat i *
      (Q'.ofNat (b - j) * rightShellFactorialCoefficient qs (i - 1) j l +
        Q'.ofNat (c - l) * rightShellFactorialCoefficient qt (i - 1) j l) +
    -(Q'.ofNat (a - i) *
      (Q'.ofNat j * rightShellFactorialCoefficient qs i (j - 1) l +
        Q'.ofNat l * rightShellFactorialCoefficient qt i j (l - 1)))

/-- Specialization of the exact carrier identity to the proof-carrying
first/second and first/third physical channel maps. -/
theorem rightShellFactorialCoefficient_outerShift_transport
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpb : q.p < b) (hpc : q.p < c) (hr : 0 < q.r)
    (i j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hjb : j < b) (hlc : l < c)
    (hhigh : q.p < j + l) (hdegree : j + l + q.p ≤ b + c) :
    outerShiftReconstruction
        (reduceFirstSecondRightChannel q ha hb hpb hr)
        (reduceFirstThirdRightChannel q ha hc hpc hr) i j l ≈
      rightShellFactorialCoefficient q i j l := by
  let qs := reduceFirstSecondRightChannel q ha hb hpb hr
  let qt := reduceFirstThirdRightChannel q ha hc hpc hr
  have hsj : qs.p ≤ (j - 1) + l := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    omega
  have hsl : qt.p ≤ j + (l - 1) := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    omega
  have hs : qs.p ≤ j + l := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    omega
  have ht : qt.p ≤ j + l := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    omega
  have hq : q.p ≤ j + l := by omega
  have hbase := nestedFactorialCarrier_two_direction_transport
    a b c q.p q.r i j l hr hj hl hjb hlc hhigh hdegree
  unfold outerShiftReconstruction rightShellFactorialCoefficient
  rw [if_pos hs, if_pos ht, if_pos hsj, if_pos hsl, if_pos hq]
  have hqs := reduceFirstSecondRightChannel_intermediate q ha hb hpb hr
  have hqt := reduceFirstThirdRightChannel_intermediate q ha hc hpc hr
  have hfs : (b - 1) + c - 2 * q.p = b + c - 2 * q.p - 1 := by
    omega
  have hft : b + (c - 1) - 2 * q.p = b + c - 2 * q.p - 1 := by
    omega
  have hqf : q.intermediate = b + c - 2 * q.p := rfl
  have hsi : (reduceFirstSecondRightChannel q ha hb hpb hr).intermediate =
      b + c - 2 * q.p - 1 := by
    rw [hqs, hqf]
  have hti : (reduceFirstThirdRightChannel q ha hc hpc hr).intermediate =
      b + c - 2 * q.p - 1 := by
    rw [hqt, hqf]
  rw [hsi, hti, hqf]
  simp only [hahnEntry, reduceFirstSecondRightChannel,
    reduceFirstThirdRightChannel]
  rw [show j + l - j = l by omega,
    show (j - 1) + l - (j - 1) = l by omega,
    show j + (l - 1) - j = l - 1 by omega,
    show j - 1 + l - q.p = j + l - q.p - 1 by omega,
    show j + (l - 1) - q.p = j + l - q.p - 1 by omega]
  simpa only [hfs, hft] using hbase

/-- Every coefficient used by the strict physical outer-shift transport is
constructively nonzero.  Hence later residual cancellation cannot be vacuous. -/
theorem outerShiftReconstruction_factors_pos
    (a b c i j l : Nat) (hi : i < a) (hi0 : 0 < i)
    (hj : 0 < j) (hl : 0 < l) (hjb : j < b) (hlc : l < c) :
    0 < i * (b - j) ∧ 0 < i * (c - l) ∧
      0 < (a - i) * j ∧ 0 < (a - i) * l := by
  refine ⟨Nat.mul_pos hi0 (by omega), Nat.mul_pos hi0 (by omega),
    Nat.mul_pos (by omega) hj, Nat.mul_pos (by omega) hl⟩

/-- Coefficientwise invariance is not the residual transport mechanism: the
upper correction coefficient changes under an `N-2` first/second shift even
at a strict physical block.  Any full correction transport must therefore
prove the common commutator remainder, rather than silently reuse the current
three coefficients on the shifted rows. -/
theorem naive_upperCorrectionCoefficient_shift_invariance_refuted :
    ¬ (omegaCorrectionUpperCoefficient 5 4 4 7 1 ≈
      omegaCorrectionUpperCoefficient 4 3 4 7 1) := by
  decide

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.tvFallQ_degree_split
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.transvectFactorialCoeff_coordinate_degree_split
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.transvectFactorialCoeff_complement_degree_split
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.nestedFactorialCarrier_two_direction_transport
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.rightShellFactorialCoefficient_outerShift_transport
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.outerShiftReconstruction_factors_pos
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport.naive_upperCorrectionCoefficient_shift_invariance_refuted
