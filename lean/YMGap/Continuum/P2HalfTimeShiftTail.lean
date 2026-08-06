/-
Track 11.7-fusion / R4h -- exact sharp-cutoff shift rows and the physical
half-time high-shift certificate.

The exact strand reindex identifies the physical Clebsch box with a sharply
truncated lag-correlation line sum.  This module changes the order of its two
finite sums once more:

  lineSum(lagCorr w N,t) ~= sum_{r<=N} shiftRow(w,N,t,r),

where `shiftRow` is the autoconvolution of the coefficient tail `c_r,...,c_N`.
It also proves, for an arbitrary nonnegative sequence, the weighted successor
identity behind

  (s+1) A_{s+1} <= q (s+2) A_s

whenever every coefficient successor is at most `q` times its predecessor.
Thus the large finite row comparison is replaced by one theorem about finite
computation.

The physical specialization below uses reciprocal Bernoulli.  If

  D_k <= (r+1)(2r+1-s),

then every coefficient at shift `r` or above has successor ratio at most
`blockWeight(k)^(s+2)`.  This is the explicit high-shift payment condition.

Honest scope: the exact reindex, generic successor compiler, and every row at
or above `ceil((5*2^k+s)/2)` are proved here, as is their aggregate.  The
strictly smaller low-shift prefix still has to be paid; no all-scale control
family or Yang--Mills mass gap is claimed by this module alone.

Constructive contract: Mathlib-free `Nat`/`Q'`; no `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
import YMGap.Continuum.P2BlockCompatibleScheduleClosed
import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.ReciprocalBernoulliUpper

namespace YMGap.Continuum.P2HalfTimeShiftTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact sharp-cutoff shift rows -/

/-- The coefficient tail beginning at shift `r`, with the physical cutoff
installed as a Boolean mask. -/
def cutoffCoeff (w : Q') (N r n : Nat) : Q' :=
  if n + r < N + 1 then coeffW w (n + r) else 0

/-- The `r`-th sharply truncated autoconvolution row. -/
def cutoffShiftRow (w : Q') (N t r : Nat) : Q' :=
  fsum (fun p => cutoffCoeff w N r p * cutoffCoeff w N r (t - p)) (t + 1)

private theorem fsum_zero_extension {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i, n <= i -> (f i).eqv 0) :
    (fsum f m).eqv (fsum f n) := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (Q'.eqv_of_eq (Q'.add_zero' _))

/-- A Boolean-masked finite sum agrees with its exact prefix. -/
theorem fsum_masked_prefix (f : Nat -> Q') {n m : Nat}
    (hnm : n <= m) :
    (fsum (fun i => if i < n then f i else 0) m).eqv (fsum f n) := by
  have hext :
      (fsum (fun i => if i < n then f i else 0) m).eqv
        (fsum (fun i => if i < n then f i else 0) n) := by
    apply fsum_zero_extension hnm
    intro i hi
    rw [if_neg (Nat.not_lt_of_ge hi)]
    exact Q'.eqv_refl 0
  have hprefix :
      (fsum (fun i => if i < n then f i else 0) n).eqv (fsum f n) := by
    apply fsum_eqv_congr_lt
    intro i hi
    rw [if_pos hi]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hext hprefix

private theorem strand_cutoff_iff (N t p r : Nat) (hp : p < t + 1) :
    r < nP N t p ↔ p + r < N + 1 ∧ (t - p) + r < N + 1 := by
  unfold nP
  rcases Nat.le_total p (t - p) with hle | hge
  · simp only [Nat.max_eq_right hle]
    constructor
    · intro hr
      constructor <;> omega
    · rintro ⟨_, hright⟩
      omega
  · simp only [Nat.max_eq_left hge]
    constructor
    · intro hr
      constructor <;> omega
    · rintro ⟨hleft, _⟩
      omega

/-- The strand mask is exactly the product of the two endpoint cutoff masks. -/
theorem truncatedStrandTerm_eq_cutoffProduct (w : Q') (N t p r : Nat)
    (hp : p < t + 1) :
    (truncatedStrandTerm w N t p r).eqv
      (cutoffCoeff w N r p * cutoffCoeff w N r (t - p)) := by
  by_cases hr : r < nP N t p
  · have hends := (strand_cutoff_iff N t p r hp).mp hr
    unfold truncatedStrandTerm cutoffCoeff ccT
    rw [if_pos hr, if_pos hends.1, if_pos hends.2]
    exact Q'.eqv_refl _
  · have hnot : ¬ (p + r < N + 1 ∧ (t - p) + r < N + 1) := by
      exact fun h => hr ((strand_cutoff_iff N t p r hp).mpr h)
    unfold truncatedStrandTerm cutoffCoeff
    rw [if_neg hr]
    by_cases hpN : p + r < N + 1
    · have hqN : ¬ (t - p) + r < N + 1 := by
        exact fun h => hnot ⟨hpN, h⟩
      rw [if_pos hpN, if_neg hqN]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)
    · rw [if_neg hpN]
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)

/-- The sharply truncated lag-correlation line sum is exactly the sum of its
cutoff autoconvolution rows, with the shift coordinate outermost. -/
theorem lineSum_eq_cutoffShiftRows (w : Q') (N t : Nat) :
    (lineSum (lagCorr w N) t).eqv
      (fsum (fun r => cutoffShiftRow w N t r) (N + 1)) := by
  have eprefix :
      (lineSum (lagCorr w N) t).eqv
        (fsum (fun p => fsum (fun r =>
          truncatedStrandTerm w N t p r) (N + 1)) (t + 1)) := by
    unfold lineSum
    apply fsum_eqv_congr_lt
    intro p hp
    rw [lagCorr_ccT]
    unfold truncatedStrandTerm
    exact Q'.eqv_symm
      (fsum_masked_prefix (ccT w t p) (Nat.sub_le _ _))
  have eswap :
      (fsum (fun p => fsum (fun r =>
        truncatedStrandTerm w N t p r) (N + 1)) (t + 1)).eqv
        (fsum (fun r => fsum (fun p =>
          truncatedStrandTerm w N t p r) (t + 1)) (N + 1)) :=
    fsum_swap (fun p r => truncatedStrandTerm w N t p r) (t + 1) (N + 1)
  have erows :
      (fsum (fun r => fsum (fun p =>
        truncatedStrandTerm w N t p r) (t + 1)) (N + 1)).eqv
        (fsum (fun r => cutoffShiftRow w N t r) (N + 1)) := by
    apply fsum_eqv_congr_lt
    intro r _
    unfold cutoffShiftRow
    apply fsum_eqv_congr_lt
    intro p hp
    exact truncatedStrandTerm_eq_cutoffProduct w N t p r hp
  exact Q'.eqv_trans _ _ _ eprefix (Q'.eqv_trans _ _ _ eswap erows)

/-! ## 2. A proof-about-computation successor compiler -/

/-- Autoconvolution row of an arbitrary sequence. -/
def autoRow (x : Nat -> Q') (t : Nat) : Q' :=
  fsum (fun p => x p * x (t - p)) (t + 1)

private theorem weighted_cover (G : Nat -> Q') (s : Nat) :
    (Q'.ofNat (s + 1) * fsum G (s + 2)).eqv
      (fsum (fun p =>
        Q'.ofNat (p + 1) * G (p + 1) +
          Q'.ofNat (s - p + 1) * G p) (s + 1)) := by
  have econst :
      (Q'.ofNat (s + 1) * fsum G (s + 2)).eqv
        (fsum (fun j => Q'.ofNat (s + 1) * G j) (s + 2)) :=
    fsum_const_mul (Q'.ofNat (s + 1)) G (s + 2)
  have eterm :
      (fsum (fun j => Q'.ofNat (s + 1) * G j) (s + 2)).eqv
        (fsum (fun j =>
          Q'.ofNat j * G j + Q'.ofNat (s + 1 - j) * G j) (s + 2)) := by
    apply fsum_eqv_congr_lt
    intro j hj
    have hsum : j + (s + 1 - j) = s + 1 := by omega
    have hc : (Q'.ofNat (s + 1)).eqv
        (Q'.ofNat j + Q'.ofNat (s + 1 - j)) := by
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat hsum.symm))
        (Q'.ofNat_add_eqv j (s + 1 - j))
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (G j) hc)
      (Q'.add_mul_eqv _ _ _)
  have eadd :
      (fsum (fun j =>
        Q'.ofNat j * G j + Q'.ofNat (s + 1 - j) * G j) (s + 2)).eqv
        (fsum (fun j => Q'.ofNat j * G j) (s + 2) +
          fsum (fun j => Q'.ofNat (s + 1 - j) * G j) (s + 2)) :=
    fsum_add _ _ _
  have efirst :
      (fsum (fun j => Q'.ofNat j * G j) (s + 2)).eqv
        (fsum (fun p => Q'.ofNat (p + 1) * G (p + 1)) (s + 1)) := by
    let H : Nat -> Q' := fun j => Q'.ofNat j * G j
    have hshift := AFRateCalibration.fsum_shift_cons H (s + 1)
    have hzero : H 0 ≈ (0 : Q') := by
      unfold H
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (G 0) Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ _ _ hshift
      (Q'.eqv_trans _
        ((0 : Q') + fsum (fun p => Q'.ofNat (p + 1) * G (p + 1)) (s + 1)) _
        (Q'.add_eqv_congr_right _ _ _ hzero)
        (Q'.eqv_of_eq (Q'.zero_add' _)))
  have esecond :
      (fsum (fun j => Q'.ofNat (s + 1 - j) * G j) (s + 2)).eqv
        (fsum (fun p => Q'.ofNat (s - p + 1) * G p) (s + 1)) := by
    rw [fsum_succ]
    have hlast : Q'.ofNat (s + 1 - (s + 1)) * G (s + 1) ≈ (0 : Q') := by
      have hz : Q'.ofNat (s + 1 - (s + 1)) ≈ (0 : Q') := by
        simpa only [Nat.sub_self] using Q'.ofNat_zero_eqv
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hz)
        (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (fsum_eqv_congr_lt _ _ (s + 1)
        (fun p hp => Q'.eqv_of_eq (by congr 2 <;> omega))) hlast)
      (Q'.eqv_of_eq (Q'.add_zero' _))
  exact Q'.eqv_trans _ _ _ econst
    (Q'.eqv_trans _ _ _ eterm
      (Q'.eqv_trans _ _ _ eadd
        (Q'.eqv_trans _
          (fsum (fun p => Q'.ofNat (p + 1) * G (p + 1)) (s + 1) +
            fsum (fun p => Q'.ofNat (s - p + 1) * G p) (s + 1)) _
          (Q'.add_eqv_congr' efirst esecond)
          (Q'.eqv_symm (fsum_add _ _ _)))))

/-- Exact weighted successor identity for an arbitrary autoconvolution. -/
theorem autoRow_succ_weighted (x : Nat -> Q') (s : Nat) :
    (Q'.ofNat (s + 1) * autoRow x (s + 1)).eqv
      (fsum (fun p =>
        Q'.ofNat (p + 1) * (x (p + 1) * x (s - p)) +
          Q'.ofNat (s - p + 1) * (x p * x (s - p + 1))) (s + 1)) := by
  unfold autoRow
  have h := weighted_cover
    (fun j => x j * x ((s + 1) - j)) s
  exact Q'.eqv_trans _ _ _ h
    (fsum_eqv_congr_lt _ _ (s + 1) (fun p hp => by
      apply Q'.add_eqv_congr'
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_of_eq (congrArg x (by omega))))
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_of_eq (congrArg x (by omega))))))

/-- If every coefficient successor is at most `q` times its predecessor,
then the corresponding autoconvolution has the exact adjacent half-time
ratio.  This is the computation-theoretic replacement for checking every
row separately. -/
theorem autoRow_succ_le_of_step {x : Nat -> Q'} {q : Q'}
    (hx0 : forall n, (0 : Q') <= x n)
    (hstep : forall n, x (n + 1) <= q * x n) (s : Nat) :
    Q'.ofNat (s + 1) * autoRow x (s + 1) <=
      q * (Q'.ofNat (s + 2) * autoRow x s) := by
  have hterms :
      fsum (fun p =>
        Q'.ofNat (p + 1) * (x (p + 1) * x (s - p)) +
          Q'.ofNat (s - p + 1) * (x p * x (s - p + 1))) (s + 1) <=
      fsum (fun p => Q'.ofNat (s + 2) *
        (q * (x p * x (s - p)))) (s + 1) := by
    apply fsum_mono_lt
    intro p hp
    let B := x p * x (s - p)
    have hB0 : (0 : Q') <= B := Q'.mul_nonneg _ _ (hx0 _) (hx0 _)
    have hfirst0 :
        x (p + 1) * x (s - p) <= q * B := by
      have h := Q'.mul_le_mul_of_nonneg_right _ _ _ (hstep p) (hx0 (s - p))
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (by
          dsimp only [B]
          exact Q'.mul_assoc_eqv q (x p) (x (s - p))))
    have hsecond0 :
        x p * x (s - p + 1) <= q * B := by
      have h := Q'.mul_le_mul_of_nonneg_left _ _ _ (hstep (s - p)) (hx0 p)
      have he : (x p * (q * x (s - p))).eqv (q * B) := by
        dsimp only [B]
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (x p) q (x (s - p))))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (x p) q))
            (Q'.mul_assoc_eqv q (x p) (x (s - p))))
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)
    have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ _ hfirst0
      (ExpNeg.ofNat_nonneg' (p + 1))
    have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond0
      (ExpNeg.ofNat_nonneg' (s - p + 1))
    have hadd := Q'.add_le_add hfirst hsecond
    have hcoef :
        (Q'.ofNat (p + 1) * (q * B) +
          Q'.ofNat (s - p + 1) * (q * B)).eqv
          (Q'.ofNat (s + 2) * (q * B)) := by
      have hn : (p + 1) + (s - p + 1) = s + 2 := by omega
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))
            (Q'.eqv_of_eq (congrArg Q'.ofNat hn))))
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hcoef)
  have eright :
      (fsum (fun p => Q'.ofNat (s + 2) *
        (q * (x p * x (s - p)))) (s + 1)).eqv
        (q * (Q'.ofNat (s + 2) * autoRow x s)) := by
    unfold autoRow
    refine Q'.eqv_trans _
      (Q'.ofNat (s + 2) *
        fsum (fun p => q * (x p * x (s - p))) (s + 1)) _
      (Q'.eqv_symm (fsum_const_mul _ _ _)) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (s + 2) *
        (q * fsum (fun p => x p * x (s - p)) (s + 1))) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (fsum_const_mul _ _ _))) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (s + 2)) q _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (Q'.ofNat (s + 2)) q))
        (Q'.mul_assoc_eqv q (Q'.ofNat (s + 2)) _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (autoRow_succ_weighted x s))
    (Q'.le_trans' _ _ _ hterms (Q'.le_of_eqv eright))

/-! ## 3. Reciprocal-Bernoulli payment for the physical coefficient tail -/

private theorem physical_payment_q (k s b : Nat)
    (hpay : physicalWeightDen k <=
      (b + 1) * (2 * b + 1 - s)) :
    (1 : Q') <= Q'.ofNat ((b + 1) * (2 * b + 1 - s)) * blockMargin k := by
  let D := physicalWeightDen k
  let P := (b + 1) * (2 * b + 1 - s)
  have hclosed : blockMargin k ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) := by
    simpa only [D] using blockMargin_eqv_closed k
  have hunit : (1 : Q') <=
      Q'.mkPos 1 D (physicalWeightDen_pos k) * Q'.ofNat P := by
    have h :=
      P2RetunedFenceIntegralCertificate.ofNat_le_mkPos_mul_of_cross
        1 P 1 D (physicalWeightDen_pos k) (by
          simpa only [D, P, Nat.one_mul] using hpay)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (1 : Q') ≈ Q'.ofNat 1)) h
  have etarget :
      (Q'.mkPos 1 D (physicalWeightDen_pos k) * Q'.ofNat P).eqv
        (Q'.ofNat P * blockMargin k) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _)
      (Q'.mul_eqv_congr_left (Q'.ofNat P) _ _ (Q'.eqv_symm hclosed))
  exact Q'.le_trans' _ _ _ hunit (Q'.le_of_eqv etarget)

/-- Reciprocal Bernoulli converts one natural-number payment into a symbolic
coefficient successor bound at the physical weight. -/
theorem coeffW_succ_le_physical_halfTime (k s b : Nat)
    (hsb : s <= 2 * b + 1)
    (hpay : physicalWeightDen k <=
      (b + 1) * (2 * b + 1 - s)) :
    coeffW (blockWeight k) (b + 1) <=
      qpow (blockWeight k) (s + 2) * coeffW (blockWeight k) b := by
  let u := blockMargin k
  let w := blockWeight k
  let m := 2 * b + 1 - s
  let B := Q'.ofNat (b + 1)
  let C := Q'.ofNat (b + 2)
  have hmadd : s + 2 + m = 2 * b + 3 := by
    unfold m
    omega
  have hpayQ : (1 : Q') <= Q'.ofNat ((b + 1) * m) * u := by
    simpa only [m, u] using physical_payment_q k s b hpay
  have hdim : C <= B * bernDen u m := by
    have hbase : B + (1 : Q') <=
        B + Q'.ofNat ((b + 1) * m) * u :=
      Q'.add_le_add (Q'.le_refl' B) hpayQ
    have eleft : C ≈ B + (1 : Q') := by
      unfold B C
      have hn : b + 2 = (b + 1) + 1 := by omega
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat hn))
        (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (b + 1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide)))
    have eright :
        (B + Q'.ofNat ((b + 1) * m) * u).eqv
          (B * bernDen u m) := by
      have eP : Q'.ofNat ((b + 1) * m) ≈ B * Q'.ofNat m := by
        unfold B
        exact HeatKernelRGStep.ofNat_mul_eqv (b + 1) m
      unfold bernDen
      refine Q'.eqv_trans _
        (B * (1 : Q') + B * (Q'.ofNat m * u)) _ ?_ ?_
      · apply Q'.add_eqv_congr'
        · exact Q'.eqv_symm (Q'.mul_one_eqv B)
        · exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ u eP)
            (Q'.mul_assoc_eqv B (Q'.ofNat m) u)
      · exact Q'.eqv_symm (Q'.mul_add_eqv B 1 (Q'.ofNat m * u))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv eright))
  have hbern : qpow w m * bernDen u m <= (1 : Q') := by
    simpa only [w, u, blockWeight, oneSub] using
      oneSub_pow_mul_bernDen_le (blockMargin_nonneg k)
        (blockMargin_le_one k) m
  have hsmall : C * qpow w m <= B := by
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w m) hdim
      (qpow_nonneg w (blockWeight_nonneg k) m)
    have ereorder : (B * bernDen u m) * qpow w m ≈
        B * (qpow w m * bernDen u m) := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv B (bernDen u m) (qpow w m))
        (Q'.mul_eqv_congr_left B _ _
          (Q'.mul_comm_eqv (bernDen u m) (qpow w m)))
    have hscale := Q'.mul_le_mul_of_nonneg_left _ _ B hbern
      (ExpNeg.ofNat_nonneg' (b + 1))
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereorder)
        (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.mul_one_eqv B))))
  have hcross :
      Q'.ofNat (b + 2) * qpow w (2 * b + 3) <=
        qpow w (s + 2) * Q'.ofNat (b + 1) := by
    have hp : qpow w (2 * b + 3) ≈
        qpow w (s + 2) * qpow w m := by
      rw [← hmadd]
      exact qpow_add w (s + 2) m
    have escale :
        (C * qpow w (2 * b + 3)).eqv
          (qpow w (s + 2) * (C * qpow w m)) := by
      refine Q'.eqv_trans _ (C * (qpow w (s + 2) * qpow w m)) _
        (Q'.mul_eqv_congr_left C _ _ hp) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv C (qpow w (s + 2)) (qpow w m)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv C (qpow w (s + 2))))
          (Q'.mul_assoc_eqv (qpow w (s + 2)) C (qpow w m)))
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (qpow w (s + 2)) hsmall
      (qpow_nonneg w (blockWeight_nonneg k) (s + 2))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv escale) hscaled
  simpa only [w, B, C] using
    coeffW_succ_le_of_cross (w := blockWeight k)
      (R := qpow (blockWeight k) (s + 2)) b
      (blockWeight_nonneg k) hcross

/-- Every masked tail coefficient is nonnegative. -/
theorem cutoffCoeff_nonneg {w : Q'} (hw0 : (0 : Q') <= w)
    (N r n : Nat) : (0 : Q') <= cutoffCoeff w N r n := by
  unfold cutoffCoeff
  split
  · exact coeffW_nonneg hw0 _
  · exact Q'.le_refl' 0

/-- A payment at the base shift propagates to every later coefficient in the
same cutoff row. -/
theorem cutoffCoeff_step_physical_of_payment (k N s r : Nat)
    (hsr : s <= 2 * r + 1)
    (hpay : physicalWeightDen k <=
      (r + 1) * (2 * r + 1 - s)) (n : Nat) :
    cutoffCoeff (blockWeight k) N r (n + 1) <=
      qpow (blockWeight k) (s + 2) *
        cutoffCoeff (blockWeight k) N r n := by
  by_cases hnext : n + 1 + r < N + 1
  · have hcur : n + r < N + 1 := by omega
    unfold cutoffCoeff
    rw [if_pos hnext, if_pos hcur]
    have hsb : s <= 2 * (n + r) + 1 := by omega
    have hleft : r + 1 <= n + r + 1 := by omega
    have hright : 2 * r + 1 - s <= 2 * (n + r) + 1 - s := by omega
    have hpay' : physicalWeightDen k <=
        (n + r + 1) * (2 * (n + r) + 1 - s) :=
      Nat.le_trans hpay (Nat.mul_le_mul hleft hright)
    simpa only [show n + 1 + r = n + r + 1 by omega] using
      coeffW_succ_le_physical_halfTime k s (n + r) hsb hpay'
  · unfold cutoffCoeff
    rw [if_neg hnext]
    exact Q'.mul_nonneg _ _
      (qpow_nonneg _ (blockWeight_nonneg k) _)
      (by
        split
        · exact coeffW_nonneg (blockWeight_nonneg k) _
        · exact Q'.le_refl' 0)

/-- The high-shift payment closes one entire sharply truncated physical row. -/
theorem cutoffShiftRow_physical_halfTime_of_payment (k N s r : Nat)
    (hsr : s <= 2 * r + 1)
    (hpay : physicalWeightDen k <=
      (r + 1) * (2 * r + 1 - s)) :
    dimQ s * cutoffShiftRow (blockWeight k) N (s + 1) r <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * cutoffShiftRow (blockWeight k) N s r) := by
  simpa only [dimQ, cutoffShiftRow, autoRow] using
    autoRow_succ_le_of_step
      (fun n => cutoffCoeff_nonneg (blockWeight_nonneg k) N r n)
      (cutoffCoeff_step_physical_of_payment k N s r hsr hpay) s

/-! ## 4. An explicit all-scale high-shift threshold -/

/-- Constructive ceiling of one half. -/
def ceilHalf (n : Nat) : Nat := (n + 1) / 2

theorem le_two_ceilHalf (n : Nat) : n <= 2 * ceilHalf n := by
  unfold ceilHalf
  omega

theorem two_ceilHalf_le_add_one (n : Nat) :
    2 * ceilHalf n <= n + 1 := by
  unfold ceilHalf
  omega

/-- A uniform high-shift threshold.  It is within a factor `5/2` of the heat
length, plus the exact half-channel displacement. -/
def physicalTailStart (k s : Nat) : Nat :=
  ceilHalf (5 * 2 ^ k + s)

/-- The explicit threshold pays the reciprocal-Bernoulli denominator at every
physical scale and channel. -/
theorem physicalTailStart_payment (k s : Nat) :
    physicalWeightDen k <=
      (physicalTailStart k s + 1) *
        (2 * physicalTailStart k s + 1 - s) := by
  let A := 2 ^ k
  let R := physicalTailStart k s
  let X := A * A
  let P := (R + 1) * (2 * R + 1 - s)
  have hceil : 5 * A + s <= 2 * R := by
    simpa only [R, physicalTailStart, A] using le_two_ceilHalf (5 * 2 ^ k + s)
  have hleft : 5 * A <= 2 * (R + 1) := by omega
  have hright : 5 * A <= 2 * R + 1 - s := by omega
  have hmul : (5 * A) * (5 * A) <=
      (2 * (R + 1)) * (2 * R + 1 - s) :=
    Nat.mul_le_mul hleft hright
  have h25 : 25 * X <= 2 * P := by
    calc
      25 * X = (5 * A) * (5 * A) := by
        unfold X
        ac_rfl
      _ <= (2 * (R + 1)) * (2 * R + 1 - s) := hmul
      _ = 2 * P := by
        unfold P
        ac_rfl
  have h12 : 12 * X <= P := by omega
  unfold physicalWeightDen
  rw [CasimirMoment.four_pow_eq]
  simpa only [A, R, X, P] using h12

theorem physicalTailStart_channel (k s : Nat) :
    s <= 2 * physicalTailStart k s + 1 := by
  have h := le_two_ceilHalf (5 * 2 ^ k + s)
  unfold physicalTailStart
  omega

/-- Every row at or above the explicit threshold satisfies the physical
half-time ratio. -/
theorem cutoffShiftRow_physical_halfTime_tail (k N s r : Nat)
    (hr : physicalTailStart k s <= r) :
    dimQ s * cutoffShiftRow (blockWeight k) N (s + 1) r <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * cutoffShiftRow (blockWeight k) N s r) := by
  let R := physicalTailStart k s
  have hsr : s <= 2 * r + 1 :=
    Nat.le_trans (physicalTailStart_channel k s) (by omega)
  have hleft : R + 1 <= r + 1 := by omega
  have hright : 2 * R + 1 - s <= 2 * r + 1 - s := by omega
  have hpay : physicalWeightDen k <= (r + 1) * (2 * r + 1 - s) :=
    Nat.le_trans (physicalTailStart_payment k s)
      (Nat.mul_le_mul hleft hright)
  exact cutoffShiftRow_physical_halfTime_of_payment k N s r hsr hpay

/-! ## 5. Aggregate tail discharge and the strict low-shift residual -/

/-- Clamp the analytic threshold to the finite row range. -/
def physicalSplitStart (k N s : Nat) : Nat :=
  Nat.min (physicalTailStart k s) (N + 1)

/-- Rows below the physical high-shift threshold. -/
def physicalLowShiftSum (k N s t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalSplitStart k N s)

/-- Rows at or above the physical high-shift threshold. -/
def physicalHighShiftSum (k N s t : Nat) : Q' :=
  let R := physicalSplitStart k N s
  fsum (fun j => cutoffShiftRow (blockWeight k) N t (R + j))
    (N + 1 - R)

theorem physicalSplitStart_le (k N s : Nat) :
    physicalSplitStart k N s <= N + 1 :=
  Nat.min_le_right _ _

private theorem physicalTailStart_le_split_add {k N s j : Nat}
    (hj : j < N + 1 - physicalSplitStart k N s) :
    physicalTailStart k s <= physicalSplitStart k N s + j := by
  by_cases hT : physicalTailStart k s <= N + 1
  · simp only [physicalSplitStart, Nat.min_eq_left hT]
    omega
  · have hNT : N + 1 <= physicalTailStart k s := Nat.le_of_not_ge hT
    simp only [physicalSplitStart, Nat.min_eq_right hNT] at hj
    omega

/-- Exact low/high decomposition of the line sum at the explicit physical
threshold. -/
theorem lineSum_eq_physicalLow_add_high (k N s t : Nat) :
    (lineSum (lagCorr (blockWeight k) N) t).eqv
      (physicalLowShiftSum k N s t + physicalHighShiftSum k N s t) := by
  let R := physicalSplitStart k N s
  have hR : R <= N + 1 := physicalSplitStart_le k N s
  have hcount : R + (N + 1 - R) = N + 1 := by omega
  have hsplit := fsum_split_at
    (fun r => cutoffShiftRow (blockWeight k) N t r)
    R (N + 1 - R)
  rw [hcount] at hsplit
  exact Q'.eqv_trans _ _ _
    (lineSum_eq_cutoffShiftRows (blockWeight k) N t)
    (by simpa only [physicalLowShiftSum, physicalHighShiftSum, R] using hsplit)

/-- The entire aggregate of high-shift rows is discharged for every physical
scale. -/
theorem physicalHighShiftSum_halfTime (k N s : Nat) :
    dimQ s * physicalHighShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalHighShiftSum k N s s) := by
  let R := physicalSplitStart k N s
  let L := N + 1 - R
  let q := qpow (blockWeight k) (s + 2)
  have hterms :
      fsum (fun j => dimQ s *
        cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L <=
      fsum (fun j => q * (dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j))) L := by
    apply fsum_mono_lt
    intro j hj
    exact cutoffShiftRow_physical_halfTime_tail k N s (R + j)
      (physicalTailStart_le_split_add (by simpa only [R, L] using hj))
  have eleft :
      (dimQ s * physicalHighShiftSum k N s (s + 1)).eqv
        (fsum (fun j => dimQ s *
          cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L) := by
    unfold physicalHighShiftSum
    simpa only [R, L] using
      fsum_const_mul (dimQ s)
        (fun j => cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L
  have eright :
      (fsum (fun j => q * (dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j))) L).eqv
        (q * (dimQ (s + 1) * physicalHighShiftSum k N s s)) := by
    refine Q'.eqv_trans _
      (q * fsum (fun j => dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j)) L) _
      (Q'.eqv_symm (fsum_const_mul q _ L)) ?_
    apply Q'.mul_eqv_congr_left q
    refine Q'.eqv_trans _
      (dimQ (s + 1) * fsum (fun j =>
        cutoffShiftRow (blockWeight k) N s (R + j)) L) _
      (Q'.eqv_symm (fsum_const_mul (dimQ (s + 1)) _ L)) ?_
    apply Q'.mul_eqv_congr_left (dimQ (s + 1))
    unfold physicalHighShiftSum
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hterms (Q'.le_of_eqv eright))

/-- The only remaining half-time input after the explicit high-shift tail is
removed: the prefix of rows strictly below `physicalTailStart`. -/
structure P2PhysicalLowShiftPrefixRatio (k N : Nat) : Type where
  low : forall s, 1 <= s -> s < 2 * N ->
    dimQ s * physicalLowShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalLowShiftSum k N s s)

/-- A low-shift prefix certificate plus the proved high-shift theorem closes
the full physical line-sum ratio. -/
def P2PhysicalLowShiftPrefixRatio.toLineSum {k N : Nat}
    (T : P2PhysicalLowShiftPrefixRatio k N) :
    P2HalfTimeLineSumTailRatio N (blockWeight k) where
  tail := fun s hs hsN => by
    let q := qpow (blockWeight k) (s + 2)
    let P1 := physicalLowShiftSum k N s (s + 1)
    let H1 := physicalHighShiftSum k N s (s + 1)
    let P0 := physicalLowShiftSum k N s s
    let H0 := physicalHighShiftSum k N s s
    have hsum := Q'.add_le_add (T.low s hs hsN)
      (physicalHighShiftSum_halfTime k N s)
    have eleft :
        (dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
          (dimQ s * P1 + dimQ s * H1) := by
      refine Q'.eqv_trans _
        (dimQ s * (P1 + H1)) _
        (Q'.mul_eqv_congr_left (dimQ s) _ _ (by
          simpa only [P1, H1] using
            lineSum_eq_physicalLow_add_high k N s (s + 1))) ?_
      exact Q'.mul_add_eqv _ _ _
    have eright :
        (q * (dimQ (s + 1) * P0) +
          q * (dimQ (s + 1) * H0)).eqv
          (q * (dimQ (s + 1) *
            lineSum (lagCorr (blockWeight k) N) s)) := by
      refine Q'.eqv_trans _
        (q * (dimQ (s + 1) * P0 + dimQ (s + 1) * H0)) _
        (Q'.eqv_symm (Q'.mul_add_eqv q _ _)) ?_
      apply Q'.mul_eqv_congr_left q
      refine Q'.eqv_trans _
        (dimQ (s + 1) * (P0 + H0)) _
        (Q'.eqv_symm (Q'.mul_add_eqv (dimQ (s + 1)) P0 H0)) ?_
      apply Q'.mul_eqv_congr_left (dimQ (s + 1))
      simpa only [P0, H0] using
        Q'.eqv_symm (lineSum_eq_physicalLow_add_high k N s s)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv eright))

/-- The remaining schedule-wide input after the canonical high-shift sector
has been physically discharged. -/
structure BlockCompatibleP2LowShiftPrefixFromFour : Type where
  low : forall k, 4 <= k ->
    P2PhysicalLowShiftPrefixRatio k (blockNcut k)

/-- The strict low-shift residual compiles back to the reviewed schedule-wide
line-sum input. -/
def BlockCompatibleP2LowShiftPrefixFromFour.toLineSumTail
    (T : BlockCompatibleP2LowShiftPrefixFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.low k hk).toLineSum

/-- End-to-end: paying only the low-shift prefix now reaches the reviewed
all-scale canonical control family. -/
def BlockCompatibleP2LowShiftPrefixFromFour.toControlFamily
    (T : BlockCompatibleP2LowShiftPrefixFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

/-- The removed tail is genuinely nonempty already in channel one at every
physical scale, so the new residual is strictly smaller there. -/
theorem physical_mode_one_tail_nonempty (k : Nat) :
  physicalTailStart k 1 < blockNcut k + 1 := by
  have hceil := two_ceilHalf_le_add_one (5 * 2 ^ k + 1)
  have hpowPos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  rw [blockNcut_closed]
  unfold physicalTailStart
  omega

end YMGap.Continuum.P2HalfTimeShiftTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeShiftTail.fsum_masked_prefix
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.truncatedStrandTerm_eq_cutoffProduct
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.lineSum_eq_cutoffShiftRows
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.autoRow_succ_weighted
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.autoRow_succ_le_of_step
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.coeffW_succ_le_physical_halfTime
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffCoeff_step_physical_of_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffShiftRow_physical_halfTime_of_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalTailStart_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffShiftRow_physical_halfTime_tail
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.lineSum_eq_physicalLow_add_high
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftSum_halfTime
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalLowShiftPrefixRatio.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowShiftPrefixFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowShiftPrefixFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physical_mode_one_tail_nonempty
