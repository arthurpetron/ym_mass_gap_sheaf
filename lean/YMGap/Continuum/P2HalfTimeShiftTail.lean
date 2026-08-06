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
or above `ceil((5*2^k+s)/2)` are proved here, as is their aggregate.  The full
ratio is then normalized, in both directions, to the sharp comparison between
the signed low-sector debt and the summed high-sector row reserve.  That
comparison is further normalized exactly to one full finite double sum of
local successor atoms, with a one-integer-sign certificate interface.  The
schedule-wide sign theorem remains open; no all-scale control family or
Yang--Mills mass gap is claimed by this module alone.

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

/-- Signed adjacent reserve of one autoconvolution row. -/
def autoRowReserve (q : Q') (x : Nat -> Q') (s : Nat) : Q' :=
  q * (Q'.ofNat (s + 2) * autoRow x s) +
    -(Q'.ofNat (s + 1) * autoRow x (s + 1))

/-- Constant-shape local reserve atom.  Summing these atoms is exactly the
row reserve, by the weighted successor identity below. -/
def autoStepReserve (q : Q') (x : Nat -> Q') (s p : Nat) : Q' :=
  q * (Q'.ofNat (s + 2) * (x p * x (s - p))) +
    -(Q'.ofNat (p + 1) * (x (p + 1) * x (s - p)) +
      Q'.ofNat (s - p + 1) * (x p * x (s - p + 1)))

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

/-- Exact proof-about-computation normal form: a whole adjacent row reserve is
the finite sum of `s+1` local successor atoms. -/
theorem autoRowReserve_eq_stepSum (q : Q') (x : Nat -> Q') (s : Nat) :
    (autoRowReserve q x s).eqv
      (fsum (fun p => autoStepReserve q x s p) (s + 1)) := by
  let G := fun p => x p * x (s - p)
  let W := fun p =>
    Q'.ofNat (p + 1) * (x (p + 1) * x (s - p)) +
      Q'.ofNat (s - p + 1) * (x p * x (s - p + 1))
  have ebase :
      (q * (Q'.ofNat (s + 2) * autoRow x s)).eqv
        (fsum (fun p => q * (Q'.ofNat (s + 2) * G p)) (s + 1)) := by
    have einner : (Q'.ofNat (s + 2) * autoRow x s).eqv
        (fsum (fun p => Q'.ofNat (s + 2) * G p) (s + 1)) := by
      unfold autoRow
      simpa only [G] using
        fsum_const_mul (Q'.ofNat (s + 2)) G (s + 1)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ einner)
      (fsum_const_mul q (fun p => Q'.ofNat (s + 2) * G p) (s + 1))
  have eneg : (-(Q'.ofNat (s + 1) * autoRow x (s + 1))).eqv
      (fsum (fun p => -(W p)) (s + 1)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (autoRow_succ_weighted x s))
      (Q'.eqv_symm (fsum_neg W (s + 1)))
  unfold autoRowReserve autoStepReserve
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ebase eneg)
    (Q'.eqv_symm (fsum_add
      (fun p => q * (Q'.ofNat (s + 2) * G p))
      (fun p => -(W p)) (s + 1)))

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

/-! ## 6. The exact low-debt / high-reserve balance -/

/-- Signed failure of the isolated low prefix.  Positive values are precisely
the debt which must be paid by the high-shift sector. -/
def physicalLowShiftDebt (k N s : Nat) : Q' :=
  dimQ s * physicalLowShiftSum k N s (s + 1) +
    -(qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalLowShiftSum k N s s))

/-- Signed surplus of the proved high-shift sector.  The preceding theorem
shows that this quantity is nonnegative, but the full line-sum inequality
needs the sharper comparison with `physicalLowShiftDebt`. -/
def physicalHighShiftReserve (k N s : Nat) : Q' :=
  qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalHighShiftSum k N s s) +
    -(dimQ s * physicalHighShiftSum k N s (s + 1))

/-- One signed high-shift reserve contribution.  This is the constant-size
unit consumed by an external certificate generator or a symbolic pairing
argument. -/
def physicalHighShiftRowReserve (k N s r : Nat) : Q' :=
  qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * cutoffShiftRow (blockWeight k) N s r) +
    -(dimQ s * cutoffShiftRow (blockWeight k) N (s + 1) r)

/-- The physical row reserve is definitionally the generic autoconvolution
reserve of the masked coefficient tail. -/
theorem physicalHighShiftRowReserve_eq_autoRowReserve (k N s r : Nat) :
    (physicalHighShiftRowReserve k N s r).eqv
      (autoRowReserve (qpow (blockWeight k) (s + 2))
        (fun n => cutoffCoeff (blockWeight k) N r n) s) := by
  unfold physicalHighShiftRowReserve autoRowReserve cutoffShiftRow dimQ
  exact Q'.eqv_refl _

/-- Each physical high-row reserve is an explicit finite sum of local atoms. -/
theorem physicalHighShiftRowReserve_eq_stepSum (k N s r : Nat) :
    (physicalHighShiftRowReserve k N s r).eqv
      (fsum (fun p => autoStepReserve
        (qpow (blockWeight k) (s + 2))
        (fun n => cutoffCoeff (blockWeight k) N r n) s p) (s + 1)) :=
  Q'.eqv_trans _ _ _
    (physicalHighShiftRowReserve_eq_autoRowReserve k N s r)
    (autoRowReserve_eq_stepSum _ _ s)

/-- Every row in the proved high sector contributes a nonnegative reserve. -/
theorem physicalHighShiftRowReserve_nonneg (k N s r : Nat)
    (hr : physicalTailStart k s <= r) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  let rowL := dimQ s * cutoffShiftRow (blockWeight k) N (s + 1) r
  let rowR := qpow (blockWeight k) (s + 2) *
    (dimQ (s + 1) * cutoffShiftRow (blockWeight k) N s r)
  have hadd := Q'.add_le_add_right _ _ (-rowL)
    (cutoffShiftRow_physical_halfTime_tail k N s r hr)
  have eleft : (rowL + -rowL).eqv (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv rowL (-rowL))
      (Q'.neg_add_self_eqv rowL)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
    (by simpa only [physicalHighShiftRowReserve, rowL, rowR] using hadd)

/-- The high reserve as an explicit finite list of row contributions. -/
def physicalHighShiftRowReserveSum (k N s : Nat) : Q' :=
  let R := physicalSplitStart k N s
  fsum (fun j => physicalHighShiftRowReserve k N s (R + j))
    (N + 1 - R)

/-- Fully local double-sum normal form of the high reserve. -/
def physicalHighShiftLocalReserveSum (k N s : Nat) : Q' :=
  let R := physicalSplitStart k N s
  fsum (fun j => fsum (fun p => autoStepReserve
    (qpow (blockWeight k) (s + 2))
    (fun n => cutoffCoeff (blockWeight k) N (R + j) n) s p) (s + 1))
    (N + 1 - R)

theorem physicalHighShiftRowReserveSum_eq_local (k N s : Nat) :
    (physicalHighShiftRowReserveSum k N s).eqv
      (physicalHighShiftLocalReserveSum k N s) := by
  unfold physicalHighShiftRowReserveSum physicalHighShiftLocalReserveSum
  apply fsum_eqv_congr
  intro j
  exact physicalHighShiftRowReserve_eq_stepSum k N s
    (physicalSplitStart k N s + j)

private theorem balance_of_debt_le_reserve
    {lowL lowR highL highR : Q'}
    (h : lowL + -lowR <= highR + -highL) :
    lowL + highL <= lowR + highR := by
  have hadd := Q'.add_le_add_right _ _ (lowR + highL) h
  have eleft : ((lowL + -lowR) + (lowR + highL)).eqv
      (lowL + highL) := by
    refine Q'.eqv_trans _ (lowL + ((-lowR + lowR) + highL)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv lowL (-lowR) (lowR + highL))
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-lowR) lowR highL)))
    · exact Q'.eqv_trans _ (lowL + ((0 : Q') + highL)) _
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.add_eqv_congr_right _ _ highL
            (Q'.neg_add_self_eqv lowR)))
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.eqv_of_eq (Q'.zero_add' highL)))
  have eright : ((highR + -highL) + (lowR + highL)).eqv
      (lowR + highR) := by
    refine Q'.eqv_trans _ (highR + ((-highL + lowR) + highL)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv highR (-highL) (lowR + highL))
        (Q'.add_eqv_congr_left highR _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-highL) lowR highL)))
    · refine Q'.eqv_trans _ (highR + (lowR + (-highL + highL))) _ ?_ ?_
      · apply Q'.add_eqv_congr_left highR
        exact Q'.eqv_trans _ ((lowR + -highL) + highL) _
          (Q'.add_eqv_congr_right _ _ highL
            (Q'.add_comm_eqv (-highL) lowR))
          (Q'.add_assoc_eqv lowR (-highL) highL)
      · exact Q'.eqv_trans _ (highR + lowR) _
          (Q'.add_eqv_congr_left highR _ _
            (Q'.eqv_trans _ (lowR + 0) _
              (Q'.add_eqv_congr_left lowR _ _
                (Q'.neg_add_self_eqv highL))
              (Q'.eqv_of_eq (Q'.add_zero' lowR))))
          (Q'.add_comm_eqv highR lowR)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

private theorem debt_le_reserve_of_balance
    {lowL lowR highL highR : Q'}
    (h : lowL + highL <= lowR + highR) :
    lowL + -lowR <= highR + -highL := by
  have hadd := Q'.add_le_add_right _ _ ((-lowR) + (-highL)) h
  have eleft : ((lowL + highL) + ((-lowR) + (-highL))).eqv
      (lowL + -lowR) := by
    refine Q'.eqv_trans _
      ((lowL + -lowR) + (highL + -highL)) _
      (Q'.add_swap_inner lowL highL (-lowR) (-highL)) ?_
    have hzero : (highL + -highL).eqv (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv highL (-highL))
        (Q'.neg_add_self_eqv highL)
    exact Q'.eqv_trans _ ((lowL + -lowR) + 0) _
      (Q'.add_eqv_congr_left (lowL + -lowR) _ _ hzero)
      (Q'.eqv_of_eq (Q'.add_zero' (lowL + -lowR)))
  have eright : ((lowR + highR) + ((-lowR) + (-highL))).eqv
      (highR + -highL) := by
    refine Q'.eqv_trans _
      ((lowR + -lowR) + (highR + -highL)) _
      (Q'.add_swap_inner lowR highR (-lowR) (-highL)) ?_
    have hzero : (lowR + -lowR).eqv (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv lowR (-lowR))
        (Q'.neg_add_self_eqv lowR)
    exact Q'.eqv_trans _ ((0 : Q') + (highR + -highL)) _
      (Q'.add_eqv_congr_right _ _ (highR + -highL) hzero)
      (Q'.eqv_of_eq (Q'.zero_add' (highR + -highL)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

/-- The high-shift theorem has a nonnegative signed reserve. -/
theorem physicalHighShiftReserve_nonneg (k N s : Nat) :
    (0 : Q') <= physicalHighShiftReserve k N s := by
  let highL := dimQ s * physicalHighShiftSum k N s (s + 1)
  let highR := qpow (blockWeight k) (s + 2) *
    (dimQ (s + 1) * physicalHighShiftSum k N s s)
  have hadd := Q'.add_le_add_right _ _ (-highL)
    (physicalHighShiftSum_halfTime k N s)
  have eleft : (highL + -highL).eqv (0 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv highL (-highL))
      (Q'.neg_add_self_eqv highL)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
    (by simpa only [physicalHighShiftReserve, highL, highR] using hadd)

/-- Finite-sum normalization of the high reserve.  Consequently the remaining
analytic certificate is a single comparison with a sum of constant-shape row
atoms, not a recomputation of the original Clebsch box. -/
theorem physicalHighShiftRowReserveSum_eq_reserve (k N s : Nat) :
    (physicalHighShiftRowReserveSum k N s).eqv
      (physicalHighShiftReserve k N s) := by
  let R := physicalSplitStart k N s
  let L := N + 1 - R
  let q := qpow (blockWeight k) (s + 2)
  let d0 := dimQ (s + 1)
  let d1 := dimQ s
  let row0 := fun j => cutoffShiftRow (blockWeight k) N s (R + j)
  let row1 := fun j => cutoffShiftRow (blockWeight k) N (s + 1) (R + j)
  have ed0 : (d0 * physicalHighShiftSum k N s s).eqv
      (fsum (fun j => d0 * row0 j) L) := by
    unfold physicalHighShiftSum
    simpa only [R, L, d0, row0] using fsum_const_mul d0 row0 L
  have eq0 : (q * (d0 * physicalHighShiftSum k N s s)).eqv
      (fsum (fun j => q * (d0 * row0 j)) L) := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ed0)
      (fsum_const_mul q (fun j => d0 * row0 j) L)
  have ed1 : (d1 * physicalHighShiftSum k N s (s + 1)).eqv
      (fsum (fun j => d1 * row1 j) L) := by
    unfold physicalHighShiftSum
    simpa only [R, L, d1, row1] using fsum_const_mul d1 row1 L
  have eneg : (fsum (fun j => -(d1 * row1 j)) L).eqv
      (-(d1 * physicalHighShiftSum k N s (s + 1))) := by
    exact Q'.eqv_trans _ _ _ (fsum_neg (fun j => d1 * row1 j) L)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm ed1))
  unfold physicalHighShiftRowReserveSum physicalHighShiftRowReserve
  dsimp only
  exact Q'.eqv_trans _ _ _
    (fsum_add (fun j => q * (d0 * row0 j))
      (fun j => -(d1 * row1 j)) L)
    (Q'.eqv_trans _
      (q * (d0 * physicalHighShiftSum k N s s) +
        -(d1 * physicalHighShiftSum k N s (s + 1))) _
      (Q'.add_eqv_congr' (Q'.eqv_symm eq0) eneg)
      (by
        unfold physicalHighShiftReserve
        exact Q'.eqv_refl _))

/-! ## 7. Exact full-reserve proof-about-computation normal form -/

/-- Reserve summed over every cutoff row, before any low/high split. -/
def physicalFullRowReserveSum (k N s : Nat) : Q' :=
  fsum (fun r => physicalHighShiftRowReserve k N s r) (N + 1)

/-- Fully local double sum over every row and every successor atom.  This is
the smallest uniform expression currently exposed to a certificate generator:
one signed rational, with no sector split or intermediate convolution. -/
def physicalFullLocalReserveSum (k N s : Nat) : Q' :=
  fsum (fun r => fsum (fun p => autoStepReserve
    (qpow (blockWeight k) (s + 2))
    (fun n => cutoffCoeff (blockWeight k) N r n) s p) (s + 1)) (N + 1)

/-- The signed reserve of the original physical line-sum inequality. -/
def physicalLineReserve (k N s : Nat) : Q' :=
  qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * lineSum (lagCorr (blockWeight k) N) s) +
    -(dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1))

theorem physicalFullRowReserveSum_eq_local (k N s : Nat) :
    (physicalFullRowReserveSum k N s).eqv
      (physicalFullLocalReserveSum k N s) := by
  unfold physicalFullRowReserveSum physicalFullLocalReserveSum
  apply fsum_eqv_congr
  intro r
  exact physicalHighShiftRowReserve_eq_stepSum k N s r

/-- Summing the row reserves reconstructs the signed reserve of the original
line-sum ratio exactly. -/
theorem physicalFullRowReserveSum_eq_lineReserve (k N s : Nat) :
    (physicalFullRowReserveSum k N s).eqv
      (physicalLineReserve k N s) := by
  let q := qpow (blockWeight k) (s + 2)
  let d0 := dimQ (s + 1)
  let d1 := dimQ s
  let row0 := fun r => cutoffShiftRow (blockWeight k) N s r
  let row1 := fun r => cutoffShiftRow (blockWeight k) N (s + 1) r
  have ed0 : (d0 * lineSum (lagCorr (blockWeight k) N) s).eqv
      (fsum (fun r => d0 * row0 r) (N + 1)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left d0 _ _
        (lineSum_eq_cutoffShiftRows (blockWeight k) N s))
      (fsum_const_mul d0 row0 (N + 1))
  have eq0 : (q * (d0 * lineSum (lagCorr (blockWeight k) N) s)).eqv
      (fsum (fun r => q * (d0 * row0 r)) (N + 1)) := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ed0)
      (fsum_const_mul q (fun r => d0 * row0 r) (N + 1))
  have ed1 : (d1 * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
      (fsum (fun r => d1 * row1 r) (N + 1)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left d1 _ _
        (lineSum_eq_cutoffShiftRows (blockWeight k) N (s + 1)))
      (fsum_const_mul d1 row1 (N + 1))
  have eneg : (fsum (fun r => -(d1 * row1 r)) (N + 1)).eqv
      (-(d1 * lineSum (lagCorr (blockWeight k) N) (s + 1))) := by
    exact Q'.eqv_trans _ _ _ (fsum_neg (fun r => d1 * row1 r) (N + 1))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm ed1))
  unfold physicalFullRowReserveSum physicalHighShiftRowReserve
  exact Q'.eqv_trans _ _ _
    (fsum_add (fun r => q * (d0 * row0 r))
      (fun r => -(d1 * row1 r)) (N + 1))
    (Q'.eqv_trans _
      (q * (d0 * lineSum (lagCorr (blockWeight k) N) s) +
        -(d1 * lineSum (lagCorr (blockWeight k) N) (s + 1))) _
      (Q'.add_eqv_congr' (Q'.eqv_symm eq0) eneg)
      (by
        unfold physicalLineReserve
        exact Q'.eqv_refl _))

/-- The full local double sum is exactly the original line reserve. -/
theorem physicalFullLocalReserveSum_eq_lineReserve (k N s : Nat) :
    (physicalFullLocalReserveSum k N s).eqv
      (physicalLineReserve k N s) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (physicalFullRowReserveSum_eq_local k N s))
    (physicalFullRowReserveSum_eq_lineReserve k N s)

private theorem le_of_reserve_nonneg {left right : Q'}
    (h : (0 : Q') <= right + -left) : left <= right := by
  have hadd := Q'.add_le_add_right _ _ left h
  have eleft : ((0 : Q') + left).eqv left :=
    Q'.eqv_of_eq (Q'.zero_add' left)
  have eright : ((right + -left) + left).eqv right := by
    exact Q'.eqv_trans _ (right + (-left + left)) _
      (Q'.add_assoc_eqv right (-left) left)
      (Q'.eqv_trans _ (right + 0) _
        (Q'.add_eqv_congr_left right _ _ (Q'.neg_add_self_eqv left))
        (Q'.eqv_of_eq (Q'.add_zero' right)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

private theorem reserve_nonneg_of_le {left right : Q'}
    (h : left <= right) : (0 : Q') <= right + -left := by
  have hadd := Q'.add_le_add_right _ _ (-left) h
  have eleft : (left + -left).eqv (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv left (-left))
      (Q'.neg_add_self_eqv left)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft)) hadd

/-- Exact local-reserve carrier.  Unlike a termwise positivity input, this
permits all cancellation inside the finite double sum. -/
structure P2PhysicalFullLocalReserveCertificate (k N : Nat) : Type where
  total : forall s, 1 <= s -> s < 2 * N ->
    (0 : Q') <= physicalFullLocalReserveSum k N s

/-- The local-reserve carrier implies the original line-sum ratio. -/
def P2PhysicalFullLocalReserveCertificate.toLineSum {k N : Nat}
    (T : P2PhysicalFullLocalReserveCertificate k N) :
    P2HalfTimeLineSumTailRatio N (blockWeight k) where
  tail := fun s hs hsN => by
    have hline : (0 : Q') <= physicalLineReserve k N s :=
      Q'.le_trans' _ _ _ (T.total s hs hsN)
        (Q'.le_of_eqv (physicalFullLocalReserveSum_eq_lineReserve k N s))
    exact le_of_reserve_nonneg (by
      simpa only [physicalLineReserve] using hline)

/-- Conversely, the original line-sum ratio supplies the full local-reserve
certificate.  Hence the double-sum carrier is an exact normalization, not a
stronger analytic assumption. -/
def P2PhysicalFullLocalReserveCertificate.ofLineSum {k N : Nat}
    (T : P2HalfTimeLineSumTailRatio N (blockWeight k)) :
    P2PhysicalFullLocalReserveCertificate k N where
  total := fun s hs hsN => by
    have hline : (0 : Q') <= physicalLineReserve k N s := by
      apply reserve_nonneg_of_le
      exact T.tail s hs hsN
    exact Q'.le_trans' _ _ _ hline
      (Q'.ge_of_eqv (physicalFullLocalReserveSum_eq_lineReserve k N s))

/-- Pure-integer sign atom for the full local reserve.  Because every `Q'`
denominator is positive, this one numerator sign is sound and complete. -/
def physicalFullLocalReserveAt (k N s : Nat) : Prop :=
  (0 : Int) <= (physicalFullLocalReserveSum k N s).num

instance physicalFullLocalReserveAtDecidable (k N s : Nat) :
    Decidable (physicalFullLocalReserveAt k N s) := by
  unfold physicalFullLocalReserveAt
  infer_instance

theorem physicalFullLocalReserveAt_sound (k N s : Nat)
    (h : physicalFullLocalReserveAt k N s) :
    (0 : Q') <= physicalFullLocalReserveSum k N s := by
  exact (Q'.zero_le_iff_num_nonneg _).mpr h

/-- One integer numerator sign closes the corresponding original line-sum
cell.  Exposing this pointwise form lets a compiler splice already-proved
boundary cells into a residual certificate family instead of demanding a
second proof of them. -/
theorem physicalFullLocalReserveAt_lineSum (k N s : Nat)
    (h : physicalFullLocalReserveAt k N s) :
    dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * lineSum (lagCorr (blockWeight k) N) s) := by
  have hline : (0 : Q') <= physicalLineReserve k N s :=
    Q'.le_trans' _ _ _ (physicalFullLocalReserveAt_sound k N s h)
      (Q'.le_of_eqv (physicalFullLocalReserveSum_eq_lineReserve k N s))
  exact le_of_reserve_nonneg (by
    simpa only [physicalLineReserve] using hline)

/-- Proof-about-computation carrier: one integer sign certificate per physical
channel, with rational reconstruction proved once above. -/
structure P2PhysicalFullLocalNumeratorCertificate (k N : Nat) : Type where
  nonneg : forall s, 1 <= s -> s < 2 * N ->
    physicalFullLocalReserveAt k N s

def P2PhysicalFullLocalNumeratorCertificate.toLocal {k N : Nat}
    (T : P2PhysicalFullLocalNumeratorCertificate k N) :
    P2PhysicalFullLocalReserveCertificate k N where
  total := fun s hs hsN =>
    physicalFullLocalReserveAt_sound k N s (T.nonneg s hs hsN)

/-- Sharp remaining datum: the proved high-shift surplus must dominate the
signed low-shift debt.  Unlike an independent low-prefix ratio, this permits
the cancellation which is present in the physical line sum. -/
structure P2PhysicalLowHighReserve (k N : Nat) : Type where
  reserve : forall s, 1 <= s -> s < 2 * N ->
    physicalLowShiftDebt k N s <= physicalHighShiftReserve k N s

/-- Proof-about-computation carrier targeting the fully local reserve normal
form.  Its only field is a finite rational comparison between the low debt and
the double sum of constant-shape atoms. -/
structure P2PhysicalLocalReserveCertificate (k N : Nat) : Type where
  atomBound : forall s, 1 <= s -> s < 2 * N ->
    physicalLowShiftDebt k N s <= physicalHighShiftLocalReserveSum k N s

def P2PhysicalLocalReserveCertificate.toReserve {k N : Nat}
    (T : P2PhysicalLocalReserveCertificate k N) :
    P2PhysicalLowHighReserve k N where
  reserve := fun s hs hsN => by
    have hlocal := T.atomBound s hs hsN
    have elocal : (physicalHighShiftLocalReserveSum k N s).eqv
        (physicalHighShiftReserve k N s) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (physicalHighShiftRowReserveSum_eq_local k N s))
        (physicalHighShiftRowReserveSum_eq_reserve k N s)
    exact Q'.le_trans' _ _ _ hlocal (Q'.le_of_eqv elocal)

/-- The exact debt/reserve comparison closes the physical line-sum ratio. -/
def P2PhysicalLowHighReserve.toLineSum {k N : Nat}
    (T : P2PhysicalLowHighReserve k N) :
    P2HalfTimeLineSumTailRatio N (blockWeight k) where
  tail := fun s hs hsN => by
    let q := qpow (blockWeight k) (s + 2)
    let lowL := dimQ s * physicalLowShiftSum k N s (s + 1)
    let lowR := q * (dimQ (s + 1) * physicalLowShiftSum k N s s)
    let highL := dimQ s * physicalHighShiftSum k N s (s + 1)
    let highR := q * (dimQ (s + 1) * physicalHighShiftSum k N s s)
    have hbalance : lowL + highL <= lowR + highR :=
      balance_of_debt_le_reserve (by
        simpa only [physicalLowShiftDebt, physicalHighShiftReserve,
          lowL, lowR, highL, highR, q] using T.reserve s hs hsN)
    have eleft :
        (dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
          (lowL + highL) := by
      refine Q'.eqv_trans _
        (dimQ s * (physicalLowShiftSum k N s (s + 1) +
          physicalHighShiftSum k N s (s + 1))) _
        (Q'.mul_eqv_congr_left (dimQ s) _ _
          (lineSum_eq_physicalLow_add_high k N s (s + 1))) ?_
      simpa only [lowL, highL] using Q'.mul_add_eqv (dimQ s)
        (physicalLowShiftSum k N s (s + 1))
        (physicalHighShiftSum k N s (s + 1))
    have eright : (lowR + highR).eqv
        (q * (dimQ (s + 1) *
          lineSum (lagCorr (blockWeight k) N) s)) := by
      refine Q'.eqv_trans _
        (q * (dimQ (s + 1) * physicalLowShiftSum k N s s +
          dimQ (s + 1) * physicalHighShiftSum k N s s)) _ ?_ ?_
      · simpa only [lowR, highR] using
          Q'.eqv_symm (Q'.mul_add_eqv q
            (dimQ (s + 1) * physicalLowShiftSum k N s s)
            (dimQ (s + 1) * physicalHighShiftSum k N s s))
      · apply Q'.mul_eqv_congr_left q
        refine Q'.eqv_trans _
          (dimQ (s + 1) *
            (physicalLowShiftSum k N s s +
              physicalHighShiftSum k N s s)) _
          (Q'.eqv_symm (Q'.mul_add_eqv (dimQ (s + 1)) _ _)) ?_
        apply Q'.mul_eqv_congr_left (dimQ (s + 1))
        exact Q'.eqv_symm (lineSum_eq_physicalLow_add_high k N s s)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hbalance (Q'.le_of_eqv eright))

/-- Conversely, the line-sum ratio supplies exactly the debt/reserve
comparison.  Thus this carrier loses no analytic content; it only exposes
where the cancellation lives. -/
def P2PhysicalLowHighReserve.ofLineSum {k N : Nat}
    (T : P2HalfTimeLineSumTailRatio N (blockWeight k)) :
    P2PhysicalLowHighReserve k N where
  reserve := fun s hs hsN => by
    let q := qpow (blockWeight k) (s + 2)
    let lowL := dimQ s * physicalLowShiftSum k N s (s + 1)
    let lowR := q * (dimQ (s + 1) * physicalLowShiftSum k N s s)
    let highL := dimQ s * physicalHighShiftSum k N s (s + 1)
    let highR := q * (dimQ (s + 1) * physicalHighShiftSum k N s s)
    have eleft :
        (dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
          (lowL + highL) := by
      refine Q'.eqv_trans _
        (dimQ s * (physicalLowShiftSum k N s (s + 1) +
          physicalHighShiftSum k N s (s + 1))) _
        (Q'.mul_eqv_congr_left (dimQ s) _ _
          (lineSum_eq_physicalLow_add_high k N s (s + 1))) ?_
      simpa only [lowL, highL] using Q'.mul_add_eqv (dimQ s)
        (physicalLowShiftSum k N s (s + 1))
        (physicalHighShiftSum k N s (s + 1))
    have eright : (lowR + highR).eqv
        (q * (dimQ (s + 1) *
          lineSum (lagCorr (blockWeight k) N) s)) := by
      refine Q'.eqv_trans _
        (q * (dimQ (s + 1) * physicalLowShiftSum k N s s +
          dimQ (s + 1) * physicalHighShiftSum k N s s)) _ ?_ ?_
      · simpa only [lowR, highR] using
          Q'.eqv_symm (Q'.mul_add_eqv q
            (dimQ (s + 1) * physicalLowShiftSum k N s s)
            (dimQ (s + 1) * physicalHighShiftSum k N s s))
      · apply Q'.mul_eqv_congr_left q
        refine Q'.eqv_trans _
          (dimQ (s + 1) *
            (physicalLowShiftSum k N s s +
              physicalHighShiftSum k N s s)) _
          (Q'.eqv_symm (Q'.mul_add_eqv (dimQ (s + 1)) _ _)) ?_
        apply Q'.mul_eqv_congr_left (dimQ (s + 1))
        exact Q'.eqv_symm (lineSum_eq_physicalLow_add_high k N s s)
    have hbalance : lowL + highL <= lowR + highR :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
        (Q'.le_trans' _ _ _ (T.tail s hs hsN) (Q'.ge_of_eqv eright))
    simpa only [physicalLowShiftDebt, physicalHighShiftReserve,
      lowL, lowR, highL, highR, q] using
        debt_le_reserve_of_balance hbalance

/-- Schedule-wide sharp reserve data beginning at the first unchecked
physical scale. -/
structure BlockCompatibleP2LowHighReserveFromFour : Type where
  reserve : forall k, 4 <= k ->
    P2PhysicalLowHighReserve k (blockNcut k)

/-- Schedule-wide local-atom certificate family. -/
structure BlockCompatibleP2LocalReserveFromFour : Type where
  cert : forall k, 4 <= k ->
    P2PhysicalLocalReserveCertificate k (blockNcut k)

/-- Schedule-wide exact full-local-reserve family. -/
structure BlockCompatibleP2FullLocalReserveFromFour : Type where
  cert : forall k, 4 <= k ->
    P2PhysicalFullLocalReserveCertificate k (blockNcut k)

/-- Schedule-wide integer-sign version of the full-local-reserve family. -/
structure BlockCompatibleP2FullLocalNumeratorFromFour : Type where
  cert : forall k, 4 <= k ->
    P2PhysicalFullLocalNumeratorCertificate k (blockNcut k)

def BlockCompatibleP2LocalReserveFromFour.toReserve
    (T : BlockCompatibleP2LocalReserveFromFour) :
    BlockCompatibleP2LowHighReserveFromFour where
  reserve := fun k hk => (T.cert k hk).toReserve

def BlockCompatibleP2FullLocalNumeratorFromFour.toLocal
    (T : BlockCompatibleP2FullLocalNumeratorFromFour) :
    BlockCompatibleP2FullLocalReserveFromFour where
  cert := fun k hk => (T.cert k hk).toLocal

def BlockCompatibleP2FullLocalReserveFromFour.toLineSumTail
    (T : BlockCompatibleP2FullLocalReserveFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.cert k hk).toLineSum

def BlockCompatibleP2LowHighReserveFromFour.toLineSumTail
    (T : BlockCompatibleP2LowHighReserveFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.reserve k hk).toLineSum

/-- End-to-end compiler from the sharp debt/reserve comparison to the reviewed
all-scale physical control family. -/
def BlockCompatibleP2LowHighReserveFromFour.toControlFamily
    (T : BlockCompatibleP2LowHighReserveFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

def BlockCompatibleP2LocalReserveFromFour.toControlFamily
    (T : BlockCompatibleP2LocalReserveFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toReserve.toControlFamily

/-- End-to-end exact compiler from full local reserve signs to the reviewed
all-scale physical control family. -/
def BlockCompatibleP2FullLocalReserveFromFour.toControlFamily
    (T : BlockCompatibleP2FullLocalReserveFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

/-- End-to-end proof-about-computation compiler from integer numerator signs
to the reviewed all-scale physical control family. -/
def BlockCompatibleP2FullLocalNumeratorFromFour.toControlFamily
    (T : BlockCompatibleP2FullLocalNumeratorFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLocal.toControlFamily

/-- A stronger compatibility input which forces the low prefix to close on
its own.  It is sufficient, but the sharp active carrier above permits the
necessary low/high cancellation. -/
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

/-- Schedule-wide version of the stronger independent-low-prefix input.  The
active sharp route is `BlockCompatibleP2LowHighReserveFromFour`. -/
structure BlockCompatibleP2LowShiftPrefixFromFour : Type where
  low : forall k, 4 <= k ->
    P2PhysicalLowShiftPrefixRatio k (blockNcut k)

/-- The stronger independent-low-prefix input compiles back to the reviewed
schedule-wide line-sum input. -/
def BlockCompatibleP2LowShiftPrefixFromFour.toLineSumTail
    (T : BlockCompatibleP2LowShiftPrefixFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.low k hk).toLineSum

/-- End-to-end compatibility compiler for the stronger low-prefix route. -/
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
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.autoRowReserve_eq_stepSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.autoRow_succ_le_of_step
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.coeffW_succ_le_physical_halfTime
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffCoeff_step_physical_of_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffShiftRow_physical_halfTime_of_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalTailStart_payment
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.cutoffShiftRow_physical_halfTime_tail
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.lineSum_eq_physicalLow_add_high
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftSum_halfTime
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftReserve_nonneg
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftRowReserve_eq_stepSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftRowReserve_nonneg
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftRowReserveSum_eq_local
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalHighShiftRowReserveSum_eq_reserve
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalFullRowReserveSum_eq_local
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalFullRowReserveSum_eq_lineReserve
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalFullLocalReserveSum_eq_lineReserve
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalFullLocalReserveCertificate.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalFullLocalReserveCertificate.ofLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalFullLocalReserveAt_sound
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physicalFullLocalReserveAt_lineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalFullLocalNumeratorCertificate.toLocal
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalLocalReserveCertificate.toReserve
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalLowHighReserve.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalLowHighReserve.ofLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowHighReserveFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowHighReserveFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LocalReserveFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2FullLocalReserveFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2FullLocalNumeratorFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.P2PhysicalLowShiftPrefixRatio.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowShiftPrefixFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.BlockCompatibleP2LowShiftPrefixFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeShiftTail.physical_mode_one_tail_nonempty
