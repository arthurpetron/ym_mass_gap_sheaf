/-
# Actual regularized-series identification on the positive unit interval

The binary exponent and mantissa are computed from the original rational.
The logarithm is the existing faithful dyadicLogValue, never a free scale-log
field. The finite dyadic defect costs at most 3/(N+1), uniformly in the
exponent; x*k <= 1 controls the accumulated log2 coefficient. Together with
the actual artanh-window comparison these give an equality cutoff independent
of the rational input. No cutoff is extracted from CReal.Equiv.

This closes a scalar identification needed by the original conditional
entropy route. It supplies neither that Haar/limit join nor the signed
late-response estimate, physical scaling, or a Yang--Mills mass gap.
-/

import YMGap.Continuum.RegularizedLogDyadicFiniteDefect
import YMGap.Continuum.RegularizedLogBinaryReduction
import YMGap.Continuum.RegularizedLogWindowIdentification

namespace YMGap.Continuum.RegularizedLogBinaryIdentification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RegularizedLogPolynomial (partialSum modulus)
open YMGap.Continuum.RegularizedLogRationalAlgebra (value)
open YMGap.Continuum.RegularizedLogDyadicFiniteDefect
open YMGap.Continuum.RegularizedLogBinaryReduction
open YMGap.Continuum.RebasedExpShiftSupportReduction (dyadicLogValue)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  tc (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  q_add_congr h (Q'.neg_eqv_congr _ _ k)

def sixth : Q' := Q'.mkPos 1 6 (by decide)

/-- Recoverable uniform cutoff, independent of the computed binary exponent. -/
def identificationRate (epsilon : Q') : Nat :=
  max (modulus (sixth*epsilon))
    (RegularizedLogWindowIdentification.identificationRate (sixth*epsilon))

private theorem ofNat_nonnegative (k : Nat) : (0 : Q') ≤ Q'.ofNat k := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg k

/-- The apparent exponent growth is canceled by the actual dyadic scale. -/
theorem dyadicCoefficient_le_one (m : Q') (hm0 : (0 : Q') ≤ m) (hm1 : m ≤ 1)
    (k : Nat) : (HalfPow.half^k*m)*Q'.ofNat k ≤ 1 := by
  have hk0 := ofNat_nonnegative k
  have hinv0 := Q'.invSucc_nonneg k
  have hk1 : Q'.ofNat k ≤ Q'.ofNat (k+1) :=
    ClusterCount.ofNat_le_ofNat (Nat.le_succ k)
  have hscale : HalfPow.half^k*Q'.ofNat k ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (HalfPow.pow_half_le_invSucc k) hk0)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hk1 hinv0)
        (Q'.le_of_eqv (tc (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc k))))
  have hring : (HalfPow.half^k*m)*Q'.ofNat k ≈ (HalfPow.half^k*Q'.ofNat k)*m :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => HalfPow.half^k | 1 => m | _ => Q'.ofNat k)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hring)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hscale hm0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv m)) hm1))

private theorem window_error (m : Q') (hm0 : (0 : Q') ≤ m) (hm1 : m ≤ 1)
    (hhalf : HalfPow.half ≤ m) (hmPlus : (0 : Q') < m+1)
    (hyb : Q'.abs (CRealLog.yOf m hmPlus) ≤ CRealLog.recipOdd 1)
    (delta : Q') (hd : (0 : Q') < delta) (n : Nat)
    (hn : RegularizedLogWindowIdentification.identificationRate delta ≤ n) :
    Q'.abs (partialSum m n+m*(CRealLog.logRat m hmPlus hyb).approx n) ≤ delta := by
  have h := RegularizedLogWindowIdentification.value_logRat_approx
    m hm0 hm1 hhalf hmPlus hyb delta hd n hn
  have ha := CReal.abs_sub_le_of_bounds h.1 h.2
  have hpin : partialSum m n+m*(CRealLog.logRat m hmPlus hyb).approx n ≈
      partialSum m n+ -(-(m*(CRealLog.logRat m hmPlus hyb).approx n)) :=
    q_add_congr (Q'.eqv_refl _) (Q'.eqv_symm (Q'.neg_neg_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin)) ha

private theorem half_log2_error (delta : Q') (hd : (0 : Q') < delta) (n : Nat)
    (hn : RegularizedLogWindowIdentification.identificationRate delta ≤ n) :
    Q'.abs (2*partialSum HalfPow.half n-CRealLog.log2.approx n) ≤ 2*delta := by
  have h := window_error HalfPow.half HalfPow.half_nonneg (by decide)
    (Q'.le_refl' _) CRealLogOddness.oneHalf_plus_one_pos
    CRealLogOddness.yOf_oneHalf_window delta hd n hn
  have hp : partialSum HalfPow.half n+HalfPow.half*
      (CRealLog.logRat CRealLogOddness.oneHalf CRealLogOddness.oneHalf_plus_one_pos
        CRealLogOddness.yOf_oneHalf_window).approx n ≈
      partialSum HalfPow.half n-HalfPow.half*CRealLog.log2.approx n :=
    tc (q_add_congr (Q'.eqv_refl _) (mc (Q'.eqv_refl _)
      (CRealLogOddness.logRat_oneHalf_approx_eqv_neg_log2_approx n)))
      (q_add_congr (Q'.eqv_refl _) (Q'.mul_neg_eqv _ _))
  have hsmall : Q'.abs (partialSum HalfPow.half n-HalfPow.half*CRealLog.log2.approx n) ≤ delta :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hp)) h
  have hdouble : 2*(HalfPow.half*CRealLog.log2.approx n) ≈ CRealLog.log2.approx n :=
    tc (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (tc (mc (by decide : (2 : Q')*HalfPow.half ≈ 1) (Q'.eqv_refl _))
        (Q'.one_mul_eqv _))
  have hpin : 2*(partialSum HalfPow.half n-HalfPow.half*CRealLog.log2.approx n) ≈
      2*partialSum HalfPow.half n-CRealLog.log2.approx n :=
    tc (poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
      (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
      (by decide) (fun | 0 => partialSum HalfPow.half n | _ => HalfPow.half*CRealLog.log2.approx n))
      (sc (Q'.eqv_refl _) hdouble)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsmall (by decide)))

/-- Finite comparison with the actual log2 and window-log streams. The
explicit cutoff above is the same for every exponent and admissible mantissa. -/
theorem reduced_error (m : Q') (hm0 : (0 : Q') ≤ m) (hm1 : m ≤ 1)
    (hhalf : HalfPow.half ≤ m) (hmPlus : (0 : Q') < m+1)
    (hyb : Q'.abs (CRealLog.yOf m hmPlus) ≤ CRealLog.recipOdd 1)
    (k : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : identificationRate epsilon ≤ n) :
    Q'.abs (partialSum (HalfPow.half^k*m) n -
      (HalfPow.half^k*m)*(Q'.ofNat k*CRealLog.log2.approx n-
        (CRealLog.logRat m hmPlus hyb).approx n)) ≤ epsilon := by
  let delta := sixth*epsilon
  have hd : (0 : Q') < delta := Q'.mul_pos (by decide : (0 : Q') < sixth) he
  have hnTail : modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnWindow : RegularizedLogWindowIdentification.identificationRate delta ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hinv : Q'.invSucc n ≤ delta := Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hnTail) (HalfPow.invSucc_den_le delta hd)
  let s := HalfPow.half^k
  let C := (s*m)*Q'.ofNat k
  let D := (s*m)*(Q'.ofNat k*(2*partialSum HalfPow.half n))+
    s*partialSum m n-partialSum (s*m) n
  let A := C*(2*partialSum HalfPow.half n-CRealLog.log2.approx n)
  let B := s*(partialSum m n+m*(CRealLog.logRat m hmPlus hyb).approx n)
  have hs0 := Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg k
  have hs1 := HKPos.pow_le_one HalfPow.half_nonneg (by decide : HalfPow.half ≤ (1 : Q')) k
  have hC0 : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ hs0 hm0) (ofNat_nonnegative k)
  have hC1 : C ≤ 1 := dyadicCoefficient_le_one m hm0 hm1 k
  have hD := mixed_defect_bounds m hm0 hm1 k n
  change (0 : Q') ≤ D ∧ D ≤ 3*Q'.invSucc n at hD
  have hDabs : Q'.abs (-D) ≤ 3*delta := by
    have h := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' D))
      (by rw [ExpNeg.abs_of_nonneg hD.1]; exact hD.2)
    exact Q'.le_trans' _ _ _ h
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hinv (by decide))
  have hA : Q'.abs A ≤ 2*delta := by
    have h := ExpNeg.abs_mul_le C (2*partialSum HalfPow.half n-CRealLog.log2.approx n)
    rw [ExpNeg.abs_of_nonneg hC0] at h
    exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hC1 (Q'.abs_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
        (half_log2_error delta hd n hnWindow)))
  have hB : Q'.abs B ≤ delta := by
    have h := ExpNeg.abs_mul_le s (partialSum m n+m*(CRealLog.logRat m hmPlus hyb).approx n)
    rw [ExpNeg.abs_of_nonneg hs0] at h
    exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hs1 (Q'.abs_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
        (window_error m hm0 hm1 hhalf hmPlus hyb delta hd n hnWindow)))
  have hpin : partialSum (s*m) n-(s*m)*(Q'.ofNat k*CRealLog.log2.approx n-
      (CRealLog.logRat m hmPlus hyb).approx n) ≈ (-D+A)+B :=
    poly_identity_of_normal_eq
      (.add (.var 5) (.neg (.mul (.mul (.var 0) (.var 1))
        (.add (.mul (.var 2) (.var 6)) (.neg (.var 7))))))
      (.add (.add (.neg (.add (.add (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.mul (.const 2) (.var 3))))
          (.mul (.var 0) (.var 4))) (.neg (.var 5))))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.add (.mul (.const 2) (.var 3)) (.neg (.var 6)))))
        (.mul (.var 0) (.add (.var 4) (.mul (.var 1) (.var 7)))))
      (by decide) (fun
        | 0 => s
        | 1 => m
        | 2 => Q'.ofNat k
        | 3 => partialSum HalfPow.half n
        | 4 => partialSum m n
        | 5 => partialSum (s*m) n
        | 6 => CRealLog.log2.approx n
        | _ => (CRealLog.logRat m hmPlus hyb).approx n)
  have hsum : Q'.abs ((-D+A)+B) ≤ (3*delta+2*delta)+delta :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_add_le (-D+A) B)
      (Q'.add_le_add (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le (-D) A)
        (Q'.add_le_add hDabs hA)) hB)
  have hbudget : (3*delta+2*delta)+delta ≈ epsilon :=
    tc (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 3) (.var 0)) (.mul (.const 2) (.var 0))) (.var 0))
      (.mul (.const 6) (.var 0)) (by decide) (fun _ => delta))
      (tc (Q'.eqv_symm (Q'.mul_assoc_eqv 6 sixth epsilon))
        (tc (mc (by decide : (6 : Q')*sixth ≈ 1) (Q'.eqv_refl epsilon))
          (Q'.one_mul_eqv epsilon)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hbudget))

private theorem close_of_abs_sub {a b epsilon : Q'}
    (h : Q'.abs (a-b) ≤ epsilon) : a ≤ b+epsilon ∧ b ≤ a+epsilon := by
  refine ⟨CReal.le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h), ?_⟩
  have hp : b-a ≈ -(a-b) := poly_identity_of_normal_eq
    (.add (.var 1) (.neg (.var 0))) (.neg (.add (.var 0) (.neg (.var 1))))
    (by decide) (fun | 0 => a | _ => b)
  exact CReal.le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) h))

/-- The ORIGINAL rational input and approximation index are retained.
The existing faithful binary-log value is now pinned to the actual series. -/
theorem value_binaryLog_approx (x : Q') (hx0 : (0 : Q') < x) (hx1 : x ≤ 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : identificationRate epsilon ≤ n) :
    (value x (Q'.le_of_lt hx0) hx1).approx n ≤
      (CReal.neg (CReal.mul (CReal.ofQ' x) (dyadicLogValue (binaryReduction x hx0 hx1)))).approx n+epsilon ∧
    (CReal.neg (CReal.mul (CReal.ofQ' x) (dyadicLogValue (binaryReduction x hx0 hx1)))).approx n ≤
      (value x (Q'.le_of_lt hx0) hx1).approx n+epsilon := by
  let red := binaryReduction x hx0 hx1
  have hb := binaryReduction_m_bounds x hx0 hx1
  have hs := binaryReduction_halfPow_scaling x hx0 hx1
  have hl := binaryReduction_log_approx x hx0 hx1 n
  have hp : partialSum x n+x*(dyadicLogValue red).approx n ≈
      partialSum (HalfPow.half^red.down*red.m) n-
        (HalfPow.half^red.down*red.m)*(Q'.ofNat red.down*CRealLog.log2.approx n-
          (CRealLog.logRat red.m red.hm1 red.hyb).approx n) :=
    tc (q_add_congr (partial_congr hs n) (mc hs hl))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.var 1) (.add (.neg (.var 2)) (.var 3))))
        (.add (.var 0) (.neg (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))))
        (by decide) (fun
          | 0 => partialSum (HalfPow.half^red.down*red.m) n
          | 1 => HalfPow.half^red.down*red.m
          | 2 => Q'.ofNat red.down*CRealLog.log2.approx n
          | _ => (CRealLog.logRat red.m red.hm1 red.hyb).approx n))
  have h := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (reduced_error red.m hb.1 hb.2.1 hb.2.2 red.hm1 red.hyb red.down epsilon he n hn)
  have hdouble : partialSum x n+ -(-(x*(dyadicLogValue red).approx n)) ≈
      partialSum x n+x*(dyadicLogValue red).approx n :=
    q_add_congr (Q'.eqv_refl _) (Q'.neg_neg_eqv _)
  exact close_of_abs_sub (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdouble)) h)

theorem value_binaryLog (x : Q') (hx0 : (0 : Q') < x) (hx1 : x ≤ 1) :
    CReal.Equiv (value x (Q'.le_of_lt hx0) hx1)
      (CReal.neg (CReal.mul (CReal.ofQ' x) (dyadicLogValue (binaryReduction x hx0 hx1)))) :=
  fun epsilon he => ⟨identificationRate epsilon,
    fun n hn => value_binaryLog_approx x hx0 hx1 epsilon he n hn⟩

end YMGap.Continuum.RegularizedLogBinaryIdentification

#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.sixth
#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.identificationRate
#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.dyadicCoefficient_le_one
#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.reduced_error
#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.value_binaryLog_approx
#print axioms YMGap.Continuum.RegularizedLogBinaryIdentification.value_binaryLog
