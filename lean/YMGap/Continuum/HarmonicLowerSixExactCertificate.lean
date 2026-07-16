import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerLowEvaluation
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseCertificate
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.HarmonicLowerSixExactCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuinticWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLower
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerLowEvaluation
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRows
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighDenseCertificate
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem semantic_neg_num (a : Q') : (-a).num = -a.num := rfl
private theorem semantic_ofInt_num (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem semantic_ofInt_den (z : Int) : ((Q'.ofInt z).den : Int) = 1 := rfl

local macro "semantic_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp_all only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               semantic_neg_num, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               semantic_ofInt_num, semantic_ofInt_den,
               SummableInverseSquare.unit_num,
               SummableInverseSquare.unit_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

private theorem add_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ha)
    (Q'.add_eqv_congr_left _ _ _ hb)

private theorem add_scaled {S b₀ b₁ a₀ a₁ : Q'}
    (h₀ : b₀ ≈ S * a₀) (h₁ : b₁ ≈ S * a₁) :
    b₀ + b₁ ≈ S * (a₀ + a₁) :=
  Q'.eqv_trans _ _ _ (add_congr₂ h₀ h₁)
    (Q'.eqv_symm (Q'.mul_add_eqv S a₀ a₁))

private theorem mul_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_swap_first (a b c : Q') : a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem scaled_sub (S N X : Q') :
    S * N + -(S * X) ≈ S * (N + -X) := by
  refine Q'.eqv_trans _ (S * N + S * (-X)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_neg_eqv S X))
  exact Q'.eqv_symm (Q'.mul_add_eqv S N (-X))

abbrev PE := RingNormaliser.PolyExpr

private def qc (z : Int) : Q' := Q'.ofInt z
private def qadd (a b : Q') : Q' := a + b
private def qmul (a b : Q') : Q' := a * b
private def qneg (a : Q') : Q' := -a
private def qpow (a : Q') (n : Nat) : Q' := RingNormaliser.qpow a n
private def qsub (a b : Q') : Q' := qadd a (qneg b)

private def qFall (x : Q') : Nat → Q'
  | 0 => qc 1
  | r + 1 => qmul (qFall x r) (qsub x (qc r))

private def qFallingNat (n : Nat) : Nat → Nat
  | 0 => 1
  | r + 1 => qFallingNat n r * (n - r)

private theorem ofNat_sub_eq (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) = qsub (Q'.ofNat a) (qc b) := by
  unfold qsub qadd qneg qc
  change Q'.ofNat (a - b) =
    Q'.add (Q'.ofNat a) (Q'.neg (Q'.ofInt (Int.ofNat b)))
  have hcast : Int.ofNat (a - b) = Int.ofNat a - Int.ofNat b :=
    Int.ofNat_sub h
  unfold Q'.ofNat Q'.ofInt Q'.add Q'.neg Q'.den
  rw [hcast]
  simp [Int.sub_eq_add_neg]

private theorem ofNat_add_eq_exact (a b : Nat) :
    Q'.ofNat (a + b) = qadd (Q'.ofNat a) (Q'.ofNat b) := by
  unfold qadd
  change Q'.ofNat (a + b) = Q'.add (Q'.ofNat a) (Q'.ofNat b)
  unfold Q'.ofNat Q'.add Q'.den
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  simp

private theorem qFall_ofNat_le (N r : Nat) (hr : r ≤ N) :
    qFall (Q'.ofNat N) r ≈ Q'.ofNat (qFallingNat N r) := by
  induction r with
  | zero =>
      unfold qFall qFallingNat qc
      exact Q'.eqv_refl _
  | succ r ih =>
      unfold qFall qFallingNat
      have hrN : r ≤ N := by omega
      have hsub := ofNat_sub_eq N r hrN
      rw [← hsub]
      exact Q'.eqv_trans _
        (Q'.ofNat (qFallingNat N r) * Q'.ofNat (N - r)) _
        (Q'.mul_eqv_congr_right _ _ _ (ih hrN))
        (Q'.eqv_symm
          (HeatKernelRGStep.ofNat_mul_eqv (qFallingNat N r) (N - r)))

private theorem qFallingNat_zero_of_lt (N : Nat) : ∀ r, N < r →
    qFallingNat N r = 0
  | 0, h => by omega
  | r + 1, h => by
      simp only [qFallingNat]
      by_cases hr : r ≤ N
      · have hrN : r = N := by omega
        rw [hrN, Nat.sub_self, Nat.mul_zero]
      · rw [qFallingNat_zero_of_lt N r (by omega), Nat.zero_mul]

private theorem qFall_ofNat (N : Nat) : ∀ r,
    qFall (Q'.ofNat N) r ≈ Q'.ofNat (qFallingNat N r)
  | 0 => by
      unfold qFall qFallingNat qc
      exact Q'.eqv_refl _
  | r + 1 => by
      unfold qFall qFallingNat
      by_cases hr : r ≤ N
      · have hsub := ofNat_sub_eq N r hr
        rw [← hsub]
        exact Q'.eqv_trans _
          (Q'.ofNat (qFallingNat N r) * Q'.ofNat (N - r)) _
          (Q'.mul_eqv_congr_right _ _ _ (qFall_ofNat N r))
          (Q'.eqv_symm
            (HeatKernelRGStep.ofNat_mul_eqv (qFallingNat N r) (N - r)))
      · have hz : qFallingNat N r = 0 :=
          qFallingNat_zero_of_lt N r (by omega)
        rw [hz, Nat.zero_mul]
        have hq0 : qFall (Q'.ofNat N) r ≈ Q'.ofNat 0 := by
          simpa only [hz] using qFall_ofNat N r
        refine Q'.eqv_trans _
          (Q'.ofNat 0 * qsub (Q'.ofNat N) (qc r)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ hq0
        exact Q'.eqv_trans _
          (0 * qsub (Q'.ofNat N) (qc r)) _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
          (Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
            (Q'.eqv_symm Q'.ofNat_zero_eqv))

private theorem ofNat_mul_eqv_of_eq {a b c d : Nat}
    (h : a * b = c * d) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat c * Q'.ofNat d := by
  exact Q'.eqv_trans _ (Q'.ofNat (a * b)) _
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv a b))
    (Q'.eqv_trans _ (Q'.ofNat (c * d)) _
      (Q'.eqv_of_eq (congrArg Q'.ofNat h))
      (HeatKernelRGStep.ofNat_mul_eqv c d))

private theorem scaled_qFall_eqv
    (c C m r : Nat) (hr : r ≤ m)
    (h : c * qFallingNat m r = 720 * C) :
    qmul (qc (Int.ofNat c)) (qFall (Q'.ofNat m) r) ≈
      Q'.ofNat 720 * Q'.ofNat C := by
  unfold qmul qc
  refine Q'.eqv_trans _
    (Q'.ofNat c * Q'.ofNat (qFallingNat m r)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (qFall_ofNat_le m r hr)
  exact ofNat_mul_eqv_of_eq h

private theorem scaled_qFall_eqv_all
    (c C m r : Nat) (h : c * qFallingNat m r = 720 * C) :
    qmul (qc (Int.ofNat c)) (qFall (Q'.ofNat m) r) ≈
      Q'.ofNat 720 * Q'.ofNat C := by
  unfold qmul qc
  refine Q'.eqv_trans _
    (Q'.ofNat c * Q'.ofNat (qFallingNat m r)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (qFall_ofNat m r)
  exact ofNat_mul_eqv_of_eq h

private theorem scaled_qFall_custom
    (c s C m r : Nat) (h : c * qFallingNat m r = s * C) :
    qmul (qc (Int.ofNat c)) (qFall (Q'.ofNat m) r) ≈
      Q'.ofNat s * Q'.ofNat C := by
  unfold qmul qc
  refine Q'.eqv_trans _
    (Q'.ofNat c * Q'.ofNat (qFallingNat m r)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (qFall_ofNat m r)
  exact ofNat_mul_eqv_of_eq h

private theorem rnqpow_mul_base (a b : Q') : ∀ n,
    RingNormaliser.qpow (a * b) n ≈
      RingNormaliser.qpow a n * RingNormaliser.qpow b n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show RingNormaliser.qpow (a * b) n * (a * b) ≈
        (RingNormaliser.qpow a n * a) * (RingNormaliser.qpow b n * b)
      refine Q'.eqv_trans _
        ((RingNormaliser.qpow a n * RingNormaliser.qpow b n) * (a * b)) _
        (Q'.mul_eqv_congr_right _ _ _ (rnqpow_mul_base a b n)) ?_
      semantic_ring

private theorem rnqpow_one : ∀ n,
    RingNormaliser.qpow (1 : Q') n ≈ (1 : Q')
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      show RingNormaliser.qpow (1 : Q') n * 1 ≈ 1
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_right _ _ _ (rnqpow_one n))
        (Q'.one_mul_eqv 1)

private theorem rnqpow_cancel {D u : Q'} (hDu : D * u ≈ (1 : Q'))
    (a r : Nat) :
    RingNormaliser.qpow D (a + r) * RingNormaliser.qpow u r ≈
      RingNormaliser.qpow D a := by
  have hsplit := RingNormaliser.qpow_add D a r
  have hprod :
      RingNormaliser.qpow D r * RingNormaliser.qpow u r ≈ (1 : Q') :=
    Q'.eqv_trans _ (RingNormaliser.qpow (D * u) r) _
      (Q'.eqv_symm (rnqpow_mul_base D u r))
      (Q'.eqv_trans _ (RingNormaliser.qpow (1 : Q') r) _
        (RingNormaliser.qpow_eqv_congr hDu r) (rnqpow_one r))
  exact Q'.eqv_trans _
    ((RingNormaliser.qpow D a * RingNormaliser.qpow D r) *
      RingNormaliser.qpow u r) _
    (Q'.mul_eqv_congr_right _ _ _ hsplit)
    (Q'.eqv_trans _
      (RingNormaliser.qpow D a *
        (RingNormaliser.qpow D r * RingNormaliser.qpow u r)) _
      (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ (RingNormaliser.qpow D a * 1) _
        (Q'.mul_eqv_congr_left _ _ _ hprod)
        (Q'.mul_one_eqv _)))

private theorem scaled_power_term {D u P C : Q'}
    (hDu : D * u ≈ (1 : Q'))
    (hP : P ≈ Q'.ofNat 720 * C)
    (a r : Nat) (har : a + r = 6) :
    P * RingNormaliser.qpow D a ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D 6) *
        (C * RingNormaliser.qpow u r) := by
  have hcancel :
      RingNormaliser.qpow D 6 * RingNormaliser.qpow u r ≈
        RingNormaliser.qpow D a := by
    have h := rnqpow_cancel hDu a r
    simpa only [har] using h
  refine Q'.eqv_trans _
    ((Q'.ofNat 720 * C) * RingNormaliser.qpow D a) _
    (Q'.mul_eqv_congr_right _ _ _ hP) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 720 * C) *
      (RingNormaliser.qpow D 6 * RingNormaliser.qpow u r)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcancel)) ?_
  semantic_ring

private theorem scaled_power_term_neg {D u P C : Q'}
    (hDu : D * u ≈ (1 : Q'))
    (hP : P ≈ Q'.ofNat 720 * C)
    (a r : Nat) (har : a + r = 6) :
    -(P * RingNormaliser.qpow D a) ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D 6) *
        (-(C * RingNormaliser.qpow u r)) := by
  have h := Q'.neg_eqv_congr _ _
    (scaled_power_term hDu hP a r har)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_symm
      (Q'.mul_neg_eqv
        (Q'.ofNat 720 * RingNormaliser.qpow D 6)
        (C * RingNormaliser.qpow u r)))

private theorem harmonic_den_mul_unit (k : Nat) :
    Q'.ofNat (k + 2) * harmU k ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem modeExpr_eqv (n : Nat) :
    qadd (qmul (qc 2) (Q'.ofNat n)) (qc 1) ≈ Q'.ofNat (2 * n + 1) := by
  refine Q'.eqv_trans _ (Q'.ofNat (2 * n) + Q'.ofNat 1) _ ?_ ?_
  · simpa [qadd, qmul, qc] using
      Q'.add_eqv_congr_right
        (Q'.ofNat 2 * Q'.ofNat n) (Q'.ofNat (2 * n)) (Q'.ofNat 1)
        (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 n))
  exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * n) 1)

private theorem succExpr_eqv (n : Nat) :
    qadd (Q'.ofNat n) (qc 1) ≈ Q'.ofNat (n + 1) := by
  simpa [qadd, qc] using Q'.eqv_symm (Q'.ofNat_add_eqv n 1)

private theorem qFall_congr {x y : Q'} (hxy : x ≈ y) : ∀ r,
    qFall x r ≈ qFall y r
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      exact mul_congr₂ (qFall_congr hxy r)
        (add_congr₂ hxy (Q'.neg_eqv_congr _ _ (Q'.eqv_refl (qc r))))

def qTaylorScaled (D m : Q') : Q' :=
  qadd
    (qadd
      (qadd
        (qadd
          (qadd
            (qmul (qc 720) (qpow D 6))
            (qneg (qmul (qmul (qc 720) m) (qpow D 5))))
          (qmul (qmul (qc 360) (qFall m 2)) (qpow D 4)))
        (qneg (qmul (qmul (qc 120) (qFall m 3)) (qpow D 3))))
      (qmul (qmul (qc 30) (qFall m 4)) (qpow D 2)))
    (qadd
      (qneg (qmul (qmul (qc 6) (qFall m 5)) D))
      (qFall m 6))

private theorem qTaylorScaled_congr (D : Q') {x y : Q'} (hxy : x ≈ y) :
    qTaylorScaled D x ≈ qTaylorScaled D y := by
  have hx : ∀ r, qFall x r ≈ qFall y r := qFall_congr hxy
  unfold qTaylorScaled
  exact add_congr₂
    (add_congr₂
      (add_congr₂
        (add_congr₂
          (add_congr₂ (Q'.eqv_refl _)
            (Q'.neg_eqv_congr _ _
              (mul_congr₂
                (mul_congr₂ (Q'.eqv_refl _) hxy) (Q'.eqv_refl _))))
          (mul_congr₂
            (mul_congr₂ (Q'.eqv_refl _) (hx 2)) (Q'.eqv_refl _)))
        (Q'.neg_eqv_congr _ _
          (mul_congr₂
            (mul_congr₂ (Q'.eqv_refl _) (hx 3)) (Q'.eqv_refl _))))
      (mul_congr₂
        (mul_congr₂ (Q'.eqv_refl _) (hx 4)) (Q'.eqv_refl _)))
    (add_congr₂
      (Q'.neg_eqv_congr _ _
        (mul_congr₂
          (mul_congr₂ (Q'.eqv_refl _) (hx 5)) (Q'.eqv_refl _)))
      (hx 6))

def qSlopeScaled (D N : Q') : Q' :=
  let m := qadd (qmul (qc 2) N) (qc 1)
  qsub (qmul (qmul (qc 720) N) (qpow D 6))
    (qmul (qadd N (qc 1)) (qTaylorScaled D m))

def qDriftFactorScaled (D N : Q') : Q' :=
  let d := qsub (qpow D 2) (qc 1)
  let r := qadd (qmul (qc 2) d) (qc 1)
  let N2 := qpow N 2
  qadd
    (qadd
      (qmul (qc 2) (qpow d 4))
      (qmul (qmul (qmul (qc 2) N2) r) (qpow d 2)))
    (qmul (qmul N2 (qsub N2 (qc 1))) (qpow r 2))

def qInnerNextScaled (D N : Q') : Q' :=
  let A := qadd N (qc 1)
  let m := qadd (qmul (qc 2) N) (qc 1)
  let T := qSlopeScaled D N
  qadd
    (qadd
      (qmul (qc 28) (qpow T 2))
      (qneg (qmul (qmul (qmul (qc 11520) A) (qFall m 7))
        (qpow D 5))))
    (qneg (qmul (qmul (qmul (qc 3628800) (qpow N 2))
      (qadd (qmul (qc 12) (qpow D 2)) (qc 1))) (qpow D 9)))

def qInnerOldScaled (D N : Q') : Q' :=
  let A := qadd N (qc 1)
  let m := qadd (qmul (qc 2) N) (qc 1)
  let T := qSlopeScaled D N
  qadd
    (qadd
      (qmul (qc 28) (qpow T 2))
      (qmul (qmul (qmul (qc 8640) A) (qFall m 7)) (qpow D 5)))
    (qneg (qmul (qmul (qmul (qc 3628800) (qpow N 2))
      (qadd (qmul (qc 12) (qpow D 2)) (qc 1))) (qpow D 9)))

def qCarrierScaled (D N : Q') : Q' :=
  let D1 := qadd D (qc 1)
  let d := qsub (qpow D 2) (qc 1)
  qsub
    (qmul (qmul (qDriftFactorScaled D N) (qInnerNextScaled D1 N))
      (qpow D 11))
    (qmul (qmul (qmul (qc 2) (qpow d 4)) (qInnerOldScaled D N))
      (qpow D1 11))

def qFlux (D N : Q') : Q' :=
  qadd
    (qadd
      (qadd
        (qadd
          (qadd
            (qadd
              (qadd
                (qadd
                  (qmul (qmul (qc 192) N) (qpow D 4))
                  (qmul (qmul (qc 384) (qpow N 3)) (qpow D 3)))
                (qneg (qmul (qmul (qc 6) N) (qpow D 3))))
              (qneg (qmul (qmul (qc 384) (qpow N 5)) (qpow D 2))))
            (qmul (qmul (qc 576) (qpow N 4)) (qpow D 2)))
          (qmul (qmul (qc 184) (qpow N 3)) (qpow D 2)))
        (qmul (qmul (qc 224) (qpow N 5)) D))
      (qneg (qmul (qc 256) (qpow N 7))))
    (qadd (qmul (qc 576) (qpow N 6)) (qmul (qc 3) (qpow D 3)))

def qCommonDen (D : Q') : Q' :=
  qmul
    (qmul
      (qmul (qc 7257600) (qpow (qsub (qpow D 2) (qc 1)) 4))
      (qpow D 12))
    (qpow (qadd D (qc 1)) 11)

def qExactLowerNumerator (D N : Q') : Q' :=
  let A := qadd N (qc 1)
  let D1 := qadd D (qc 1)
  let d := qsub (qpow D 2) (qc 1)
  let T := qSlopeScaled D N
  let main :=
    qadd
      (qmul (qmul (qc 48) (qpow D 5)) (qCarrierScaled D N))
      (qmul (qsub (qFlux D N) (qmul (qc 6) (qpow D 3)))
        (qCommonDen D))
  let oldFluxScaled := qsub (qmul (qmul (qc 720) N) (qpow D 6)) T
  qsub
    (qmul (qpow A 2) main)
    (qmul
      (qmul
        (qmul (qc 14) (qpow d 4))
        (qpow D1 11))
      (qmul (qpow oldFluxScaled 2) (qFlux D (qadd N (qc 1)))))

def genericEnvironment (D N : Q') (i : Nat) : Q' :=
  if i = 0 then D else if i = 1 then N else 0

def pGeneric : PE :=
  pExactLowerNumerator (.var 0) (.var 1)

theorem eval_pGeneric_eq (D N : Q') :
    RingNormaliser.eval (genericEnvironment D N) pGeneric =
      qExactLowerNumerator D N := by
  rfl

theorem qFlux_eq_physical (D N : Q') :
    qFlux D N ≈
      HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux.lowerSixDiscreteHermiteFluxPoly
        D N := by
  unfold qFlux qc qadd qmul qneg qpow
    HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux.lowerSixDiscreteHermiteFluxPoly
  semantic_ring

theorem qTaylorScaled_eq_physical (n k : Nat) :
    qTaylorScaled (Q'.ofNat (k + 2))
        (Q'.ofNat (2 * n + 1)) ≈
      (Q'.ofNat 720 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 6) *
        oneSubTaylor6 (harmU k) (2 * n + 1) := by
  let m := 2 * n + 1
  have h2 := lowerSixQuadraticCoeff_double m
  have h3 := cubicCoeff_six m
  have h4 := quarticCoeff_twentyFour m
  have h5 := quinticCoeff_oneTwenty m
  have h6 := sexticCoeff_sevenTwenty m
  have h2n : 720 * lowerSixQuadraticCoeff m =
      360 * (m * (m - 1)) := by omega
  have h3n : 720 * cubicCoeff m =
      120 * (m * (m - 1) * (m - 2)) := by omega
  have h4n : 720 * quarticCoeff m =
      30 * (m * (m - 1) * (m - 2) * (m - 3)) := by omega
  have h5n : 720 * quinticCoeff m =
      6 * (m * (m - 1) * (m - 2) * (m - 3) * (m - 4)) := by omega
  have h6n : 720 * sexticCoeff m =
      m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) := h6
  have hf2 : 360 * qFallingNat m 2 =
      720 * lowerSixQuadraticCoeff m := by
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h2n.symm
  have hf3 : 120 * qFallingNat m 3 =
      720 * cubicCoeff m := by
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h3n.symm
  have hf4 : 30 * qFallingNat m 4 =
      720 * quarticCoeff m := by
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h4n.symm
  have hf5 : 6 * qFallingNat m 5 =
      720 * quinticCoeff m := by
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h5n.symm
  have hf6 : 1 * qFallingNat m 6 =
      720 * sexticCoeff m := by
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h6n.symm
  let D := Q'.ofNat (k + 2)
  let mq := Q'.ofNat m
  let S := Q'.ofNat 720 * RingNormaliser.qpow D 6
  let u := harmU k
  let a₀ : Q' := 1
  let a₁ := -(Q'.ofNat m * RingNormaliser.qpow u 1)
  let a₂ := Q'.ofNat (lowerSixQuadraticCoeff m) * RingNormaliser.qpow u 2
  let a₃ := -(Q'.ofNat (cubicCoeff m) * RingNormaliser.qpow u 3)
  let a₄ := Q'.ofNat (quarticCoeff m) * RingNormaliser.qpow u 4
  let a₅ := -(Q'.ofNat (quinticCoeff m) * RingNormaliser.qpow u 5)
  let a₆ := Q'.ofNat (sexticCoeff m) * RingNormaliser.qpow u 6
  let b₀ := qmul (qc 720) (qpow D 6)
  let b₁ := qneg (qmul (qmul (qc 720) mq) (qpow D 5))
  let b₂ := qmul (qmul (qc 360) (qFall mq 2)) (qpow D 4)
  let b₃ := qneg (qmul (qmul (qc 120) (qFall mq 3)) (qpow D 3))
  let b₄ := qmul (qmul (qc 30) (qFall mq 4)) (qpow D 2)
  let b₅ := qneg (qmul (qmul (qc 6) (qFall mq 5)) D)
  let b₆ := qFall mq 6
  have hDu : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact harmonic_den_mul_unit k
  have hp₁ : qmul (qc 720) mq ≈ Q'.ofNat 720 * Q'.ofNat m := by
    dsimp only [mq]
    exact Q'.eqv_refl _
  have hp₂ : qmul (qc 360) (qFall mq 2) ≈
      Q'.ofNat 720 * Q'.ofNat (lowerSixQuadraticCoeff m) := by
    dsimp only [mq]
    exact scaled_qFall_eqv_all 360 (lowerSixQuadraticCoeff m) m 2 hf2
  have hp₃ : qmul (qc 120) (qFall mq 3) ≈
      Q'.ofNat 720 * Q'.ofNat (cubicCoeff m) := by
    dsimp only [mq]
    exact scaled_qFall_eqv_all 120 (cubicCoeff m) m 3 hf3
  have hp₄ : qmul (qc 30) (qFall mq 4) ≈
      Q'.ofNat 720 * Q'.ofNat (quarticCoeff m) := by
    dsimp only [mq]
    exact scaled_qFall_eqv_all 30 (quarticCoeff m) m 4 hf4
  have hp₅ : qmul (qc 6) (qFall mq 5) ≈
      Q'.ofNat 720 * Q'.ofNat (quinticCoeff m) := by
    dsimp only [mq]
    exact scaled_qFall_eqv_all 6 (quinticCoeff m) m 5 hf5
  have hp₆mul : qmul (qc 1) (qFall mq 6) ≈
      Q'.ofNat 720 * Q'.ofNat (sexticCoeff m) := by
    dsimp only [mq]
    exact scaled_qFall_eqv_all 1 (sexticCoeff m) m 6 hf6
  have hp₆ : qFall mq 6 ≈
      Q'.ofNat 720 * Q'.ofNat (sexticCoeff m) := by
    refine Q'.eqv_trans _ (qmul (qc 1) (qFall mq 6)) _ ?_ hp₆mul
    simpa only [qmul, qc] using Q'.eqv_symm (Q'.one_mul_eqv (qFall mq 6))
  have hb₀ : b₀ ≈ S * a₀ := by
    dsimp only [b₀, S, a₀, D]
    change Q'.ofInt 720 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 6 ≈
      (Q'.ofNat 720 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 6) * 1
    exact Q'.eqv_symm
      (Q'.mul_one_eqv
        (Q'.ofNat 720 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 6))
  have hb₁ : b₁ ≈ S * a₁ := by
    dsimp only [b₁, S, a₁]
    simpa only [qneg, qmul, qpow] using
      scaled_power_term_neg hDu hp₁ 5 1 (by decide)
  have hb₂ : b₂ ≈ S * a₂ := by
    dsimp only [b₂, S, a₂]
    simpa only [qmul, qpow] using
      scaled_power_term hDu hp₂ 4 2 (by decide)
  have hb₃ : b₃ ≈ S * a₃ := by
    dsimp only [b₃, S, a₃]
    simpa only [qneg, qmul, qpow] using
      scaled_power_term_neg hDu hp₃ 3 3 (by decide)
  have hb₄ : b₄ ≈ S * a₄ := by
    dsimp only [b₄, S, a₄]
    simpa only [qmul, qpow] using
      scaled_power_term hDu hp₄ 2 4 (by decide)
  have hb₅ : b₅ ≈ S * a₅ := by
    have hDpow : D ≈ RingNormaliser.qpow D 1 := by
      simpa only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero] using
        Q'.eqv_symm (Q'.one_mul_eqv D)
    have hleft :
        -(qmul (qc 6) (qFall mq 5) * D) ≈
          -(qmul (qc 6) (qFall mq 5) * RingNormaliser.qpow D 1) :=
      Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hDpow)
    dsimp only [b₅, S, a₅]
    refine Q'.eqv_trans _ _ _ ?_
      (scaled_power_term_neg hDu hp₅ 1 5 (by decide))
    simpa only [qneg, qmul] using hleft
  have hb₆ : b₆ ≈ S * a₆ := by
    have hleft : qFall mq 6 ≈
        qFall mq 6 * RingNormaliser.qpow D 0 := by
      simpa only [RingNormaliser.qpow_zero] using
        Q'.eqv_symm (Q'.mul_one_eqv (qFall mq 6))
    dsimp only [b₆, S, a₆]
    exact Q'.eqv_trans _ _ _ hleft
      (scaled_power_term hDu hp₆ 0 6 (by decide))
  have h₀₁ := add_scaled hb₀ hb₁
  have h₀₂ := add_scaled h₀₁ hb₂
  have h₀₃ := add_scaled h₀₂ hb₃
  have h₀₄ := add_scaled h₀₃ hb₄
  have hreassoc :
      (((((b₀ + b₁) + b₂) + b₃) + b₄) + (b₅ + b₆)) ≈
        ((((((b₀ + b₁) + b₂) + b₃) + b₄) + b₅) + b₆) :=
    Q'.eqv_symm
      (Q'.add_assoc_eqv ((((b₀ + b₁) + b₂) + b₃) + b₄) b₅ b₆)
  have hall :
      (((((b₀ + b₁) + b₂) + b₃) + b₄) + (b₅ + b₆)) ≈
        S * ((((((a₀ + a₁) + a₂) + a₃) + a₄) + a₅) + a₆) :=
    Q'.eqv_trans _ _ _ hreassoc (add_scaled (add_scaled h₀₄ hb₅) hb₆)
  have hu1 : RingNormaliser.qpow u 1 ≈ u := by
    simpa only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero] using
      Q'.one_mul_eqv u
  have hu2 : RingNormaliser.qpow u 2 ≈ u * u := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hu3 : RingNormaliser.qpow u 3 ≈ u * (u * u) := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hu4 : RingNormaliser.qpow u 4 ≈ u * (u * (u * u)) := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hu5 : RingNormaliser.qpow u 5 ≈ u * (u * (u * (u * u))) := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hu6 : RingNormaliser.qpow u 6 ≈
      u * (u * (u * (u * (u * u)))) := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have ha₀ : a₀ ≈ (1 : Q') := Q'.eqv_refl _
  have ha₁ : a₁ ≈ -(Q'.ofNat m * u) :=
    Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hu1)
  have ha₂ : a₂ ≈
      Q'.ofNat (lowerSixQuadraticCoeff m) * (u * u) :=
    Q'.mul_eqv_congr_left _ _ _ hu2
  have ha₃ : a₃ ≈
      -(Q'.ofNat (cubicCoeff m) * (u * (u * u))) :=
    Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hu3)
  have ha₄ : a₄ ≈
      Q'.ofNat (quarticCoeff m) * (u * (u * (u * u))) :=
    Q'.mul_eqv_congr_left _ _ _ hu4
  have ha₅ : a₅ ≈
      -(Q'.ofNat (quinticCoeff m) * (u * (u * (u * (u * u))))) :=
    Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hu5)
  have ha₆ : a₆ ≈
      Q'.ofNat (sexticCoeff m) * (u * (u * (u * (u * (u * u))))) :=
    Q'.mul_eqv_congr_left _ _ _ hu6
  have haSum := add_congr₂
    (add_congr₂
      (add_congr₂
        (add_congr₂
          (add_congr₂
            (add_congr₂ ha₀ ha₁) ha₂) ha₃) ha₄) ha₅)
    ha₆
  have hphys :
      ((((((a₀ + a₁) + a₂) + a₃) + a₄) + a₅) + a₆) ≈
        oneSubTaylor6 u m := by
    simpa only [oneSubTaylor6, oneSubTaylor5, oneSubTaylor4,
      oneSubTaylor3, oneSubTaylor2] using haSum
  have hfinal := Q'.eqv_trans _ _ _ hall
    (Q'.mul_eqv_congr_left _ _ _ hphys)
  dsimp only [b₀, b₁, b₂, b₃, b₄, b₅, b₆,
    S, D, mq, u] at hfinal
  simpa only [qTaylorScaled, qadd, qmul, qneg, m] using hfinal

theorem qSlopeScaled_eq_physical (n k : Nat) :
    qSlopeScaled (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      Q'.ofNat 720 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 6 *
          rootSlopeTaylor6 (harmU k) n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let m := 2 * n + 1
  let mq := qadd (qmul (qc 2) N) (qc 1)
  let mNat := Q'.ofNat m
  let S := Q'.ofNat 720 * RingNormaliser.qpow D 6
  let T := oneSubTaylor6 (harmU k) (2 * n + 1)
  let Aq := qadd N (qc 1)
  let A := Q'.ofNat (n + 1)
  have hmq : mq ≈ mNat := by
    dsimp only [mq, mNat, N, m]
    exact modeExpr_eqv n
  have htNat : qTaylorScaled D mNat ≈ S * T := by
    dsimp only [D, mNat, m, S, T]
    exact qTaylorScaled_eq_physical n k
  have ht : qTaylorScaled D mq ≈ S * T :=
    Q'.eqv_trans _ _ _ (qTaylorScaled_congr D hmq) htNat
  have hA : Aq ≈ A := by
    dsimp only [Aq, A, N]
    exact succExpr_eqv n
  have hfirst :
      qmul (qmul (qc 720) N) (qpow D 6) ≈ S * N := by
    dsimp only [S]
    simp only [qpow, RingNormaliser.qpow]
    unfold qmul qc
    semantic_ring
  have hsecond : Aq * qTaylorScaled D mq ≈ S * (A * T) := by
    refine Q'.eqv_trans _ (A * (S * T)) _ (mul_congr₂ hA ht) ?_
    exact mul_swap_first A S T
  have hsum :
      qmul (qmul (qc 720) N) (qpow D 6) +
          -(Aq * qTaylorScaled D mq) ≈
        S * (N + -(A * T)) := by
    refine Q'.eqv_trans _ (S * N + -(S * (A * T))) _ ?_ ?_
    · exact add_congr₂ hfirst (Q'.neg_eqv_congr _ _ hsecond)
    exact scaled_sub S N (A * T)
  dsimp only [D, N, m, mq, mNat, S, T, Aq, A] at hsum
  simpa only [qSlopeScaled, qsub, qadd, qmul, qneg,
    rootSlopeTaylor6] using hsum

private def qDriftFormula (d N2 : Q') : Q' :=
  let r := Q'.ofNat 2 * d + 1
  (Q'.ofNat 2 * RingNormaliser.qpow d 4 +
      ((Q'.ofNat 2 * N2) * r) * RingNormaliser.qpow d 2) +
    (N2 * (N2 + -(1 : Q'))) * RingNormaliser.qpow r 2

private theorem qDriftFormula_congr {d d' N2 N2' : Q'}
    (hd : d ≈ d') (hN : N2 ≈ N2') :
    qDriftFormula d N2 ≈ qDriftFormula d' N2' := by
  let r := Q'.ofNat 2 * d + 1
  let r' := Q'.ofNat 2 * d' + 1
  have hr : r ≈ r' := by
    exact add_congr₂ (mul_congr₂ (Q'.eqv_refl _) hd) (Q'.eqv_refl _)
  unfold qDriftFormula
  dsimp only [r, r'] at hr
  exact add_congr₂
    (add_congr₂
      (mul_congr₂ (Q'.eqv_refl _)
        (RingNormaliser.qpow_eqv_congr hd 4))
      (mul_congr₂
        (mul_congr₂
          (mul_congr₂ (Q'.eqv_refl _) hN) hr)
        (RingNormaliser.qpow_eqv_congr hd 2)))
    (mul_congr₂
      (mul_congr₂ hN
        (add_congr₂ hN (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))))
      (RingNormaliser.qpow_eqv_congr hr 2))

private theorem rnqpow_two_eqv (x : Q') :
    RingNormaliser.qpow x 2 ≈ x * x := by
  simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
  semantic_ring

private theorem qHarmonicDriftDen_eqv (k : Nat) :
    qsub (RingNormaliser.qpow (Q'.ofNat (k + 2)) 2) (qc 1) ≈
      Q'.ofNat (driftDen k) := by
  have hD2 : RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 ≈
      Q'.ofNat ((k + 2) * (k + 2)) :=
    Q'.eqv_trans _ _ _ (rnqpow_two_eqv _)
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (k + 2) (k + 2)))
  have hsqPos : 0 < (k + 2) * (k + 2) :=
    Nat.mul_pos (by omega) (by omega)
  have hsub := ofNat_sub_eq ((k + 2) * (k + 2)) 1 (by omega)
  refine Q'.eqv_trans _
    (qsub (Q'.ofNat ((k + 2) * (k + 2))) (qc 1)) _ ?_ ?_
  · exact add_congr₂ hD2
      (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))
  exact Q'.eqv_of_eq (by
    unfold driftDen
    exact hsub.symm)

private theorem two_quadratic_coeff_eqv (M : Nat) :
    Q'.ofNat 2 * Q'.ofNat (lowerSixQuadraticCoeff M) ≈
      Q'.ofNat M * (Q'.ofNat M + -(1 : Q')) := by
  have hc := lowerSixQuadraticCoeff_double M
  refine Q'.eqv_trans _ (Q'.ofNat (2 * lowerSixQuadraticCoeff M)) _
    (Q'.eqv_symm
      (HeatKernelRGStep.ofNat_mul_eqv 2 (lowerSixQuadraticCoeff M))) ?_
  rw [hc]
  cases M with
  | zero =>
      simp only [Nat.zero_mul]
      semantic_ring
  | succ M =>
      have hsub := ofNat_sub_eq (M + 1) 1 (by omega)
      refine Q'.eqv_trans _
        (Q'.ofNat (M + 1) * Q'.ofNat (M + 1 - 1)) _
        (HeatKernelRGStep.ofNat_mul_eqv (M + 1) (M + 1 - 1)) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_of_eq (by
          simpa only [qc, qsub, qadd, qneg] using hsub))

private theorem driftFormula_eqv_scaled
    {d N2 C v : Q'} (hdv : d * v ≈ (1 : Q'))
    (hC : Q'.ofNat 2 * C ≈ N2 * (N2 + -(1 : Q'))) :
    qDriftFormula d N2 ≈
      (Q'.ofNat 2 * RingNormaliser.qpow d 4) *
        (((1 : Q') + N2 * ((v + v) + v * v)) +
          C * (((v + v) + v * v) * ((v + v) + v * v))) := by
  let r := Q'.ofNat 2 * d + 1
  let E := (v + v) + v * v
  have hv2 : RingNormaliser.qpow v 2 ≈ v * v := rnqpow_two_eqv v
  have htwo : Q'.ofNat 2 * v ≈ v + v := by
    refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * v) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)
    semantic_ring
  have hrRaw : r * (v * v) ≈ E := by
    refine Q'.eqv_trans _
      (Q'.ofNat 2 * ((d * v) * v) + v * v) _ ?_ ?_
    · dsimp only [r]
      semantic_ring
    refine Q'.eqv_trans _
      (Q'.ofNat 2 * ((1 : Q') * v) + v * v) _ ?_ ?_
    · exact add_congr₂
        (mul_congr₂ (Q'.eqv_refl _)
          (mul_congr₂ hdv (Q'.eqv_refl _)))
        (Q'.eqv_refl _)
    dsimp only [E]
    exact add_congr₂
      (Q'.eqv_trans _ (Q'.ofNat 2 * v) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv v)) htwo)
      (Q'.eqv_refl _)
  have hE : E ≈ r * RingNormaliser.qpow v 2 := by
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (r * (v * v)) _
        (Q'.mul_eqv_congr_left _ _ _ hv2) hrRaw)
  have hcancel2 :
      RingNormaliser.qpow d 4 * RingNormaliser.qpow v 2 ≈
        RingNormaliser.qpow d 2 := by
    simpa only using rnqpow_cancel hdv 2 2
  have hcancel4 :
      RingNormaliser.qpow d 4 * RingNormaliser.qpow v 4 ≈ (1 : Q') := by
    simpa only [RingNormaliser.qpow_zero] using rnqpow_cancel hdv 0 4
  have hlin : RingNormaliser.qpow d 4 * E ≈
      r * RingNormaliser.qpow d 2 := by
    refine Q'.eqv_trans _
      (RingNormaliser.qpow d 4 *
        (r * RingNormaliser.qpow v 2)) _
      (Q'.mul_eqv_congr_left _ _ _ hE) ?_
    refine Q'.eqv_trans _
      (r * (RingNormaliser.qpow d 4 * RingNormaliser.qpow v 2)) _
      (by semantic_ring) ?_
    exact Q'.mul_eqv_congr_left _ _ _ hcancel2
  have hEsq : E * E ≈
      RingNormaliser.qpow r 2 * RingNormaliser.qpow v 4 := by
    refine Q'.eqv_trans _
      ((r * RingNormaliser.qpow v 2) *
        (r * RingNormaliser.qpow v 2)) _
      (mul_congr₂ hE hE) ?_
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hquad : RingNormaliser.qpow d 4 * (E * E) ≈
      RingNormaliser.qpow r 2 := by
    refine Q'.eqv_trans _
      (RingNormaliser.qpow d 4 *
        (RingNormaliser.qpow r 2 * RingNormaliser.qpow v 4)) _
      (Q'.mul_eqv_congr_left _ _ _ hEsq) ?_
    refine Q'.eqv_trans _
      (RingNormaliser.qpow r 2 *
        (RingNormaliser.qpow d 4 * RingNormaliser.qpow v 4)) _
      (by semantic_ring) ?_
    exact Q'.eqv_trans _ (RingNormaliser.qpow r 2 * 1) _
      (Q'.mul_eqv_congr_left _ _ _ hcancel4)
      (Q'.mul_one_eqv _)
  have hexpand :
      (Q'.ofNat 2 * RingNormaliser.qpow d 4) *
          (((1 : Q') + N2 * E) + C * (E * E)) ≈
        (Q'.ofNat 2 * RingNormaliser.qpow d 4 +
          (Q'.ofNat 2 * N2) * (RingNormaliser.qpow d 4 * E)) +
          (Q'.ofNat 2 * C) * (RingNormaliser.qpow d 4 * (E * E)) := by
    semantic_ring
  have hterms :
      (Q'.ofNat 2 * RingNormaliser.qpow d 4 +
          (Q'.ofNat 2 * N2) * (RingNormaliser.qpow d 4 * E)) +
          (Q'.ofNat 2 * C) * (RingNormaliser.qpow d 4 * (E * E)) ≈
        qDriftFormula d N2 := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * RingNormaliser.qpow d 4 +
          (Q'.ofNat 2 * N2) * (r * RingNormaliser.qpow d 2)) +
        (N2 * (N2 + -(1 : Q'))) * RingNormaliser.qpow r 2) _ ?_ ?_
    · exact add_congr₂
        (add_congr₂ (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_left _ _ _ hlin))
        (mul_congr₂ hC hquad)
    have hreassoc :
        ((Q'.ofNat 2 * RingNormaliser.qpow d 4 +
            (Q'.ofNat 2 * N2) * (r * RingNormaliser.qpow d 2)) +
          (N2 * (N2 + -(1 : Q'))) * RingNormaliser.qpow r 2) ≈
          (Q'.ofNat 2 * RingNormaliser.qpow d 4 +
            ((Q'.ofNat 2 * N2) * r) * RingNormaliser.qpow d 2) +
          (N2 * (N2 + -(1 : Q'))) * RingNormaliser.qpow r 2 := by
      semantic_ring
    simpa only [qDriftFormula, r] using hreassoc
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hexpand hterms)

private theorem ofNat_mul_unit_eqv_one (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

theorem qDriftFactorScaled_eq_physical (k n : Nat) :
    qDriftFactorScaled (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 2 *
        RingNormaliser.qpow (Q'.ofNat (driftDen k)) 4) *
        lowerSixQuadraticTaylorFactor k n := by
  let d := Q'.ofNat (driftDen k)
  let N2 := Q'.ofNat (n * n)
  let C := Q'.ofNat (lowerSixQuadraticCoeff (n * n))
  let v := unit (driftDen k) (driftDen_pos k)
  have hD2 : RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 ≈
      Q'.ofNat ((k + 2) * (k + 2)) :=
    Q'.eqv_trans _ _ _ (rnqpow_two_eqv _)
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (k + 2) (k + 2)))
  have hsqPos : 0 < (k + 2) * (k + 2) :=
    Nat.mul_pos (by omega) (by omega)
  have hsub := ofNat_sub_eq ((k + 2) * (k + 2)) 1 (by omega)
  have hd :
      qsub (RingNormaliser.qpow (Q'.ofNat (k + 2)) 2) (qc 1) ≈ d := by
    refine Q'.eqv_trans _
      (qsub (Q'.ofNat ((k + 2) * (k + 2))) (qc 1)) _ ?_ ?_
    · exact add_congr₂ hD2
        (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))
    dsimp only [d]
    exact Q'.eqv_of_eq (by
      unfold driftDen
      exact hsub.symm)
  have hN2 : RingNormaliser.qpow (Q'.ofNat n) 2 ≈ N2 := by
    dsimp only [N2]
    exact Q'.eqv_trans _ _ _ (rnqpow_two_eqv _)
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv n n))
  have hformula :
      qDriftFactorScaled (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
        qDriftFormula d N2 := by
    unfold qDriftFactorScaled
    change qDriftFormula
      (qsub (RingNormaliser.qpow (Q'.ofNat (k + 2)) 2) (qc 1))
      (RingNormaliser.qpow (Q'.ofNat n) 2) ≈ qDriftFormula d N2
    exact qDriftFormula_congr hd hN2
  have hdv : d * v ≈ (1 : Q') := by
    dsimp only [d, v]
    exact ofNat_mul_unit_eqv_one (driftDen k) (driftDen_pos k)
  have hC : Q'.ofNat 2 * C ≈ N2 * (N2 + -(1 : Q')) := by
    dsimp only [C, N2]
    exact two_quadratic_coeff_eqv (n * n)
  have hscaled := driftFormula_eqv_scaled hdv hC
  refine Q'.eqv_trans _ _ _ hformula ?_
  dsimp only [d, N2, C, v] at hscaled ⊢
  unfold lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixDriftExcess
  exact hscaled

private theorem rnqpow_seven_eqv (u : Q') :
    RingNormaliser.qpow u 7 ≈
      u * (u * (u * (u * (u * (u * u))))) := by
  simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
  semantic_ring

private theorem scaled_slope_square {D Ts T : Q'}
    (hT : Ts ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D 6) * T) :
    Q'.ofNat 28 * RingNormaliser.qpow Ts 2 ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
        (Q'.ofNat 4 * (T * T)) := by
  have hTsq : RingNormaliser.qpow Ts 2 ≈
      ((Q'.ofNat 720 * RingNormaliser.qpow D 6) * T) *
        ((Q'.ofNat 720 * RingNormaliser.qpow D 6) * T) :=
    Q'.eqv_trans _ _ _ (rnqpow_two_eqv Ts) (mul_congr₂ hT hT)
  have hD12 : RingNormaliser.qpow D 12 ≈
      RingNormaliser.qpow D 6 * RingNormaliser.qpow D 6 := by
    simpa only using RingNormaliser.qpow_add D 6 6
  have hcoef :
      Q'.ofNat 28 * (Q'.ofNat 720 * Q'.ofNat 720) ≈
        Q'.ofNat 3628800 * Q'.ofNat 4 := by
    decide
  refine Q'.eqv_trans _
    (Q'.ofNat 28 *
      (((Q'.ofNat 720 * RingNormaliser.qpow D 6) * T) *
        ((Q'.ofNat 720 * RingNormaliser.qpow D 6) * T))) _
    (Q'.mul_eqv_congr_left _ _ _ hTsq) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 28 * (Q'.ofNat 720 * Q'.ofNat 720)) *
      ((RingNormaliser.qpow D 6 * RingNormaliser.qpow D 6) * (T * T))) _
    (by semantic_ring) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 3628800 * Q'.ofNat 4) *
      (RingNormaliser.qpow D 12 * (T * T))) _ ?_ ?_
  · exact mul_congr₂ hcoef
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hD12))
  semantic_ring

private theorem scaled_septic_term {D u P A C L : Q'}
    (hDu : D * u ≈ (1 : Q'))
    (hP : P ≈ (Q'.ofNat 3628800 * L) * (A * C)) :
    P * RingNormaliser.qpow D 5 ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
        (L * (A *
          (C * (u * (u * (u * (u * (u * (u * u))))))))) := by
  have hcancel :
      RingNormaliser.qpow D 12 * RingNormaliser.qpow u 7 ≈
        RingNormaliser.qpow D 5 := by
    simpa only using rnqpow_cancel hDu 5 7
  have hu7 := rnqpow_seven_eqv u
  refine Q'.eqv_trans _
    (((Q'.ofNat 3628800 * L) * (A * C)) *
      RingNormaliser.qpow D 5) _
    (Q'.mul_eqv_congr_right _ _ _ hP) ?_
  refine Q'.eqv_trans _
    (((Q'.ofNat 3628800 * L) * (A * C)) *
      (RingNormaliser.qpow D 12 * RingNormaliser.qpow u 7)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcancel)) ?_
  refine Q'.eqv_trans _
    (((Q'.ofNat 3628800 * L) * (A * C)) *
      (RingNormaliser.qpow D 12 *
        (u * (u * (u * (u * (u * (u * u)))))))) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hu7)) ?_
  semantic_ring

private theorem scaled_profile_scalar {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) :
    (Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1) *
        RingNormaliser.qpow D 9 ≈
      RingNormaliser.qpow D 12 *
        (u * (Q'.ofNat 12 + u * u)) := by
  have hu1 : RingNormaliser.qpow u 1 ≈ u := by
    simpa only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero] using
      Q'.one_mul_eqv u
  have hu3 : RingNormaliser.qpow u 3 ≈ u * (u * u) := by
    simp only [RingNormaliser.qpow_succ, RingNormaliser.qpow_zero]
    semantic_ring
  have hc1 : RingNormaliser.qpow D 12 * u ≈
      RingNormaliser.qpow D 11 :=
    Q'.eqv_trans _
      (RingNormaliser.qpow D 12 * RingNormaliser.qpow u 1) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hu1))
      (by simpa only using rnqpow_cancel hDu 11 1)
  have hc3 : RingNormaliser.qpow D 12 * (u * (u * u)) ≈
      RingNormaliser.qpow D 9 :=
    Q'.eqv_trans _
      (RingNormaliser.qpow D 12 * RingNormaliser.qpow u 3) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hu3))
      (by simpa only using rnqpow_cancel hDu 9 3)
  have hD29 : RingNormaliser.qpow D 2 * RingNormaliser.qpow D 9 ≈
      RingNormaliser.qpow D 11 := by
    exact Q'.eqv_symm (by
      simpa only using RingNormaliser.qpow_add D 2 9)
  have hleft :
      (Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1) *
          RingNormaliser.qpow D 9 ≈
        Q'.ofNat 12 * RingNormaliser.qpow D 11 +
          RingNormaliser.qpow D 9 := by
    refine Q'.eqv_trans _
      (Q'.ofNat 12 *
          (RingNormaliser.qpow D 2 * RingNormaliser.qpow D 9) +
        RingNormaliser.qpow D 9) _ (by semantic_ring) ?_
    exact add_congr₂
      (Q'.mul_eqv_congr_left _ _ _ hD29) (Q'.eqv_refl _)
  have hright :
      RingNormaliser.qpow D 12 *
          (u * (Q'.ofNat 12 + u * u)) ≈
        Q'.ofNat 12 * RingNormaliser.qpow D 11 +
          RingNormaliser.qpow D 9 := by
    refine Q'.eqv_trans _
      (Q'.ofNat 12 * (RingNormaliser.qpow D 12 * u) +
        RingNormaliser.qpow D 12 * (u * (u * u))) _
      (by semantic_ring) ?_
    exact add_congr₂ (Q'.mul_eqv_congr_left _ _ _ hc1) hc3
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

private theorem scaled_profile_term {D u N2 N2q : Q'}
    (hDu : D * u ≈ (1 : Q')) (hN2 : N2q ≈ N2) :
    ((Q'.ofNat 3628800 * N2q) *
        (Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1)) *
        RingNormaliser.qpow D 9 ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
        ((u * (Q'.ofNat 12 + u * u)) * N2) := by
  have hp := scaled_profile_scalar hDu
  refine Q'.eqv_trans _
    (Q'.ofNat 3628800 * N2q *
      ((Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1) *
        RingNormaliser.qpow D 9)) _ (by semantic_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 3628800 * N2 *
      (RingNormaliser.qpow D 12 *
        (u * (Q'.ofNat 12 + u * u)))) _
      (mul_congr₂
      (mul_congr₂ (Q'.eqv_refl _) hN2) hp) ?_
  semantic_ring

private def qOldSepticTerm (D N : Q') : Q' :=
  let A := qadd N (qc 1)
  let m := qadd (qmul (qc 2) N) (qc 1)
  qmul (qmul (qmul (qc 8640) A) (qFall m 7)) (qpow D 5)

private def qNextSepticTerm (D N : Q') : Q' :=
  let A := qadd N (qc 1)
  let m := qadd (qmul (qc 2) N) (qc 1)
  qmul (qmul (qmul (qc 11520) A) (qFall m 7)) (qpow D 5)

private def qProfileTerm (D N : Q') : Q' :=
  qmul (qmul (qmul (qc 3628800) (qpow N 2))
    (qadd (qmul (qc 12) (qpow D 2)) (qc 1))) (qpow D 9)

private theorem qOldSepticTerm_eq_physical (k n : Nat) :
    qOldSepticTerm (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 3628800 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 12) *
        (Q'.ofNat 12 * rootSlopeTaylor6Error (harmU k) n) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let Aq := qadd N (qc 1)
  let mq := qadd (qmul (qc 2) N) (qc 1)
  let A := Q'.ofNat (n + 1)
  let m := 2 * n + 1
  let C := Q'.ofNat (septicCoeff m)
  let u := harmU k
  let P := qmul (qmul (qc 8640) Aq) (qFall mq 7)
  have hAq : Aq ≈ A := by
    dsimp only [Aq, A, N]
    exact succExpr_eqv n
  have hmq : mq ≈ Q'.ofNat m := by
    dsimp only [mq, N, m]
    exact modeExpr_eqv n
  have hfall : qFallingNat m 7 = 5040 * septicCoeff m := by
    have h7 := septicCoeff_fiveThousandForty m
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h7.symm
  have holdNat : 8640 * qFallingNat m 7 =
      (3628800 * 12) * septicCoeff m := by
    rw [hfall, ← Nat.mul_assoc]
  have hfallCongr : qFall mq 7 ≈ qFall (Q'.ofNat m) 7 :=
    qFall_congr hmq 7
  have hbase0 : qmul (qc 8640) (qFall mq 7) ≈
      Q'.ofNat (3628800 * 12) * C := by
    refine Q'.eqv_trans _
      (qmul (qc 8640) (qFall (Q'.ofNat m) 7)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hfallCongr
    dsimp only [C]
    exact scaled_qFall_custom 8640 (3628800 * 12)
      (septicCoeff m) m 7 holdNat
  have hscale12 : Q'.ofNat (3628800 * 12) ≈
      Q'.ofNat 3628800 * Q'.ofNat 12 :=
    HeatKernelRGStep.ofNat_mul_eqv 3628800 12
  have hbase : qmul (qc 8640) (qFall mq 7) ≈
      (Q'.ofNat 3628800 * Q'.ofNat 12) * C :=
    Q'.eqv_trans _ _ _ hbase0
      (Q'.mul_eqv_congr_right _ _ _ hscale12)
  have hP : P ≈
      (Q'.ofNat 3628800 * Q'.ofNat 12) * (A * C) := by
    refine Q'.eqv_trans _
      (Aq * (qmul (qc 8640) (qFall mq 7))) _ (by
        dsimp only [P]
        simp only [qmul]
        semantic_ring) ?_
    refine Q'.eqv_trans _
      (A * ((Q'.ofNat 3628800 * Q'.ofNat 12) * C)) _
      (mul_congr₂ hAq hbase) ?_
    semantic_ring
  have hDu : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact harmonic_den_mul_unit k
  have herr := scaled_septic_term hDu hP
  change P * RingNormaliser.qpow D 5 ≈
    (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
      (Q'.ofNat 12 * (A *
        (C * (u * (u * (u * (u * (u * (u * u)))))))))
  exact herr

private theorem qNextSepticTerm_eq_physical (j n : Nat) :
    qNextSepticTerm (Q'.ofNat (j + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 3628800 *
        RingNormaliser.qpow (Q'.ofNat (j + 2)) 12) *
        (Q'.ofNat 16 * rootSlopeTaylor6Error (harmU j) n) := by
  let D := Q'.ofNat (j + 2)
  let N := Q'.ofNat n
  let Aq := qadd N (qc 1)
  let mq := qadd (qmul (qc 2) N) (qc 1)
  let A := Q'.ofNat (n + 1)
  let m := 2 * n + 1
  let C := Q'.ofNat (septicCoeff m)
  let u := harmU j
  let P := qmul (qmul (qc 11520) Aq) (qFall mq 7)
  have hAq : Aq ≈ A := by
    dsimp only [Aq, A, N]
    exact succExpr_eqv n
  have hmq : mq ≈ Q'.ofNat m := by
    dsimp only [mq, N, m]
    exact modeExpr_eqv n
  have hfall : qFallingNat m 7 = 5040 * septicCoeff m := by
    have h7 := septicCoeff_fiveThousandForty m
    simpa only [qFallingNat, Nat.sub_zero, Nat.one_mul] using h7.symm
  have hnextNat : 11520 * qFallingNat m 7 =
      (3628800 * 16) * septicCoeff m := by
    rw [hfall, ← Nat.mul_assoc]
  have hfallCongr : qFall mq 7 ≈ qFall (Q'.ofNat m) 7 :=
    qFall_congr hmq 7
  have hbase0 : qmul (qc 11520) (qFall mq 7) ≈
      Q'.ofNat (3628800 * 16) * C := by
    refine Q'.eqv_trans _
      (qmul (qc 11520) (qFall (Q'.ofNat m) 7)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hfallCongr
    dsimp only [C]
    exact scaled_qFall_custom 11520 (3628800 * 16)
      (septicCoeff m) m 7 hnextNat
  have hscale16 : Q'.ofNat (3628800 * 16) ≈
      Q'.ofNat 3628800 * Q'.ofNat 16 :=
    HeatKernelRGStep.ofNat_mul_eqv 3628800 16
  have hbase : qmul (qc 11520) (qFall mq 7) ≈
      (Q'.ofNat 3628800 * Q'.ofNat 16) * C :=
    Q'.eqv_trans _ _ _ hbase0
      (Q'.mul_eqv_congr_right _ _ _ hscale16)
  have hP : P ≈
      (Q'.ofNat 3628800 * Q'.ofNat 16) * (A * C) := by
    refine Q'.eqv_trans _
      (Aq * (qmul (qc 11520) (qFall mq 7))) _ (by
        dsimp only [P]
        simp only [qmul]
        semantic_ring) ?_
    refine Q'.eqv_trans _
      (A * ((Q'.ofNat 3628800 * Q'.ofNat 16) * C)) _
      (mul_congr₂ hAq hbase) ?_
    semantic_ring
  have hDu : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact harmonic_den_mul_unit j
  have herr := scaled_septic_term hDu hP
  change P * RingNormaliser.qpow D 5 ≈
    (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
      (Q'.ofNat 16 * (A *
        (C * (u * (u * (u * (u * (u * (u * u)))))))))
  exact herr

private theorem qProfileTerm_eq_physical (k n : Nat) :
    qProfileTerm (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 3628800 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 12) *
        (lowerSixDirichletProfile k * Q'.ofNat (n * n)) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let N2q := RingNormaliser.qpow N 2
  let N2 := Q'.ofNat (n * n)
  let u := harmU k
  have hDu : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact harmonic_den_mul_unit k
  have hN2 : N2q ≈ N2 := by
    dsimp only [N2q, N2, N]
    exact Q'.eqv_trans _ _ _ (rnqpow_two_eqv _)
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv n n))
  have hp := scaled_profile_term hDu hN2
  change
    ((Q'.ofNat 3628800 * N2q) *
        (Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1)) *
        RingNormaliser.qpow D 9 ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) *
        ((u * (Q'.ofNat 12 + u * u)) * N2)
  exact hp

private theorem assemble_inner_old
    {scale squareQ errorQ profileQ T E profile : Q'}
    (hsquare : squareQ ≈ scale * (Q'.ofNat 4 * (T * T)))
    (herror : errorQ ≈ scale * (Q'.ofNat 12 * E))
    (hprofile : profileQ ≈ scale * profile) :
    (squareQ + errorQ) + -profileQ ≈
      scale * (Q'.ofNat 4 * (T * T + Q'.ofNat 3 * E) + -profile) := by
  have hcombined := add_congr₂ (add_congr₂ hsquare herror)
    (Q'.neg_eqv_congr _ _ hprofile)
  refine Q'.eqv_trans _ _ _ hcombined ?_
  refine Q'.eqv_trans _
    (scale * ((Q'.ofNat 4 * (T * T) + Q'.ofNat 12 * E) + -profile)) _
    (by semantic_ring) ?_
  have h12 : Q'.ofNat 12 ≈ Q'.ofNat 4 * Q'.ofNat 3 := by
    simpa only using HeatKernelRGStep.ofNat_mul_eqv 4 3
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * (T * T) +
      (Q'.ofNat 4 * Q'.ofNat 3) * E + -profile) _ ?_ ?_
  · exact add_congr₂
      (add_congr₂ (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_right _ _ _ h12))
      (Q'.eqv_refl _)
  semantic_ring

private theorem assemble_inner_next
    {scale squareQ errorQ profileQ T E profile : Q'}
    (hsquare : squareQ ≈ scale * (Q'.ofNat 4 * (T * T)))
    (herror : errorQ ≈ scale * (Q'.ofNat 16 * E))
    (hprofile : profileQ ≈ scale * profile) :
    (squareQ + -errorQ) + -profileQ ≈
      scale *
        (Q'.ofNat 4 * (T * T + -(Q'.ofNat 4 * E)) + -profile) := by
  have hcombined := add_congr₂
    (add_congr₂ hsquare (Q'.neg_eqv_congr _ _ herror))
    (Q'.neg_eqv_congr _ _ hprofile)
  refine Q'.eqv_trans _ _ _ hcombined ?_
  refine Q'.eqv_trans _
    (scale * ((Q'.ofNat 4 * (T * T) + -(Q'.ofNat 16 * E)) +
      -profile)) _ (by semantic_ring) ?_
  have h16 : Q'.ofNat 16 ≈ Q'.ofNat 4 * Q'.ofNat 4 := by
    simpa only using HeatKernelRGStep.ofNat_mul_eqv 4 4
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * (T * T) +
      -((Q'.ofNat 4 * Q'.ofNat 4) * E) + -profile) _ ?_ ?_
  · exact add_congr₂
      (add_congr₂ (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ _ h16)))
      (Q'.eqv_refl _)
  semantic_ring

theorem qInnerOldScaled_eq_physical (k n : Nat) :
    qInnerOldScaled (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 3628800 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 12) *
        (Q'.ofNat 4 *
            (rootSlopeTaylor6 (harmU k) n * rootSlopeTaylor6 (harmU k) n +
              Q'.ofNat 3 * rootSlopeTaylor6Error (harmU k) n) +
          -(lowerSixDirichletProfile k * Q'.ofNat (n * n))) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let Tq := qSlopeScaled D N
  let T := rootSlopeTaylor6 (harmU k) n
  let E := rootSlopeTaylor6Error (harmU k) n
  let N2 := Q'.ofNat (n * n)
  let scale := Q'.ofNat 3628800 * RingNormaliser.qpow D 12
  have hT : Tq ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D 6) * T := by
    dsimp only [Tq, D, N, T]
    exact qSlopeScaled_eq_physical n k
  have hsquare : Q'.ofNat 28 * RingNormaliser.qpow Tq 2 ≈
      scale * (Q'.ofNat 4 * (T * T)) := by
    dsimp only [scale]
    exact scaled_slope_square hT
  have herror := qOldSepticTerm_eq_physical k n
  have hprofile := qProfileTerm_eq_physical k n
  have hfinal := assemble_inner_old hsquare herror hprofile
  change
    (Q'.ofNat 28 * RingNormaliser.qpow Tq 2 +
        qOldSepticTerm D N) + -qProfileTerm D N ≈
      scale *
        (Q'.ofNat 4 * (T * T + Q'.ofNat 3 * E) +
          -(lowerSixDirichletProfile k * N2))
  exact hfinal

theorem qInnerNextScaled_eq_physical (k n : Nat) :
    qInnerNextScaled (Q'.ofNat (k + 3)) (Q'.ofNat n) ≈
      (Q'.ofNat 3628800 *
        RingNormaliser.qpow (Q'.ofNat (k + 3)) 12) *
        (Q'.ofNat 4 *
            (rootSlopeTaylor6 (harmU (k + 1)) n *
                rootSlopeTaylor6 (harmU (k + 1)) n +
              -(Q'.ofNat 4 * rootSlopeTaylor6Error (harmU (k + 1)) n)) +
          -(lowerSixDirichletProfile (k + 1) * Q'.ofNat (n * n))) := by
  let D1 := Q'.ofNat (k + 3)
  let N := Q'.ofNat n
  let Tq := qSlopeScaled D1 N
  let T := rootSlopeTaylor6 (harmU (k + 1)) n
  let E := rootSlopeTaylor6Error (harmU (k + 1)) n
  let N2 := Q'.ofNat (n * n)
  let scale := Q'.ofNat 3628800 * RingNormaliser.qpow D1 12
  have hT : Tq ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D1 6) * T := by
    dsimp only [Tq, D1, N, T]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      qSlopeScaled_eq_physical n (k + 1)
  have hsquare : Q'.ofNat 28 * RingNormaliser.qpow Tq 2 ≈
      scale * (Q'.ofNat 4 * (T * T)) := by
    dsimp only [scale]
    exact scaled_slope_square hT
  have herror : qNextSepticTerm D1 N ≈
      scale * (Q'.ofNat 16 * E) := by
    dsimp only [D1, N, scale, E]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      qNextSepticTerm_eq_physical (k + 1) n
  have hprofile : qProfileTerm D1 N ≈
      scale * (lowerSixDirichletProfile (k + 1) * N2) := by
    dsimp only [D1, N, scale, N2]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      qProfileTerm_eq_physical (k + 1) n
  have hfinal := assemble_inner_next hsquare herror hprofile
  change
    (Q'.ofNat 28 * RingNormaliser.qpow Tq 2 +
        -qNextSepticTerm D1 N) + -qProfileTerm D1 N ≈
      scale *
        (Q'.ofNat 4 * (T * T + -(Q'.ofNat 4 * E)) +
          -(lowerSixDirichletProfile (k + 1) * N2))
  exact hfinal

private theorem carrier_factor
    (d4 D D1 F innerNext innerOld : Q') :
    (((Q'.ofNat 2 * d4) * F) *
          ((Q'.ofNat 3628800 * RingNormaliser.qpow D1 12) * innerNext)) *
        RingNormaliser.qpow D 11 +
      -(((Q'.ofNat 2 * d4) *
          ((Q'.ofNat 3628800 * RingNormaliser.qpow D 12) * innerOld)) *
        RingNormaliser.qpow D1 11) ≈
      (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 11) *
          RingNormaliser.qpow D1 11) *
        ((D1 * F) * innerNext + -(D * innerOld)) := by
  have hD12 : RingNormaliser.qpow D 12 ≈
      RingNormaliser.qpow D 11 * D := by
    change RingNormaliser.qpow D 11 * D ≈
      RingNormaliser.qpow D 11 * D
    exact Q'.eqv_refl _
  have hD1_12 : RingNormaliser.qpow D1 12 ≈
      RingNormaliser.qpow D1 11 * D1 := by
    change RingNormaliser.qpow D1 11 * D1 ≈
      RingNormaliser.qpow D1 11 * D1
    exact Q'.eqv_refl _
  have hpowers :
      (((Q'.ofNat 2 * d4) * F) *
            ((Q'.ofNat 3628800 * RingNormaliser.qpow D1 12) * innerNext)) *
          RingNormaliser.qpow D 11 +
        -(((Q'.ofNat 2 * d4) *
            ((Q'.ofNat 3628800 * RingNormaliser.qpow D 12) * innerOld)) *
          RingNormaliser.qpow D1 11) ≈
        (((Q'.ofNat 2 * d4) * F) *
            ((Q'.ofNat 3628800 *
              (RingNormaliser.qpow D1 11 * D1)) * innerNext)) *
            RingNormaliser.qpow D 11 +
          -(((Q'.ofNat 2 * d4) *
            ((Q'.ofNat 3628800 *
              (RingNormaliser.qpow D 11 * D)) * innerOld)) *
            RingNormaliser.qpow D1 11) := by
    exact add_congr₂
      (mul_congr₂
        (mul_congr₂ (Q'.eqv_refl _)
          (mul_congr₂
            (mul_congr₂ (Q'.eqv_refl _) hD1_12)
            (Q'.eqv_refl _)))
        (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _
        (mul_congr₂
          (mul_congr₂ (Q'.eqv_refl _)
            (mul_congr₂
              (mul_congr₂ (Q'.eqv_refl _) hD12)
              (Q'.eqv_refl _)))
          (Q'.eqv_refl _)))
  have hfactor :
      (((Q'.ofNat 2 * d4) * F) *
          ((Q'.ofNat 3628800 *
            (RingNormaliser.qpow D1 11 * D1)) * innerNext)) *
          RingNormaliser.qpow D 11 +
        -(((Q'.ofNat 2 * d4) *
          ((Q'.ofNat 3628800 *
            (RingNormaliser.qpow D 11 * D)) * innerOld)) *
          RingNormaliser.qpow D1 11) ≈
        ((((Q'.ofNat 2 * Q'.ofNat 3628800) * d4) *
            RingNormaliser.qpow D 11) * RingNormaliser.qpow D1 11) *
          ((D1 * F) * innerNext + -(D * innerOld)) := by
    semantic_ring
  have hcoef : Q'.ofNat 2 * Q'.ofNat 3628800 ≈
      Q'.ofNat 7257600 := by
    simpa only using
      Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 3628800)
  have hcommon :
      ((((Q'.ofNat 2 * Q'.ofNat 3628800) * d4) *
          RingNormaliser.qpow D 11) * RingNormaliser.qpow D1 11) ≈
        (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 11) *
          RingNormaliser.qpow D1 11) :=
    mul_congr₂
      (mul_congr₂ (mul_congr₂ hcoef (Q'.eqv_refl _))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hpowers
    (Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_right _ _ _ hcommon))

private def physicalInnerNext (k n : Nat) : Q' :=
  Q'.ofNat 4 *
      (rootSlopeTaylor6 (harmU (k + 1)) n *
          rootSlopeTaylor6 (harmU (k + 1)) n +
        -(Q'.ofNat 4 * rootSlopeTaylor6Error (harmU (k + 1)) n)) +
    -(lowerSixDirichletProfile (k + 1) * Q'.ofNat (n * n))

private def physicalInnerOld (k n : Nat) : Q' :=
  Q'.ofNat 4 *
      (rootSlopeTaylor6 (harmU k) n * rootSlopeTaylor6 (harmU k) n +
        Q'.ofNat 3 * rootSlopeTaylor6Error (harmU k) n) +
    -(lowerSixDirichletProfile k * Q'.ofNat (n * n))

private def physicalCarrier (k n : Nat) : Q' :=
  (Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n) *
      physicalInnerNext k n +
    -(Q'.ofNat (k + 2) * physicalInnerOld k n)

private def physicalCarrierScale (k : Nat) : Q' :=
  Q'.ofNat 7257600 *
      RingNormaliser.qpow (Q'.ofNat (driftDen k)) 4 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 11 *
    RingNormaliser.qpow (Q'.ofNat (k + 3)) 11

theorem qCarrierScaled_eq_physical (k n : Nat) :
    qCarrierScaled (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      physicalCarrierScale k * physicalCarrier k n := by
  let D := Q'.ofNat (k + 2)
  let D1 := Q'.ofNat (k + 3)
  let N := Q'.ofNat n
  let dExpr := qsub (RingNormaliser.qpow D 2) (qc 1)
  let d := Q'.ofNat (driftDen k)
  let d4 := RingNormaliser.qpow d 4
  let F := lowerSixQuadraticTaylorFactor k n
  let innerNext := physicalInnerNext k n
  let innerOld := physicalInnerOld k n
  let carrier := (D1 * F) * innerNext + -(D * innerOld)
  let common :=
    ((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 11) *
      RingNormaliser.qpow D1 11
  have hD1eq : qadd D (qc 1) = D1 := by
    dsimp only [D, D1]
    have h := (ofNat_add_eq_exact (k + 2) 1).symm
    simpa only [qc, show k + 2 + 1 = k + 3 by omega] using h
  have hd : dExpr ≈ d := by
    dsimp only [dExpr, D, d]
    exact qHarmonicDriftDen_eqv k
  have hd4 : RingNormaliser.qpow dExpr 4 ≈ d4 := by
    exact RingNormaliser.qpow_eqv_congr hd 4
  have hdrift : qDriftFactorScaled D N ≈
      (Q'.ofNat 2 * d4) * F := by
    dsimp only [D, N, d4, d, F]
    exact qDriftFactorScaled_eq_physical k n
  have hnext : qInnerNextScaled (qadd D (qc 1)) N ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D1 12) * innerNext := by
    rw [hD1eq]
    dsimp only [D1, N, innerNext]
    exact qInnerNextScaled_eq_physical k n
  have hold : qInnerOldScaled D N ≈
      (Q'.ofNat 3628800 * RingNormaliser.qpow D 12) * innerOld := by
    dsimp only [D, N, innerOld]
    exact qInnerOldScaled_eq_physical k n
  have hD1pow : RingNormaliser.qpow (qadd D (qc 1)) 11 ≈
      RingNormaliser.qpow D1 11 := by
    rw [hD1eq]
    exact Q'.eqv_refl _
  have hfirst :
      (qDriftFactorScaled D N * qInnerNextScaled (qadd D (qc 1)) N) *
          RingNormaliser.qpow D 11 ≈
        (((Q'.ofNat 2 * d4) * F) *
          ((Q'.ofNat 3628800 * RingNormaliser.qpow D1 12) * innerNext)) *
          RingNormaliser.qpow D 11 :=
    mul_congr₂ (mul_congr₂ hdrift hnext) (Q'.eqv_refl _)
  have hsecond :
      ((Q'.ofNat 2 * RingNormaliser.qpow dExpr 4) *
          qInnerOldScaled D N) * RingNormaliser.qpow (qadd D (qc 1)) 11 ≈
        ((Q'.ofNat 2 * d4) *
          ((Q'.ofNat 3628800 * RingNormaliser.qpow D 12) * innerOld)) *
          RingNormaliser.qpow D1 11 :=
    mul_congr₂
      (mul_congr₂
        (mul_congr₂ (Q'.eqv_refl _) hd4) hold) hD1pow
  have hraw := add_congr₂ hfirst (Q'.neg_eqv_congr _ _ hsecond)
  have hfactor := carrier_factor d4 D D1 F innerNext innerOld
  change
    (qDriftFactorScaled D N * qInnerNextScaled (qadd D (qc 1)) N) *
        RingNormaliser.qpow D 11 +
      -(((Q'.ofNat 2 * RingNormaliser.qpow dExpr 4) *
          qInnerOldScaled D N) *
        RingNormaliser.qpow (qadd D (qc 1)) 11) ≈ common * carrier
  exact Q'.eqv_trans _ _ _ hraw hfactor

private def physicalCommonDen (k : Nat) : Q' :=
  Q'.ofNat 7257600 *
      RingNormaliser.qpow (Q'.ofNat (driftDen k)) 4 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 12 *
    RingNormaliser.qpow (Q'.ofNat (k + 3)) 11

private def physicalMain (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  Q'.ofNat 48 * RingNormaliser.qpow D 4 * physicalCarrier k n +
    lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n) +
    -(Q'.ofNat 6 * RingNormaliser.qpow D 3)

private def physicalOldFlux (k n : Nat) : Q' :=
  Q'.ofNat n + -rootSlopeTaylor6 (harmU k) n

private def physicalOldPayment (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  (physicalOldFlux k n * physicalOldFlux k n) *
    lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))

private def physicalExactLower (k n : Nat) : Q' :=
  let A := Q'.ofNat (n + 1)
  (A * A) * physicalMain k n + -physicalOldPayment k n

private theorem physicalExactLower_eq (k n : Nat) :
    physicalExactLower k n =
      lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n := by
  rfl

private def qMainTerm (D N : Q') : Q' :=
  qadd
    (qmul (qmul (qc 48) (qpow D 5)) (qCarrierScaled D N))
    (qmul (qsub (qFlux D N) (qmul (qc 6) (qpow D 3)))
      (qCommonDen D))

private def qOldFluxTerm (D N : Q') : Q' :=
  qsub (qmul (qmul (qc 720) N) (qpow D 6)) (qSlopeScaled D N)

private def qOldPayment (D N : Q') : Q' :=
  let D1 := qadd D (qc 1)
  let d := qsub (qpow D 2) (qc 1)
  let oldFlux := qOldFluxTerm D N
  qmul
    (qmul
      (qmul (qc 14) (qpow d 4))
      (qpow D1 11))
    (qmul (qpow oldFlux 2) (qFlux D (qadd N (qc 1))))

theorem qCommonDen_eq_physical (k : Nat) :
    qCommonDen (Q'.ofNat (k + 2)) ≈ physicalCommonDen k := by
  let D := Q'.ofNat (k + 2)
  let D1 := Q'.ofNat (k + 3)
  let dExpr := qsub (RingNormaliser.qpow D 2) (qc 1)
  let d := Q'.ofNat (driftDen k)
  have hD1eq : qadd D (qc 1) = D1 := by
    dsimp only [D, D1]
    have h := (ofNat_add_eq_exact (k + 2) 1).symm
    simpa only [qc, show k + 2 + 1 = k + 3 by omega] using h
  have hd : dExpr ≈ d := by
    dsimp only [dExpr, D, d]
    exact qHarmonicDriftDen_eqv k
  have hd4 := RingNormaliser.qpow_eqv_congr hd 4
  have hD1pow : RingNormaliser.qpow (qadd D (qc 1)) 11 ≈
      RingNormaliser.qpow D1 11 := by
    rw [hD1eq]
    exact Q'.eqv_refl _
  change
    ((Q'.ofNat 7257600 * RingNormaliser.qpow dExpr 4) *
        RingNormaliser.qpow D 12) *
        RingNormaliser.qpow (qadd D (qc 1)) 11 ≈
      ((Q'.ofNat 7257600 * RingNormaliser.qpow d 4) *
        RingNormaliser.qpow D 12) * RingNormaliser.qpow D1 11
  exact mul_congr₂
    (mul_congr₂
      (mul_congr₂ (Q'.eqv_refl _) hd4) (Q'.eqv_refl _))
    hD1pow

private theorem main_carrier_factor (d4 D D1 C : Q') :
    (Q'.ofNat 48 * RingNormaliser.qpow D 5) *
        ((((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 11) *
          RingNormaliser.qpow D1 11) * C) ≈
      (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
          RingNormaliser.qpow D1 11) *
        ((Q'.ofNat 48 * RingNormaliser.qpow D 4) * C) := by
  have hpow : RingNormaliser.qpow D 5 * RingNormaliser.qpow D 11 ≈
      RingNormaliser.qpow D 12 * RingNormaliser.qpow D 4 := by
    exact Q'.eqv_trans _ (RingNormaliser.qpow D 16) _
      (Q'.eqv_symm (by
        simpa only using RingNormaliser.qpow_add D 5 11))
      (by simpa only using RingNormaliser.qpow_add D 12 4)
  let pref :=
    ((Q'.ofNat 48 * Q'.ofNat 7257600) * d4) *
      RingNormaliser.qpow D1 11
  refine Q'.eqv_trans _
    (pref *
      ((RingNormaliser.qpow D 5 * RingNormaliser.qpow D 11) * C)) _
    (by dsimp only [pref]; semantic_ring) ?_
  refine Q'.eqv_trans _
    (pref *
      ((RingNormaliser.qpow D 12 * RingNormaliser.qpow D 4) * C)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hpow)) ?_
  dsimp only [pref]
  semantic_ring

theorem qMainTerm_eq_physical (k n : Nat) :
    qMainTerm (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      physicalCommonDen k * physicalMain k n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let d4 := RingNormaliser.qpow (Q'.ofNat (driftDen k)) 4
  let D1 := Q'.ofNat (k + 3)
  let carrier := physicalCarrier k n
  let carrierScale :=
    ((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 11) *
      RingNormaliser.qpow D1 11
  let common :=
    ((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
      RingNormaliser.qpow D1 11
  let carrierTerm :=
    (Q'.ofNat 48 * RingNormaliser.qpow D 4) * carrier
  let J := lowerSixDiscreteHermiteFluxPoly D N
  let diff := J + -(Q'.ofNat 6 * RingNormaliser.qpow D 3)
  have hcarrier : qCarrierScaled D N ≈ carrierScale * carrier := by
    dsimp only [D, N, carrierScale, carrier, d4, D1]
    exact qCarrierScaled_eq_physical k n
  have hcarrierTerm :
      (Q'.ofNat 48 * RingNormaliser.qpow D 5) * qCarrierScaled D N ≈
        common * carrierTerm := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 48 * RingNormaliser.qpow D 5) *
        (carrierScale * carrier)) _
      (Q'.mul_eqv_congr_left _ _ _ hcarrier) ?_
    dsimp only [carrierScale, common, carrierTerm]
    exact main_carrier_factor d4 D D1 carrier
  have hflux : qFlux D N ≈ J := by
    dsimp only [J]
    exact qFlux_eq_physical D N
  have hdiff :
      qsub (qFlux D N) (qmul (qc 6) (qpow D 3)) ≈ diff := by
    dsimp only [diff]
    exact add_congr₂ hflux
      (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))
  have hcommon : qCommonDen D ≈ common := by
    dsimp only [D, common, d4, D1]
    exact qCommonDen_eq_physical k
  have hfluxTerm :
      qmul (qsub (qFlux D N) (qmul (qc 6) (qpow D 3)))
          (qCommonDen D) ≈ common * diff := by
    refine Q'.eqv_trans _ (diff * common) _
      (mul_congr₂ hdiff hcommon) ?_
    exact Q'.mul_comm_eqv diff common
  have hsum := add_congr₂ hcarrierTerm hfluxTerm
  have hfactor : common * carrierTerm + common * diff ≈
      common * (carrierTerm + diff) :=
    Q'.eqv_symm (Q'.mul_add_eqv common carrierTerm diff)
  have hmain : carrierTerm + diff ≈ physicalMain k n := by
    change carrierTerm +
        (J + -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) ≈
      (carrierTerm + J) +
        -(Q'.ofNat 6 * RingNormaliser.qpow D 3)
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv carrierTerm J
        (-(Q'.ofNat 6 * RingNormaliser.qpow D 3)))
  change
    (Q'.ofNat 48 * RingNormaliser.qpow D 5) * qCarrierScaled D N +
      qmul (qsub (qFlux D N) (qmul (qc 6) (qpow D 3)))
        (qCommonDen D) ≈ common * physicalMain k n
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_left _ _ _ hmain))

private theorem old_payment_factor
    (d4 D D1 oldQ old Jq J : Q')
    (hold : oldQ ≈
      (Q'.ofNat 720 * RingNormaliser.qpow D 6) * old)
    (hJ : Jq ≈ J) :
    ((Q'.ofNat 14 * d4) * RingNormaliser.qpow D1 11) *
        (RingNormaliser.qpow oldQ 2 * Jq) ≈
      (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
          RingNormaliser.qpow D1 11) * ((old * old) * J) := by
  have holdSq : RingNormaliser.qpow oldQ 2 ≈
      (((Q'.ofNat 720 * RingNormaliser.qpow D 6) * old) *
        ((Q'.ofNat 720 * RingNormaliser.qpow D 6) * old)) :=
    Q'.eqv_trans _ _ _ (rnqpow_two_eqv oldQ) (mul_congr₂ hold hold)
  have hD12 : RingNormaliser.qpow D 12 ≈
      RingNormaliser.qpow D 6 * RingNormaliser.qpow D 6 := by
    simpa only using RingNormaliser.qpow_add D 6 6
  have hcoef :
      Q'.ofNat 14 * (Q'.ofNat 720 * Q'.ofNat 720) ≈
        Q'.ofNat 7257600 := by
    decide
  refine Q'.eqv_trans _
    ((Q'.ofNat 14 * d4) * RingNormaliser.qpow D1 11 *
      ((((Q'.ofNat 720 * RingNormaliser.qpow D 6) * old) *
        ((Q'.ofNat 720 * RingNormaliser.qpow D 6) * old)) * J)) _ ?_ ?_
  · exact mul_congr₂ (Q'.eqv_refl _)
      (mul_congr₂ holdSq hJ)
  refine Q'.eqv_trans _
    (((Q'.ofNat 14 * (Q'.ofNat 720 * Q'.ofNat 720)) * d4) *
      (RingNormaliser.qpow D 6 * RingNormaliser.qpow D 6) *
      RingNormaliser.qpow D1 11 * ((old * old) * J)) _
    (by semantic_ring) ?_
  refine Q'.eqv_trans _
    (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
      RingNormaliser.qpow D1 11 * ((old * old) * J)) _ ?_ ?_
  · exact mul_congr₂
      (mul_congr₂
        (mul_congr₂
          (mul_congr₂ hcoef (Q'.eqv_refl _))
          (Q'.eqv_symm hD12))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  exact Q'.eqv_refl _

theorem qOldPayment_eq_physical (k n : Nat) :
    qOldPayment (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      physicalCommonDen k * physicalOldPayment k n := by
  let D := Q'.ofNat (k + 2)
  let D1 := Q'.ofNat (k + 3)
  let N := Q'.ofNat n
  let dExpr := qsub (RingNormaliser.qpow D 2) (qc 1)
  let d := Q'.ofNat (driftDen k)
  let d4 := RingNormaliser.qpow d 4
  let oldQ := qOldFluxTerm D N
  let old := physicalOldFlux k n
  let Jq := qFlux D (qadd N (qc 1))
  let J := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))
  let common :=
    ((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
      RingNormaliser.qpow D1 11
  have hD1eq : qadd D (qc 1) = D1 := by
    dsimp only [D, D1]
    have h := (ofNat_add_eq_exact (k + 2) 1).symm
    simpa only [qc, show k + 2 + 1 = k + 3 by omega] using h
  have hN1eq : qadd N (qc 1) = Q'.ofNat (n + 1) := by
    dsimp only [N]
    have h := (ofNat_add_eq_exact n 1).symm
    simpa only [qc] using h
  have hd : dExpr ≈ d := by
    dsimp only [dExpr, D, d]
    exact qHarmonicDriftDen_eqv k
  have hd4 := RingNormaliser.qpow_eqv_congr hd 4
  have hD1pow : RingNormaliser.qpow (qadd D (qc 1)) 11 ≈
      RingNormaliser.qpow D1 11 := by
    rw [hD1eq]
    exact Q'.eqv_refl _
  let Tq := qSlopeScaled D N
  let T := rootSlopeTaylor6 (harmU k) n
  let S := Q'.ofNat 720 * RingNormaliser.qpow D 6
  have hT : Tq ≈ S * T := by
    dsimp only [Tq, T, S, D, N]
    exact qSlopeScaled_eq_physical n k
  have hfirst :
      (Q'.ofNat 720 * N) * RingNormaliser.qpow D 6 ≈ S * N := by
    dsimp only [S]
    semantic_ring
  have holdQ : oldQ ≈ S * old := by
    have hraw := add_congr₂ hfirst (Q'.neg_eqv_congr _ _ hT)
    refine Q'.eqv_trans _ _ _ hraw ?_
    dsimp only [old, physicalOldFlux]
    exact scaled_sub S N T
  have hJ : Jq ≈ J := by
    dsimp only [Jq, J]
    rw [hN1eq]
    exact qFlux_eq_physical D (Q'.ofNat (n + 1))
  have houter :
      ((Q'.ofNat 14 * RingNormaliser.qpow dExpr 4) *
          RingNormaliser.qpow (qadd D (qc 1)) 11) *
          (RingNormaliser.qpow oldQ 2 * Jq) ≈
        ((Q'.ofNat 14 * d4) * RingNormaliser.qpow D1 11) *
          (RingNormaliser.qpow oldQ 2 * Jq) :=
    mul_congr₂
      (mul_congr₂
        (mul_congr₂ (Q'.eqv_refl _) hd4) hD1pow)
      (Q'.eqv_refl _)
  have hfactor := old_payment_factor d4 D D1 oldQ old Jq J holdQ hJ
  change
    ((Q'.ofNat 14 * RingNormaliser.qpow dExpr 4) *
        RingNormaliser.qpow (qadd D (qc 1)) 11) *
        (RingNormaliser.qpow oldQ 2 * Jq) ≈
      common * physicalOldPayment k n
  refine Q'.eqv_trans _ _ _ houter ?_
  dsimp only [common]
  change
    ((Q'.ofNat 14 * d4) * RingNormaliser.qpow D1 11) *
        (RingNormaliser.qpow oldQ 2 * Jq) ≈
      (((Q'.ofNat 7257600 * d4) * RingNormaliser.qpow D 12) *
        RingNormaliser.qpow D1 11) * ((old * old) * J)
  exact hfactor

private theorem qASquare_eq_physical (n : Nat) :
    RingNormaliser.qpow (qadd (Q'.ofNat n) (qc 1)) 2 ≈
      Q'.ofNat (n + 1) * Q'.ofNat (n + 1) := by
  have hA : qadd (Q'.ofNat n) (qc 1) = Q'.ofNat (n + 1) := by
    have h := (ofNat_add_eq_exact n 1).symm
    simpa only [qc] using h
  rw [hA]
  exact rnqpow_two_eqv _

private theorem assemble_exact_lower
    {Aq2 mainQ oldQ common A main old : Q'}
    (hA : Aq2 ≈ A * A)
    (hmain : mainQ ≈ common * main)
    (hold : oldQ ≈ common * old) :
    Aq2 * mainQ + -oldQ ≈
      common * ((A * A) * main + -old) := by
  refine Q'.eqv_trans _
    ((A * A) * (common * main) + -(common * old)) _ ?_ ?_
  · exact add_congr₂ (mul_congr₂ hA hmain)
      (Q'.neg_eqv_congr _ _ hold)
  semantic_ring

theorem qExactLowerNumerator_eq_physical (k n : Nat) :
    qExactLowerNumerator (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      physicalCommonDen k *
        lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let A := Q'.ofNat (n + 1)
  let Aq := qadd N (qc 1)
  let Aq2 := RingNormaliser.qpow Aq 2
  let mainQ := qMainTerm D N
  let oldQ := qOldPayment D N
  let common := physicalCommonDen k
  let main := physicalMain k n
  let old := physicalOldPayment k n
  have hA : Aq2 ≈ A * A := by
    dsimp only [Aq2, Aq, A, N]
    exact qASquare_eq_physical n
  have hmain : mainQ ≈ common * main := by
    dsimp only [mainQ, common, main, D, N]
    exact qMainTerm_eq_physical k n
  have hold : oldQ ≈ common * old := by
    dsimp only [oldQ, common, old, D, N]
    exact qOldPayment_eq_physical k n
  have hfinal := assemble_exact_lower hA hmain hold
  have hphysical : physicalExactLower k n =
      lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n :=
    physicalExactLower_eq k n
  change Aq2 * mainQ + -oldQ ≈
    common * lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n
  exact Q'.eqv_trans _ _ _ hfinal
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_of_eq hphysical))

private theorem polyEval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb => exact mul_congr₂ iha ihb
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem qExactLowerNumerator_congr
    {D D' N N' : Q'} (hD : D ≈ D') (hN : N ≈ N') :
    qExactLowerNumerator D N ≈ qExactLowerNumerator D' N' := by
  rw [← eval_pGeneric_eq D N, ← eval_pGeneric_eq D' N']
  apply polyEval_eqv_congr
  intro i
  unfold genericEnvironment
  by_cases hi0 : i = 0
  · rw [if_pos hi0, if_pos hi0]
    exact hD
  · rw [if_neg hi0, if_neg hi0]
    by_cases hi1 : i = 1
    · rw [if_pos hi1, if_pos hi1]
      exact hN
    · rw [if_neg hi1, if_neg hi1]
      exact Q'.eqv_refl _

private theorem eval_pExactLowerLow_eq (X : Q') (n : Nat) :
    RingNormaliser.eval (lowEnvironment X) (pExactLowerLow n) =
      qExactLowerNumerator (qadd (qc 8191) X) (Q'.ofNat n) := by
  rfl

private theorem eval_pExactLowerHigh_eq (M Z : Q') :
    RingNormaliser.eval (highEnvironment M Z) pExactLowerHigh =
      qExactLowerNumerator
        (qadd (qmul (qc 2) (qpow (qadd M (qc 8)) 2)) Z)
        (qadd M (qc 8)) := by
  rfl

private theorem qExactLowerNumerator_nonnegative_low
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ 7) :
    (0 : Q') ≤ qExactLowerNumerator (Q'.ofNat (k + 2)) (Q'.ofNat n) := by
  let xNat := k - 8189
  let X := Q'.ofNat xNat
  have hX : (0 : Q') ≤ X := by
    dsimp only [X]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hcert := pExactLowerLow_eval_nonnegative hn X hX
  rw [eval_pExactLowerLow_eq] at hcert
  have hNat : 8191 + xNat = k + 2 := by
    dsimp only [xNat]
    omega
  have hD : qadd (qc 8191) X = Q'.ofNat (k + 2) := by
    have hadd := (ofNat_add_eq_exact 8191 xNat).symm
    rw [hNat] at hadd
    simpa only [qc, X] using hadd
  have hnum :
      qExactLowerNumerator (qadd (qc 8191) X) (Q'.ofNat n) ≈
        qExactLowerNumerator (Q'.ofNat (k + 2)) (Q'.ofNat n) :=
    qExactLowerNumerator_congr (Q'.eqv_of_eq hD) (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ hcert (Q'.le_of_eqv hnum)

private theorem thetaWindowLeft_two_sq_le_den_local
    {k n : Nat} (hn : n ≤ thetaWindowLeft k) :
    2 * (n * n) ≤ k + 2 := by
  let c := thetaWindowCenter k
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have hsquare : (2 * n) * (2 * n) ≤ c * c :=
    Nat.mul_le_mul h2n h2n
  have hcSq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hfour : 4 * (n * n) ≤ 2 * (k + 2) + 1 := by
    have heq : 4 * (n * n) = (2 * n) * (2 * n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_trans hsquare hcSq
  omega

private theorem qExactLowerNumerator_nonnegative_high
    {k n : Nat} (hn8 : 8 ≤ n) (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ qExactLowerNumerator (Q'.ofNat (k + 2)) (Q'.ofNat n) := by
  let mNat := n - 8
  let zNat := k + 2 - 2 * (n * n)
  let M := Q'.ofNat mNat
  let Z := Q'.ofNat zNat
  have hM : (0 : Q') ≤ M := by
    dsimp only [M]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hZ : (0 : Q') ≤ Z := by
    dsimp only [Z]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hcert := pExactLowerHigh_eval_nonnegative M Z hM hZ
  rw [eval_pExactLowerHigh_eq] at hcert
  have hNnat : mNat + 8 = n := by
    dsimp only [mNat]
    omega
  have hN : qadd M (qc 8) = Q'.ofNat n := by
    have hadd := (ofNat_add_eq_exact mNat 8).symm
    rw [hNnat] at hadd
    simpa only [M, qc] using hadd
  have hN2 : qpow (qadd M (qc 8)) 2 ≈ Q'.ofNat (n * n) := by
    refine Q'.eqv_trans _ (qpow (Q'.ofNat n) 2) _
      (RingNormaliser.qpow_eqv_congr (Q'.eqv_of_eq hN) 2) ?_
    exact Q'.eqv_trans _ (Q'.ofNat n * Q'.ofNat n) _
      (rnqpow_two_eqv _) (HeatKernelRGStep.ofNat_mul_eqv n n)
  have htwo :
      qmul (qc 2) (qpow (qadd M (qc 8)) 2) ≈
        Q'.ofNat (2 * (n * n)) := by
    change Q'.ofNat 2 * RingNormaliser.qpow (qadd M (qc 8)) 2 ≈
      Q'.ofNat (2 * (n * n))
    exact Q'.eqv_trans _ (Q'.ofNat 2 * Q'.ofNat (n * n)) _
      (Q'.mul_eqv_congr_left _ _ _ hN2)
      (HeatKernelRGStep.ofNat_mul_eqv 2 (n * n))
  have hden : 2 * (n * n) ≤ k + 2 :=
    thetaWindowLeft_two_sq_le_den_local hn
  have hNat : 2 * (n * n) + zNat = k + 2 := by
    dsimp only [zNat]
    omega
  have hD :
      qadd (qmul (qc 2) (qpow (qadd M (qc 8)) 2)) Z ≈
        Q'.ofNat (k + 2) := by
    refine Q'.eqv_trans _
      (qadd (Q'.ofNat (2 * (n * n))) (Q'.ofNat zNat)) _
      (add_congr₂ htwo (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ (Q'.ofNat (2 * (n * n) + zNat)) _
      (Q'.eqv_of_eq (ofNat_add_eq_exact (2 * (n * n)) zNat).symm) ?_
    exact Q'.eqv_of_eq (congrArg Q'.ofNat hNat)
  have hnum := qExactLowerNumerator_congr hD (Q'.eqv_of_eq hN)
  exact Q'.le_trans' _ _ _ hcert (Q'.le_of_eqv hnum)

private theorem ofNat_pos_of_pos {a : Nat} (ha : 0 < a) :
    (0 : Q') < Q'.ofNat a := by
  cases a with
  | zero => omega
  | succ a => exact Q'.ofNat_succ_pos a

private theorem rnqpow_pos_local (x : Q') (hx : (0 : Q') < x) : ∀ n,
    (0 : Q') < RingNormaliser.qpow x n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n + 1 => Q'.mul_pos (rnqpow_pos_local x hx n) hx

private theorem physicalCommonDen_pos (k : Nat) :
    (0 : Q') < physicalCommonDen k := by
  have hD : (0 : Q') < Q'.ofNat (k + 2) := by
    have h := Q'.ofNat_succ_pos (k + 1)
    simpa only [show k + 1 + 1 = k + 2 by omega] using h
  have hD1 : (0 : Q') < Q'.ofNat (k + 3) := by
    have h := Q'.ofNat_succ_pos (k + 2)
    simpa only [show k + 2 + 1 = k + 3 by omega] using h
  unfold physicalCommonDen
  exact Q'.mul_pos
    (Q'.mul_pos
      (Q'.mul_pos
        (Q'.ofNat_succ_pos 7257599)
        (rnqpow_pos_local _ (ofNat_pos_of_pos (driftDen_pos k)) 4))
      (rnqpow_pos_local _ hD 12))
    (rnqpow_pos_local _ hD1 11)

private theorem qExactLowerNumerator_nonnegative
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ qExactLowerNumerator (Q'.ofNat (k + 2)) (Q'.ofNat n) := by
  by_cases hn7 : n ≤ 7
  · exact qExactLowerNumerator_nonnegative_low hk hn7
  · exact qExactLowerNumerator_nonnegative_high (by omega) hn

theorem lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_nonnegative_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤
      lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n := by
  have hnum := qExactLowerNumerator_nonnegative hk hn
  have hsemantic := qExactLowerNumerator_eq_physical k n
  have hproduct : (0 : Q') ≤
      physicalCommonDen k *
        lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n :=
    Q'.le_trans' _ _ _ hnum (Q'.le_of_eqv hsemantic)
  exact Q'.nonneg_of_mul_pos (physicalCommonDen_pos k) hproduct

theorem lowerSixDiscreteHermiteRemainder_nonnegative_exact_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ lowerSixDiscreteHermiteRemainder k n :=
  lowerSixDiscreteHermiteRemainder_nonnegative_of_Taylor6ExactErrorLower
    hk hn
      (lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_nonnegative_large
        hk hn)

#print axioms eval_pGeneric_eq
#print axioms qFlux_eq_physical
#print axioms qTaylorScaled_eq_physical
#print axioms qSlopeScaled_eq_physical
#print axioms qDriftFactorScaled_eq_physical
#print axioms qInnerOldScaled_eq_physical
#print axioms qInnerNextScaled_eq_physical
#print axioms qCarrierScaled_eq_physical
#print axioms qCommonDen_eq_physical
#print axioms qMainTerm_eq_physical
#print axioms qOldPayment_eq_physical
#print axioms qExactLowerNumerator_eq_physical
#print axioms lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_nonnegative_large
#print axioms lowerSixDiscreteHermiteRemainder_nonnegative_exact_large

end YMGap.Continuum.HarmonicLowerSixExactCertificate
