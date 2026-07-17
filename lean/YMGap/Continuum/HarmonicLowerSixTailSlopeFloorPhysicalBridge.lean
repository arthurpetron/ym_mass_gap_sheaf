import YMGap.Continuum.HarmonicLowerSixTailSlopeReduction
import YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
import YMGap.RG.PolylogTail

namespace YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.RG
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.HarmonicLowerSixExactCertificate
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem test_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "test_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               test_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_add, Int.natCast_one,
               Int.natCast_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

def octicCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => octicCoeff m + septicCoeff m

def nonicCoeff : Nat → Nat
  | 0 => 0
  | m + 1 => nonicCoeff m + octicCoeff m

private def tailPow8 (u : Q') : Q' :=
  u * (u * (u * (u * (u * (u * (u * u))))))

private def tailPow9 (u : Q') : Q' := u * tailPow8 u

private def tailPow10 (u : Q') : Q' := u * tailPow9 u

def oneSubTaylor8 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor7 u m + Q'.ofNat (octicCoeff m) * tailPow8 u

def oneSubTaylor9 (u : Q') (m : Nat) : Q' :=
  oneSubTaylor8 u m + -(Q'.ofNat (nonicCoeff m) * tailPow9 u)

def lowerSixTailOldPowerUpper (k n : Nat) : Q' :=
  oneSubTaylor8 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)

def lowerSixTailOldPowerLower (k n : Nat) : Q' :=
  oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)

def lowerSixTailNextPowerUpper (k n : Nat) : Q' :=
  oneSubTaylor8 (HarmonicCutoffBoundary.harmU (k + 1)) (2 * n + 1)

def lowerSixTailNextSlopeFloor (k n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * lowerSixTailNextPowerUpper k n)

private theorem oneSubTaylor8_step (u : Q') (m : Nat) :
    oneSubTaylor8 u m * ((1 : Q') + -u) ≈
      oneSubTaylor8 u (m + 1) +
        -(Q'.ofNat (octicCoeff m) * tailPow9 u) := by
  let T := oneSubTaylor7 u m
  let Tnext := oneSubTaylor7 u (m + 1)
  let S := Q'.ofNat (septicCoeff m)
  let O := Q'.ofNat (octicCoeff m)
  let P8 := tailPow8 u
  let P9 := tailPow9 u
  let r := (1 : Q') + -u
  have hseven : T * r ≈ Tnext + S * P8 := by
    dsimp only [T, Tnext, S, P8, r]
    exact oneSubTaylor7_step_eqv u m
  have hoctic : Q'.ofNat (octicCoeff (m + 1)) ≈ O + S := by
    rw [octicCoeff]
    dsimp only [O, S]
    exact Q'.ofNat_add_eqv _ _
  have hnext : oneSubTaylor8 u (m + 1) ≈
      Tnext + (O + S) * P8 := by
    unfold oneSubTaylor8
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ P8 hoctic)
  have hdistribute : (T + O * P8) * r ≈
      T * r + (O * P8) * r := by
    test_ring
  have hreplace : T * r + (O * P8) * r ≈
      (Tnext + S * P8) + (O * P8) * r :=
    Q'.add_eqv_congr' hseven (Q'.eqv_refl _)
  have halgebra : (Tnext + S * P8) + (O * P8) * r ≈
      (Tnext + (O + S) * P8) + -(O * P9) := by
    dsimp only [P9, P8, r, tailPow9, tailPow8]
    test_ring
  have htarget : (Tnext + (O + S) * P8) + -(O * P9) ≈
      oneSubTaylor8 u (m + 1) + -(O * P9) :=
    Q'.add_eqv_congr' (Q'.eqv_symm hnext) (Q'.eqv_refl _)
  unfold oneSubTaylor8
  dsimp only [T, Tnext, S, O, P8, P9, r] at hdistribute hreplace halgebra htarget ⊢
  exact Q'.eqv_trans _ _ _ hdistribute
    (Q'.eqv_trans _ _ _ hreplace
      (Q'.eqv_trans _ _ _ halgebra htarget))

private theorem oneSubTaylor9_step (u : Q') (m : Nat) :
    oneSubTaylor9 u m * ((1 : Q') + -u) ≈
      oneSubTaylor9 u (m + 1) +
        Q'.ofNat (nonicCoeff m) * tailPow10 u := by
  let T := oneSubTaylor8 u m
  let Tnext := oneSubTaylor8 u (m + 1)
  let O := Q'.ofNat (octicCoeff m)
  let N := Q'.ofNat (nonicCoeff m)
  let P9 := tailPow9 u
  let P10 := tailPow10 u
  let r := (1 : Q') + -u
  have height : T * r ≈ Tnext + -(O * P9) := by
    dsimp only [T, Tnext, O, P9, r]
    exact oneSubTaylor8_step u m
  have hnonic : Q'.ofNat (nonicCoeff (m + 1)) ≈ N + O := by
    rw [nonicCoeff]
    dsimp only [N, O]
    exact Q'.ofNat_add_eqv _ _
  have hnext : oneSubTaylor9 u (m + 1) ≈
      Tnext + -((N + O) * P9) := by
    unfold oneSubTaylor9
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ P9 hnonic))
  have hdistribute : (T + -(N * P9)) * r ≈
      T * r + (-(N * P9)) * r := by
    test_ring
  have hreplace : T * r + (-(N * P9)) * r ≈
      (Tnext + -(O * P9)) + (-(N * P9)) * r :=
    Q'.add_eqv_congr' height (Q'.eqv_refl _)
  have halgebra :
      (Tnext + -(O * P9)) + (-(N * P9)) * r ≈
        (Tnext + -((N + O) * P9)) + N * P10 := by
    dsimp only [P10, P9, r, tailPow10, tailPow9, tailPow8]
    test_ring
  have htarget : (Tnext + -((N + O) * P9)) + N * P10 ≈
      oneSubTaylor9 u (m + 1) + N * P10 :=
    Q'.add_eqv_congr' (Q'.eqv_symm hnext) (Q'.eqv_refl _)
  unfold oneSubTaylor9
  dsimp only [T, Tnext, O, N, P9, P10, r] at hdistribute hreplace halgebra htarget ⊢
  exact Q'.eqv_trans _ _ _ hdistribute
    (Q'.eqv_trans _ _ _ hreplace
      (Q'.eqv_trans _ _ _ halgebra htarget))

private theorem oneSubTaylor8_zero (u : Q') :
    oneSubTaylor8 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor8 oneSubTaylor7 oneSubTaylor6 oneSubTaylor5
    oneSubTaylor4 oneSubTaylor3 oneSubTaylor2 octicCoeff septicCoeff
    sexticCoeff quinticCoeff quarticCoeff cubicCoeff
    lowerSixQuadraticCoeff
  test_ring

private theorem oneSubTaylor9_zero (u : Q') :
    oneSubTaylor9 u 0 ≈ (1 : Q') := by
  unfold oneSubTaylor9 oneSubTaylor8 oneSubTaylor7 oneSubTaylor6
    oneSubTaylor5 oneSubTaylor4 oneSubTaylor3 oneSubTaylor2 nonicCoeff
    octicCoeff septicCoeff sexticCoeff quinticCoeff quarticCoeff cubicCoeff
    lowerSixQuadraticCoeff
  test_ring

private theorem ninth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ tailPow9 u := by
  unfold tailPow9 tailPow8
  exact
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu
        (Q'.mul_nonneg _ _ hu
          (Q'.mul_nonneg _ _ hu
            (Q'.mul_nonneg _ _ hu
              (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu)))))))

private theorem tenth_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    (0 : Q') ≤ tailPow10 u := by
  unfold tailPow10 tailPow9 tailPow8
  exact
  Q'.mul_nonneg _ _ hu
    (Q'.mul_nonneg _ _ hu
      (Q'.mul_nonneg _ _ hu
        (Q'.mul_nonneg _ _ hu
          (Q'.mul_nonneg _ _ hu
            (Q'.mul_nonneg _ _ hu
              (Q'.mul_nonneg _ _ hu
                (Q'.mul_nonneg _ _ hu (Q'.mul_nonneg _ _ hu hu))))))))

/-- Even alternating truncation: `(1-u)^m ≤ T8`. -/
theorem qpow_oneSub_le_taylor8
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, qpow ((1 : Q') + -u) m ≤ oneSubTaylor8 u m
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (oneSubTaylor8_zero u))
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (octicCoeff m) * tailPow9 u
      have hr0 : (0 : Q') ≤ r := Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (qpow_oneSub_le_taylor8 hu0 hu1 m) hr0
      have hstep := oneSubTaylor8_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (ninth_nonnegative hu0)
      have hnegE : -E ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hE0
      have hdrop := Q'.add_le_add_left (oneSubTaylor8 u (m + 1))
        (-E) (0 : Q') hnegE
      have hzero : oneSubTaylor8 u (m + 1) + (0 : Q') ≈
          oneSubTaylor8 u (m + 1) := QPoly.q_add_zero_eqv _
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
          (Q'.le_trans' _ _ _ hdrop (Q'.le_of_eqv hzero)))

/-- Odd alternating truncation: `T9 ≤ (1-u)^m`. -/
theorem taylor9_le_qpow_oneSub
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    ∀ m, oneSubTaylor9 u m ≤ qpow ((1 : Q') + -u) m
  | 0 => Q'.le_of_eqv (oneSubTaylor9_zero u)
  | m + 1 => by
      let r := (1 : Q') + -u
      let E := Q'.ofNat (nonicCoeff m) * tailPow10 u
      have hr0 : (0 : Q') ≤ r := Q'.sub_nonneg_of_le hu1
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ r
        (taylor9_le_qpow_oneSub hu0 hu1 m) hr0
      have hstep := oneSubTaylor9_step u m
      have hE0 : (0 : Q') ≤ E :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (tenth_nonnegative hu0)
      have hadd := Q'.add_le_self_of_nonneg
        (oneSubTaylor9 u (m + 1)) E hE0
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hstep)) hmul)

private theorem binom_one_test : ∀ m : Nat, binom m 1 = m
  | 0 => rfl
  | m + 1 => by
      rw [binom_succ_succ, binom_zero_right, binom_one_test m]
      exact Nat.add_comm 1 m

private theorem quadraticCoeff_eq_binom : ∀ m : Nat,
    lowerSixQuadraticCoeff m = binom m 2
  | 0 => rfl
  | m + 1 => by
      rw [lowerSixQuadraticCoeff, binom_succ_succ,
        quadraticCoeff_eq_binom m, binom_one_test]
      ac_rfl

private theorem cubicCoeff_eq_binom : ∀ m : Nat,
    cubicCoeff m = binom m 3
  | 0 => rfl
  | m + 1 => by
      rw [cubicCoeff, binom_succ_succ, cubicCoeff_eq_binom m,
        quadraticCoeff_eq_binom]
      ac_rfl

private theorem quarticCoeff_eq_binom : ∀ m : Nat,
    quarticCoeff m = binom m 4
  | 0 => rfl
  | m + 1 => by
      rw [quarticCoeff, binom_succ_succ, quarticCoeff_eq_binom m,
        cubicCoeff_eq_binom]
      ac_rfl

private theorem quinticCoeff_eq_binom : ∀ m : Nat,
    quinticCoeff m = binom m 5
  | 0 => rfl
  | m + 1 => by
      rw [quinticCoeff, binom_succ_succ, quinticCoeff_eq_binom m,
        quarticCoeff_eq_binom]
      ac_rfl

private theorem sexticCoeff_eq_binom : ∀ m : Nat,
    sexticCoeff m = binom m 6
  | 0 => rfl
  | m + 1 => by
      rw [sexticCoeff, binom_succ_succ, sexticCoeff_eq_binom m,
        quinticCoeff_eq_binom]
      ac_rfl

private theorem septicCoeff_eq_binom : ∀ m : Nat,
    septicCoeff m = binom m 7
  | 0 => rfl
  | m + 1 => by
      rw [septicCoeff, binom_succ_succ, septicCoeff_eq_binom m,
        sexticCoeff_eq_binom]
      ac_rfl

private theorem octicCoeff_eq_binom : ∀ m : Nat,
    octicCoeff m = binom m 8
  | 0 => rfl
  | m + 1 => by
      rw [octicCoeff, binom_succ_succ, octicCoeff_eq_binom m,
        septicCoeff_eq_binom]
      ac_rfl

private theorem nonicCoeff_eq_binom : ∀ m : Nat,
    nonicCoeff m = binom m 9
  | 0 => rfl
  | m + 1 => by
      rw [nonicCoeff, binom_succ_succ, nonicCoeff_eq_binom m,
        octicCoeff_eq_binom]
      ac_rfl

#print axioms binom_one_test
#check YMGap.Continuum.ThetaResidualPascalTelescope.choose_adjacent_cross
#check YMGap.Continuum.HarmonicThetaPascalEvaluation.pnChoose_eq_binom
#check YMGap.Continuum.HarmonicLowerSixExactCertificate.qTaylorScaled_eq_physical

private def localCoeff (m : Nat) : Nat → Nat
  | 0 => 1
  | 1 => m
  | 2 => lowerSixQuadraticCoeff m
  | 3 => cubicCoeff m
  | 4 => quarticCoeff m
  | 5 => quinticCoeff m
  | 6 => sexticCoeff m
  | 7 => septicCoeff m
  | 8 => octicCoeff m
  | 9 => nonicCoeff m
  | _ => 0

private def localPower (u : Q') : Nat → Q'
  | 0 => 1
  | 1 => u
  | 2 => u * u
  | 3 => u * (u * u)
  | 4 => u * (u * (u * u))
  | 5 => u * (u * (u * (u * u)))
  | 6 => u * (u * (u * (u * (u * u))))
  | 7 => u * (u * (u * (u * (u * (u * u)))))
  | 8 => u * (u * (u * (u * (u * (u * (u * u))))))
  | 9 => u * (u * (u * (u * (u * (u * (u * (u * u)))))))
  | _ => 0

private def localUnsignedTerm (u : Q') (m j : Nat) : Q' :=
  Q'.ofNat (localCoeff m j) * localPower u j

private def localSignedTerm (u : Q') (m : Nat) : Nat → Q'
  | 0 => localUnsignedTerm u m 0
  | 1 => -(localUnsignedTerm u m 1)
  | 2 => localUnsignedTerm u m 2
  | 3 => -(localUnsignedTerm u m 3)
  | 4 => localUnsignedTerm u m 4
  | 5 => -(localUnsignedTerm u m 5)
  | 6 => localUnsignedTerm u m 6
  | 7 => -(localUnsignedTerm u m 7)
  | 8 => localUnsignedTerm u m 8
  | 9 => -(localUnsignedTerm u m 9)
  | _ => 0

private def localTaylorTrunc (u : Q') (m : Nat) : Nat → Q'
  | 0 => 1
  | 1 => (1 : Q') + -(Q'.ofNat m * u)
  | 2 => oneSubTaylor2 u m
  | 3 => oneSubTaylor3 u m
  | 4 => oneSubTaylor4 u m
  | 5 => oneSubTaylor5 u m
  | 6 => oneSubTaylor6 u m
  | 7 => oneSubTaylor7 u m
  | 8 => oneSubTaylor8 u m
  | 9 => oneSubTaylor9 u m
  | _ => 0

private theorem localTaylorTrunc_step (u : Q') (m j : Nat) (hj : j < 9) :
    localTaylorTrunc u m (j + 1) ≈
      localTaylorTrunc u m j + localSignedTerm u m (j + 1) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold localTaylorTrunc localSignedTerm localUnsignedTerm localPower
      localCoeff oneSubTaylor9
      oneSubTaylor8 oneSubTaylor7 oneSubTaylor6 oneSubTaylor5 oneSubTaylor4
      oneSubTaylor3 oneSubTaylor2 tailPow9 tailPow8 <;>
    exact Q'.eqv_refl _

private theorem localCoeff_eq_choose (m j : Nat) (hj : j ≤ 9) :
    localCoeff m j = PNPaths.choose m j := by
  have hpn (r : Nat) : PNPaths.choose m r = binom m r :=
    pnChoose_eq_binom m r
  rcases j with _ | j
  · simp [localCoeff, PNPaths.choose]
  rcases j with _ | j
  · simp [localCoeff, hpn, binom_one_test]
  rcases j with _ | j
  · simpa [localCoeff, hpn] using quadraticCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using cubicCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using quarticCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using quinticCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using sexticCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using septicCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using octicCoeff_eq_binom m
  rcases j with _ | j
  · simpa [localCoeff, hpn] using nonicCoeff_eq_binom m
  · omega

private def localFact : Nat → Nat
  | 0 => 1
  | j + 1 => (j + 1) * localFact j

private def localFalling (m : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => localFalling m j * (m - j)

private theorem localFact_mul_choose_eq_falling : ∀ j m : Nat, j ≤ m →
    localFact j * PNPaths.choose m j = localFalling m j
  | 0, m, _ => by simp [localFact, localFalling, PNPaths.choose]
  | j + 1, m, hjm => by
      have hjlt : j < m := by omega
      have hadj :=
        YMGap.Continuum.ThetaResidualPascalTelescope.choose_adjacent_cross
          m j hjlt
      have ih := localFact_mul_choose_eq_falling j m (by omega)
      simp only [localFact, localFalling]
      calc
        (j + 1) * localFact j * PNPaths.choose m (j + 1) =
            localFact j * ((j + 1) * PNPaths.choose m (j + 1)) := by ac_rfl
        _ = localFact j * ((m - j) * PNPaths.choose m j) := by rw [hadj]
        _ = (localFact j * PNPaths.choose m j) * (m - j) := by ac_rfl
        _ = localFalling m j * (m - j) := by rw [ih]

private def localFactorialAbs : Nat → Nat
  | 0 => 362880 | 1 => 362880 | 2 => 181440 | 3 => 60480
  | 4 => 15120 | 5 => 3024 | 6 => 504 | 7 => 72 | 8 => 9
  | 9 => 1 | _ => 0

private theorem localFactorial_split (j : Nat) (hj : j ≤ 9) :
    362880 = localFactorialAbs j * localFact j := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem localCoeff_scale (m j : Nat) (hj : j ≤ 9) (hjm : j ≤ m) :
    362880 * localCoeff m j = localFactorialAbs j * localFalling m j := by
  rw [localCoeff_eq_choose m j hj, localFactorial_split j hj]
  calc
    (localFactorialAbs j * localFact j) * PNPaths.choose m j =
        localFactorialAbs j * (localFact j * PNPaths.choose m j) := by ac_rfl
    _ = localFactorialAbs j * localFalling m j := by
      rw [localFact_mul_choose_eq_falling j m hjm]

private theorem ofNat_sub_eqv_local (a b : Nat) (h : b ≤ a) :
    Q'.ofNat a + -(Q'.ofNat b) ≈ Q'.ofNat (a - b) := by
  change (Int.ofNat a * 1 + (-Int.ofNat b) * 1) * 1 =
    Int.ofNat (a - b) * 1
  simp only [Int.mul_one]
  simpa [Int.sub_eq_add_neg] using (Int.ofNat_sub h).symm

private theorem mode_eval_eqv (D : Q') (n : Nat) :
    RingNormaliser.eval
        (tailTaylor9Rho D (Q'.ofNat n)) tailTaylor9ModeExpr ≈
      Q'.ofNat (2 * n + 1) := by
  change Q'.ofInt 2 * Q'.ofNat n + Q'.ofInt 1 ≈
    Q'.ofNat (2 * n + 1)
  have hmul : Q'.ofInt 2 * Q'.ofNat n ≈ Q'.ofNat (2 * n) := by
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 n)
  have hadd : Q'.ofNat (2 * n) + Q'.ofInt 1 ≈
      Q'.ofNat (2 * n + 1) := by
    exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * n) 1)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hmul (Q'.eqv_refl _)) hadd

private theorem falling_eval_eqv (D : Q') (n : Nat) : ∀ j : Nat,
    j ≤ 2 * n + 1 →
      RingNormaliser.eval
          (tailTaylor9Rho D (Q'.ofNat n))
          (tailTaylor9FallingExpr j) ≈
        Q'.ofNat (localFalling (2 * n + 1) j)
  | 0, _ => by
      unfold tailTaylor9FallingExpr localFalling RingNormaliser.eval
      decide
  | j + 1, hj => by
      let rho := tailTaylor9Rho D (Q'.ofNat n)
      let m := 2 * n + 1
      have ih := falling_eval_eqv D n j (by omega)
      have hmode : RingNormaliser.eval rho tailTaylor9ModeExpr ≈
          Q'.ofNat m := by
        dsimp only [rho, m]
        exact mode_eval_eqv D n
      have hneg : RingNormaliser.eval rho (.const (-(Int.ofNat j))) ≈
          -(Q'.ofNat j) := by
        exact Q'.eqv_of_eq rfl
      have hfactor :
          RingNormaliser.eval rho
              (.add tailTaylor9ModeExpr (.const (-(Int.ofNat j)))) ≈
            Q'.ofNat (m - j) := by
        have hadd := Q'.add_eqv_congr' hmode hneg
        exact Q'.eqv_trans _ _ _ hadd (ofNat_sub_eqv_local m j (by omega))
      have hmul :
          RingNormaliser.eval rho (tailTaylor9FallingExpr j) *
              RingNormaliser.eval rho
                (.add tailTaylor9ModeExpr (.const (-(Int.ofNat j)))) ≈
            Q'.ofNat (localFalling m j) * Q'.ofNat (m - j) := by
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ ih)
          (Q'.mul_eqv_congr_left _ _ _ hfactor)
      unfold tailTaylor9FallingExpr RingNormaliser.eval
      dsimp only [rho, m] at hmul ⊢
      exact Q'.eqv_trans _ _ _ hmul
        (Q'.eqv_symm
          (HeatKernelRGStep.ofNat_mul_eqv
            (localFalling (2 * n + 1) j) (2 * n + 1 - j)))

private theorem localCoeff_scale_eqv (D : Q') (n j : Nat)
    (hj : j ≤ 9) (hjm : j ≤ 2 * n + 1) :
    Q'.ofNat 362880 * Q'.ofNat (localCoeff (2 * n + 1) j) ≈
      Q'.ofNat (localFactorialAbs j) *
        RingNormaliser.eval
          (tailTaylor9Rho D (Q'.ofNat n))
          (tailTaylor9FallingExpr j) := by
  have hscale := localCoeff_scale (2 * n + 1) j hj hjm
  have hleft :
      Q'.ofNat 362880 * Q'.ofNat (localCoeff (2 * n + 1) j) ≈
        Q'.ofNat (362880 * localCoeff (2 * n + 1) j) :=
    Q'.eqv_symm
      (HeatKernelRGStep.ofNat_mul_eqv 362880
        (localCoeff (2 * n + 1) j))
  rw [hscale] at hleft
  have hsplit :
      Q'.ofNat (localFactorialAbs j * localFalling (2 * n + 1) j) ≈
        Q'.ofNat (localFactorialAbs j) *
          Q'.ofNat (localFalling (2 * n + 1) j) :=
    HeatKernelRGStep.ofNat_mul_eqv _ _
  have hfall := falling_eval_eqv D n j hjm
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hfall)))

private theorem rnqpow_mul_base_test (a b : Q') : ∀ r,
    RingNormaliser.qpow (a * b) r ≈
      RingNormaliser.qpow a r * RingNormaliser.qpow b r
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | r + 1 => by
      show RingNormaliser.qpow (a * b) r * (a * b) ≈
        (RingNormaliser.qpow a r * a) * (RingNormaliser.qpow b r * b)
      refine Q'.eqv_trans _
        ((RingNormaliser.qpow a r * RingNormaliser.qpow b r) * (a * b)) _
        (Q'.mul_eqv_congr_right _ _ _ (rnqpow_mul_base_test a b r)) ?_
      test_ring

private theorem rnqpow_one_test : ∀ r,
    RingNormaliser.qpow (1 : Q') r ≈ (1 : Q')
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      show RingNormaliser.qpow (1 : Q') r * 1 ≈ 1
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_right _ _ _ (rnqpow_one_test r))
        (Q'.one_mul_eqv 1)

private theorem rnqpow_cancel_test {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (a r : Nat) :
    RingNormaliser.qpow D (a + r) * RingNormaliser.qpow u r ≈
      RingNormaliser.qpow D a := by
  have hsplit := RingNormaliser.qpow_add D a r
  have hprod :
      RingNormaliser.qpow D r * RingNormaliser.qpow u r ≈ (1 : Q') :=
    Q'.eqv_trans _ (RingNormaliser.qpow (D * u) r) _
      (Q'.eqv_symm (rnqpow_mul_base_test D u r))
      (Q'.eqv_trans _ (RingNormaliser.qpow (1 : Q') r) _
        (RingNormaliser.qpow_eqv_congr hDu r) (rnqpow_one_test r))
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

private theorem scale_monomial_eqv {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (j : Nat) (hj : j ≤ 9) :
    RingNormaliser.qpow D 9 * RingNormaliser.qpow u j ≈
      RingNormaliser.qpow D (9 - j) := by
  have h := rnqpow_cancel_test hDu (9 - j) j
  have hsum : 9 - j + j = 9 := Nat.sub_add_cancel hj
  rw [hsum] at h
  exact h

private theorem localPower_eqv_qpow (u : Q') (j : Nat) (hj : j ≤ 9) :
    localPower u j ≈ RingNormaliser.qpow u j := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [localPower, RingNormaliser.qpow]
  · exact Q'.eqv_refl _
  · exact Q'.eqv_symm (Q'.one_mul_eqv u)
  · exact Q'.mul_eqv_congr_right _ _ u
      (Q'.eqv_symm (Q'.one_mul_eqv u))
  all_goals test_ring

private def certificateUnsignedTerm (D : Q') (n j : Nat) : Q' :=
  Q'.ofNat (localFactorialAbs j) *
    (RingNormaliser.eval
        (tailTaylor9Rho D (Q'.ofNat n))
        (tailTaylor9FallingExpr j) *
      RingNormaliser.qpow D (9 - j))

private theorem unsigned_term_bridge {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n j : Nat)
    (hj : j ≤ 9) (hjm : j ≤ 2 * n + 1) :
    certificateUnsignedTerm D n j ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        localUnsignedTerm u (2 * n + 1) j := by
  let F := RingNormaliser.eval
    (tailTaylor9Rho D (Q'.ofNat n)) (tailTaylor9FallingExpr j)
  let A := Q'.ofNat (localFactorialAbs j)
  let C := Q'.ofNat (localCoeff (2 * n + 1) j)
  let P := localPower u j
  let S := Q'.ofNat 362880
  let D9 := RingNormaliser.qpow D 9
  let Da := RingNormaliser.qpow D (9 - j)
  have hcoeff : S * C ≈ A * F := by
    dsimp only [S, C, A, F]
    exact localCoeff_scale_eqv D n j hj hjm
  have hpower : D9 * P ≈ Da := by
    have hp := localPower_eqv_qpow u j hj
    have hreplace : D9 * P ≈
        D9 * RingNormaliser.qpow u j :=
      Q'.mul_eqv_congr_left D9 _ _ hp
    exact Q'.eqv_trans _ _ _ hreplace
      (scale_monomial_eqv hDu j hj)
  have hregroupL : A * (F * Da) ≈ (A * F) * Da := by
    test_ring
  have hreplaceCoeff : (A * F) * Da ≈ (S * C) * Da :=
    Q'.mul_eqv_congr_right _ _ Da (Q'.eqv_symm hcoeff)
  have hreplacePower : (S * C) * Da ≈ (S * C) * (D9 * P) :=
    Q'.mul_eqv_congr_left (S * C) _ _ (Q'.eqv_symm hpower)
  have hregroupR : (S * C) * (D9 * P) ≈ (S * D9) * (C * P) := by
    test_ring
  unfold certificateUnsignedTerm localUnsignedTerm
  change A * (F * Da) ≈ (S * D9) * (C * P)
  exact Q'.eqv_trans _ _ _ hregroupL
    (Q'.eqv_trans _ _ _ hreplaceCoeff
      (Q'.eqv_trans _ _ _ hreplacePower hregroupR))

private theorem ofInt_nat_mul_eqv (a : Nat) (X : Q') :
    Q'.ofInt (Int.ofNat a) * X ≈ Q'.ofNat a * X :=
  Q'.mul_eqv_congr_right _ _ X (Q'.eqv_of_eq rfl)

private theorem ofInt_negNat_mul_eqv (a : Nat) (X : Q') :
    Q'.ofInt (-(Int.ofNat a)) * X ≈ -(Q'.ofNat a * X) := by
  exact Q'.eqv_trans _ (-(Q'.ofNat a) * X) _
    (Q'.mul_eqv_congr_right _ _ X (Q'.eqv_of_eq rfl))
    (Q'.neg_mul_eqv (Q'.ofNat a) X)

private theorem factorialTerm_bridge {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n j : Nat)
    (hj : j ≤ 9) (hjm : j ≤ 2 * n + 1) :
    RingNormaliser.eval
        (tailTaylor9Rho D (Q'.ofNat n))
        (tailTaylor9FactorialTerm j) ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        localSignedTerm u (2 * n + 1) j := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hu := unsigned_term_bridge hDu n 0 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 0) ≈
          certificateUnsignedTerm D n 0 := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_nat_mul_eqv 362880
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 0) * RingNormaliser.qpow D 9))
    simpa [localSignedTerm] using Q'.eqv_trans _ _ _ hc hu
  · have hu := unsigned_term_bridge hDu n 1 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 1) ≈
          -(certificateUnsignedTerm D n 1) := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_negNat_mul_eqv 362880
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 1) * RingNormaliser.qpow D 8))
    have hneg := Q'.neg_eqv_congr _ _ hu
    have hphase :
        -((Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
            localUnsignedTerm u (2 * n + 1) 1) ≈
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
            (-(localUnsignedTerm u (2 * n + 1) 1)) :=
      Q'.eqv_symm
        (Q'.mul_neg_eqv
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
          (localUnsignedTerm u (2 * n + 1) 1))
    simpa [localSignedTerm] using
      Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hneg hphase)
  · have hu := unsigned_term_bridge hDu n 2 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 2) ≈
          certificateUnsignedTerm D n 2 := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_nat_mul_eqv 181440
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 2) * RingNormaliser.qpow D 7))
    simpa [localSignedTerm] using Q'.eqv_trans _ _ _ hc hu
  · have hu := unsigned_term_bridge hDu n 3 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 3) ≈
          -(certificateUnsignedTerm D n 3) := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_negNat_mul_eqv 60480
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 3) * RingNormaliser.qpow D 6))
    have hneg := Q'.neg_eqv_congr _ _ hu
    have hphase := Q'.eqv_symm
      (Q'.mul_neg_eqv
        (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
        (localUnsignedTerm u (2 * n + 1) 3))
    simpa [localSignedTerm] using
      Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hneg hphase)
  · have hu := unsigned_term_bridge hDu n 4 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 4) ≈
          certificateUnsignedTerm D n 4 := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_nat_mul_eqv 15120
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 4) * RingNormaliser.qpow D 5))
    simpa [localSignedTerm] using Q'.eqv_trans _ _ _ hc hu
  · have hu := unsigned_term_bridge hDu n 5 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 5) ≈
          -(certificateUnsignedTerm D n 5) := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_negNat_mul_eqv 3024
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 5) * RingNormaliser.qpow D 4))
    have hneg := Q'.neg_eqv_congr _ _ hu
    have hphase := Q'.eqv_symm
      (Q'.mul_neg_eqv
        (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
        (localUnsignedTerm u (2 * n + 1) 5))
    simpa [localSignedTerm] using
      Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hneg hphase)
  · have hu := unsigned_term_bridge hDu n 6 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 6) ≈
          certificateUnsignedTerm D n 6 := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_nat_mul_eqv 504
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 6) * RingNormaliser.qpow D 3))
    simpa [localSignedTerm] using Q'.eqv_trans _ _ _ hc hu
  · have hu := unsigned_term_bridge hDu n 7 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 7) ≈
          -(certificateUnsignedTerm D n 7) := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_negNat_mul_eqv 72
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 7) * RingNormaliser.qpow D 2))
    have hneg := Q'.neg_eqv_congr _ _ hu
    have hphase := Q'.eqv_symm
      (Q'.mul_neg_eqv
        (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
        (localUnsignedTerm u (2 * n + 1) 7))
    simpa [localSignedTerm] using
      Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hneg hphase)
  · have hu := unsigned_term_bridge hDu n 8 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 8) ≈
          certificateUnsignedTerm D n 8 := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_nat_mul_eqv 9
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 8) * RingNormaliser.qpow D 1))
    simpa [localSignedTerm] using Q'.eqv_trans _ _ _ hc hu
  · have hu := unsigned_term_bridge hDu n 9 (by omega) (by omega)
    have hc :
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm 9) ≈
          -(certificateUnsignedTerm D n 9) := by
      simpa [tailTaylor9FactorialTerm, tailTaylor9FactorialCoefficient,
        certificateUnsignedTerm, RingNormaliser.eval] using
        (ofInt_negNat_mul_eqv 1
          (RingNormaliser.eval
              (tailTaylor9Rho D (Q'.ofNat n))
              (tailTaylor9FallingExpr 9) * RingNormaliser.qpow D 0))
    have hneg := Q'.neg_eqv_congr _ _ hu
    have hphase := Q'.eqv_symm
      (Q'.mul_neg_eqv
        (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
        (localUnsignedTerm u (2 * n + 1) 9))
    simpa [localSignedTerm] using
      Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hneg hphase)

/-- Factorial-scaled alternating Taylor prefix used by the exact eighth- and
ninth-order physical bridges. -/
def tailTaylor9Prefix : Nat → RingNormaliser.PolyExpr
  | 0 => tailTaylor9FactorialTerm 0
  | j + 1 =>
      .add (tailTaylor9Prefix j) (tailTaylor9FactorialTerm (j + 1))

private theorem factorialPrefix_bridge {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n j : Nat)
    (hj : j ≤ 9) (hjm : j ≤ 2 * n + 1) :
    RingNormaliser.eval
        (tailTaylor9Rho D (Q'.ofNat n))
        (tailTaylor9Prefix j) ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        localTaylorTrunc u (2 * n + 1) j := by
  induction j with
  | zero =>
      have hterm := factorialTerm_bridge hDu n 0 (by omega) (by omega)
      have hzero :
          localSignedTerm u (2 * n + 1) 0 ≈
            localTaylorTrunc u (2 * n + 1) 0 := by
        unfold localSignedTerm localUnsignedTerm localCoeff localPower
          localTaylorTrunc
        exact Q'.mul_one_eqv (Q'.ofNat 1)
      exact Q'.eqv_trans _ _ _ hterm
        (Q'.mul_eqv_congr_left
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) _ _ hzero)
  | succ j ih =>
      have hjlt : j < 9 := by omega
      have hprefix := ih (by omega) (by omega)
      have hterm := factorialTerm_bridge hDu n (j + 1) (by omega) (by omega)
      have hadd := Q'.add_eqv_congr' hprefix hterm
      have hfactor :
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
                localTaylorTrunc u (2 * n + 1) j +
              (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
                localSignedTerm u (2 * n + 1) (j + 1) ≈
            (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
              (localTaylorTrunc u (2 * n + 1) j +
                localSignedTerm u (2 * n + 1) (j + 1)) :=
        Q'.eqv_symm
          (Q'.mul_add_eqv
            (Q'.ofNat 362880 * RingNormaliser.qpow D 9)
            (localTaylorTrunc u (2 * n + 1) j)
            (localSignedTerm u (2 * n + 1) (j + 1)))
      have hstep := localTaylorTrunc_step u (2 * n + 1) j hjlt
      have hreplace :
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
              (localTaylorTrunc u (2 * n + 1) j +
                localSignedTerm u (2 * n + 1) (j + 1)) ≈
            (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
              localTaylorTrunc u (2 * n + 1) (j + 1) :=
        Q'.mul_eqv_congr_left
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) _ _
          (Q'.eqv_symm hstep)
      change
        RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9Prefix j) +
          RingNormaliser.eval
            (tailTaylor9Rho D (Q'.ofNat n))
            (tailTaylor9FactorialTerm (j + 1)) ≈
          (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
            localTaylorTrunc u (2 * n + 1) (j + 1)
      exact Q'.eqv_trans _ _ _ hadd
        (Q'.eqv_trans _ _ _ hfactor hreplace)

private theorem tailTaylor9Cleared_prefix_normal :
    CoreBResidualSimplex.fastNormalize tailTaylor9ClearedExpr =
      CoreBResidualSimplex.fastNormalize (tailTaylor9Prefix 9) := by
  rfl

/-- Exact evaluation of the eighth-order factorial prefix at a reciprocal
physical point. -/
theorem tailTaylor8Prefix_physical_bridge {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval
        (tailTaylor9Rho D (Q'.ofNat n))
        (tailTaylor9Prefix 8) ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        oneSubTaylor8 u (2 * n + 1) := by
  have hprefix := factorialPrefix_bridge hDu n 8 (by omega) (by omega)
  simpa [localTaylorTrunc] using hprefix

/-- Exact evaluation of the cleared ninth-order certificate at a reciprocal
physical point. -/
theorem tailTaylor9Cleared_physical_bridge {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (n : Nat) (hn : 4 ≤ n) :
    tailTaylor9Cleared D (Q'.ofNat n) ≈
      (Q'.ofNat 362880 * RingNormaliser.qpow D 9) *
        oneSubTaylor9 u (2 * n + 1) := by
  have hm : 9 ≤ 2 * n + 1 := by omega
  have hpoly :=
    TensorBernsteinHomogeneousCertificate.eval_eqv_of_fastNormalize_eq
      tailTaylor9ClearedExpr (tailTaylor9Prefix 9)
      tailTaylor9Cleared_prefix_normal
      (tailTaylor9Rho D (Q'.ofNat n))
  have hprefix := factorialPrefix_bridge hDu n 9 (by omega) hm
  unfold tailTaylor9Cleared
  exact Q'.eqv_trans _ _ _ hpoly hprefix

private theorem local_harmDen_mul_harmU (k : Nat) :
    Q'.ofNat (k + 2) * HarmonicCutoffBoundary.harmU k ≈ (1 : Q') := by
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (by
      unfold HarmonicCutoffBoundary.harmU SummableInverseSquare.unit
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
        Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
        Int.mul_one, Int.one_mul]
      have h1n : (1 : Q').num = 1 := rfl
      have h1d : ((1 : Q').den : Int) = 1 := rfl
      rw [h1n, h1d, Int.mul_one, Int.one_mul])

theorem tail_harmU_mul_den (k : Nat) :
    HarmonicCutoffBoundary.harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (local_harmDen_mul_harmU k)

private theorem local_rnqpow_pos {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat,
      (0 : Q') < RingNormaliser.qpow value exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 =>
      Q'.mul_pos (local_rnqpow_pos hvalue exponent) hvalue

private theorem lowerSixTailOldPowerLower_explicit_nonnegative_of_le_den
    {k n : Nat} (hk : 390 ≤ k)
    (hleft : HarmonicMovingDeterminantThetaWindow.thetaWindowLeft k + 1 ≤ n)
    (hn : n ≤ k + 2) :
    (0 : Q') ≤ oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1) := by
  have hc : 9 ≤
      HarmonicMovingDeterminantThetaWindow.thetaWindowCenter k :=
    HarmonicMovingDeterminantThetaWindow.thetaWindowCenter_ge_nine (by omega)
  have hn4 : 4 ≤ n := by
    unfold HarmonicMovingDeterminantThetaWindow.thetaWindowLeft at hleft
    omega
  have hD : tailTaylor9ChartBase ≤ k + 2 := by
    unfold tailTaylor9ChartBase
    omega
  have hcert := tailTaylor9Cleared_nonnegative (k + 2) n hD hn
  have hbridge := tailTaylor9Cleared_physical_bridge
    (local_harmDen_mul_harmU k) n hn4
  have hscaled :
      (0 : Q') ≤
        (Q'.ofNat 362880 *
            RingNormaliser.qpow (Q'.ofNat (k + 2)) 9) *
          oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1) :=
    Q'.le_trans' _ _ _ hcert (Q'.le_of_eqv hbridge)
  have hDpos : (0 : Q') < Q'.ofNat (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega]
    exact Q'.ofNat_succ_pos (k + 1)
  have hscalePos :
      (0 : Q') < Q'.ofNat 362880 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 9 :=
    Q'.mul_pos (by decide) (local_rnqpow_pos hDpos 9)
  exact YMGap.Continuum.FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    hscalePos hscaled

/-- On the low-step branch `n ≤ k+2`, the exact ninth-order homogeneous
certificate supplies positivity of the old-power lower enclosure. -/
theorem lowerSixTailOldPowerLower_nonnegative_of_le_den
    {k n : Nat} (hk : 390 ≤ k)
    (hleft : HarmonicMovingDeterminantThetaWindow.thetaWindowLeft k + 1 ≤ n)
    (hn : n ≤ k + 2) :
    (0 : Q') ≤ lowerSixTailOldPowerLower k n := by
  unfold lowerSixTailOldPowerLower
  exact lowerSixTailOldPowerLower_explicit_nonnegative_of_le_den hk hleft hn

private def slopeFloorShift : Nat → RingNormaliser.PolyExpr
  | 0 => .add (.var 0) (.const 1)
  | 1 => .var 1
  | _ => .const 0

private def slopeFloorCertificateScaledExpr : RingNormaliser.PolyExpr :=
  .mul (.const 144)
    (.mul (slopeFloorShift 0) lowerSixTailNextSlopeFloorClearedExpr)

private def slopeFloorPhysicalScaledExpr : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 362880)
      (.mul (.var 1) (.pow (slopeFloorShift 0) 9)))
    (.neg
      (.mul (.add (.var 1) (.const 1))
        (TensorBernsteinHomogeneousCertificate.substitute
          slopeFloorShift (tailTaylor9Prefix 8))))

private theorem slopeFloor_bridge_normal :
    CoreBResidualSimplex.fastNormalize slopeFloorCertificateScaledExpr =
      CoreBResidualSimplex.fastNormalize slopeFloorPhysicalScaledExpr := by
  rfl

theorem slopeFloorCleared_physical_bridge {D u : Q'}
    (hDu : (D + Q'.ofInt 1) * u ≈ (1 : Q'))
    (n : Nat) (hn : 4 ≤ n) :
    Q'.ofNat 144 *
        ((D + Q'.ofInt 1) *
          lowerSixTailNextSlopeFloorCleared D (Q'.ofNat n)) ≈
      (Q'.ofNat 362880 *
          RingNormaliser.qpow (D + Q'.ofInt 1) 9) *
        (Q'.ofNat n +
          -(Q'.ofNat (n + 1) * oneSubTaylor8 u (2 * n + 1))) := by
  let rho : Nat → Q'
    | 0 => D
    | 1 => Q'.ofNat n
    | _ => 0
  let Dp := D + Q'.ofInt 1
  have hpoly :=
    TensorBernsteinHomogeneousCertificate.eval_eqv_of_fastNormalize_eq
      slopeFloorCertificateScaledExpr slopeFloorPhysicalScaledExpr
      slopeFloor_bridge_normal rho
  have hsub :=
    TensorBernsteinHomogeneousCertificate.eval_substitute
      rho slopeFloorShift (tailTaylor9Prefix 8)
  have hrho :
      (fun i => RingNormaliser.eval rho (slopeFloorShift i)) =
        tailTaylor9Rho Dp (Q'.ofNat n) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with _ | i
    · rfl
    rcases i with _ | i
    · rfl
    · rfl
  rw [hrho] at hsub
  have hprefix := factorialPrefix_bridge hDu n 8 (by omega) (by omega)
  have hsubprefix := Q'.eqv_trans _ _ _ hsub hprefix
  have hNplus :
      Q'.ofNat n + Q'.ofInt 1 ≈ Q'.ofNat (n + 1) := by
    simpa using Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
  have hsecond :
      (Q'.ofNat n + Q'.ofInt 1) *
          RingNormaliser.eval rho
            (TensorBernsteinHomogeneousCertificate.substitute
              slopeFloorShift (tailTaylor9Prefix 8)) ≈
        Q'.ofNat (n + 1) *
          ((Q'.ofNat 362880 * RingNormaliser.qpow Dp 9) *
            oneSubTaylor8 u (2 * n + 1)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hNplus)
      (Q'.mul_eqv_congr_left _ _ _ hsubprefix)
  have hphysical :
      RingNormaliser.eval rho slopeFloorPhysicalScaledExpr ≈
        (Q'.ofNat 362880 * RingNormaliser.qpow Dp 9) *
          (Q'.ofNat n +
            -(Q'.ofNat (n + 1) * oneSubTaylor8 u (2 * n + 1))) := by
    have hreplace := Q'.add_eqv_congr'
      (Q'.eqv_refl
        (Q'.ofNat 362880 *
          (Q'.ofNat n * RingNormaliser.qpow Dp 9)))
      (Q'.neg_eqv_congr _ _ hsecond)
    have hshape :
        RingNormaliser.eval rho slopeFloorPhysicalScaledExpr ≈
          Q'.ofNat 362880 *
              (Q'.ofNat n * RingNormaliser.qpow Dp 9) +
            -(Q'.ofNat (n + 1) *
              ((Q'.ofNat 362880 * RingNormaliser.qpow Dp 9) *
                oneSubTaylor8 u (2 * n + 1))) := by
      simpa [slopeFloorPhysicalScaledExpr, rho, Dp,
        slopeFloorShift, RingNormaliser.eval] using hreplace
    exact Q'.eqv_trans _ _ _ hshape (by test_ring)
  have hfull := Q'.eqv_trans _ _ _ hpoly hphysical
  dsimp only [Dp] at hfull ⊢
  simpa [slopeFloorCertificateScaledExpr, slopeFloorShift,
    lowerSixTailNextSlopeFloorCleared, rho, RingNormaliser.eval] using hfull

private theorem lowerSixTailNextSlopeFloor_explicit_nonnegative
    {k n : Nat} (hk : 390 ≤ k)
    (hleft : HarmonicMovingDeterminantThetaWindow.thetaWindowLeft k + 1 ≤ n)
    (hnright : n ≤ HarmonicGrowingAnchorPF2.growingAnchor k) :
    (0 : Q') ≤
      Q'.ofNat n +
        -(Q'.ofNat (n + 1) *
          oneSubTaylor8 (HarmonicCutoffBoundary.harmU (k + 1))
            (2 * n + 1)) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  have hc : 2 * tailEnvelopeModeChartBase ≤
      HarmonicMovingDeterminantThetaWindow.thetaWindowCenter k := by
    unfold HarmonicMovingDeterminantThetaWindow.thetaWindowCenter
      HarmonicMovingDeterminantThetaWindow.thetaWindowLength
    apply ChebOrthoMidpointEst.isqrt_ge
    unfold tailEnvelopeModeChartBase
    omega
  have h64Nat : tailEnvelopeModeChartBase ≤ n := by
    unfold HarmonicMovingDeterminantThetaWindow.thetaWindowLeft at hleft
    omega
  have hn4 : 4 ≤ n := by
    unfold tailEnvelopeModeChartBase at h64Nat
    omega
  have hNpos : (0 : Q') < N := by
    dsimp only [N]
    rw [show n = (n - 1) + 1 by omega]
    exact Q'.ofNat_succ_pos (n - 1)
  have h64 : Q'.ofNat tailEnvelopeModeChartBase ≤ N := by
    dsimp only [N]
    exact CReal.ofNat_le_ofNat h64Nat
  have hsq : Q'.ofNat (n * n) ≈ N * N := by
    dsimp only [N]
    exact HeatKernelRGStep.ofNat_mul_eqv n n
  have hdenNat : k + 2 ≤ 2 * (n * n) :=
    HarmonicLowerSixTailCorridor.lowerSixTail_den_le_two_sq_of_left_succ_le
      hleft
  have htwoSq :
      Q'.ofNat (2 * (n * n)) ≈ Q'.ofNat 2 * (N * N) := by
    exact Q'.eqv_trans _ _ _
      (HeatKernelRGStep.ofNat_mul_eqv 2 (n * n))
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hsq)
  have hD2N2 : D ≤ Q'.ofNat 2 * (N * N) := by
    exact Q'.le_trans' _ _ _
      (by
        dsimp only [D]
        exact CReal.ofNat_le_ofNat hdenNat)
      (Q'.le_of_eqv htwoSq)
  have hcert :
      (0 : Q') ≤ lowerSixTailNextSlopeFloorCleared D N := by
    by_cases hN2DNat : n * n ≤ k + 2
    · have hN2D : N * N ≤ D :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
          (by
            dsimp only [D]
            exact CReal.ofNat_le_ofNat hN2DNat)
      exact lowerSixTailNextSlopeFloorCleared_nonnegative_chartA
        hNpos h64 hN2D hD2N2
    · have hDN2Nat : k + 2 ≤ n * n := by omega
      have h91Nat : tailEnvelopeModeChartBase ≤ n := h64Nat
      have h91 : Q'.ofNat tailEnvelopeModeChartBase ≤ N := by
        dsimp only [N]
        exact CReal.ofNat_le_ofNat h91Nat
      have hDN2 : D ≤ N * N :=
        Q'.le_trans' _ _ _
          (by
            dsimp only [D]
            exact CReal.ofNat_le_ofNat hDN2Nat)
          (Q'.le_of_eqv hsq)
      have hnTwoDNat : n ≤ 2 * (k + 2) := by
        simpa [HarmonicGrowingAnchorPF2.growingAnchor] using hnright
      have htwoD :
          Q'.ofNat (2 * (k + 2)) ≈ Q'.ofNat 2 * D := by
        dsimp only [D]
        exact HeatKernelRGStep.ofNat_mul_eqv 2 (k + 2)
      have hN2D : N ≤ Q'.ofNat 2 * D :=
        Q'.le_trans' _ _ _
          (by
            dsimp only [N]
            exact CReal.ofNat_le_ofNat hnTwoDNat)
          (Q'.le_of_eqv htwoD)
      have hmul91 :
          Q'.ofNat 2 * Q'.ofNat tailEnvelopeModeChartBase ≤ Q'.ofNat 2 * N :=
        Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) h91 (by decide)
      have hsub91 := Q'.add_le_add_right
        (Q'.ofNat 2 * Q'.ofNat tailEnvelopeModeChartBase) (Q'.ofNat 2 * N)
        (-(1 : Q')) hmul91
      have hTwoNOnePos :
          (0 : Q') < Q'.ofNat 2 * N + -(1 : Q') :=
        HeatKernelRGStep.lt_of_lt_of_le (by decide) hsub91
      exact lowerSixTailNextSlopeFloorCleared_nonnegative_chartB
        hNpos h91 hN2D hDN2 hTwoNOnePos
  have hDpEqv :
      D + Q'.ofInt 1 ≈ Q'.ofNat (k + 3) := by
    dsimp only [D]
    simpa [show k + 2 + 1 = k + 3 by omega] using
      Q'.eqv_symm (Q'.ofNat_add_eqv (k + 2) 1)
  have hDu :
      (D + Q'.ofInt 1) * HarmonicCutoffBoundary.harmU (k + 1) ≈
        (1 : Q') := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hDpEqv)
      (by
        simpa [show k + 1 + 2 = k + 3 by omega] using
          local_harmDen_mul_harmU (k + 1))
  have hbridge := slopeFloorCleared_physical_bridge hDu n hn4
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    rw [show k + 2 = (k + 1) + 1 by omega]
    exact Q'.ofNat_succ_pos (k + 1)
  have hDpPos : (0 : Q') < D + Q'.ofInt 1 :=
    Q'.add_pos hDpos (by decide)
  have hleftScaled :
      (0 : Q') ≤ Q'.ofNat 144 *
        ((D + Q'.ofInt 1) * lowerSixTailNextSlopeFloorCleared D N) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hDpPos) hcert)
  have hscaled :
      (0 : Q') ≤
        (Q'.ofNat 362880 * RingNormaliser.qpow (D + Q'.ofInt 1) 9) *
          (Q'.ofNat n +
            -(Q'.ofNat (n + 1) *
              oneSubTaylor8 (HarmonicCutoffBoundary.harmU (k + 1))
                (2 * n + 1))) :=
    Q'.le_trans' _ _ _ hleftScaled (Q'.le_of_eqv hbridge)
  have hscalePos :
      (0 : Q') < Q'.ofNat 362880 *
        RingNormaliser.qpow (D + Q'.ofInt 1) 9 :=
    Q'.mul_pos (by decide) (local_rnqpow_pos hDpPos 9)
  exact YMGap.Continuum.FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    hscalePos hscaled

/-- The certified next-scale slope floor is nonnegative throughout the
physical lower-six tail corridor. -/
theorem lowerSixTailNextSlopeFloor_nonnegative
    {k n : Nat} (hk : 390 ≤ k)
    (hleft : HarmonicMovingDeterminantThetaWindow.thetaWindowLeft k + 1 ≤ n)
    (hnright : n ≤ HarmonicGrowingAnchorPF2.growingAnchor k) :
    (0 : Q') ≤ lowerSixTailNextSlopeFloor k n := by
  unfold lowerSixTailNextSlopeFloor lowerSixTailNextPowerUpper
  exact lowerSixTailNextSlopeFloor_explicit_nonnegative hk hleft hnright

#print axioms qpow_oneSub_le_taylor8
#print axioms taylor9_le_qpow_oneSub
#print axioms tailTaylor8Prefix_physical_bridge
#print axioms tailTaylor9Cleared_physical_bridge
#print axioms lowerSixTailOldPowerLower_nonnegative_of_le_den
#print axioms slopeFloorCleared_physical_bridge
#print axioms lowerSixTailNextSlopeFloor_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
