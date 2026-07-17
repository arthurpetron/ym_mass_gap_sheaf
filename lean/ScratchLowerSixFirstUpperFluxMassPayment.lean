import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual
import YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
import YMGap.Continuum.HarmonicRetuneFloor

namespace ScratchLowerSixFirstUpperFluxMassPayment

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
open YMGap.Continuum.HarmonicRetuneFloor
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem first_upper_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "first_upper_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               first_upper_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem qpow_eqv_pow (q : Q') : ∀ n, qpow q n ≈ q ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      refine Q'.eqv_trans _ (q ^ n * q) _
        (Q'.mul_eqv_congr_right _ _ q (qpow_eqv_pow q n)) ?_
      exact Q'.mul_comm_eqv (q ^ n) q

private theorem pow_eqv_qpow (q : Q') (n : Nat) :
    q ^ n ≈ qpow q n := Q'.eqv_symm (qpow_eqv_pow q n)

/-! ## Remote Gaussian endpoint: seven exact inverse powers -/

private theorem lowerSixModeWeight_eqv_harmonicPower (k n : Nat) :
    lowerSixModeWeight k n ≈ qpow (harmW k) (2 * (n * n)) := by
  unfold lowerSixModeWeight
  refine Q'.eqv_trans _
    (qpow (harmW k) (n * n) * qpow (harmW k) (n * n)) _
    (FusionQuotientCollapse.qpow_mul_self (harmW k) (n * n)) ?_
  have htwo : (n * n) + (n * n) = 2 * (n * n) := by omega
  rw [← htwo]
  exact Q'.eqv_symm
    (HeatKernelRGStep.qpow_add (harmW k) (n * n) (n * n))

private theorem harmonic_half_power_seven_blocks_le_invPower
    (k : Nat) :
    qpow (harmW k) ((k + 2) * (7 * (k + 2))) ≤
      RingNormaliser.qpow (Q'.invSucc (k + 2)) 7 := by
  let D := k + 2
  have hblocks := harmonic_blocks_le_half_pow k (7 * D)
  have hhalf : HalfPow.half ^ D ≤ Q'.invSucc D :=
    HalfPow.pow_half_le_invSucc D
  have hhalf0 : (0 : Q') ≤ HalfPow.half ^ D :=
    Q'.pow_nonneg _ HalfPow.half_nonneg D
  have hpow := FusedAmplitudeDerivation.qpow_mono_base hhalf0 hhalf 7
  have hleft : HalfPow.half ^ (7 * D) ≈
      RingNormaliser.qpow (HalfPow.half ^ D) 7 := by
    refine Q'.eqv_trans _ (qpow HalfPow.half (D * 7)) _ ?_ ?_
    · rw [show 7 * D = D * 7 by omega]
      exact pow_eqv_qpow _ _
    · refine Q'.eqv_trans _
        (RingNormaliser.qpow (qpow HalfPow.half D) 7) _
        (Q'.eqv_symm
          (HeatKernelRGStep.qpow_qpow HalfPow.half D 7)) ?_
      exact RingNormaliser.qpow_eqv_congr (qpow_eqv_pow HalfPow.half D) 7
  dsimp only [D] at hblocks hhalf hhalf0 hpow hleft ⊢
  exact Q'.le_trans' _ _ _ hblocks
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hpow)

private theorem ofNat_mul_invSucc_le_one (D : Nat) :
    Q'.ofNat D * Q'.invSucc D ≤ (1 : Q') := by
  have hcast : Q'.ofNat D ≤ Q'.ofNat (D + 1) :=
    CReal.ofNat_le_ofNat (by omega)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.invSucc D)
    hcast (Q'.invSucc_nonneg D)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc D))

private theorem seventh_scaled_invPower_le_one (D : Nat) :
    RingNormaliser.qpow (Q'.ofNat D) 7 *
        RingNormaliser.qpow (Q'.invSucc D) 7 ≤ (1 : Q') := by
  have hD0 : (0 : Q') ≤ Q'.ofNat D := HeatKernelRGStep.zero_le_ofNat D
  have hI0 : (0 : Q') ≤ Q'.invSucc D := Q'.invSucc_nonneg D
  have hprod := ofNat_mul_invSucc_le_one D
  have hp := FusedAmplitudeDerivation.qpow_mono_base
    (Q'.mul_nonneg _ _ hD0 hI0) hprod 7
  have halgebra :
      RingNormaliser.qpow (Q'.ofNat D) 7 *
          RingNormaliser.qpow (Q'.invSucc D) 7 ≈
        RingNormaliser.qpow (Q'.ofNat D * Q'.invSucc D) 7 := by
    induction 7 with
    | zero =>
        unfold RingNormaliser.qpow
        exact Q'.eqv_symm (Q'.one_mul_eqv 1)
    | succ n ih =>
        unfold RingNormaliser.qpow
        refine Q'.eqv_trans _
          ((RingNormaliser.qpow (Q'.ofNat D) n *
              RingNormaliser.qpow (Q'.invSucc D) n) *
            (Q'.ofNat D * Q'.invSucc D)) _ ?_ ?_
        · first_upper_ring
        · exact Q'.mul_eqv_congr_right _ _ _ ih
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halgebra)
    (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (by decide)))

/-- The remote Gaussian endpoint cancels seven full polynomial powers of the
harmonic denominator. -/
theorem lowerSixFirstUpperWeight_scaled_seven_le_one (k : Nat) :
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 7 *
        lowerSixModeWeight k (growingAnchor k + 1) ≤ (1 : Q') := by
  let D := k + 2
  let N := growingAnchor k + 1
  have hweightEq := lowerSixModeWeight_eqv_harmonicPower k N
  have hexp : D * (7 * D) ≤ 2 * (N * N) := by
    have hbase : 2 * D ≤ N := by
      dsimp only [D, N]
      unfold growingAnchor
      omega
    have hsquare : (2 * D) * (2 * D) ≤ N * N :=
      Nat.mul_le_mul hbase hbase
    have hscaled := Nat.mul_le_mul_left 2 hsquare
    calc
      D * (7 * D) = 7 * (D * D) := by ac_rfl
      _ ≤ 8 * (D * D) := by omega
      _ = 2 * ((2 * D) * (2 * D)) := by ac_rfl
      _ ≤ 2 * (N * N) := hscaled
  have hanti := HeatKernelRGStep.qpow_antitone
    (harmW_nonneg k) (harmW_le_one k) (D * (7 * D))
      (2 * (N * N)) hexp
  have hremote : lowerSixModeWeight k N ≤
      RingNormaliser.qpow (Q'.invSucc D) 7 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hweightEq)
      (Q'.le_trans' _ _ _ hanti
        (harmonic_half_power_seven_blocks_le_invPower k))
  have hD7 : (0 : Q') ≤ RingNormaliser.qpow (Q'.ofNat D) 7 :=
    ringQpow_nonnegative (HeatKernelRGStep.zero_le_ofNat D) 7
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hremote hD7
  dsimp only [D, N] at hscaled ⊢
  exact Q'.le_trans' _ _ _ hscaled
    (seventh_scaled_invPower_le_one (k + 2))

/-! ## Exact translated polynomial certificate for the remote flux -/

private abbrev PE := RingNormaliser.PolyExpr

private def pFirstUpperFluxD : PE :=
  let D : PE := .var 0
  let N : PE := .add (.mul (.const 2) D) (.const 1)
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let N3 := .pow N 3
  let N4 := .pow N 4
  let N5 := .pow N 5
  let N6 := .pow N 6
  let N7 := .pow N 7
  .add (.mul (.mul (.const 192) N) D4)
    (.add (.mul (.mul (.const 384) N3) D3)
      (.add (.neg (.mul (.mul (.const 6) N) D3))
        (.add (.neg (.mul (.mul (.const 384) N5) D2))
          (.add (.mul (.mul (.const 576) N4) D2)
            (.add (.mul (.mul (.const 184) N3) D2)
              (.add (.mul (.mul (.const 224) N5) D)
                (.add (.neg (.mul (.const 256) N7))
                  (.add (.mul (.const 576) N6)
                    (.mul (.const 3) D3)))))))))

private def pFirstUpperFluxDExpanded : PE :=
  let D : PE := .var 0
  .add (.neg (.mul (.const 45056) (.pow D 7)))
    (.add (.neg (.mul (.const 89088) (.pow D 6)))
      (.add (.neg (.mul (.const 49344) (.pow D 5)))
        (.add (.mul (.const 15956) (.pow D 4))
          (.add (.mul (.const 31693) (.pow D 3))
            (.add (.mul (.const 15672) (.pow D 2))
              (.add (.mul (.const 3552) D) (.const 320)))))))

private theorem pFirstUpperFluxD_normal :
    RingNormaliser.normalize pFirstUpperFluxD =
      RingNormaliser.normalize pFirstUpperFluxDExpanded := by decide

private def pFirstUpperFluxGapTranslated : PE :=
  let t : PE := .var 0
  let D : PE := .add (.const 1) t
  .add (.mul (.const 130000) (.pow D 7))
    (.add (.neg (.mul (.const 45056) (.pow D 7)))
      (.add (.neg (.mul (.const 89088) (.pow D 6)))
        (.add (.neg (.mul (.const 49344) (.pow D 5)))
          (.add (.mul (.const 15956) (.pow D 4))
            (.add (.mul (.const 31693) (.pow D 3))
              (.add (.mul (.const 15672) (.pow D 2))
                (.add (.mul (.const 3552) D) (.const 320))))))))

private def pFirstUpperFluxGapExpanded : PE :=
  let t : PE := .var 0
  .add (.const 13705)
    (.add (.mul (.const 7159) t)
      (.add (.mul (.const 160551) (.pow t 2))
        (.add (.mul (.const 793357) (.pow t 3))
          (.add (.mul (.const 1405956) (.pow t 4))
            (.add (.mul (.const 1199952) (.pow t 5))
              (.add (.mul (.const 505520) (.pow t 6))
                (.mul (.const 84944) (.pow t 7))))))))

private theorem pFirstUpperFluxGap_normal :
    RingNormaliser.normalize pFirstUpperFluxGapTranslated =
      RingNormaliser.normalize pFirstUpperFluxGapExpanded := by decide

private def firstUpperFluxGapExpanded (t : Q') : Q' :=
  Q'.ofNat 13705 + Q'.ofNat 7159 * t +
    Q'.ofNat 160551 * RingNormaliser.qpow t 2 +
    Q'.ofNat 793357 * RingNormaliser.qpow t 3 +
    Q'.ofNat 1405956 * RingNormaliser.qpow t 4 +
    Q'.ofNat 1199952 * RingNormaliser.qpow t 5 +
    Q'.ofNat 505520 * RingNormaliser.qpow t 6 +
    Q'.ofNat 84944 * RingNormaliser.qpow t 7

private theorem firstUpperFluxGapExpanded_nonnegative {t : Q'}
    (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ firstUpperFluxGapExpanded t := by
  unfold firstUpperFluxGapExpanded
  repeat' apply Q'.zero_le_add
  · decide
  · exact Q'.mul_nonneg _ _ (by decide) ht
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 2)
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 3)
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 4)
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 5)
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 6)
  · exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative ht 7)

private theorem firstUpperFlux_specialized_identity (D : Q') :
    lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat 2 * D + 1) ≈
      -(Q'.ofNat 45056 * RingNormaliser.qpow D 7) +
      (-(Q'.ofNat 89088 * RingNormaliser.qpow D 6) +
      (-(Q'.ofNat 49344 * RingNormaliser.qpow D 5) +
      (Q'.ofNat 15956 * RingNormaliser.qpow D 4 +
      (Q'.ofNat 31693 * RingNormaliser.qpow D 3 +
      (Q'.ofNat 15672 * RingNormaliser.qpow D 2 +
      (Q'.ofNat 3552 * D + Q'.ofNat 320)))))) := by
  simpa [pFirstUpperFluxD, pFirstUpperFluxDExpanded,
    lowerSixDiscreteHermiteFluxPoly, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFirstUpperFluxD pFirstUpperFluxDExpanded
      pFirstUpperFluxD_normal (fun _ => D))

private theorem firstUpperFluxGap_identity (t : Q') :
    Q'.ofNat 130000 * RingNormaliser.qpow ((1 : Q') + t) 7 +
        lowerSixDiscreteHermiteFluxPoly ((1 : Q') + t)
          (Q'.ofNat 2 * ((1 : Q') + t) + 1) ≈
      firstUpperFluxGapExpanded t := by
  let D := (1 : Q') + t
  have hflux := firstUpperFlux_specialized_identity D
  have hgap :
      Q'.ofNat 130000 * RingNormaliser.qpow D 7 +
          (-(Q'.ofNat 45056 * RingNormaliser.qpow D 7) +
          (-(Q'.ofNat 89088 * RingNormaliser.qpow D 6) +
          (-(Q'.ofNat 49344 * RingNormaliser.qpow D 5) +
          (Q'.ofNat 15956 * RingNormaliser.qpow D 4 +
          (Q'.ofNat 31693 * RingNormaliser.qpow D 3 +
          (Q'.ofNat 15672 * RingNormaliser.qpow D 2 +
          (Q'.ofNat 3552 * D + Q'.ofNat 320))))))) ≈
        firstUpperFluxGapExpanded t := by
    simpa [D, pFirstUpperFluxGapTranslated,
      pFirstUpperFluxGapExpanded, firstUpperFluxGapExpanded,
      RingNormaliser.eval] using
      (RingNormaliser.poly_identity_of_normal_eq
        pFirstUpperFluxGapTranslated pFirstUpperFluxGapExpanded
        pFirstUpperFluxGap_normal (fun _ => t))
  dsimp only [D] at hflux hgap ⊢
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hflux) hgap

private theorem one_add_cast_pred_eqv {D : Nat} (hD : 1 ≤ D) :
    (1 : Q') + Q'.ofNat (D - 1) ≈ Q'.ofNat D := by
  have hnat : 1 + (D - 1) = D := by omega
  refine Q'.eqv_trans _ (Q'.ofNat 1 + Q'.ofNat (D - 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv 1 (D - 1)))
      (Q'.eqv_of_eq (congrArg Q'.ofNat hnat))

/-- Exact degree-seven envelope for the signed remote endpoint polynomial.
The proof is the nonnegative translated polynomial with coefficients
`13705, 7159, ..., 84944`; no numerical approximation enters. -/
theorem lowerSixFirstUpperFluxPoly_neg_le_scaled_seven
    {D : Nat} (hD : 1 ≤ D) :
    -(lowerSixDiscreteHermiteFluxPoly (Q'.ofNat D)
        (Q'.ofNat (2 * D + 1))) ≤
      Q'.ofNat 130000 * RingNormaliser.qpow (Q'.ofNat D) 7 := by
  let t := Q'.ofNat (D - 1)
  have ht : (0 : Q') ≤ t := HeatKernelRGStep.zero_le_ofNat _
  have hgap0 := firstUpperFluxGapExpanded_nonnegative ht
  have hgapEq := firstUpperFluxGap_identity t
  have hgap : (0 : Q') ≤
      Q'.ofNat 130000 * RingNormaliser.qpow ((1 : Q') + t) 7 +
        lowerSixDiscreteHermiteFluxPoly ((1 : Q') + t)
          (Q'.ofNat 2 * ((1 : Q') + t) + 1) :=
    Q'.le_trans' _ _ _ hgap0 (Q'.le_of_eqv (Q'.eqv_symm hgapEq))
  have hDeq := one_add_cast_pred_eqv hD
  have hNeq : Q'.ofNat 2 * ((1 : Q') + t) + 1 ≈
      Q'.ofNat (2 * D + 1) := by
    refine Q'.eqv_trans _ (Q'.ofNat 2 * Q'.ofNat D + 1) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hDeq)
    · refine Q'.eqv_trans _ (Q'.ofNat (2 * D) + Q'.ofNat 1) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 D)) (by decide)
      · exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * D) 1)
  have hrewrite :
      Q'.ofNat 130000 * RingNormaliser.qpow ((1 : Q') + t) 7 +
          lowerSixDiscreteHermiteFluxPoly ((1 : Q') + t)
            (Q'.ofNat 2 * ((1 : Q') + t) + 1) ≈
        Q'.ofNat 130000 * RingNormaliser.qpow (Q'.ofNat D) 7 +
          lowerSixDiscreteHermiteFluxPoly (Q'.ofNat D)
            (Q'.ofNat (2 * D + 1)) := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (RingNormaliser.qpow_eqv_congr hDeq 7))
      (by
        unfold lowerSixDiscreteHermiteFluxPoly
        repeat' first
          | apply Q'.add_eqv_congr'
          | apply Q'.neg_eqv_congr
          | apply Q'.mul_eqv_congr'
          | apply RingNormaliser.qpow_eqv_congr
          | exact hDeq
          | exact hNeq
          | exact Q'.eqv_refl _)
  have hgap' : (0 : Q') ≤
      Q'.ofNat 130000 * RingNormaliser.qpow (Q'.ofNat D) 7 +
        lowerSixDiscreteHermiteFluxPoly (Q'.ofNat D)
          (Q'.ofNat (2 * D + 1)) :=
    Q'.le_trans' _ _ _ hgap (Q'.le_of_eqv hrewrite)
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hgap' (Q'.le_of_eqv (by first_upper_ring))

#print axioms lowerSixFirstUpperWeight_scaled_seven_le_one
#print axioms lowerSixFirstUpperFluxPoly_neg_le_scaled_seven

end ScratchLowerSixFirstUpperFluxMassPayment
