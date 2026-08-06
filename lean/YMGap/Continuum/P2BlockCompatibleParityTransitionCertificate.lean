/-
Track 11.7-fusion / R4f -- proof-about-computation certificates for the
physical parity transitions.

Both transition schemas are cross-ratio inequalities between four weighted
Clebsch-box states.  Clearing the common coefficient denominator twice and
the fixed retuned heat power turns either schema into one `Nat` comparison.
This file proves the generic soundness theorem once, then exposes the honest
all-scale frontier as a pure-arithmetic family.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose
import YMGap.Continuum.P2RetunedParityStrandCompiler

namespace YMGap.Continuum.P2BlockCompatibleParityTransitionCertificate

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Cleared natural-number image of `boxTailBase`. -/
def scaledBoxBaseAt (num den N s : Nat) : Nat :=
  (s + 2) * scaledCoeffAt num den N s

/-- Cleared natural-number image of `boxTailLeft`. -/
def scaledBoxLeftAt (num den N s : Nat) : Nat :=
  (s + 1) * scaledCoeffAt num den N (s + 1)

/-- One generic cleared box cross-ratio cell. -/
def integralBoxCrossAt
    (num den qnum qden N p a b c d : Nat) : Prop :=
  scaledBoxBaseAt num den N a * scaledBoxLeftAt num den N b * qden ^ p <=
    qnum ^ p *
      (scaledBoxBaseAt num den N c * scaledBoxLeftAt num den N d)

instance integralBoxCrossAtDecidable
    (num den qnum qden N p a b c d : Nat) :
    Decidable (integralBoxCrossAt num den qnum qden N p a b c d) := by
  unfold integralBoxCrossAt
  infer_instance

private theorem scale_boxTailBase_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * boxTailBase N w s ≈
      Q'.ofNat (scaledBoxBaseAt num den N s) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (den ^ (2 * c4 N)) *
      (dimQ (s + 1) * bondMovedCoeff N w 2 s)) _ ?_ ?_
  · unfold boxTailBase
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (bondMovedCoeff_eq_boxSum N s)))
  · simpa only [scaledBoxBaseAt] using
      scaledDimCoeffAt_reconstruct num den hden w hw N (s + 1) s

private theorem scale_boxTailLeft_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * boxTailLeft N w s ≈
      Q'.ofNat (scaledBoxLeftAt num den N s) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (den ^ (2 * c4 N)) *
      (dimQ s * bondMovedCoeff N w 2 (s + 1))) _ ?_ ?_
  · unfold boxTailLeft
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (bondMovedCoeff_eq_boxSum N (s + 1))))
  · simpa only [scaledBoxLeftAt] using
      scaledDimCoeffAt_reconstruct num den hden w hw N s (s + 1)

/-- Generic soundness of the natural-number cross-product cell for an
arbitrary rational power base.  The checker is untrusted computation; this
theorem is the load-bearing proof. -/
theorem integralBoxCrossAt_sound_of_base
    (num den qnum qden N p a b c d : Nat)
    (hden : 0 < den) (hqden : 0 < qden)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (q : Q') (hq : q ≈ Q'.mkPos qnum qden hqden)
    (h : integralBoxCrossAt num den qnum qden N p a b c d) :
    boxTailBase N w a * boxTailLeft N w b <=
      (qpow q p * boxTailBase N w c) *
        boxTailLeft N w d := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  let x := boxTailBase N w a
  let y := boxTailLeft N w b
  let z := boxTailBase N w c
  let u := boxTailLeft N w d
  let xn := scaledBoxBaseAt num den N a
  let yn := scaledBoxLeftAt num den N b
  let zn := scaledBoxBaseAt num den N c
  let un := scaledBoxLeftAt num den N d
  let qp := qpow q p
  have hcross : xn * yn * qden ^ p <= qnum ^ p * (zn * un) := by
    simpa only [xn, yn, zn, un] using h
  have hrat := ofNat_le_mkPos_mul_of_cross
    (xn * yn) (zn * un) (qnum ^ p) (qden ^ p)
      (Nat.pow_pos hqden) hcross
  have hqp : qp ≈
      Q'.mkPos ((qnum ^ p : Nat) : Int) (qden ^ p)
        (Nat.pow_pos hqden) := by
    refine Q'.eqv_trans _ _ _
      (BondMovingRelResidual.qpow_eqv_congr_base hq p) ?_
    exact qpow_mkPosNat_eqv qnum qden hqden p
  have hcore0 : Q'.ofNat (xn * yn) <= qp * Q'.ofNat (zn * un) :=
    Q'.le_trans' _ _ _ hrat (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hqp)))
  have hcore : Q'.ofNat (xn * yn) <=
      qp * (Q'.ofNat zn * Q'.ofNat un) :=
    Q'.le_trans' _ _ _ hcore0 (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left qp _ _
        (Q'.eqv_symm
          (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv zn un))))
  have hx : scale * x ≈ Q'.ofNat xn := by
    simpa only [scale, x, xn] using
      scale_boxTailBase_reconstruct num den hden w hw N a
  have hy : scale * y ≈ Q'.ofNat yn := by
    simpa only [scale, y, yn] using
      scale_boxTailLeft_reconstruct num den hden w hw N b
  have hz : scale * z ≈ Q'.ofNat zn := by
    simpa only [scale, z, zn] using
      scale_boxTailBase_reconstruct num den hden w hw N c
  have hu : scale * u ≈ Q'.ofNat un := by
    simpa only [scale, u, un] using
      scale_boxTailLeft_reconstruct num den hden w hw N d
  have hleft : (scale * x) * (scale * y) ≈ Q'.ofNat (xn * yn) :=
    Q'.eqv_trans _ _ _ (mul_eqv_both hx hy)
      (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv xn yn)
  have hright : qp * ((scale * z) * (scale * u)) ≈
      qp * (Q'.ofNat zn * Q'.ofNat un) :=
    Q'.mul_eqv_congr_left qp _ _ (mul_eqv_both hz hu)
  have hscaled : (scale * x) * (scale * y) <=
      qp * ((scale * z) * (scale * u)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hright))
  let scaleSq := scale * scale
  have hleftRegroup : (scale * x) * (scale * y) ≈
      scaleSq * (x * y) := mul_four_regroup scale x scale y
  have hinnerRegroup : (scale * z) * (scale * u) ≈
      scaleSq * (z * u) := mul_four_regroup scale z scale u
  have hrightRegroup : qp * ((scale * z) * (scale * u)) ≈
      scaleSq * (qp * (z * u)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left qp _ _ hinnerRegroup) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv qp scaleSq (z * u))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (z * u)
        (Q'.mul_comm_eqv qp scaleSq)) ?_
    exact Q'.mul_assoc_eqv scaleSq qp (z * u)
  have hcancelReady : scaleSq * (x * y) <=
      scaleSq * (qp * (z * u)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleftRegroup)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrightRegroup))
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((den ^ (2 * c4 N) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos hden)
  have hraw : x * y <= qp * (z * u) :=
    Q'.le_of_mul_le_mul_left hcancelReady (Q'.mul_pos hscale hscale)
  have htarget : (qp * z) * u ≈ qp * (z * u) :=
    Q'.mul_assoc_eqv qp z u
  have hfinal : x * y <= (qp * z) * u :=
    Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv htarget)
  simpa only [x, y, z, u, qp] using hfinal

/-- Retuned specialization retained for the canonical parity carrier. -/
theorem integralBoxCrossAt_sound
    (num den qnum qden N p a b c d : Nat)
    (hden : 0 < den) (hqden : 0 < qden)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (hq : p2RetunedWeight w ≈ Q'.mkPos qnum qden hqden)
    (h : integralBoxCrossAt num den qnum qden N p a b c d) :
    boxTailBase N w a * boxTailLeft N w b <=
      (qpow (p2RetunedWeight w) p * boxTailBase N w c) *
        boxTailLeft N w d :=
  integralBoxCrossAt_sound_of_base
    num den qnum qden N p a b c d hden hqden w hw
    (p2RetunedWeight w) hq h

/-- Pure-`Nat` odd two-step cell on the physical schedule. -/
def physicalBoxOddTransitionAt (k m : Nat) : Prop :=
  integralBoxCrossAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) 4 (2 * m + 1) (2 * m + 3)
      (2 * m + 3) (2 * m + 1)

/-- Pure-`Nat` preceding-odd to even insertion cell. -/
def physicalBoxEvenTransitionAt (k m : Nat) : Prop :=
  integralBoxCrossAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) 2 (2 * m - 1) (2 * m)
      (2 * m) (2 * m - 1)

instance physicalBoxOddTransitionAtDecidable (k m : Nat) :
    Decidable (physicalBoxOddTransitionAt k m) := by
  unfold physicalBoxOddTransitionAt
  infer_instance

instance physicalBoxEvenTransitionAtDecidable (k m : Nat) :
    Decidable (physicalBoxEvenTransitionAt k m) := by
  unfold physicalBoxEvenTransitionAt
  infer_instance

theorem physicalBoxOddTransitionAt_sound (k m : Nat)
    (h : physicalBoxOddTransitionAt k m) :
    boxTailBase (blockNcut k) (blockWeight k) (2 * m + 1) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m + 3) <=
      (qpow (p2RetunedWeight (blockWeight k)) 4 *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m + 3)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m + 1) :=
  integralBoxCrossAt_sound
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) 4 (2 * m + 1) (2 * m + 3)
      (2 * m + 3) (2 * m + 1)
    (physicalWeightDen_pos k) (physicalRetunedDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockRetunedWeight_eqv_closed k) h

theorem physicalBoxEvenTransitionAt_sound (k m : Nat)
    (h : physicalBoxEvenTransitionAt k m) :
    boxTailBase (blockNcut k) (blockWeight k) (2 * m - 1) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m) <=
      (qpow (p2RetunedWeight (blockWeight k)) 2 *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m - 1) :=
  integralBoxCrossAt_sound
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) 2 (2 * m - 1) (2 * m)
      (2 * m) (2 * m - 1)
    (physicalWeightDen_pos k) (physicalRetunedDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockRetunedWeight_eqv_closed k) h

/-- The honest transition carrier after proof compilation: every field is a
natural-number inequality, with no rational normalization. -/
structure BlockCompatibleP2IntegralParityTransitionsFromFour : Type where
  odd : forall k m, 4 <= k -> 2 * m + 3 < 2 * blockNcut k ->
    physicalBoxOddTransitionAt k m
  even : forall k m, 4 <= k -> 1 <= m -> 2 * m < 2 * blockNcut k ->
    physicalBoxEvenTransitionAt k m

/-- Rational box transition data consumed by the parity compiler. -/
structure BlockCompatibleP2BoxParityTransitionsFromFour : Type where
  transitions : forall k, 4 <= k ->
    P2RetunedBoxCoreParityTransitions (blockNcut k) (blockWeight k)

def BlockCompatibleP2IntegralParityTransitionsFromFour.toBox
    (T : BlockCompatibleP2IntegralParityTransitionsFromFour) :
    BlockCompatibleP2BoxParityTransitionsFromFour where
  transitions := fun k hk => {
    oddStep := fun m hm => physicalBoxOddTransitionAt_sound k m (T.odd k m hk hm)
    evenBridge := fun m hm1 hm =>
      physicalBoxEvenTransitionAt_sound k m (T.even k m hk hm1 hm)
  }

/-- Insert the proved all-cutoff physical head into the head-free transition
carrier expected by the existing parity-strand compiler. -/
def BlockCompatibleP2BoxParityTransitionsFromFour.withPhysicalHead
    (T : BlockCompatibleP2BoxParityTransitionsFromFour) :
    BlockCompatibleP2BoxParityTransitionsFromFourHeadFromEight where
  transitions := T.transitions
  head := fun k hk => by
    let r := k - 8
    have hr : r + 8 = k := by
      dsimp only [r]
      omega
    have h := physical_box_head r
    rw [hr] at h
    simpa only [boxTailLeft, boxTailRight, boxTailBase,
      show 1 + 1 = 2 by decide,
      show 2 * 1 + 3 = 5 by decide] using h

#print axioms integralBoxCrossAt_sound_of_base
#print axioms integralBoxCrossAt_sound
#print axioms physicalBoxOddTransitionAt_sound
#print axioms physicalBoxEvenTransitionAt_sound
#print axioms BlockCompatibleP2IntegralParityTransitionsFromFour.toBox
#print axioms BlockCompatibleP2BoxParityTransitionsFromFour.withPhysicalHead

end YMGap.Continuum.P2BlockCompatibleParityTransitionCertificate
