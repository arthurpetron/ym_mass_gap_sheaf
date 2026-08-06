/-
Track 11.7-fusion / R4d -- physical obstruction to the schedule-wide
strong-Turan carrier.

The block-compatible coefficient frontier currently asks for the strengthened
dimension-weighted Turan inequality at every scale.  This module checks the
first adverse physical atom exactly: `k=2`, `N=19`, `s=2`.  A generic
common-denominator reconstruction transports any physical inequality to a
small natural-number cross product, which the kernel refutes.

Consequently `BlockCompatibleP2BoxStrongTuranData` is empty.  The all-cutoff
`CanonicalBulkControl` route must be repointed to a weaker coefficient
compiler; adding more conditional consumers to this carrier cannot close the
physical frontier.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2VacNormIntegralCertificate
import YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
import YMGap.Continuum.P2RetunedHeadThreeTuranCompiler

namespace YMGap.Continuum.P2BlockCompatibleStrongTuranObstruction

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 5000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2RetunedHeadThreeTuranCompiler
open YMGap.Continuum.P2RetunedStrongTuranCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

theorem blockWeight_two_eqv :
    blockWeight 2 ≈ Q'.mkPos 191 192 (by decide) := by
  unfold blockWeight blockMargin SpectralLocalizationCrux.q112 blockQuarter
    qpow
  decide

theorem blockRetunedSquare_two_eqv :
    qpow (p2RetunedWeight (blockWeight 2)) 2 ≈
      Q'.mkPos ((383 ^ 2 : Nat) : Int) (384 ^ 2)
        (Nat.pow_pos (by decide)) := by
  unfold p2RetunedWeight renormWFix renormTauFix blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

def blockTwoScaledCoeff (mode : Nat) : Nat :=
  scaledCoeffAt 191 192 19 mode

/-- Cleared form of the proposed strong-Turan atom at `k=2` and an arbitrary
mode.  This exposes further adverse cells without repeating the rational
reconstruction proof. -/
def blockTwoIntegralStrongTuranAt (s : Nat) : Prop :=
  (((s + 2) * blockTwoScaledCoeff s) *
      ((s + 2) * blockTwoScaledCoeff (s + 2))) *
      384 ^ 2 <=
    383 ^ 2 *
      (((s + 3) * blockTwoScaledCoeff (s + 1)) *
        ((s + 1) * blockTwoScaledCoeff (s + 1)))

/-- First adverse cleared atom. -/
def blockTwoIntegralStrongTuranAtTwo : Prop :=
  blockTwoIntegralStrongTuranAt 2

instance blockTwoIntegralStrongTuranAtTwoDecidable :
    Decidable blockTwoIntegralStrongTuranAtTwo := by
  unfold blockTwoIntegralStrongTuranAtTwo blockTwoIntegralStrongTuranAt
  infer_instance

/-- The proof-about-computation certificate: the cleared physical atom is
strictly false. -/
theorem blockTwoIntegralStrongTuranAtTwo_false :
    ¬ blockTwoIntegralStrongTuranAtTwo := by decide

private theorem cross_of_ofNat_le_mkPos_mul
    (A B num den : Nat) (hden : 0 < den)
    (h : Q'.ofNat A <= Q'.mkPos num den hden * Q'.ofNat B) :
    A * den <= num * B := by
  have hInt : (A : Int) * (den : Int) <= (num : Int) * (B : Int) := by
    change (Q'.ofNat A).num *
        ((Q'.mkPos num den hden * Q'.ofNat B).den : Int) <=
      (Q'.mkPos num den hden * Q'.ofNat B).num *
        ((Q'.ofNat A).den : Int) at h
    simpa only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
      Int.mul_one] using h
  exact Int.ofNat_le.mp (by
    simpa only [Int.natCast_mul] using hInt)

/-- Any physical strong-Turan proof at scale two transports to the generic
cleared natural-number comparison. -/
theorem blockTwoPhysicalTuran_implies_integralAt (s : Nat)
    (h :
      (dimQ (s + 1) * bondMovedCoeff 19 (blockWeight 2) 2 s) *
          (dimQ (s + 1) * bondMovedCoeff 19 (blockWeight 2) 2 (s + 2)) <=
        (qpow (p2RetunedWeight (blockWeight 2)) 2 *
            (dimQ (s + 2) * bondMovedCoeff 19 (blockWeight 2) 2 (s + 1))) *
          (dimQ s * bondMovedCoeff 19 (blockWeight 2) 2 (s + 1))) :
    blockTwoIntegralStrongTuranAt s := by
  let scale := Q'.ofNat (192 ^ (2 * c4 19))
  let scaleSq := scale * scale
  let x := dimQ (s + 1) * bondMovedCoeff 19 (blockWeight 2) 2 s
  let y := dimQ (s + 1) * bondMovedCoeff 19 (blockWeight 2) 2 (s + 2)
  let z := dimQ (s + 2) * bondMovedCoeff 19 (blockWeight 2) 2 (s + 1)
  let u := dimQ s * bondMovedCoeff 19 (blockWeight 2) 2 (s + 1)
  let xn := (s + 2) * blockTwoScaledCoeff s
  let yn := (s + 2) * blockTwoScaledCoeff (s + 2)
  let zn := (s + 3) * blockTwoScaledCoeff (s + 1)
  let un := (s + 1) * blockTwoScaledCoeff (s + 1)
  let q2 := qpow (p2RetunedWeight (blockWeight 2)) 2
  have hphysical : x * y <= (q2 * z) * u := by
    simpa only [x, y, z, u, q2] using h
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((192 ^ (2 * c4 19) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 192))
  have hscaleSq : (0 : Q') < scaleSq := Q'.mul_pos hscale hscale
  have hscaled : scaleSq * (x * y) <= scaleSq * ((q2 * z) * u) :=
    Q'.mul_le_mul_of_nonneg_left _ _ scaleSq hphysical
      (Q'.le_of_lt hscaleSq)
  have hx : scale * x ≈ Q'.ofNat xn := by
    simpa only [scale, x, xn, blockTwoScaledCoeff] using
      (scaledDimCoeffAt_reconstruct 191 192 (by decide)
        (blockWeight 2) blockWeight_two_eqv 19 (s + 1) s)
  have hy : scale * y ≈ Q'.ofNat yn := by
    simpa only [scale, y, yn, blockTwoScaledCoeff] using
      (scaledDimCoeffAt_reconstruct 191 192 (by decide)
        (blockWeight 2) blockWeight_two_eqv 19 (s + 1) (s + 2))
  have hz : scale * z ≈ Q'.ofNat zn := by
    simpa only [scale, z, zn, blockTwoScaledCoeff] using
      (scaledDimCoeffAt_reconstruct 191 192 (by decide)
        (blockWeight 2) blockWeight_two_eqv 19 (s + 2) (s + 1))
  have hu : scale * u ≈ Q'.ofNat un := by
    simpa only [scale, u, un, blockTwoScaledCoeff] using
      (scaledDimCoeffAt_reconstruct 191 192 (by decide)
        (blockWeight 2) blockWeight_two_eqv 19 s (s + 1))
  have hleftRegroup : (scale * x) * (scale * y) ≈ scaleSq * (x * y) :=
    mul_four_regroup scale x scale y
  have hinnerRegroup : (scale * z) * (scale * u) ≈
      scaleSq * (z * u) :=
    mul_four_regroup scale z scale u
  have hrightRegroup : q2 * ((scale * z) * (scale * u)) ≈
      scaleSq * (q2 * (z * u)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q2 _ _ hinnerRegroup) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv q2 scaleSq (z * u))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (z * u)
        (Q'.mul_comm_eqv q2 scaleSq)) ?_
    exact Q'.mul_assoc_eqv scaleSq q2 (z * u)
  have hrightScaled : scaleSq * ((q2 * z) * u) ≈
      q2 * ((scale * z) * (scale * u)) := by
    refine Q'.eqv_trans _ (scaleSq * (q2 * (z * u))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left scaleSq _ _
        (Q'.mul_assoc_eqv q2 z u)
    · exact Q'.eqv_symm hrightRegroup
  have hscaledForms : (scale * x) * (scale * y) <=
      q2 * ((scale * z) * (scale * u)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftRegroup)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrightScaled))
  have hleftNat : (scale * x) * (scale * y) ≈
      Q'.ofNat (xn * yn) :=
    Q'.eqv_trans _ _ _ (mul_eqv_both hx hy)
      (FusionRDFactor.ofNat_mul_eqv xn yn |> Q'.eqv_symm)
  have hrightNat : q2 * ((scale * z) * (scale * u)) ≈
      q2 * (Q'.ofNat zn * Q'.ofNat un) :=
    Q'.mul_eqv_congr_left q2 _ _ (mul_eqv_both hz hu)
  have hcore : Q'.ofNat (xn * yn) <=
      q2 * (Q'.ofNat zn * Q'.ofNat un) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleftNat)
      (Q'.le_trans' _ _ _ hscaledForms (Q'.le_of_eqv hrightNat))
  have hq2 : q2 ≈
      Q'.mkPos ((383 ^ 2 : Nat) : Int) (384 ^ 2)
        (Nat.pow_pos (by decide)) := by
    simpa only [q2] using blockRetunedSquare_two_eqv
  have hratRight :
      q2 * (Q'.ofNat zn * Q'.ofNat un) ≈
        Q'.mkPos ((383 ^ 2 : Nat) : Int) (384 ^ 2)
            (Nat.pow_pos (by decide)) * Q'.ofNat (zn * un) := by
    refine Q'.eqv_trans _
      (Q'.mkPos ((383 ^ 2 : Nat) : Int) (384 ^ 2)
          (Nat.pow_pos (by decide)) *
        (Q'.ofNat zn * Q'.ofNat un)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hq2
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (FusionRDFactor.ofNat_mul_eqv zn un))
  have hrat : Q'.ofNat (xn * yn) <=
      Q'.mkPos ((383 ^ 2 : Nat) : Int) (384 ^ 2)
          (Nat.pow_pos (by decide)) * Q'.ofNat (zn * un) :=
    Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv hratRight)
  have hnat := cross_of_ofNat_le_mkPos_mul
    (xn * yn) (zn * un) (383 ^ 2) (384 ^ 2)
    (Nat.pow_pos (by decide)) hrat
  simpa only [blockTwoIntegralStrongTuranAt, xn, yn, zn, un] using hnat

/-- Compatibility wrapper for the first adverse atom. -/
theorem blockTwoPhysicalTuran_implies_integral
    (h :
      (dimQ 3 * bondMovedCoeff 19 (blockWeight 2) 2 2) *
          (dimQ 3 * bondMovedCoeff 19 (blockWeight 2) 2 4) <=
        (qpow (p2RetunedWeight (blockWeight 2)) 2 *
            (dimQ 4 * bondMovedCoeff 19 (blockWeight 2) 2 3)) *
          (dimQ 2 * bondMovedCoeff 19 (blockWeight 2) 2 3)) :
    blockTwoIntegralStrongTuranAtTwo :=
  blockTwoPhysicalTuran_implies_integralAt 2 h

theorem blockTwoPhysicalStrongTuran_false :
    ¬ ((dimQ 3 * bondMovedCoeff 19 (blockWeight 2) 2 2) *
          (dimQ 3 * bondMovedCoeff 19 (blockWeight 2) 2 4) <=
        (qpow (p2RetunedWeight (blockWeight 2)) 2 *
            (dimQ 4 * bondMovedCoeff 19 (blockWeight 2) 2 3)) *
          (dimQ 2 * bondMovedCoeff 19 (blockWeight 2) 2 3)) := by
  intro h
  exact blockTwoIntegralStrongTuranAtTwo_false
    (blockTwoPhysicalTuran_implies_integral h)

/-- The proposed repaired carrier is also adverse at `k=2,s=4`. -/
theorem blockTwoIntegralStrongTuranAtFour_false :
    ¬ blockTwoIntegralStrongTuranAt 4 := by
  unfold blockTwoIntegralStrongTuranAt
  decide

theorem blockTwoPhysicalStrongTuranFour_false :
    ¬ ((dimQ 5 * bondMovedCoeff 19 (blockWeight 2) 2 4) *
          (dimQ 5 * bondMovedCoeff 19 (blockWeight 2) 2 6) ≤
        (qpow (p2RetunedWeight (blockWeight 2)) 2 *
            (dimQ 6 * bondMovedCoeff 19 (blockWeight 2) 2 5)) *
          (dimQ 4 * bondMovedCoeff 19 (blockWeight 2) 2 5)) := by
  intro h
  exact blockTwoIntegralStrongTuranAtFour_false
    (blockTwoPhysicalTuran_implies_integralAt 4 h)

/-- The schedule-wide strong-Turan carrier is constructively empty. -/
theorem noBlockCompatibleP2StrongTuranData
    (T : BlockCompatibleP2StrongTuranData) : False := by
  have h := (T.strongTuran 2).turan 2 (by decide) (by decide)
  rw [show blockNcut 2 = 19 by decide] at h
  exact blockTwoPhysicalStrongTuran_false h

/-- Therefore its weighted-box predecessor is also constructively empty. -/
theorem noBlockCompatibleP2BoxStrongTuranData
    (T : BlockCompatibleP2BoxStrongTuranData) : False :=
  noBlockCompatibleP2StrongTuranData T.toStrongTuranData

/-- The first head-three/Turan-from-three replacement is still too strong:
its `k=2,s=4` recurrence atom is constructively false. -/
theorem noBlockCompatibleP2HeadThreeTuranData
    (T : BlockCompatibleP2HeadThreeTuranData) : False := by
  have h := (T.headThreeTuran 2).turan 4 (by decide) (by decide)
  rw [show blockNcut 2 = 19 by decide] at h
  exact blockTwoPhysicalStrongTuranFour_false h

theorem noBlockCompatibleP2BoxHeadThreeTuranData
    (T : BlockCompatibleP2BoxHeadThreeTuranData) : False :=
  noBlockCompatibleP2HeadThreeTuranData T.toHeadThreeTuranData

#print axioms blockWeight_two_eqv
#print axioms blockRetunedSquare_two_eqv
#print axioms blockTwoIntegralStrongTuranAtTwo_false
#print axioms blockTwoPhysicalStrongTuran_false
#print axioms blockTwoIntegralStrongTuranAtFour_false
#print axioms blockTwoPhysicalStrongTuranFour_false
#print axioms noBlockCompatibleP2StrongTuranData
#print axioms noBlockCompatibleP2BoxStrongTuranData
#print axioms noBlockCompatibleP2HeadThreeTuranData
#print axioms noBlockCompatibleP2BoxHeadThreeTuranData

end YMGap.Continuum.P2BlockCompatibleStrongTuranObstruction
