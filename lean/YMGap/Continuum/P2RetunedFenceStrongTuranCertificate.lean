/-
Track 11.7-fusion / R2l -- integral certificates for the strong-Turan residual.

The common-denominator evaluator from `P2RetunedFenceIntegralCertificate`
reconstructs each physical coefficient from a natural number.  This module
uses that reconstruction twice, proves once that a cleared integer Turan
inequality implies the physical weighted-box inequality, and packages bounded
Boolean scans as `P2RetunedStrongTuran` data.

The checker is untrusted computation.  Only its general soundness theorem and
closed `by decide` results enter the proof graph.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2RetunedFenceIntegralCertificate
import YMGap.Continuum.P2RetunedStrongTuranCompiler

namespace YMGap.Continuum.P2RetunedFenceStrongTuranCertificate

set_option maxRecDepth 30000
set_option exponentiation.threshold 5000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2RetunedRatioCertificate
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedStrongTuranCompiler
open YMGap.Continuum.RebasedBulkLocalizationBridge

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Cleared strong-Turan atom at the physical fence.  Both bond-moved
coefficients carry the same `12^(2*C4(N))` scale, so it disappears from this
natural-number cross product. -/
def integralStrongTuranAt (N s : Nat) : Prop :=
  (((s + 2) * scaledCoeff N s) *
      ((s + 2) * scaledCoeff N (s + 2))) * 24 ^ 2 ≤
    23 ^ 2 *
      (((s + 3) * scaledCoeff N (s + 1)) *
        ((s + 1) * scaledCoeff N (s + 1)))

instance integralStrongTuranAtDecidable (N s : Nat) :
    Decidable (integralStrongTuranAt N s) := by
  unfold integralStrongTuranAt
  infer_instance

/-- A bounded scan beginning at the actual mode `start`. -/
def integralStrongTuranBlockCheck (N start length : Nat) : Bool :=
  (List.range length).all fun i =>
    decide (integralStrongTuranAt N (start + i))

/-- Soundness of one cleared integer atom.  The proof reconstructs all four
coefficient factors, regroups the two common scales, cancels their strictly
positive square, and leaves exactly the physical strong-Turan inequality. -/
theorem integralStrongTuranAt_sound {N s : Nat}
    (h : integralStrongTuranAt N s) :
    (dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 s) *
        (dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 2)) ≤
      (qpow (p2RetunedWeight RebasedBulkLocalizationBridge.fenceW) 2 *
          (dimQ (s + 2) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1))) *
        (dimQ s * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1)) := by
  let scale := Q'.ofNat (12 ^ (2 * c4 N))
  let x := dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 s
  let y := dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 2)
  let z := dimQ (s + 2) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1)
  let u := dimQ s * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1)
  let xn := (s + 2) * scaledCoeff N s
  let yn := (s + 2) * scaledCoeff N (s + 2)
  let zn := (s + 3) * scaledCoeff N (s + 1)
  let un := (s + 1) * scaledCoeff N (s + 1)
  let q2 := qpow (p2RetunedWeight RebasedBulkLocalizationBridge.fenceW) 2
  have hcross : xn * yn * 24 ^ 2 ≤ 23 ^ 2 * (zn * un) := by
    simpa only [xn, yn, zn, un] using h
  have hrat := ofNat_le_mkPos_mul_of_cross
    (xn * yn) (zn * un) (23 ^ 2) (24 ^ 2)
    (Nat.pow_pos (by decide)) hcross
  have hq2 : q2 ≈
      Q'.mkPos ((23 ^ 2 : Nat) : Int) (24 ^ 2) (Nat.pow_pos (by decide)) := by
    simpa only [q2] using qpow_retuned_eqv 2
  have hcore0 : Q'.ofNat (xn * yn) ≤
      q2 * Q'.ofNat (zn * un) :=
    Q'.le_trans' _ _ _ hrat (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm hq2)))
  have hcore : Q'.ofNat (xn * yn) ≤
      q2 * (Q'.ofNat zn * Q'.ofNat un) := by
    exact Q'.le_trans' _ _ _ hcore0 (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left q2 _ _
        (Q'.eqv_symm
          (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv zn un))))
  have hx : scale * x ≈ Q'.ofNat xn := by
    simpa only [scale, x, xn] using
      scale_dim_coeff_reconstruct N (s + 1) s
  have hy : scale * y ≈ Q'.ofNat yn := by
    simpa only [scale, y, yn] using
      scale_dim_coeff_reconstruct N (s + 1) (s + 2)
  have hz : scale * z ≈ Q'.ofNat zn := by
    simpa only [scale, z, zn] using
      scale_dim_coeff_reconstruct N (s + 2) (s + 1)
  have hu : scale * u ≈ Q'.ofNat un := by
    simpa only [scale, u, un] using
      scale_dim_coeff_reconstruct N s (s + 1)
  have hleft : (scale * x) * (scale * y) ≈ Q'.ofNat (xn * yn) :=
    Q'.eqv_trans _ _ _ (mul_eqv_both hx hy)
      (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv xn yn)
  have hright : q2 * ((scale * z) * (scale * u)) ≈
      q2 * (Q'.ofNat zn * Q'.ofNat un) :=
    Q'.mul_eqv_congr_left q2 _ _ (mul_eqv_both hz hu)
  have hscaled : (scale * x) * (scale * y) ≤
      q2 * ((scale * z) * (scale * u)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hright))
  let scaleSq := scale * scale
  have hleftRegroup : (scale * x) * (scale * y) ≈ scaleSq * (x * y) := by
    exact mul_four_regroup scale x scale y
  have hinnerRegroup : (scale * z) * (scale * u) ≈ scaleSq * (z * u) := by
    exact mul_four_regroup scale z scale u
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
  have hcancelReady : scaleSq * (x * y) ≤
      scaleSq * (q2 * (z * u)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleftRegroup)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrightRegroup))
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((12 ^ (2 * c4 N) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 12))
  have hscaleSq : (0 : Q') < scaleSq := Q'.mul_pos hscale hscale
  have hraw : x * y ≤ q2 * (z * u) :=
    Q'.le_of_mul_le_mul_left hcancelReady hscaleSq
  have htarget : (q2 * z) * u ≈ q2 * (z * u) :=
    Q'.mul_assoc_eqv q2 z u
  have hfinal : x * y ≤ (q2 * z) * u :=
    Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv htarget)
  simpa only [x, y, z, u, q2] using hfinal

/-- Soundness of one bounded integer scan. -/
theorem integralStrongTuranBlockCheck_sound {N start length s : Nat}
    (hcheck : integralStrongTuranBlockCheck N start length = true)
    (hlo : start ≤ s) (hhi : s < start + length) :
    (dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 s) *
        (dimQ (s + 1) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 2)) ≤
      (qpow (p2RetunedWeight RebasedBulkLocalizationBridge.fenceW) 2 *
          (dimQ (s + 2) * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1))) *
        (dimQ s * bondMovedCoeff N RebasedBulkLocalizationBridge.fenceW 2 (s + 1)) := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length := List.mem_range.mpr hi
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hsEq : start + (s - start) = s := by omega
  apply integralStrongTuranAt_sound
  simpa only [hsEq] using of_decide_eq_true hrow

/-- An edge atom plus a successful scan of `1 <= s`, `s+2 <= 2*N`
construct the exact strong-Turan datum. -/
def strongTuran_of_integralChecks (N : Nat)
    (hedge : integralTailAt N 1)
    (hcheck : integralStrongTuranBlockCheck N 1 (2 * N - 2) = true) :
    P2RetunedStrongTuran N RebasedBulkLocalizationBridge.fenceW
      RebasedBulkLocalizationBridge.fenceW_nonneg
      RebasedBulkLocalizationBridge.fenceW_le_one where
  edge := fun _ => integralTailAt_sound hedge
  turan := fun s hs hsupport =>
    integralStrongTuranBlockCheck_sound hcheck hs (by omega)

/-! ## Closed pilot certificate -/

theorem edgeN12 : integralTailAt 12 1 := by decide

theorem checkStrongN12 :
    integralStrongTuranBlockCheck 12 1 22 = true := by decide

def strongTuranN12 :
    P2RetunedStrongTuran 12 RebasedBulkLocalizationBridge.fenceW
      RebasedBulkLocalizationBridge.fenceW_nonneg
      RebasedBulkLocalizationBridge.fenceW_le_one :=
  strongTuran_of_integralChecks 12 edgeN12 checkStrongN12

def fenceRetunedControlN12ViaStrongTuran :
    RebasedBulkLocalizationBridge.CanonicalBulkControl 12
      RebasedBulkLocalizationBridge.fenceW 2 :=
  canonicalBulkControl_p2_of_strongTuran (by decide) (by decide)
    RebasedBulkLocalizationBridge.fenceW_le_one
    RebasedBulkLocalizationBridge.fenceW_near_continuum strongTuranN12

theorem edgeN40 : integralTailAt 40 1 := by decide

theorem checkStrongN40 :
    integralStrongTuranBlockCheck 40 1 78 = true := by decide

def strongTuranN40 :
    P2RetunedStrongTuran 40 RebasedBulkLocalizationBridge.fenceW
      RebasedBulkLocalizationBridge.fenceW_nonneg
      RebasedBulkLocalizationBridge.fenceW_le_one :=
  strongTuran_of_integralChecks 40 edgeN40 checkStrongN40

def fenceRetunedControlN40ViaStrongTuran :
    RebasedBulkLocalizationBridge.CanonicalBulkControl 40
      RebasedBulkLocalizationBridge.fenceW 2 :=
  canonicalBulkControl_p2_of_strongTuran (by decide) (by decide)
    RebasedBulkLocalizationBridge.fenceW_le_one
    RebasedBulkLocalizationBridge.fenceW_near_continuum strongTuranN40

end YMGap.Continuum.P2RetunedFenceStrongTuranCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.integralStrongTuranAt_sound
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.integralStrongTuranBlockCheck_sound
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.strongTuran_of_integralChecks
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.edgeN12
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.checkStrongN12
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.fenceRetunedControlN12ViaStrongTuran
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.edgeN40
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.checkStrongN40
#print axioms YMGap.Continuum.P2RetunedFenceStrongTuranCertificate.fenceRetunedControlN40ViaStrongTuran
