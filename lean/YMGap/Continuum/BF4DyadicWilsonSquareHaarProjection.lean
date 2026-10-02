/-
# Original Wilson energy with actual cutoff norms and retained gain

The perimeter-independent centered fourth-moment certificate contracts BOTH
omitted-mode costs into an explicit raw-source mass term and 9*rho times the
SAME raw centered square. The signed pin B=Z*OWNVar-C is retained, as are the
complete cubic, angular and Ward debts and the EXISTING projection gain.
Everything is normalized by the SAME original positive partition.

No favorable sign, useful scaling rate, physical calibration or continuum
survival is asserted. In particular raw H[q^2] is not the original partition.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderHaarProjection
import YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
import YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm

namespace YMGap.Continuum.BF4DyadicWilsonSquareHaarProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (pairCubicBudget)
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm (omittedRate)
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator (sourceHaarErrorBudget)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation (angularSquare)
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.SU2QuaternionCompleteRemainderProjection (projectionGain)
open YMGap.Continuum.SU2QuaternionCompleteRemainderHaarProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance normalizedWardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
  (quadraticRate centeredCorrection centered_sourceSquare_pin normalizedEnergy_centered_taylor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation (signedRemainder_generic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)
open YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain (normalizedProjectionGain)
open YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  sourceCharacter oddMass oddVariance

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- Explicit coupling/cutoff rate, with the fourth moment already discharged. -/
def haarVarianceRate (w : Q') (K : Nat) : Q' := quadraticRate w+9*omittedRate w K

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "q" => projectedEndpointSource w K width (terminalMessage w K width n)
local notation "psi" => oddCentered hw0 hw1 K width hK n f
local notation "Z" => oddMass w K width n
local notation "V" => oddVariance hw0 hw1 K width hK n f
local notation "C" => centeredCorrection hw0 hw1 K width hK n f

/-- All remaining numerator debts, with the centering correction SIGNED.
The raw-source mass is NOT replaced by the original interacting partition. -/
def haarCenteredDebt : Q' :=
  ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))*
    (pairCubicBudget (N width-1) q (polyMul q (polyMul psi psi))+
      pairCubicBudget (N width-1) (polyMul q psi) (polyMul q psi))+
    omittedRate w K*(HalfPow.half*H (N width) (polyMul q q))+
    ((1 : Q')-w)*((((1 : Q')-w)*((1 : Q')-w))*
      pairBudget (N width-1) q (polyMul q (angularSquare (N width-1) psi))) -
    haarVarianceRate w K*C

def normalizedHaarCenteredDebt : Q' :=
  haarCenteredDebt hw0 hw1 K width hK n scale hwidth*
    Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)

/-- The complete ORIGINAL Ward insertion is still subtracted with its sign. -/
def completeHaarCenteredDebt : Q' :=
  normalizedHaarCenteredDebt hw0 hw1 K width hK n scale hwidth-
    ((1 : Q')-w)*normalizedWardResidual hw0 hw1 K width hK n f

private theorem half_sixteen_collect (u b : Q') :
    HalfPow.half*(u+16*b)+b ≈ HalfPow.half*u+9*b :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.add (.var 1) (.mul (.const 16) (.var 2)))) (.var 2))
    (.add (.mul (.var 0) (.var 1))
      (.mul (.add (.mul (.var 0) (.const 16)) (.const 1)) (.var 2)))
    (by decide) (fun | 0 => HalfPow.half | 1 => u | _ => b))
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ b (by decide : HalfPow.half*16+1 ≈ (9 : Q'))))

/-- The actual Haar ceiling contracts its fourth moment into SAME variance.
No favorable sign is imposed on C, and all other numerator debts remain. -/
theorem paddedSquare_haarCeiling_le_varianceDebt :
    haarSquareCeiling (N width-1) w K q psi ≤
      haarVarianceRate w K*(Z*V)+haarCenteredDebt hw0 hw1 K width hK n scale hwidth := by
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let rho := omittedRate w K
  let B := H (N width) (polyMul (polyMul q psi) (polyMul q psi))
  let U := H (N width) (polyMul q q)
  let F := H (N width) (polyMul (polyMul q (polyMul psi psi)) (polyMul q (polyMul psi psi)))
  let D := ((h*h)*h)*(pairCubicBudget (N width-1) q (polyMul q (polyMul psi psi))+
    pairCubicBudget (N width-1) (polyMul q psi) (polyMul q psi))
  let T := h*((h*h)*pairBudget (N width-1) q (polyMul q (angularSquare (N width-1) psi)))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp : B ≈ Z*V-C := by
    have hp := centered_sourceSquare_pin hw0 hw1 K width hK n hf
      (paddedSquare_fringe_independent scale width hwidth)
    unfold sourceSquareMass observableSquare at hp
    simpa only [hN] using hp
  have hfour : F ≤ 16*B := paddedSquare_centered_fourth_le_sixteen_second
    hw0 hw1 K width hK n scale hwidth q (source_supported w K width n)
  have hrho : (0 : Q') ≤ rho := RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hpost := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_refl U)) hfour) HalfPow.half_nonneg)
    (Q'.le_of_eqv (Q'.eqv_refl B))
  have hbound := Q'.add_le_add
    (Q'.add_le_add_left (alpha*(quarter*B)) _ _
      (Q'.add_le_add_left D _ _ (Q'.mul_le_mul_of_nonneg_left _ _ rho hpost hrho)))
    (Q'.le_of_eqv (Q'.eqv_refl T))
  have hleft : haarSquareCeiling (N width-1) w K q psi ≈
      (alpha*(quarter*B)+(D+rho*(HalfPow.half*(U+F)+B)))+T := by
    unfold haarSquareCeiling sourceHaarErrorBudget sourceSquareMass observableSquare
    rw [hN]
    exact Q'.eqv_refl _
  have hcollect : (alpha*(quarter*B)+(D+rho*(HalfPow.half*(U+16*B)+B)))+T ≈
      haarVarianceRate w K*B+(D+rho*(HalfPow.half*U)+T) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_left _ _ _ (half_sixteen_collect U B)))) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.add (.var 3) (.mul (.var 4)
            (.add (.mul (.var 5) (.var 6)) (.mul (.const 9) (.var 2)))))) (.var 7))
        (.add (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.const 9) (.var 4))) (.var 2))
          (.add (.add (.var 3) (.mul (.var 4) (.mul (.var 5) (.var 6)))) (.var 7)))
        (by decide) (fun
          | 0 => alpha
          | 1 => quarter
          | 2 => B
          | 3 => D
          | 4 => rho
          | 5 => HalfPow.half
          | 6 => U
          | _ => T))
  have hright : haarVarianceRate w K*B+(D+rho*(HalfPow.half*U)+T) ≈
      haarVarianceRate w K*(Z*V)+haarCenteredDebt hw0 hw1 K width hK n scale hwidth :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hp) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))) (.var 4))
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.add (.var 4) (.neg (.mul (.var 0) (.var 3)))))
        (by decide) (fun
          | 0 => haarVarianceRate w K
          | 1 => Z
          | 2 => V
          | 3 => C
          | _ => D+rho*(HalfPow.half*U)+T))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hcollect hright)))

private theorem partition_cancel (a z v : Q') (hz : (0 : Q') < z) :
    (a*(z*v))*Q'.recipPos z hz ≈ a*v :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => z | 2 => v | _ => Q'.recipPos z hz))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz))
      (Q'.mul_one_eqv _))

/-- SAME partition, SAME centered source, and the EXISTING normalized gain. -/
theorem paddedSquare_remainder_haar_projection_bound (hquad : sufficientCutoff w ≤ K) :
    normalizedRemainder hw0 hw1 K width hK n psi ≤
      haarVarianceRate w K*V+normalizedHaarCenteredDebt hw0 hw1 K width hK n scale hwidth-
        (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
          normalizedProjectionGain hw0 hw1 K width hK n scale hwidth := by
  let alpha := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width-1+1) q := by
    simpa only [hN] using source_supported w K width n
  have hf : SupportedQuaternionBlocks (N width-1+1) psi := by
    simpa only [hN] using oddCentered_supported hw0 hw1 K width hK n
      (sourceCharacter_supported width _ 1)
  let g := projectionGain (N width-1) q psi Z (oddMass_positive hw0 hw1 K width hK n) hq hf
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)
  let E := haarCenteredDebt hw0 hw1 K width hK n scale hwidth
  have hb := completeRemainder_le_haar_projectionCeiling (N width-1) (Q'.le_of_lt hw0)
    hw1 K hquad q psi hq hf Z (oddMass_positive hw0 hw1 K width hK n)
  have hcap := Q'.add_le_add (paddedSquare_haarCeiling_le_varianceDebt
    hw0 hw1 K width hK n scale hwidth) (Q'.le_of_eqv (Q'.eqv_refl (-(alpha*g))))
  have hraw := Q'.le_trans' _ _ _ (Q'.le_of_eqv (signedRemainder_generic w K width n psi))
    (Q'.le_trans' _ _ _ hb hcap)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ r hraw (Q'.le_of_lt (Q'.recipPos_pos Z _))
  have halg : ((haarVarianceRate w K*(Z*V)+E)-alpha*g)*r ≈
      (haarVarianceRate w K*(Z*V))*r+E*r-alpha*(g*r) :=
    poly_identity_of_normal_eq
      (.mul (.add (.add (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.var 4))
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))
        (.neg (.mul (.var 2) (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => haarVarianceRate w K*(Z*V)
        | 1 => E
        | 2 => alpha
        | 3 => g
        | _ => r)
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ halg
    (Q'.add_eqv_congr' (Q'.add_eqv_congr'
      (partition_cancel (haarVarianceRate w K) Z V _) (Q'.eqv_refl _)) (Q'.eqv_refl _))))

/-- Actual original growing-loop energy: no raw fourth moment remains.
The complete signed cubic, angular, Ward and centering debts remain OPEN. -/
theorem paddedSquare_energy_haar_projection_bound (hquad : sufficientCutoff w ≤ K) :
    normalizedEnergy hw0 hw1 K width hK n f ≤
      ((12*Q'.ofNat (side scale))*((1 : Q')-w)+haarVarianceRate w K)*V+
        completeHaarCenteredDebt hw0 hw1 K width hK n scale hwidth-
          (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
            normalizedProjectionGain hw0 hw1 K width hK n scale hwidth := by
  let A := normalizedAngular hw0 hw1 K width hK n f
  let W := normalizedWardResidual hw0 hw1 K width hK n f
  let D := normalizedHaarCenteredDebt hw0 hw1 K width hK n scale hwidth
  let h := (1 : Q')-w
  let k := (12 : Q')*Q'.ofNat (side scale)
  let beta := haarVarianceRate w K
  let J := (HalfPow.half*(h*h))*normalizedProjectionGain hw0 hw1 K width hK n scale hwidth
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hind := paddedSquare_fringe_independent scale width hwidth
  have hward := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have hupper := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedEnergy_centered_taylor hw0 hw1 K width hK n hf hind))
    (Q'.add_le_add_left (h*A) _ _
      (paddedSquare_remainder_haar_projection_bound hw0 hw1 K width hK n scale hwidth hquad))
  have hjoin : h*A+(beta*V+D-J) ≈ h*(A+W)+beta*V+(D-h*W)-J :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.add (.add (.mul (.var 4) (.var 3)) (.var 5)) (.neg (.var 6))))
      (.add (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 4) (.var 3))) (.add (.var 5) (.neg (.mul (.var 0) (.var 2))))) (.neg (.var 6)))
      (by decide) (fun | 0 => h | 1 => A | 2 => W | 3 => V | 4 => beta | 5 => D | _ => J)
  exact Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hjoin
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hward)
        (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.var 2))) (.var 4)) (.neg (.var 5)))
        (.add (.add (.mul (.add (.mul (.var 1) (.var 0)) (.var 3)) (.var 2)) (.var 4)) (.neg (.var 5)))
        (by decide) (fun | 0 => h | 1 => k | 2 => V | 3 => beta | 4 => D-h*W | _ => J)))))

#print axioms haarVarianceRate
#print axioms haarCenteredDebt
#print axioms normalizedHaarCenteredDebt
#print axioms completeHaarCenteredDebt
#print axioms paddedSquare_haarCeiling_le_varianceDebt
#print axioms paddedSquare_remainder_haar_projection_bound
#print axioms paddedSquare_energy_haar_projection_bound

end YMGap.Continuum.BF4DyadicWilsonSquareHaarProjection
