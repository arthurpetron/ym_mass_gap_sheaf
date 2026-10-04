/-
# Joint exact heat / original angular payment with quadratic scalar residue

Keep the original raw second moment until its cap-four deficit is pinned to
the SAME odd-marginal angular energy. The exact heat cancellation has no
linear scalar residue: ad-4k is bounded by 36*(1-w^(4*side))^2. Actual channel
heat loss, original angular energy and COMPLETE signed chronological cost
remain unpaid, not replaced by the filtered-start norm or assumed small.
This is not a justified scaling trajectory, survival or physical gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeChronologicalExactChannelCost
import YMGap.Continuum.BF4DyadicWilsonSquareWardMoments
import YMGap.Continuum.SU2HeatExactSquareCreditWindow

namespace YMGap.Continuum.BF4DyadicWilsonSquareJointQuadraticDebt

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence (normalizedMoment_congr)
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
  (normalizedMoment_add normalizedMoment_one)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter sourceWord)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_pin marginalMass_positive marginalMoment_pin oddVariance normalizedWardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor (normalizedAngular)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareWardMoments (squareMoment paddedSquare_angular)
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry (squareChannelMass)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse (squareChannelIncrement)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
  (squareOriginalRawSecondMoment channelHeatLoss
    paddedSquare_energy_rawSecond_joint_increment_payment)
open YMGap.Continuum.SU2HeatExactSquareCreditWindow
  (exactSquareCredit exactSquareCredit_massResidual_quadratic_upper)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit (originalOwnBlockCost)
open YMGap.Continuum.BF4WilsonAllNomeChronologicalExactChannelCost
  (originalOwnBlockCost_energy_split originalBoundaryDrift_upper
    originalBoundaryDrift originalReferenceSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
  (normalizedSignedMultiplicationCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks terminalMessage sourceCharacter marginalWeight
  oddMass normalizedEnergy normalizedAngular squareOriginalRawSecondMoment
  squareChannelMass channelHeatLoss originalOwnBlockCost normalizedSignedMultiplicationCost

private theorem qpow_rg (w : Q') : ∀ n,
    qpow w n = YMGap.Continuum.RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun z : Q' => z*w) (qpow_rg w n)

/-- Cap-four deficit is the ACTUAL original angular energy per perimeter,
with the same odd partition. No mean, density or filtered source is changed. -/
theorem paddedSquare_rawSecond_deficit_angular_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width depth)
      (oddMass_positive hw0 hw1 K width hK depth)
    (4*Q'.ofNat (side scale))*(4-squareOriginalRawSecondMoment w K width depth scale hwidth*r) ≈
      normalizedAngular hw0 hw1 K width hK depth f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let W := marginalWeight w K width depth
  let U := squareOriginalRawSecondMoment w K width depth scale hwidth
  let Z := oddMass w K width depth
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  let m2 := squareMoment hw0 hw1 K width hK depth scale hwidth 2
  let per := 4*Q'.ofNat (side scale)
  let hW := marginalMass_positive hw0 hw1 K width hK depth
  have hfusion : RatPolyCoeffEqv (polyMul f f)
      (polyAdd polyOne (sourceCharacter width (paddedSquare scale width hwidth).edges 2)) := by
    unfold f sourceCharacter
    exact first_character_square (sourceWord width (paddedSquare scale width hwidth).edges).scalar
  have hU : U*r ≈ normalizedMoment (N width) W (polyMul f f) hW := by
    unfold U squareOriginalRawSecondMoment normalizedMoment
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.recipPos_eqv_congr Z _ (oddMass_positive hw0 hw1 K width hK depth) hW
        (marginalMass_pin w K width depth).symm)
  have hsecond : U*r ≈ 1+m2 := Q'.eqv_trans _ _ _ hU
    (Q'.eqv_trans _ _ _ (normalizedMoment_congr hW hW (.refl W) hfusion)
      (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
        (Q'.add_eqv_congr' (normalizedMoment_one hW)
          (marginalMoment_pin hw0 hw1 K width hK depth _))))
  have hshape : per*(4-U*r) ≈ per*(3-m2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left per _ _
      (Q'.add_eqv_congr_left 4 _ _ (Q'.neg_eqv_congr _ _ hsecond)))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.const 4) (.neg (.add (.const 1) (.var 1)))))
        (.mul (.var 0) (.add (.const 3) (.neg (.var 1))))
        (by decide) (fun | 0 => per | _ => m2))
  exact Q'.eqv_trans _ _ _ hshape
    (paddedSquare_angular hw0 hw1 K width hK depth scale hwidth).symm

/-- SAME original energy: the scalar part is quadratic, and BOTH actual
heat loss and original angular energy remain explicit. ENTIRE increment
and extra nonnegative increment credit are retained. -/
theorem paddedSquare_energy_joint_quadratic_angular_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width)
    (hk : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width depth)
      (oddMass_positive hw0 hw1 K width hK depth)
    let a := qpow w (12*side scale)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth depth*r
    per*((1+beta)*(4*normalizedEnergy hw0 hw1 K width hK depth f+I)+(HalfPow.half*k)*I) ≤
      144*per*(h*h)+4*per*a*(1-beta)*(channelHeatLoss w K width depth scale hwidth*r)+
        4*k*normalizedAngular hw0 hw1 K width hK depth f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let Z := oddMass w K width depth
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  let a := qpow w (12*side scale)
  let beta := qpow w (32*side scale)
  let k := exactSquareCredit w (side scale)
  let h := (1 : Q')-qpow w (4*side scale)
  let per := 4*Q'.ofNat (side scale)
  let e := energy w K width (terminalMessage w K width depth) f
  let E := normalizedEnergy hw0 hw1 K width hK depth f
  let iraw := squareChannelIncrement w K scale width hwidth depth
  let U := squareOriginalRawSecondMoment w K width depth scale hwidth
  let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
  let L := channelHeatLoss w K width depth scale hwidth
  let Ang := normalizedAngular hw0 hw1 K width hK depth f
  let P := (1+beta)*(4*E+iraw*r)+(HalfPow.half*k)*(iraw*r)
  have hper : (0 : Q') ≤ per := Q'.mul_nonneg 4 _ (by decide)
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have he : e*r ≈ E := by unfold E normalizedEnergy; exact Q'.eqv_refl _
  have hraw := Q'.mul_le_mul_of_nonneg_right _ _ r
    (paddedSquare_energy_rawSecond_joint_increment_payment
      hw0 hw1 K width hK h2 depth scale hwidth hk)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hnorm : ((1+beta)*(4*e+iraw)+(HalfPow.half*k)*iraw+4*k*U)*r ≈
      P+4*k*(U*r) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.add (.mul (.var 0) (.add (.mul (.const 4) (.var 1)) (.var 2)))
        (.mul (.var 3) (.var 2))) (.mul (.var 4) (.var 5))) (.var 6))
      (.add (.add (.mul (.var 0) (.add (.mul (.const 4) (.mul (.var 1) (.var 6)))
        (.mul (.var 2) (.var 6)))) (.mul (.var 3) (.mul (.var 2) (.var 6))))
        (.mul (.var 4) (.mul (.var 5) (.var 6))))
      (by decide) (fun
        | 0 => 1+beta | 1 => e | 2 => iraw | 3 => HalfPow.half*k
        | 4 => 4*k | 5 => U | _ => r))
      (Q'.add_eqv_congr_right _ _ (4*k*(U*r))
        (Q'.add_eqv_congr_right _ _ ((HalfPow.half*k)*(iraw*r))
          (Q'.mul_eqv_congr_left (1+beta) _ _
            (Q'.add_eqv_congr_right _ _ (iraw*r) (Q'.mul_eqv_congr_left 4 _ _ he)))))
  have hpaid : P+4*k*(U*r) ≤ 4*a*(1-beta)*(M*r) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnorm)
      (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.mul_assoc_eqv _ M r)))
  have hsub := Q'.add_le_add_right _ _ (-(4*k*(U*r))) hpaid
  have hleft : P+4*k*(U*r)+ -(4*k*(U*r)) ≈ P :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => P | _ => 4*k*(U*r))
  have hsmall : P ≤ 4*a*(1-beta)*(M*r)-4*k*(U*r) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hsub
  have hbase := Q'.mul_le_mul_of_nonneg_left _ _ per hsmall hper
  have hm : M ≈ Z+L := by
    unfold L channelHeatLoss
    exact poly_identity_of_normal_eq (.var 0)
      (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => M | _ => Z)
  have hmass : M*r ≈ 1+L*r := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r hm)
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv Z L r)
      (Q'.add_eqv_congr_right _ _ (L*r) (Q'.mul_recipPos_eqv Z _)))
  have hang : per*(4-U*r) ≈ Ang :=
    paddedSquare_rawSecond_deficit_angular_pin hw0 hw1 K width hK depth scale hwidth
  have hshape : per*(4*a*(1-beta)*(M*r)-4*k*(U*r)) ≈
      4*per*(a*(1-beta)-4*k)+4*per*a*(1-beta)*(L*r)+4*k*Ang :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left per _ _
      (Q'.add_eqv_congr_right _ _ (-(4*k*(U*r)))
        (Q'.mul_eqv_congr_left (4*a*(1-beta)) _ _ hmass)))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.mul (.mul (.mul (.const 4) (.var 1)) (.var 2))
          (.add (.const 1) (.var 5))) (.neg (.mul (.mul (.const 4) (.var 3)) (.var 4)))))
        (.add (.add (.mul (.mul (.const 4) (.var 0))
          (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.const 4) (.var 3)))))
          (.mul (.mul (.mul (.mul (.const 4) (.var 0)) (.var 1)) (.var 2)) (.var 5)))
          (.mul (.mul (.const 4) (.var 3)) (.mul (.var 0) (.add (.const 4) (.neg (.var 4))))))
        (by decide) (fun
          | 0 => per | 1 => a | 2 => 1-beta | 3 => k | 4 => U*r | _ => L*r))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left (4*k) _ _ hang)))
  have hquadratic := Q'.mul_le_mul_of_nonneg_left _ _ (4*per)
    (exactSquareCredit_massResidual_quadratic_upper hw0 hw1 (side scale))
    (Q'.mul_nonneg 4 per (by decide) hper)
  have h144 : (4*per)*(36*(h*h)) ≈ 144*per*(h*h) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 4) (.var 0)) (.mul (.const 36) (.var 1)))
      (.mul (.mul (.const 144) (.var 0)) (.var 1))
      (by decide) (fun | 0 => per | _ => h*h)
  exact Q'.le_trans' _ _ _ hbase (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
    (Q'.add_le_add_right _ _ (4*k*Ang) (Q'.add_le_add_right _ _ _
      (Q'.le_trans' _ _ _ hquadratic (Q'.le_of_eqv h144)))))

/-- The quadratic scalar cancellation reaches the SAME chronological cost,
preserving BOTH partitions and stage OWN center. ONLY drift is paid; actual
loss, original angular cost and COMPLETE Signed remain on the right. -/
theorem originalOwnBlockCost_joint_quadratic_angular_boundary_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (stage t : Nat)
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ headCutoff w+stage)
    (hk : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    let K := headCutoff w+stage
    let hK := Nat.le_add_right (headCutoff w) stage
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width (stage+t))
      (oddMass_positive hw0 hw1 K width hK (stage+t))
    let a := qpow w (12*side scale)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
    per*((1+beta)*(4*originalOwnBlockCost hw0 hw1 scale width hwidth stage t+I)+(HalfPow.half*k)*I) ≤
      144*per*(h*h)+4*per*a*(1-beta)*(channelHeatLoss w K width (stage+t) scale hwidth*r)+
        4*k*normalizedAngular hw0 hw1 K width hK (stage+t) f+
        4*per*(1+beta)*(comparisonEta hw0 hw1 width (stage+t-1)*
          originalReferenceSquare hw0 hw1 scale width hwidth stage t+
          normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f) := by
  dsimp only
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let r := Q'.recipPos (oddMass w K width (stage+t))
    (oddMass_positive hw0 hw1 K width hK (stage+t))
  let beta := qpow w (32*side scale)
  let k := exactSquareCredit w (side scale)
  let per := 4*Q'.ofNat (side scale)
  let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
  let E := normalizedEnergy hw0 hw1 K width hK (stage+t) f
  let D := originalBoundaryDrift hw0 hw1 scale width hwidth stage t
  let S := normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f
  let Cost := originalOwnBlockCost hw0 hw1 scale width hwidth stage t
  let B := comparisonEta hw0 hw1 width (stage+t-1)*
    originalReferenceSquare hw0 hw1 scale width hwidth stage t
  let P := per*((1+beta)*(4*E+I)+(HalfPow.half*k)*I)
  have hper : (0 : Q') ≤ per := Q'.mul_nonneg 4 _ (by decide)
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have hbeta : (0 : Q') ≤ beta := by
    dsimp only [beta]
    rw [qpow_rg]
    exact YMGap.Continuum.RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hcoef : (0 : Q') ≤ 4*per*(1+beta) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg 4 per (by decide) hper)
      (Q'.zero_le_add 1 beta (by decide) hbeta)
  have hcost : Cost ≈ E+D+S :=
    originalOwnBlockCost_energy_split hw0 hw1 scale width hwidth stage t
  have hshape : per*((1+beta)*(4*Cost+I)+(HalfPow.half*k)*I) ≈
      P+4*per*(1+beta)*(D+S) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left per _ _
      (Q'.add_eqv_congr_right _ _ ((HalfPow.half*k)*I)
        (Q'.mul_eqv_congr_left (1+beta) _ _
          (Q'.add_eqv_congr_right _ _ I (Q'.mul_eqv_congr_left 4 _ _ hcost)))))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.mul (.var 1) (.add (.mul (.const 4)
          (.add (.add (.var 2) (.var 3)) (.var 4))) (.var 5))) (.mul (.var 6) (.var 5))))
        (.add (.mul (.var 0) (.add (.mul (.var 1) (.add (.mul (.const 4) (.var 2)) (.var 5)))
          (.mul (.var 6) (.var 5))))
          (.mul (.mul (.mul (.const 4) (.var 0)) (.var 1)) (.add (.var 3) (.var 4))))
        (by decide) (fun
          | 0 => per | 1 => 1+beta | 2 => E | 3 => D | 4 => S
          | 5 => I | _ => HalfPow.half*k))
  have hcorrection : 4*per*(1+beta)*(D+S) ≤ 4*per*(1+beta)*(B+S) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_right _ _ S
        (originalBoundaryDrift_upper hw0 hw1 scale width hwidth stage t hdepth)) hcoef
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
    (Q'.add_le_add
      (paddedSquare_energy_joint_quadratic_angular_payment hw0 hw1 K width hK h2
        (stage+t) scale hwidth hk) hcorrection)

/-- Full original Ward substitution exposes the SIGNED loss-minus-Ward
combination. No sign or bound is assigned to Ward. Endpoint OWN variance
and the chronological filtered-start variance remain distinct. -/
theorem originalOwnBlockCost_joint_quadratic_ward_boundary_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (stage t : Nat)
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ headCutoff w+stage)
    (hk : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    let K := headCutoff w+stage
    let hK := Nat.le_add_right (headCutoff w) stage
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width (stage+t))
      (oddMass_positive hw0 hw1 K width hK (stage+t))
    let a := qpow w (12*side scale)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
    per*((1+beta)*(4*originalOwnBlockCost hw0 hw1 scale width hwidth stage t+I)+(HalfPow.half*k)*I)+
        4*k*normalizedWardResidual hw0 hw1 K width hK (stage+t) f ≤
      144*per*(h*h)+4*per*a*(1-beta)*(channelHeatLoss w K width (stage+t) scale hwidth*r)+
        12*per*k*oddVariance hw0 hw1 K width hK (stage+t) f+
        4*per*(1+beta)*(comparisonEta hw0 hw1 width (stage+t-1)*
          originalReferenceSquare hw0 hw1 scale width hwidth stage t+
          normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f) := by
  dsimp only
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let r := Q'.recipPos (oddMass w K width (stage+t))
    (oddMass_positive hw0 hw1 K width hK (stage+t))
  let a := qpow w (12*side scale)
  let beta := qpow w (32*side scale)
  let k := exactSquareCredit w (side scale)
  let h := (1 : Q')-qpow w (4*side scale)
  let per := 4*Q'.ofNat (side scale)
  let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
  let Ang := normalizedAngular hw0 hw1 K width hK (stage+t) f
  let W := normalizedWardResidual hw0 hw1 K width hK (stage+t) f
  let V := oddVariance hw0 hw1 K width hK (stage+t) f
  let R := 144*per*(h*h)+4*per*a*(1-beta)*(channelHeatLoss w K width (stage+t) scale hwidth*r)
  let C := 4*per*(1+beta)*(comparisonEta hw0 hw1 width (stage+t-1)*
    originalReferenceSquare hw0 hw1 scale width hwidth stage t+
    normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f)
  have hp := Q'.add_le_add_right _ _ (4*k*W)
    (originalOwnBlockCost_joint_quadratic_angular_boundary_paid hw0 hw1 scale width hwidth stage t
      hdepth h2 hk)
  have hcredit : 4*k*(Ang+W) ≈ 12*per*k*V :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (4*k) _ _
      (paddedSquare_normalized_ward hw0 hw1 K width hK (stage+t) scale hwidth))
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.var 0)) (.mul (.mul (.const 12) (.var 1)) (.var 2)))
        (.mul (.mul (.mul (.const 12) (.mul (.const 4) (.var 1))) (.var 0)) (.var 2))
        (by decide) (fun | 0 => k | 1 => Q'.ofNat (side scale) | _ => V))
  have hr : R+4*k*Ang+C+4*k*W ≈ R+12*per*k*V+C :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.mul (.mul (.const 4) (.var 1)) (.var 2))) (.var 3))
        (.mul (.mul (.const 4) (.var 1)) (.var 4)))
      (.add (.add (.var 0) (.mul (.mul (.const 4) (.var 1)) (.add (.var 2) (.var 4)))) (.var 3))
      (by decide) (fun | 0 => R | 1 => k | 2 => Ang | 3 => C | _ => W))
      (Q'.add_eqv_congr_right _ _ C (Q'.add_eqv_congr_left R _ _ hcredit))
  exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv hr)

#print axioms paddedSquare_rawSecond_deficit_angular_pin
#print axioms paddedSquare_energy_joint_quadratic_angular_payment
#print axioms originalOwnBlockCost_joint_quadratic_angular_boundary_paid
#print axioms originalOwnBlockCost_joint_quadratic_ward_boundary_paid

end YMGap.Continuum.BF4DyadicWilsonSquareJointQuadraticDebt
