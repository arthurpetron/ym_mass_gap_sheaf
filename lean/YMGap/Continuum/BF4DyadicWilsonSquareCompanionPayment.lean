/-
# Original chronological payment retaining the source companion

The actual companion cancels the unweighted linear channel-loss residue.
The remaining cap defect is computed from the SAME source and Wilson
observable. Its smallness is NOT assumed or proved here: it contains the
whole increment and endpoint cap deficits. The scalar quadratic ceiling
multiplies the ACTUAL channel mass / odd partition ratio, not one.
Stage OWN center, BOTH partitions and COMPLETE signed cost are unchanged.
No scaling, survival, physical gap or Clay closure follows.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit

namespace YMGap.Continuum.BF4DyadicWilsonSquareCompanionPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor (normalizedAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance normalizedWardResidual)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
  (squareChannelMass squareChannelMass_nonnegative)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse (squareChannelIncrement)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss (squareOriginalRawSecondMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit
  (squareChannelCapDeficit squareChannelObservedLoss
    squareChannelCapDeficit_eq_increment_observedLoss_pin
    paddedSquare_energy_companion_capDeficit_pin)
open YMGap.Continuum.BF4DyadicWilsonSquareJointQuadraticDebt
  (paddedSquare_rawSecond_deficit_angular_pin)
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)
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

attribute [local irreducible] terminalMessage sourceCharacter oddMass normalizedEnergy energy
  normalizedAngular squareChannelMass squareOriginalRawSecondMoment
  squareChannelCapDeficit squareChannelObservedLoss squareChannelIncrement
  originalOwnBlockCost normalizedSignedMultiplicationCost

private theorem qpow_rg (w : Q') : ∀ n,
    qpow w n = YMGap.Continuum.RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun z : Q' => z*w) (qpow_rg w n)

/-- SAME original energy, with computed source-coupled deficit. No sign
guard on k is needed for this exact cancellation followed by a scalar upper
bound; interpreting k times a square as favorable credit DOES need k>=0. -/
theorem paddedSquare_energy_companion_quadratic_angular_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width depth)
      (oddMass_positive hw0 hw1 K width hK depth)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth depth*r
    let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
    let D := squareChannelCapDeficit w K scale width hwidth depth*r
    per*((1+beta)*(4*normalizedEnergy hw0 hw1 K width hK depth f+I)+(HalfPow.half*k)*I) ≤
      144*per*(h*h)*(M*r)+4*k*normalizedAngular hw0 hw1 K width hK depth f+
        (per*(HalfPow.half*k))*D := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let Z := oddMass w K width depth
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  let a := qpow w (12*side scale)
  let beta := qpow w (32*side scale)
  let k := exactSquareCredit w (side scale)
  let F := a*(1-beta)-4*k
  let h := (1 : Q')-qpow w (4*side scale)
  let per := 4*Q'.ofNat (side scale)
  let e := energy w K width (terminalMessage w K width depth) f
  let E := normalizedEnergy hw0 hw1 K width hK depth f
  let I := squareChannelIncrement w K scale width hwidth depth
  let U := squareOriginalRawSecondMoment w K width depth scale hwidth
  let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
  let D := squareChannelCapDeficit w K scale width hwidth depth
  let Ang := normalizedAngular hw0 hw1 K width hK depth f
  let P := (1+beta)*(4*E+I*r)+(HalfPow.half*k)*(I*r)
  have hper : (0 : Q') ≤ per := Q'.mul_nonneg 4 _ (by decide)
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have hM : (0 : Q') ≤ M := squareChannelMass_nonnegative (Q'.le_of_lt hw0)
    K scale width hwidth _ (terminalMessage_supported w K width depth)
  have hMr : (0 : Q') ≤ M*r := Q'.mul_nonneg _ _ hM
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have he : e*r ≈ E := by unfold E normalizedEnergy; exact Q'.eqv_refl _
  have hraw := Q'.mul_eqv_congr_right _ _ r
    (paddedSquare_energy_companion_capDeficit_pin (w := w) K width h2 depth scale hwidth)
  have hl : ((1+beta)*(4*e+I)+(HalfPow.half*k)*I)*r ≈ P :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.add (.mul (.const 4) (.var 1)) (.var 2)))
        (.mul (.var 3) (.var 2))) (.var 4))
      (.add (.mul (.var 0) (.add (.mul (.const 4) (.mul (.var 1) (.var 4)))
        (.mul (.var 2) (.var 4)))) (.mul (.var 3) (.mul (.var 2) (.var 4))))
      (by decide) (fun | 0 => 1+beta | 1 => e | 2 => I | 3 => HalfPow.half*k | _ => r))
      (Q'.add_eqv_congr_right _ _ ((HalfPow.half*k)*(I*r))
        (Q'.mul_eqv_congr_left (1+beta) _ _
          (Q'.add_eqv_congr_right _ _ (I*r) (Q'.mul_eqv_congr_left 4 _ _ he))))
  have hr : (4*F*M+4*k*(4*Z-U)+(HalfPow.half*k)*D)*r ≈
      4*F*(M*r)+4*k*(4-U*r)+(HalfPow.half*k)*(D*r) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.mul (.const 4) (.var 2)) (.add (.mul (.const 4) (.var 3)) (.neg (.var 4)))))
        (.mul (.var 5) (.var 6))) (.var 7))
      (.add (.add (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.var 7)))
        (.mul (.mul (.const 4) (.var 2))
          (.add (.mul (.const 4) (.mul (.var 3) (.var 7))) (.neg (.mul (.var 4) (.var 7))))))
        (.mul (.var 5) (.mul (.var 6) (.var 7))))
      (by decide) (fun | 0 => F | 1 => M | 2 => k | 3 => Z | 4 => U | 5 => HalfPow.half*k | 6 => D | _ => r))
      (Q'.add_eqv_congr_right _ _ ((HalfPow.half*k)*(D*r))
        (Q'.add_eqv_congr_left (4*F*(M*r)) _ _
          (Q'.mul_eqv_congr_left (4*k) _ _
            (Q'.add_eqv_congr_right _ _ (-(U*r))
              (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _
                (Q'.mul_recipPos_eqv Z (oddMass_positive hw0 hw1 K width hK depth)))
                (Q'.mul_one_eqv 4))))))
  have hang : per*(4-U*r) ≈ Ang :=
    paddedSquare_rawSecond_deficit_angular_pin hw0 hw1 K width hK depth scale hwidth
  have hshape : per*P ≈ (4*per*(M*r))*F+4*k*Ang+(per*(HalfPow.half*k))*(D*r) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left per _ _
      (Q'.eqv_trans _ _ _ hl.symm (Q'.eqv_trans _ _ _ hraw hr)))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.add (.mul (.mul (.const 4) (.var 1)) (.var 2))
          (.mul (.mul (.const 4) (.var 3)) (.var 4))) (.mul (.var 5) (.var 6))))
        (.add (.add (.mul (.mul (.mul (.const 4) (.var 0)) (.var 2)) (.var 1))
          (.mul (.mul (.const 4) (.var 3)) (.mul (.var 0) (.var 4))))
          (.mul (.mul (.var 0) (.var 5)) (.var 6)))
        (by decide) (fun | 0 => per | 1 => F | 2 => M*r | 3 => k | 4 => 4-U*r | 5 => HalfPow.half*k | _ => D*r))
        (Q'.add_eqv_congr_right _ _ ((per*(HalfPow.half*k))*(D*r))
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left (4*k) _ _ hang))))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ (4*per*(M*r))
    (exactSquareCredit_massResidual_quadratic_upper hw0 hw1 (side scale))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg 4 per (by decide) hper) hMr)
  have h144 : (4*per*(M*r))*(36*(h*h)) ≈ 144*per*(h*h)*(M*r) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 4) (.var 0)) (.var 1)) (.mul (.const 36) (.var 2)))
      (.mul (.mul (.mul (.const 144) (.var 0)) (.var 2)) (.var 1))
      (by decide) (fun | 0 => per | 1 => M*r | _ => h*h)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
    (Q'.add_le_add_right _ _ ((per*(HalfPow.half*k))*(D*r))
      (Q'.add_le_add_right _ _ (4*k*Ang)
        (Q'.le_trans' _ _ _ hquad (Q'.le_of_eqv h144))))

/-- Actual chronological and OWN Ward consumer. ONLY boundary drift is
paid. Source-coupled deficit, COMPLETE Signed and signed Ward remain, and
endpoint OWN variance is not identified with the filtered-start norm. -/
theorem originalOwnBlockCost_companion_quadratic_ward_boundary_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (stage t : Nat)
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ headCutoff w+stage) :
    let K := headCutoff w+stage
    let hK := Nat.le_add_right (headCutoff w) stage
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width (stage+t))
      (oddMass_positive hw0 hw1 K width hK (stage+t))
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
    let M := squareChannelMass w K scale width hwidth (terminalMessage w K width (stage+t))
    let D := squareChannelCapDeficit w K scale width hwidth (stage+t)*r
    per*((1+beta)*(4*originalOwnBlockCost hw0 hw1 scale width hwidth stage t+I)+(HalfPow.half*k)*I)+
        4*k*normalizedWardResidual hw0 hw1 K width hK (stage+t) f ≤
      144*per*(h*h)*(M*r)+12*per*k*oddVariance hw0 hw1 K width hK (stage+t) f+
        (per*(HalfPow.half*k))*D+
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
  let h := (1 : Q')-qpow w (4*side scale)
  let per := 4*Q'.ofNat (side scale)
  let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
  let E := normalizedEnergy hw0 hw1 K width hK (stage+t) f
  let Drift := originalBoundaryDrift hw0 hw1 scale width hwidth stage t
  let S := normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f
  let Cost := originalOwnBlockCost hw0 hw1 scale width hwidth stage t
  let B := comparisonEta hw0 hw1 width (stage+t-1)*
    originalReferenceSquare hw0 hw1 scale width hwidth stage t
  let Ang := normalizedAngular hw0 hw1 K width hK (stage+t) f
  let W := normalizedWardResidual hw0 hw1 K width hK (stage+t) f
  let V := oddVariance hw0 hw1 K width hK (stage+t) f
  let M := squareChannelMass w K scale width hwidth (terminalMessage w K width (stage+t))
  let D := squareChannelCapDeficit w K scale width hwidth (stage+t)*r
  let R := 144*per*(h*h)*(M*r)
  let DC := (per*(HalfPow.half*k))*D
  let C := 4*per*(1+beta)*(B+S)
  let P := per*((1+beta)*(4*E+I)+(HalfPow.half*k)*I)
  have hper : (0 : Q') ≤ per := Q'.mul_nonneg 4 _ (by decide)
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have hbeta : (0 : Q') ≤ beta := by
    dsimp only [beta]; rw [qpow_rg]
    exact YMGap.Continuum.RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hcoef : (0 : Q') ≤ 4*per*(1+beta) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg 4 per (by decide) hper)
      (Q'.zero_le_add 1 beta (by decide) hbeta)
  have hcost : Cost ≈ E+Drift+S :=
    originalOwnBlockCost_energy_split hw0 hw1 scale width hwidth stage t
  have hshape : per*((1+beta)*(4*Cost+I)+(HalfPow.half*k)*I) ≈
      P+4*per*(1+beta)*(Drift+S) :=
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
        (by decide) (fun | 0 => per | 1 => 1+beta | 2 => E | 3 => Drift | 4 => S | 5 => I | _ => HalfPow.half*k))
  have hcorrection : 4*per*(1+beta)*(Drift+S) ≤ C :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_right _ _ S
        (originalBoundaryDrift_upper hw0 hw1 scale width hwidth stage t hdepth)) hcoef
  have hp : per*((1+beta)*(4*Cost+I)+(HalfPow.half*k)*I) ≤ R+4*k*Ang+DC+C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
      (Q'.add_le_add
        (paddedSquare_energy_companion_quadratic_angular_payment hw0 hw1 K width hK h2
          (stage+t) scale hwidth) hcorrection)
  have hward : 4*k*(Ang+W) ≈ 12*per*k*V :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (4*k) _ _
      (paddedSquare_normalized_ward hw0 hw1 K width hK (stage+t) scale hwidth))
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.var 0)) (.mul (.mul (.const 12) (.var 1)) (.var 2)))
        (.mul (.mul (.mul (.const 12) (.mul (.const 4) (.var 1))) (.var 0)) (.var 2))
        (by decide) (fun | 0 => k | 1 => Q'.ofNat (side scale) | _ => V))
  have hr : R+4*k*Ang+DC+C+4*k*W ≈ R+12*per*k*V+DC+C :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.add (.add (.var 0) (.mul (.mul (.const 4) (.var 1)) (.var 2)))
        (.var 3)) (.var 4)) (.mul (.mul (.const 4) (.var 1)) (.var 5)))
      (.add (.add (.add (.var 0) (.mul (.mul (.const 4) (.var 1))
        (.add (.var 2) (.var 5)))) (.var 3)) (.var 4))
      (by decide) (fun | 0 => R | 1 => k | 2 => Ang | 3 => DC | 4 => C | _ => W))
      (Q'.add_eqv_congr_right _ _ C (Q'.add_eqv_congr_right _ _ DC
        (Q'.add_eqv_congr_left R _ _ hward)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (4*k*W) hp) (Q'.le_of_eqv hr)

/-- Cancel the matching increment INSIDE the cap deficit, rather than
counting it twice. The residual is literal observable-weighted source loss
minus signed OWN Ward, with the unchanged COMPLETE chronological cost.
No bound of that residue against the SAME filtered-start norm is supplied. -/
theorem originalOwnBlockCost_observedLoss_quadratic_ward_boundary_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (stage t : Nat)
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ headCutoff w+stage) :
    let K := headCutoff w+stage
    let hK := Nat.le_add_right (headCutoff w) stage
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let r := Q'.recipPos (oddMass w K width (stage+t))
      (oddMass_positive hw0 hw1 K width hK (stage+t))
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let h := (1 : Q')-qpow w (4*side scale)
    let per := 4*Q'.ofNat (side scale)
    let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
    let M := squareChannelMass w K scale width hwidth (terminalMessage w K width (stage+t))
    let O := squareChannelObservedLoss w K scale width hwidth (stage+t)*r
    per*(1+beta)*(4*originalOwnBlockCost hw0 hw1 scale width hwidth stage t+I)+
        4*k*normalizedWardResidual hw0 hw1 K width hK (stage+t) f ≤
      144*per*(h*h)*(M*r)+12*per*k*oddVariance hw0 hw1 K width hK (stage+t) f+
        2*per*k*O+
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
  let h := (1 : Q')-qpow w (4*side scale)
  let per := 4*Q'.ofNat (side scale)
  let I := squareChannelIncrement w K scale width hwidth (stage+t)*r
  let O := squareChannelObservedLoss w K scale width hwidth (stage+t)*r
  let W := normalizedWardResidual hw0 hw1 K width hK (stage+t) f
  let Cost := originalOwnBlockCost hw0 hw1 scale width hwidth stage t
  let R := 144*per*(h*h)*(squareChannelMass w K scale width hwidth
      (terminalMessage w K width (stage+t))*r)+
    12*per*k*oddVariance hw0 hw1 K width hK (stage+t) f
  let C := 4*per*(1+beta)*(comparisonEta hw0 hw1 width (stage+t-1)*
    originalReferenceSquare hw0 hw1 scale width hwidth stage t+
    normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f)
  let credit := (per*(HalfPow.half*k))*I
  have hd : squareChannelCapDeficit w K scale width hwidth (stage+t)*r ≈ I+4*O :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r
      (squareChannelCapDeficit_eq_increment_observedLoss_pin w K width (stage+t) scale hwidth))
      (poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.mul (.const 4) (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.const 4) (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => squareChannelIncrement w K scale width hwidth (stage+t) | 1 => squareChannelObservedLoss w K scale width hwidth (stage+t) | _ => r))
  have hcoef : (per*(HalfPow.half*k))*4 ≈ 2*per*k :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.const 4))
      (.mul (.mul (.mul (.const 4) (.var 1)) (.var 0)) (.var 2))
      (by decide) (fun | 0 => per | 1 => HalfPow.half | _ => k))
      (Q'.mul_eqv_congr_right _ _ k
        (Q'.mul_eqv_congr_right _ _ per (by decide : 4*HalfPow.half ≈ 2)))
  have hdef : (per*(HalfPow.half*k))*(squareChannelCapDeficit w K scale width hwidth (stage+t)*r) ≈
      credit+2*per*k*O :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hd)
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ I (4*O))
        (Q'.add_eqv_congr_left credit _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ 4 O).symm
            (Q'.mul_eqv_congr_right _ _ O hcoef))))
  have hp := Q'.add_le_add_right _ _ (-credit)
    (originalOwnBlockCost_companion_quadratic_ward_boundary_paid hw0 hw1 scale width hwidth stage t
      hdepth h2)
  have hl : per*((1+beta)*(4*Cost+I)+(HalfPow.half*k)*I)+4*k*W-credit ≈
      per*(1+beta)*(4*Cost+I)+4*k*W :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
        (.mul (.var 3) (.var 4)))) (.var 5))
        (.neg (.mul (.mul (.var 0) (.var 3)) (.var 4))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 5))
      (by decide) (fun | 0 => per | 1 => 1+beta | 2 => 4*Cost+I | 3 => HalfPow.half*k | 4 => I | _ => 4*k*W)
  have hr : R+(per*(HalfPow.half*k))*(squareChannelCapDeficit w K scale width hwidth (stage+t)*r)+C-credit ≈
      R+2*per*k*O+C :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-credit)
      (Q'.add_eqv_congr_right _ _ C (Q'.add_eqv_congr_left R _ _ hdef)))
      (poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 3)) (.neg (.var 1)))
        (.add (.add (.var 0) (.var 2)) (.var 3))
        (by decide) (fun | 0 => R | 1 => credit | 2 => 2*per*k*O | _ => C))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv hr))

#print axioms paddedSquare_energy_companion_quadratic_angular_payment
#print axioms originalOwnBlockCost_companion_quadratic_ward_boundary_paid
#print axioms originalOwnBlockCost_observedLoss_quadratic_ward_boundary_paid

end YMGap.Continuum.BF4DyadicWilsonSquareCompanionPayment
