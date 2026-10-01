/-
# The signed family's Casimir identity in the SAME interacting variance

The actual four-link geometry supplies Casimir 12 for the complete signed
plaquette family. Weighted integration by parts retains the derivative of
the COMPLETE original marginal V*g_n*g_(n+1). Its mass and centered variance
are pinned to the existing odd chain, including every signed cross term.
No useful sign, relative bound, or scaling estimate for the residual follows.
-/

import YMGap.Continuum.SU2QuaternionWeightedCasimirWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor (normalizedAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks spatialWeight terminalMessage

/-- The complete marginal has exactly the original odd partition. -/
theorem marginalMass_pin (w : Q') (K width n : Nat) :
    H (N width) (marginalWeight w K width n) ≈ oddMass w K width n := by
  unfold marginalWeight oddMass weightedMass
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
    (fun | 0 => spatialWeight w K width
         | 1 => terminalMessage w K width n
         | _ => terminalMessage w K width (n+1)))

theorem marginalMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < H (N width) (marginalWeight w K width n) :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK n)
    (Q'.ge_of_eqv (marginalMass_pin w K width n))

theorem marginalMoment_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    normalizedMoment (N width) (marginalWeight w K width n) f
        (marginalMass_positive hw0 hw1 K width hK n) ≈
      middleRatio hw0 hw1 K width hK (n+1) n f := by
  have hraw : H (N width) (polyMul (marginalWeight w K width n) f) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width (n+1)) f)
          (terminalMessage w K width n)) := by
    unfold marginalWeight weightedMass
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.var 1))) (by decide)
      (fun | 0 => spatialWeight w K width
           | 1 => terminalMessage w K width n
           | 2 => terminalMessage w K width (n+1)
           | _ => f))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hraw)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
      (marginalMass_positive hw0 hw1 K width hK n)
      (oddMass_positive hw0 hw1 K width hK n) (marginalMass_pin w K width n)))

/-- Centered variance of the existing odd chain, not the square of a terminal. -/
def oddVariance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  middleRatio hw0 hw1 K width hK (n+1) n (polyMul f f) +
    -(middleRatio hw0 hw1 K width hK (n+1) n f *
      middleRatio hw0 hw1 K width hK (n+1) n f)

theorem marginalVariance_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    normalizedVariance (N width) (marginalWeight w K width n) f
        (marginalMass_positive hw0 hw1 K width hK n) ≈
      oddVariance hw0 hw1 K width hK n f := by
  have h := marginalMoment_pin hw0 hw1 K width hK n f
  exact Q'.add_eqv_congr' (marginalMoment_pin hw0 hw1 K width hK n (polyMul f f))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ h)))

/-- No absolute value: retain all complete-weight derivative terms and the
actual marginal mean before any quantitative estimate. -/
def wardResidual {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  totalResidual (N width) (marginalWeight w K width n) f
    (normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n))

def normalizedWardResidual {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  wardResidual hw0 hw1 K width hK n f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

/-- Actual signed-family Ward identity; the eigenpin is proved from the four
literal incident links, not supplied as a spectral hypothesis. -/
theorem family_ward {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    marginalAngular w K width n (spatialSpan width c qs) +
        wardResidual hw0 hw1 K width hK n (spatialSpan width c qs) ≈
      12*(oddMass w K width n *
        oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) := by
  have h := complete_ward_own_mean (baseLinks_positive width)
    (marginalWeight w K width n) (spatialSpan width c qs)
    (marginalMass_positive hw0 hw1 K width hK n) 12
    (spatialSpan_casimir width c qs hqs)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm (totalEnergy_finSum _ _ _)) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left 12 _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (marginalMass_pin w K width n))
        (Q'.mul_eqv_congr_left _ _ _
          (marginalVariance_pin hw0 hw1 K width hK n (spatialSpan width c qs))))))

/-- All angular and derivative-of-weight terms use the same original Z. -/
theorem family_normalized_ward {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    normalizedAngular hw0 hw1 K width hK n (spatialSpan width c qs) +
        normalizedWardResidual hw0 hw1 K width hK n (spatialSpan width c qs) ≈
      12*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs) := by
  let z := oddMass w K width n
  let v := oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)
  let r := Q'.recipPos z (oddMass_positive hw0 hw1 K width hK n)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (family_ward hw0 hw1 K width hK n qs c hqs))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 12) (.mul (.var 0) (.var 1))) (.var 2))
          (.mul (.mul (.const 12) (.var 1)) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => z | 1 => v | _ => r))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z
            (oddMass_positive hw0 hw1 K width hK n))) (Q'.mul_one_eqv _))))

#print axioms marginalMass_pin
#print axioms marginalMass_positive
#print axioms marginalMoment_pin
#print axioms oddVariance
#print axioms marginalVariance_pin
#print axioms wardResidual
#print axioms normalizedWardResidual
#print axioms family_ward
#print axioms family_normalized_ward

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
