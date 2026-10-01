/-
# The complete signed family norm with its source defect retained

For the ACTUAL terminal source and the original odd-marginal center, the
entire signed plaquette family has full heat eigenvalue lambda=w^12. Its
symmetric test norm is exactly

  D + 8*(1+lambda)*Z*Var_odd - 8*sourceNormDefect.

The defect combines the existing signed sourceCorrection with the mismatch
between raw q^2 and interacting q*Pq centering. The original joint energy
consumer retains it without a sign or smallness assumption. A useful bound
on this complete defect and on the responses/cost remains open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.SU2QuaternionProductHeatCenteredMixed
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq qpow)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatSumTest (sumTest)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
  (sourceIncrementCost singleEndedCost)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceCorrection)
open YMGap.Continuum.SU2QuaternionProductHeatCenteredMixed (centered_mixed_pin)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen (spatialSpan_fullRange)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The existing SIGNED source correction plus the actual mean mismatch.
No estimate or favorable sign is part of this definition. -/
def sourceNormDefect {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat)
    (lambda : Q') (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  let c := normalizedMoment (N width) (marginalWeight w K width depth) f
    (marginalMass_positive hw0 hw1 K width hK depth)
  lambda*sourceCorrection (N width) w K (List.range (N width)) q psi +
    (1-lambda)*c*H (N width) (polyMul (polyMul q q) psi)

/-- Exact reduction of the remaining mixed moment. The concrete family
consumer below supplies the tested eigenimage from the original geometry. -/
theorem centered_mixed_defect_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f)
    (lambda : Q')
    (heig : SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) f) (polySmul lambda f)) :
    centeredMixedMoment hw0 hw1 K width hK depth f ≈
      lambda*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f) -
        sourceNormDefect hw0 hw1 K width hK depth lambda f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  let c := normalizedMoment (N width) (marginalWeight w K width depth) f
    (marginalMass_positive hw0 hw1 K width hK depth)
  let C := sourceCorrection (N width) w K (List.range (N width)) q psi
  let R := H (N width) (polyMul (polyMul q q) psi)
  let V := oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have h := centered_mixed_pin (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq hf lambda c heig
  have hassoc : centeredMixedMoment hw0 hw1 K width hK depth f ≈
      H (N width) (polyMul (polyMul (polyMul q q) psi)
        (productMap (N width) w K (List.range (N width)) psi)) :=
    Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) psi _))
  exact Q'.eqv_trans _ _ _ hassoc
    (Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left lambda _ _
              (centered_source_square hw0 hw1 K width hK depth hf hind))
            (Q'.eqv_refl _)) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
            (.neg (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 3)) (.var 4))))
          (.add (.mul (.var 0) (.var 1))
            (.neg (.add (.mul (.var 0) (.var 2))
              (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 3)) (.var 4)))))
          (by decide) (fun | 0 => lambda | 1 => V | 2 => C | 3 => c | _ => R))))

theorem centered_norm_defect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f)
    (lambda : Q')
    (heig : SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) f) (polySmul lambda f)) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    centeredNormExpression hw0 hw1 K width hK depth f ≈
      sourceIncrementCost (N width) w K (List.range (N width)) q f +
        8*((1+lambda)*(oddMass w K width depth *
          oddVariance hw0 hw1 K width hK depth f)) -
        8*sourceNormDefect hw0 hw1 K width hK depth lambda f := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let D := sourceIncrementCost (N width) w K (List.range (N width)) q f
  let V := oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f
  let C := sourceNormDefect hw0 hw1 K width hK depth lambda f
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl D)
        (Q'.mul_eqv_congr_left 8 _ _
          (centered_mixed_defect_pin hw0 hw1 K width hK depth hf hind lambda heig)))
      (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const 8)
        (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))))
        (.mul (.const 8) (.var 2)))
      (.add (.add (.var 0) (.mul (.const 8)
        (.mul (.add (.const 1) (.var 1)) (.var 2))))
        (.neg (.mul (.const 8) (.var 3))))
      (by decide) (fun | 0 => D | 1 => lambda | 2 => V | _ => C))

/-- ALL signed coefficients and cross terms remain in the actual family;
the heat eigenpin and fringe independence are both supplied geometrically. -/
theorem padded_family_test_norm_defect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK1 : 1 ≤ K)
    {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K) (depth : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
        (sumTest (N width) q psi) (sumTest (N width) q psi) ≈
      sourceIncrementCost (N width) w K (List.range (N width)) q f +
        8*((1+qpow w 12)*(oddMass w K width depth *
          oddVariance hw0 hw1 K width hK depth f)) -
        8*sourceNormDefect hw0 hw1 K width hK depth (qpow w 12) f := by
  dsimp only
  have hf := spatialSpan_supported width c qs
  have hind := spatialSpan_fringe_independent_after_padding hwidth c qs hqs
  have heig := spatialSpan_fullRange width c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) w K hK1
  exact Q'.eqv_trans _ _ _ (centered_sum_norm hw0 hw1 K width hK depth hf hind)
    (centered_norm_defect hw0 hw1 K width hK depth hf hind (qpow w 12) heig)

/-- The exact norm reduction has an ORIGINAL energy consumer. This is
a cleared inequality with no inverse denominator and no asserted strict gain. -/
theorem padded_family_energy_defect_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK1 : 1 ≤ K)
    {base width : Nat} (hwidth : base < width) (hK : headCutoff w ≤ K) (depth : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let n := N width
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    let W := productHeat n w K (List.range n)
    let r := polyMul (jump n q) (jump n f)
    let s := sumTest n q psi
    let J := weightedPair (n+n) W r polyOne
    let M := weightedPair (n+n) W s polyOne
    let V := sourceIncrementCost n w K (List.range n) q f +
      8*((1+qpow w 12)*(oddMass w K width depth *
        oddVariance hw0 hw1 K width hK depth f)) -
      8*sourceNormDefect hw0 hw1 K width hK depth (qpow w 12) f-M*M
    let X := weightedPair (n+n) W r s-J*M
    4*V*energy w K width (terminalMessage w K width depth) f +
      V*(J*J)+X*X ≤ 2*V*singleEndedCost n w K (List.range n) q f := by
  dsimp only
  let n := N width
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth f
  let W := productHeat n w K (List.range n)
  let r := polyMul (jump n q) (jump n f)
  let s := sumTest n q psi
  let J := weightedPair (n+n) W r polyOne
  let M := weightedPair (n+n) W s polyOne
  let X := weightedPair (n+n) W r s-J*M
  let V0 := centeredNormExpression hw0 hw1 K width hK depth f-M*M
  let V := sourceIncrementCost n w K (List.range n) q f +
    8*((1+qpow w 12)*(oddMass w K width depth *
      oddVariance hw0 hw1 K width hK depth f)) -
    8*sourceNormDefect hw0 hw1 K width hK depth (qpow w 12) f-M*M
  let E := energy w K width (terminalMessage w K width depth) f
  let C := singleEndedCost n w K (List.range n) q f
  have hf := spatialSpan_supported width c qs
  have hind := spatialSpan_fringe_independent_after_padding hwidth c qs hqs
  have heig := spatialSpan_fullRange width c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) w K hK1
  have hv : V0 ≈ V := Q'.add_eqv_congr'
    (centered_norm_defect hw0 hw1 K width hK depth hf hind (qpow w 12) heig)
    (Q'.eqv_refl _)
  have hl : 4*V0*E+V0*(J*J)+X*X ≈ 4*V*E+V*(J*J)+X*X :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (qmul (qmul (Q'.eqv_refl 4) hv) (Q'.eqv_refl E))
        (qmul hv (Q'.eqv_refl (J*J)))) (Q'.eqv_refl (X*X))
  have hr : 2*V0*C ≈ 2*V*C := qmul (qmul (Q'.eqv_refl 2) hv) (Q'.eqv_refl C)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ (original_centered_energy_budget hw0 hw1 K width hK depth hf hind)
      (Q'.le_of_eqv hr))

#print axioms sourceNormDefect
#print axioms centered_mixed_defect_pin
#print axioms centered_norm_defect
#print axioms padded_family_test_norm_defect
#print axioms padded_family_energy_defect_budget

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceDefect
