/-
# A retained projection gain for the ORIGINAL growing Wilson loop

The complete centered square ceiling is sharpened by a computed nonnegative
gain, using the ORIGINAL positive partition as regularizer. The overlap is
an exact raw character expression, with the q^2 / OWN-variance correction
retained. No signed Ward, cubic, angular-pair or cutoff debt is deleted.
The gain may be zero; no useful changing-family rate is asserted.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderProjection
import YMGap.Continuum.BF4DyadicWilsonSquareWardMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare

namespace YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.SU2QuaternionCompleteRemainderProjection
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted normalizedMoment)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation (signedRemainder_generic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar (weighted_gamma_finSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareWardMoments (paddedSquare_gamma)
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  sourceWord sourceCharacter marginalWeight oddMass oddVariance

private def rawSource (w : Q') (K width n : Nat) : RatPoly :=
  projectedEndpointSource w K width (terminalMessage w K width n)

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width) (rawSource w K width n) := by
  unfold rawSource projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

private theorem firstOrder_shifted (tail : Nat) (q f : RatPoly) (c : Q')
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceFirstOrder tail q (shifted f c) ≈ sourceFirstOrder tail q f :=
  Q'.eqv_trans _ _ _ (sourceFirstOrder_eq_weightedAngularEnergy tail q (shifted f c)
    hq (QuaternionHaarDensityVariance.shifted_supported hf c))
    (Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt _ _ (tail+1) (fun i _ =>
        haar_of_coeff ((blockSquare_shifted i f c).mul_left (polyMul q q))))
      (Q'.eqv_symm (sourceFirstOrder_eq_weightedAngularEnergy tail q f hq hf)))

/-- Raw projected-source mass. This is NOT the original odd partition. -/
def rawSourceMass (w : Q') (K width n : Nat) : Q' :=
  H (N width) (polyMul (rawSource w K width n) (rawSource w K width n))

/-- Raw label-two character mass. No equality with Z times the OWN moment
is assumed; the two measures remain distinct. -/
def rawSecondCharacterMass (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  H (N width) (polyMul (polyMul (rawSource w K width n) (rawSource w K width n))
    (sourceCharacter width (paddedSquare scale width hwidth).edges 2))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "q" => rawSource w K width n
local notation "psi" => oddCentered hw0 hw1 K width hK n f
local notation "Z" => oddMass w K width n
local notation "V" => oddVariance hw0 hw1 K width hK n f
local notation "C" => centeredCorrection hw0 hw1 K width hK n f
local notation "L" => (4 : Q')*Q'.ofNat (side scale)
local notation "U0" => rawSourceMass w K width n
local notation "U2" => rawSecondCharacterMass w K width n scale hwidth

private theorem source_tail_supported : SupportedQuaternionBlocks (N width-1+1) q := by
  rw [Nat.sub_add_cancel (baseLinks_positive width)]
  exact source_supported w K width n

private theorem centered_tail_supported : SupportedQuaternionBlocks (N width-1+1) psi := by
  rw [Nat.sub_add_cancel (baseLinks_positive width)]
  exact oddCentered_supported hw0 hw1 K width hK n (sourceCharacter_supported width _ 1)

/-- New full-loop geometry removes source derivatives from this coefficient.
Centering uses the ORIGINAL mean; U2 is still explicitly raw. -/
theorem paddedSquare_firstOrder : sourceFirstOrder (N width-1) q psi ≈ L*(3*U0-U2) := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hshift := firstOrder_shifted (N width-1) q f
    (normalizedMoment (N width) (marginalWeight w K width n) f
      (marginalMass_positive hw0 hw1 K width hK n))
    (source_tail_supported K width n)
    (by simpa only [hN] using hf)
  have ha := sourceFirstOrder_eq_weightedAngularEnergy (N width-1) q f
    (source_tail_supported K width n) (by simpa only [hN] using hf)
  have hgamma : weightedAngularEnergy (N width-1) q f ≈
      H (N width) (polyMul (polyMul q q)
        (polySmul L (polyAdd (cap 4) (polyNeg (polyMul f f))))) := by
    unfold weightedAngularEnergy
    rw [hN]
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (weighted_gamma_finSum (N width) (polyMul q q) f))
      (paddedSquare_gamma scale width hwidth (polyMul q q))
  have hfusion : RatPolyCoeffEqv (polyMul f f)
      (polyAdd polyOne (sourceCharacter width (paddedSquare scale width hwidth).edges 2)) := by
    unfold sourceCharacter
    exact first_character_square (sourceWord width (paddedSquare scale width hwidth).edges).scalar
  have hpoly : RatPolyCoeffEqv
      (polyMul (polyMul q q) (polySmul L (polyAdd (cap 4) (polyNeg (polyMul f f)))))
      (polySmul L (polyAdd (polySmul 3 (polyMul q q))
        (polyNeg (polyMul (polyMul q q)
          (sourceCharacter width (paddedSquare scale width hwidth).edges 2))))) := by
    exact (RatPolyCoeffEqv.polyMul_smul_right L _ _).trans
      ((((RatPolyCoeffEqv.refl _).mul
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hfusion))).smul L).trans
        ((((RatPolyCoeffEqv.refl _).mul
          ((RatPolyCoeffEqv.refl _).add
            (RatPolyCoeffEqv.neg
              ((RatPolyCoeffEqv.one_smul polyOne).symm.add
                (RatPolyCoeffEqv.refl _))))).trans
          ((coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.var 0) (.add (.const 4)
              (.neg (.add (.const 1) (.var 1)))))
            (.add (.mul (.const 3) (.var 0)) (.neg (.mul (.var 0) (.var 1))))
            (by decide) (fun
              | 0 => polyMul q q
              | _ => sourceCharacter width (paddedSquare scale width hwidth).edges 2)).trans
            ((cap_mul_left 3 (polyMul q q)).add (RatPolyCoeffEqv.refl _)))).smul L))
  have hm : H (N width) (polyMul (polyMul q q)
      (polySmul L (polyAdd (cap 4) (polyNeg (polyMul f f))))) ≈ L*(3*U0-U2) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) L _)
        (Q'.mul_eqv_congr_left L _ _ (Q'.eqv_trans _ _ _
          (quaternionHaar_append (N width) _ _)
          (Q'.add_eqv_congr' (quaternionHaar_polySmul (N width) 3 _)
            (Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul _))
              (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) _)
                (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
                  (by decide) (fun _ => U2))))))))
  exact Q'.eqv_trans _ _ _ hshift (Q'.eqv_trans _ _ _ ha (Q'.eqv_trans _ _ _ hgamma hm))

/-- The exact source-specific overlap; q^2/OWN-variance mismatch stays SIGNED. -/
theorem paddedSquare_overlap_moments : projectionOverlap (N width-1) q psi ≈
    L*(3*U0-U2)-HalfPow.half*(Z*V-C) :=
  Q'.eqv_trans _ _ _ (projection_overlap_pin (N width-1) q psi
    (source_tail_supported K width n) (centered_tail_supported hw0 hw1 K width hK n scale hwidth))
    (Q'.add_eqv_congr' (paddedSquare_firstOrder hw0 hw1 K width hK n scale hwidth)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
        (centered_sourceSquare_pin hw0 hw1 K width hK n
          (sourceCharacter_supported width _ 1) (paddedSquare_fringe_independent scale width hwidth)))))

/-- Constructed finite nonnegative gain using epsilon=ORIGINAL partition Z,
then normalizing by this SAME Z. No scaling-gain assumption is supplied. -/
def normalizedProjectionGain : Q' :=
  projectionGain (N width-1) q psi Z (oddMass_positive hw0 hw1 K width hK n)
    (source_tail_supported K width n) (centered_tail_supported hw0 hw1 K width hK n scale hwidth) *
      Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)

theorem normalizedProjectionGain_nonnegative : (0 : Q') ≤
    normalizedProjectionGain hw0 hw1 K width hK n scale hwidth :=
  Q'.mul_nonneg _ _
    (projectionGain_nonnegative (N width-1) q psi Z (oddMass_positive hw0 hw1 K width hK n)
      (source_tail_supported K width n) (centered_tail_supported hw0 hw1 K width hK n scale hwidth))
    (Q'.le_of_lt (Q'.recipPos_pos Z (oddMass_positive hw0 hw1 K width hK n)))

private theorem partition_cancel (a z v : Q') (hz : (0 : Q') < z) :
    (a*(z*v))*Q'.recipPos z hz ≈ a*v :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => z | 2 => v | _ => Q'.recipPos z hz))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz)) (Q'.mul_one_eqv _))

attribute [local irreducible] rawSourceMass rawSecondCharacterMass
  sourceFirstOrder projectionOverlap projectionGain
  SU2QuaternionCyclicSecondOrder.sourceErrorBudget SU2QuaternionCyclicModeTaylor.pairBudget

/-- Retains a computed nonnegative part of the prior negative square.
Every ORIGINAL signed correction and all source/cutoff budgets remain. -/
theorem paddedSquare_remainder_projection_bound (hquad : sufficientCutoff w ≤ K) :
    normalizedRemainder hw0 hw1 K width hK n psi ≤
      quadraticRate w*V+normalizedCenteredError hw0 hw1 K width hK n f -
        (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
          normalizedProjectionGain hw0 hw1 K width hK n scale hwidth := by
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let g := projectionGain (N width-1) q psi Z (oddMass_positive hw0 hw1 K width hK n)
    (source_tail_supported K width n) (centered_tail_supported hw0 hw1 K width hK n scale hwidth)
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)
  let E := centeredError hw0 hw1 K width hK n f
  have hb := completeRemainder_le_projectionCeiling (N width-1) (Q'.le_of_lt hw0) hw1 K hquad q psi
    (source_tail_supported K width n) (centered_tail_supported hw0 hw1 K width hK n scale hwidth)
    Z (oddMass_positive hw0 hw1 K width hK n)
  have hp : squareCeiling (N width-1) w K q psi ≈ quadraticRate w*(Z*V)+E :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (centered_sourceSquare_pin hw0 hw1 K width hK n
            (sourceCharacter_supported width _ 1) (paddedSquare_fringe_independent scale width hwidth))))
        (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.mul (.var 1)
          (.add (.mul (.var 2) (.var 3)) (.neg (.var 4))))) (.var 5)) (.var 6))
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.add (.var 5) (.var 6)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 4)))))
        (by decide) (fun
          | 0 => alpha
          | 1 => squareQuarter
          | 2 => Z
          | 3 => V
          | 4 => C
          | 5 => SU2QuaternionCyclicSecondOrder.sourceErrorBudget (N width-1) w K q psi
          | _ => h*((h*h)*SU2QuaternionCyclicModeTaylor.pairBudget (N width-1) q
            (polyMul q (SU2QuaternionCompleteRemainderCancellation.angularSquare (N width-1) psi)))))
  have hraw := Q'.le_trans' _ _ _ (Q'.le_of_eqv (signedRemainder_generic w K width n psi))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.add_eqv_congr' hp (Q'.eqv_refl _))))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos Z (oddMass_positive hw0 hw1 K width hK n)))
  have halg : ((quadraticRate w*(Z*V)+E)-alpha*g)*r ≈
      (quadraticRate w*(Z*V))*r+E*r-alpha*(g*r) :=
    poly_identity_of_normal_eq
      (.mul (.add (.add (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.var 4))
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))
        (.neg (.mul (.var 2) (.mul (.var 3) (.var 4)))))
      (by decide) (fun | 0 => quadraticRate w*(Z*V) | 1 => E | 2 => alpha | 3 => g | _ => r)
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ halg
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (partition_cancel (quadraticRate w) Z V _) (Q'.eqv_refl _))
      (Q'.eqv_refl _))))

/-- A genuine strengthened ORIGINAL energy estimate, not a supplied bound.
No positive size for the gain or useful scaling control of the debts is claimed. -/
theorem paddedSquare_energy_projection_bound (hquad : sufficientCutoff w ≤ K) :
    normalizedEnergy hw0 hw1 K width hK n f ≤
      ((12*Q'.ofNat (side scale))*((1 : Q')-w)+quadraticRate w)*V+
        completeCenteredError hw0 hw1 K width hK n f -
          (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
            normalizedProjectionGain hw0 hw1 K width hK n scale hwidth := by
  let A := normalizedAngular hw0 hw1 K width hK n f
  let W := BF4ExactSlabFixedSpatialFamilyVarianceWard.normalizedWardResidual hw0 hw1 K width hK n f
  let D := normalizedCenteredError hw0 hw1 K width hK n f
  let h := (1 : Q')-w
  let k := (12 : Q')*Q'.ofNat (side scale)
  let beta := quadraticRate w
  let J := (HalfPow.half*(h*h))*normalizedProjectionGain hw0 hw1 K width hK n scale hwidth
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hind := paddedSquare_fringe_independent scale width hwidth
  have hward := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have hupper := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedEnergy_centered_taylor hw0 hw1 K width hK n hf hind))
    (Q'.add_le_add_left (h*A) _ _
      (paddedSquare_remainder_projection_bound hw0 hw1 K width hK n scale hwidth hquad))
  have hjoin : h*A+(beta*V+D-J) ≈ h*(A+W)+beta*V+(D-h*W)-J :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.add (.add (.mul (.var 4) (.var 3)) (.var 5)) (.neg (.var 6))))
      (.add (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 4) (.var 3))) (.add (.var 5) (.neg (.mul (.var 0) (.var 2))))) (.neg (.var 6)))
      (by decide) (fun | 0 => h | 1 => A | 2 => W | 3 => V | 4 => beta | 5 => D | _ => J)
  exact Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hjoin
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hward) (Q'.eqv_refl _))
        (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.var 2))) (.var 4)) (.neg (.var 5)))
        (.add (.add (.mul (.add (.mul (.var 1) (.var 0)) (.var 3)) (.var 2)) (.var 4)) (.neg (.var 5)))
        (by decide) (fun | 0 => h | 1 => k | 2 => V | 3 => beta | 4 => D-h*W | _ => J)))))

#print axioms rawSourceMass
#print axioms rawSecondCharacterMass
#print axioms paddedSquare_firstOrder
#print axioms paddedSquare_overlap_moments
#print axioms normalizedProjectionGain
#print axioms normalizedProjectionGain_nonnegative
#print axioms paddedSquare_remainder_projection_bound
#print axioms paddedSquare_energy_projection_bound

end YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain
