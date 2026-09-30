/-
# The whole signed plaquette-family increment on the original window

The literal Wilson family, including arbitrary coefficient signs, is shifted
as one expression. Its squared difference is coefficientwise the existing
spatial source jump squared. Consequently its finite expectation is twice
the existing original normalized temporal energy, with the SAME action and
partition. No termwise absolute values or singleton-increment sums are used.

This also transfers the known coefficient-energy floor. That floor is a
LOWER energy bound, not the relative UPPER bound needed for scaling survival.
-/

import YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
import YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy
import YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity

namespace YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (sourceCharacter_plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy (family_energy_floor)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow (lower upper)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor varianceDenominator_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (source_difference)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_smul lift_coeff)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit normalizedEnergy

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n+1 => by
      change liftHead (liftBoundary n polyZero) = polyZero
      rw [lift_zero n]
      rfl

/-- Every coefficient is shifted together, including repeated and empty
families. This is raw coefficient equality, not a carrier identification. -/
theorem source_family_shift (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (n : Nat) :
    RatPolyCoeffEqv (sourcePolynomial (shift n (familyExpression width qs c hqs)))
      (liftBoundary (n*(N width)) (spatialSpan width c qs)) := by
  induction qs with
  | nil =>
      change RatPolyCoeffEqv (polySmul 0 polyOne) (liftBoundary (n*(N width)) polyZero)
      rw [lift_zero]
      exact RatPolyCoeffEqv.zero_smul polyOne
  | cons face qs ih =>
      change RatPolyCoeffEqv
        (polyAdd (polySmul (c face)
          (liftBoundary ((0+n)*(N width))
            (BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter width
              (BF4ExactSlabFixedSpatialWilsonPlaquette.plaquetteLoop face
                (hqs face List.mem_cons_self)).edges 1)))
          (sourcePolynomial (shift n (familyExpression width qs c
            (fun p hp => hqs p (List.mem_cons_of_mem face hp))))))
        (liftBoundary (n*(N width)) (polyAdd
          (polySmul (c face) (characterPolynomial (plaquette width face).scalar 1))
          (spatialSpan width c qs)))
      rw [lift_add, lift_smul, Nat.zero_add]
      exact ((lift_coeff (n*(N width)) (sourceCharacter_plaquette width face 1)).smul (c face)).add
        (ih (fun p hp => hqs p (List.mem_cons_of_mem face hp)))

/-- The whole signed adjacent-time difference, before taking its square. -/
theorem source_difference_family (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv (sourcePolynomial (differenceAt (familyExpression width qs c hqs) 1))
      (jump width (spatialSpan width c qs)) := by
  have h0 := source_family_shift width qs c hqs 0
  have h1 := source_family_shift width qs c hqs 1
  simp only [shift_zero, Nat.zero_mul, liftBoundary] at h0
  simp only [Nat.one_mul] at h1
  exact (source_difference _ _).trans (h0.add (RatPolyCoeffEqv.neg h1))

/-- All signed cross terms remain in this single source square. -/
theorem source_square_family (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv (sourcePolynomial (squareAt (familyExpression width qs c hqs) 1))
      (polyMul (jump width (spatialSpan width c qs))
        (jump width (spatialSpan width c qs))) :=
  (source_difference_family width qs c hqs).mul
    (source_difference_family width qs c hqs)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

/-- The finite literal Wilson square is exactly twice the already constructed
original temporal energy, with its odd-chain partition unchanged. -/
theorem finite_family_increment_pin (stage depth : Nat) :
    originalWindowScalar hw0 hw1 1 (squareAt (familyExpression width qs c hqs) 1)
      stage depth depth ≈
      (2 : Q') * normalizedEnergy hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) depth (spatialSpan width c qs) :=
  Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 _ (square_within (family_within width qs c hqs) 1)
      stage depth depth)
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) depth 1 depth
        (source_square_family width qs c hqs))
      (Q'.eqv_symm (normalizedEnergy_window hw0 hw1 _ width (Nat.le_add_right _ _) depth
        (spatialSpan_supported width c qs))))

/-- Transfer the existing coefficient-energy floor; its direction is LOWER,
not the relative upper estimate required by a survival theorem. -/
theorem finite_family_increment_floor (hn : qs.Nodup) (stage depth : Nat) :
    (2 : Q') * (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs) ≤
      originalWindowScalar hw0 hw1 1 (squareAt (familyExpression width qs c hqs) 1)
        stage depth depth := by
  let b := listQSum (fun face => c face*c face) qs
  let d := 600*upper w
  let r := Q'.recipPos d (varianceDenominator_positive hw0)
  have hcancel : d*(varianceFloor w hw0*b) ≈ lower w*b :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => d | 1 => lower w | 2 => r | _ => b))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_recipPos_eqv d (varianceDenominator_positive hw0))) (Q'.one_mul_eqv _))
  have hfloor := family_energy_floor hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) depth qs hn hqs c
  have h := Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel) hfloor)
    (varianceDenominator_positive hw0)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 h (by decide))
    (Q'.ge_of_eqv (finite_family_increment_pin hw0 hw1 width qs c hqs stage depth))

/-- The SAME already-defined joint limit inherits the coefficient floor. -/
theorem family_increment_floor (hn : qs.Nodup) :
    leEv (ofQ' ((2 : Q') * (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs)))
      (increment hw0 hw1 (familyExpression width qs c hqs) (family_within width qs c hqs) 1) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 1 _ (square_within (family_within width qs c hqs) 1))
  intro epsilon he
  exact ⟨0, fun stage _ => Q'.le_trans' _ _ _
    (finite_family_increment_floor hw0 hw1 width qs c hqs hn stage stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

#print axioms source_family_shift
#print axioms source_difference_family
#print axioms source_square_family
#print axioms finite_family_increment_pin
#print axioms finite_family_increment_floor
#print axioms family_increment_floor

end YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
