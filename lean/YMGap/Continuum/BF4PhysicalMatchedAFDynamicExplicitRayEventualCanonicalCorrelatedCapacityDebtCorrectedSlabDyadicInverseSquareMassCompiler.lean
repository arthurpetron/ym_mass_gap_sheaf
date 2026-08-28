/-
# The affine SU(2) cutoff tail gives an actual inverse-square mass bound

At fixed physical scale, the arbitrary-nome SU(2) Casimir tail has an affine
dyadic cutoff schedule: one fixed nome/volume burn is followed by one retained
representation label per dyadic precision.  This module chooses that concrete
transition start and proves

  corrected-slab increment at offset k <= 2^(-k) <= 5 / (k + 2)^2.

Consequently the later new-block mass is bounded by that explicit
inverse-square term plus the exact component-merger residual; if the
executable no-merger check succeeds, the residual disappears.

This is a genuinely inhabited analytic estimate.  It does not bound route
amplification, prove all-cutoff no-merger, construct a completed gap, or make
any thermodynamic, continuum, or Clay claim.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler
import YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSimplePathUsedCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exponential decay dominates the required inverse square -/

private theorem half_mul_invSqTerm_two_le_succ
    (k : Nat) (hk : 1 <= k) :
    HalfPow.half * invSqTerm 2 (by decide) k <=
      invSqTerm 2 (by decide) (k + 1) := by
  unfold HalfPow.half invSqTerm unit
  show
    (Q'.mkPos 1 2 (by decide) *
        Q'.mkPos 1 ((k + 2) * (k + 2))
          (Nat.mul_pos (by omega) (by omega))).num *
          ((Q'.mkPos 1 (((k + 1) + 2) * ((k + 1) + 2))
            (Nat.mul_pos (by omega) (by omega))).den : Int) <=
      (Q'.mkPos 1 (((k + 1) + 2) * ((k + 1) + 2))
          (Nat.mul_pos (by omega) (by omega))).num *
        ((Q'.mkPos 1 2 (by decide) *
          Q'.mkPos 1 ((k + 2) * (k + 2))
            (Nat.mul_pos (by omega) (by omega))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Int.one_mul]
  have hkk : 1 <= k * k := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hnat :
      ((k + 1) + 2) * ((k + 1) + 2) <=
        2 * ((k + 2) * (k + 2)) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  exact_mod_cast hnat

theorem dyad_le_five_mul_invSqTerm_two (k : Nat) :
    dyad k <= Q'.ofNat 5 * invSqTerm 2 (by decide) k := by
  cases k with
  | zero => decide
  | succ k =>
      induction k with
      | zero => decide
      | succ k ih =>
          have hhalf :
              HalfPow.half * dyad (k + 1) <=
                HalfPow.half *
                  (Q'.ofNat 5 * invSqTerm 2 (by decide) (k + 1)) :=
            Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half ih
              HalfPow.half_nonneg
          have hregroup :
              HalfPow.half *
                    (Q'.ofNat 5 * invSqTerm 2 (by decide) (k + 1)) ≈
                Q'.ofNat 5 *
                  (HalfPow.half * invSqTerm 2 (by decide) (k + 1)) := by
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm
                (Q'.mul_assoc_eqv HalfPow.half (Q'.ofNat 5)
                  (invSqTerm 2 (by decide) (k + 1)))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_comm_eqv HalfPow.half (Q'.ofNat 5))) ?_
            exact Q'.mul_assoc_eqv (Q'.ofNat 5) HalfPow.half
              (invSqTerm 2 (by decide) (k + 1))
          have hstep := half_mul_invSqTerm_two_le_succ (k + 1) (by omega)
          have hscaled :
              Q'.ofNat 5 *
                    (HalfPow.half * invSqTerm 2 (by decide) (k + 1)) <=
                Q'.ofNat 5 * invSqTerm 2 (by decide) ((k + 1) + 1) :=
            Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 5) hstep
              (by decide)
          exact Q'.le_trans' _ _ _ hhalf
            (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hscaled)

/-! ## 2. The concrete affine cutoff ray -/

def matchedEventualCanonicalCorrectedSlabDyadicTransitionStart
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale : Nat) : Nat :=
  physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
    physicalNomeTensorDyadicBurn
      (trajectory.nome physicalScale)
      (plaquetteEdgeCount (centralExtent 0 + 1))

theorem matchedEventualCanonicalCorrectedSlabDyadicCurrentCutoff_eq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalCurrentCutoff
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset =
      physicalNomeTensorDyadicRetainedCutoff
        (trajectory.nome physicalScale)
        (plaquetteEdgeCount (centralExtent 0 + 1)) cutoffOffset := by
  unfold matchedEventualCanonicalCurrentCutoff
    matchedEventualCanonicalCorrectedSlabDyadicTransitionStart
    physicalNomeTensorDyadicRetainedCutoff
    physicalNomeTensorDyadicPrecision physicalNomeRetainedCutoff
  omega

/-! ## 3. Inhabited all-cutoff mass estimates -/

theorem matchedEventualCanonicalCorrectedSlabIncrement_le_dyad
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset <=
      dyad cutoffOffset := by
  let transitionStart :=
    matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory
  let current := matchedEventualCanonicalCurrentCutoff
    transitionStart physicalScale cutoffOffset
  let later := matchedEventualCanonicalLaterCutoff
    transitionStart physicalScale cutoffOffset
  have hcurrent : current =
      physicalNomeTensorDyadicRetainedCutoff
        (trajectory.nome physicalScale)
        (plaquetteEdgeCount (centralExtent 0 + 1)) cutoffOffset :=
    matchedEventualCanonicalCorrectedSlabDyadicCurrentCutoff_eq
      trajectory physicalScale cutoffOffset
  have hcurrentLater : current <= later := by
    unfold current later matchedEventualCanonicalCurrentCutoff
      matchedEventualCanonicalLaterCutoff transitionStart
    omega
  have hlater :
      physicalNomeTensorDyadicRetainedCutoff
          (trajectory.nome physicalScale)
          (plaquetteEdgeCount (centralExtent 0 + 1)) cutoffOffset <=
        later := by
    rw [<- hcurrent]
    exact hcurrentLater
  have htail := slabPhysicalNomeCutoffIncrement_le_dyad_linear
    (trajectory.nome_pos physicalScale)
    (trajectory.nome_lt_one physicalScale)
    (centralExtent 0) cutoffOffset hlater
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
  change slabParametricKCutoffIncrement
      (trajectory.nome physicalScale) current later (centralExtent 0) <= _
  rw [hcurrent]
  exact htail

theorem matchedEventualCanonicalCorrectedSlabIncrement_le_five_mul_invSq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset <=
      Q'.ofNat 5 * invSqTerm 2 (by decide) cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalCorrectedSlabIncrement_le_dyad
      trajectory physicalScale cutoffOffset)
    (dyad_le_five_mul_invSqTerm_two cutoffOffset)

theorem matchedEventualCanonicalLaterNewBlockMass_le_five_mul_invSq_add_merger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterNewBlockMass
        trajectory
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset <=
      Q'.ofNat 5 * invSqTerm 2 (by decide) cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory
          (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
          physicalScale cutoffOffset := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
      trajectory
      (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
      physicalScale cutoffOffset)
    (Q'.add_le_add_right _ _ _
      (matchedEventualCanonicalCorrectedSlabIncrement_le_five_mul_invSq
        trajectory physicalScale cutoffOffset))

theorem matchedEventualCanonicalLaterNewBlockMass_le_five_mul_invSq_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat)
    (hcheck :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
          trajectory
          (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
          physicalScale cutoffOffset = true) :
    matchedEventualCanonicalLaterNewBlockMass
        trajectory
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset <=
      Q'.ofNat 5 * invSqTerm 2 (by decide) cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
      trajectory
      (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
      physicalScale cutoffOffset hcheck)
    (matchedEventualCanonicalCorrectedSlabIncrement_le_five_mul_invSq
      trajectory physicalScale cutoffOffset)

/-! ## 4. The exact adaptive product now needs only bounded amplification -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope_le_ten_mul_coefficient_mul_invSq_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (physicalScale cutoffOffset : Nat)
    (amplificationCoefficient : Q')
    (hcheck :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
          trajectory
          (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
          physicalScale cutoffOffset = true)
    (hamplification :
      matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
          trajectory
          (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
          physicalScale cutoffOffset <= amplificationCoefficient) :
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
        trajectory
        (matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory)
        physicalScale cutoffOffset <=
      (Q'.ofNat 10 * amplificationCoefficient) *
        invSqTerm 2 (by decide) cutoffOffset := by
  let transitionStart :=
    matchedEventualCanonicalCorrectedSlabDyadicTransitionStart trajectory
  let newMass := matchedEventualCanonicalLaterNewBlockMass
    trajectory transitionStart physicalScale cutoffOffset
  let amplification :=
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  let term := invSqTerm 2 (by decide) cutoffOffset
  have hmass : newMass <= Q'.ofNat 5 * term :=
    matchedEventualCanonicalLaterNewBlockMass_le_five_mul_invSq_of_noMerger
      trajectory physicalScale cutoffOffset hcheck
  have hamplification0 : (0 : Q') <= amplification :=
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have htwo :
      Q'.ofNat 2 * newMass <= Q'.ofNat 2 * (Q'.ofNat 5 * term) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hmass (by decide)
  have hmassProduct :
      (Q'.ofNat 2 * newMass) * amplification <=
        (Q'.ofNat 2 * (Q'.ofNat 5 * term)) * amplification :=
    Q'.mul_le_mul_of_nonneg_right _ _ amplification htwo hamplification0
  have hleft0 :
      (0 : Q') <= Q'.ofNat 2 * (Q'.ofNat 5 * term) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (by decide)
        (invSqTerm_nonneg 2 (by decide) cutoffOffset))
  have hcoefficientProduct :
      (Q'.ofNat 2 * (Q'.ofNat 5 * term)) * amplification <=
        (Q'.ofNat 2 * (Q'.ofNat 5 * term)) * amplificationCoefficient :=
    Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat 2 * (Q'.ofNat 5 * term)) hamplification hleft0
  have hregroup :
      (Q'.ofNat 2 * (Q'.ofNat 5 * term)) * amplificationCoefficient ≈
        (Q'.ofNat 10 * amplificationCoefficient) * term := by
    refine Q'.eqv_trans _
      (((Q'.ofNat 2 * Q'.ofNat 5) * term) * amplificationCoefficient) _
      (Q'.mul_eqv_congr_right _ _ amplificationCoefficient
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 5) term))) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * Q'.ofNat 5) * (term * amplificationCoefficient)) _
      (Q'.mul_assoc_eqv (Q'.ofNat 2 * Q'.ofNat 5) term
        amplificationCoefficient) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * Q'.ofNat 5) * (amplificationCoefficient * term)) _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2 * Q'.ofNat 5) _ _
        (Q'.mul_comm_eqv term amplificationCoefficient)) ?_
    refine Q'.eqv_trans _
      (((Q'.ofNat 2 * Q'.ofNat 5) * amplificationCoefficient) * term) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 2 * Q'.ofNat 5)
          amplificationCoefficient term)) ?_
    have hten :
        Q'.ofNat 2 * Q'.ofNat 5 ≈ Q'.ofNat 10 := by
      decide
    have htenCoefficient :
        (Q'.ofNat 2 * Q'.ofNat 5) * amplificationCoefficient ≈
          Q'.ofNat 10 * amplificationCoefficient :=
      Q'.mul_eqv_congr_right _ _ amplificationCoefficient hten
    exact Q'.mul_eqv_congr_right _ _ term htenCoefficient
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope
  exact Q'.le_trans' _ _ _ hmassProduct
    (Q'.le_trans' _ _ _ hcoefficientProduct (Q'.le_of_eqv hregroup))

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.dyad_le_five_mul_invSqTerm_two
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualCanonicalCorrectedSlabDyadicCurrentCutoff_eq
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualCanonicalCorrectedSlabIncrement_le_dyad
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualCanonicalCorrectedSlabIncrement_le_five_mul_invSq
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualCanonicalLaterNewBlockMass_le_five_mul_invSq_add_merger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualCanonicalLaterNewBlockMass_le_five_mul_invSq_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCorrectedSlabDyadicInverseSquareMassCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveSimplePathUsedCapacityNewBlockEnvelope_le_ten_mul_coefficient_mul_invSq_of_noMerger
