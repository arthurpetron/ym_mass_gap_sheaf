/-
# Exact cutoff-two vacuum/cube physical Gram entry

The cutoff-two vacuum delta row reduces the physical vacuum/cube entry to
the vacuum boundary.  This module evaluates its production fixed weight and
the genuine cube half amplitude, obtaining the exact value `1 / 4096`.

This is a finite cutoff-two, half-extent-zero matrix entry.  It makes no
cutoff-uniform, volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonal
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem slabFaceFactorOn_zero_eqv_one
    (w : Q') (K : Nat) : ∀ ids : List Nat,
    slabFaceFactorOn w K zeroEdgeLabelling ids ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      have hcoefficient :
          coeffAt (heatKernelPacket K w) 0 ≈ 1 := by
        rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
        exact Q'.eqv_refl 1
      exact Q'.eqv_trans _ (1 * 1) _
        (q_mul_congr hcoefficient
          (slabFaceFactorOn_zero_eqv_one w K tail))
        (Q'.one_mul_eqv 1)

private theorem slabLinkMultiplicityProductOn_zero_eq_one
    (K extent : Nat) : ∀ links : List Z4Link,
    slabLinkMultiplicityProductOn K extent zeroEdgeLabelling links = 1
  | [] => rfl
  | head :: tail => by
      change
        slabExplicitLinkMultiplicity K extent zeroEdgeLabelling head *
            slabLinkMultiplicityProductOn K extent
              zeroEdgeLabelling tail = 1
      rw [slabExplicitLinkMultiplicity_zero_eq_one,
        slabLinkMultiplicityProductOn_zero_eq_one K extent tail,
        Nat.one_mul]

theorem centralBoundaryWeight_cutoffTwo_vacuum_eqv_one :
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling ≈ 1 := by
  unfold centralBoundaryWeight
  rw [assembleReflectedSlabLabelling_zero]
  unfold centralFixedWeight
  rw [slabLinkMultiplicityProductOn_zero_eq_one]
  refine Q'.eqv_trans _ (1 * Q'.ofNat 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (slabFaceFactorOn_zero_eqv_one cutoffTwoHalfCoupling 2
        (centralFixedFaceIds 0))
  · decide

private theorem natListProduct_eq_one_of_all
    {Item : Type} (value : Item → Nat) : ∀ items : List Item,
    (∀ item, item ∈ items → value item = 1) →
      natListProduct value items = 1
  | [], _ => rfl
  | head :: tail, hall => by
      rw [natListProduct, hall head List.mem_cons_self,
        natListProduct_eq_one_of_all value tail
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem)),
        Nat.one_mul]

private theorem centralLowerCube_lowerLinkMultiplicityProduct_cutoffTwo_one :
    slabLinkMultiplicityProductOn 2 1 centralLowerCubePhysical
        (centralLowerLinks 0) = 1 := by
  unfold slabLinkMultiplicityProductOn
  apply natListProduct_eq_one_of_all
  intro link hlink
  exact centralLowerCubeMultiplicity_eq_one (by decide) link
    (mem_centralLowerLinks.mp hlink).1

theorem centralHalfAmplitude_cutoffTwo_cube_vacuum_eqv_scalar :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState zeroEdgeLabelling ≈
      cutoffTwoCubeLowerFaceScalar := by
  unfold centralHalfAmplitude
  change centralLowerFactor cutoffTwoHalfCoupling 2 0
      centralLowerCubePhysical ≈ cutoffTwoCubeLowerFaceScalar
  unfold centralLowerFactor
  change slabFaceFactorOn cutoffTwoHalfCoupling 2 centralLowerCubePhysical
      (centralLowerFaceIds 0) *
        Q'.ofNat (slabLinkMultiplicityProductOn 2 1
          centralLowerCubePhysical (centralLowerLinks 0)) ≈
      cutoffTwoCubeLowerFaceScalar
  rw [centralLowerCube_lowerLinkMultiplicityProduct_cutoffTwo_one]
  refine Q'.eqv_trans _
    (cutoffTwoCubeLowerFaceScalar * Q'.ofNat 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (by
        unfold cutoffTwoCubeLowerFaceScalar
        simpa only [centralLowerCubePhysical] using
          (centralLowerCube_lowerFaceFactor_cutoffTwo_eqv
            zeroEdgeLabelling))
  · unfold cutoffTwoCubeLowerFaceScalar
    decide

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_cube_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling centralLowerCubeState ≈
      cutoffTwoCubeLowerFaceScalar := by
  have hcube : centralLowerCubeState ∈ cutoffTwoVacuumColumnCarrier := by
    unfold cutoffTwoVacuumColumnCarrier
    exact centralLowerCubeState_mem_centralPositiveHalfStates
      (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide)
  refine Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 zeroEdgeLabelling *
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState zeroEdgeLabelling) _
    (centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
      centralLowerCubeState hcube) ?_
  exact Q'.eqv_trans _
    ((1 : Q') * cutoffTwoCubeLowerFaceScalar) _
    (q_mul_congr centralBoundaryWeight_cutoffTwo_vacuum_eqv_one
      centralHalfAmplitude_cutoffTwo_cube_vacuum_eqv_scalar)
    (Q'.one_mul_eqv _)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross.centralBoundaryWeight_cutoffTwo_vacuum_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross.centralHalfAmplitude_cutoffTwo_cube_vacuum_eqv_scalar
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross.centralPhysicalReflectedKernel_cutoffTwo_vacuum_cube_eqv
