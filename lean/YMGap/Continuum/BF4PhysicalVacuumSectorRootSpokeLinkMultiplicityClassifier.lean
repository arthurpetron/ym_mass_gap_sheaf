/-
# Combinatorial BF4 vacuum-root spoke classifier

At strictly positive coupling, every heat-kernel face coefficient of a
retained lower state is strictly positive.  Therefore the all-vacuum
half-amplitude can vanish only through the literal product of lower-link
fusion multiplicities.

This module proves that equivalence at arbitrary cutoff and transports it to
the canonical finite vacuum sector.  The routing-level list of positive root
predecessors is exactly a finite filter by positivity of one natural-number
link-multiplicity product.  This removes the remaining analytic weights from
the root-spoke carrier problem.

The result does not classify the admissible labellings, bound their count,
construct distributed routes, prove a gap, construct a continuum limit, or
claim the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier
import YMGap.Continuum.FusionResidualBound

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

private theorem eliminateLinks_pos_on
    (value : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → (0 : Q') < value id) →
        (0 : Q') < eliminateLinks value ids
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hvalue => by
      exact Q'.mul_pos
        (hvalue head List.mem_cons_self)
        (eliminateLinks_pos_on value tail
          (fun id hid => hvalue id (List.mem_cons_of_mem head hid)))

private theorem qOfNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  cases value with
  | zero => contradiction
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 1. The surviving vacuum amplitude is purely multiplicity support -/

/-- The literal lower-half physical labelling with vacuum fixed and upper
coordinates. -/
def centralVacuumLowerPhysical (source : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 source
    zeroEdgeLabelling zeroEdgeLabelling

/-- The natural-number product of all lower-link fusion multiplicities seen
by a source against the all-vacuum boundary. -/
def centralVacuumLowerLinkMultiplicityProduct
    (K : Nat) (source : EdgeLabelling) : Nat :=
  slabLinkMultiplicityProductOn K (centralExtent 0)
    (centralVacuumLowerPhysical source) (centralLowerLinks 0)

theorem centralVacuumLowerFaceFactor_pos
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    (0 : Q') < slabFaceFactorOn w K
      (centralVacuumLowerPhysical source) (centralLowerFaceIds 0) := by
  have hsourceSound := boundedEdgeLabellings_sound
    K (centralLowerFaceIds 0) source hsource
  unfold slabFaceFactorOn
  apply eliminateLinks_pos_on
  intro id hid
  have hlower := mem_centralLowerFaceIds.mp hid
  have hspin : centralVacuumLowerPhysical source id < K + 1 := by
    unfold centralVacuumLowerPhysical
    rw [assembleReflectedSlabLabelling_lower hlower.1 hlower.2]
    exact hsourceSound.1 id hid
  rw [coeffAt_heatKernelPacket hspin]
  exact coeffW_pos hw _

/-- At strictly positive coupling, a retained source has positive
all-vacuum half-amplitude exactly when its lower-link multiplicity product is
positive. -/
theorem centralHalfAmplitude_vacuum_pos_iff_lowerLinkProduct_pos
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    (0 : Q') < centralHalfAmplitude w K 0
        source zeroEdgeLabelling ↔
      0 < centralVacuumLowerLinkMultiplicityProduct K source := by
  have hface := centralVacuumLowerFaceFactor_pos hw K source hsource
  unfold centralHalfAmplitude centralLowerFactor
    centralVacuumLowerLinkMultiplicityProduct centralVacuumLowerPhysical
  constructor
  · intro hamplitude
    have hqProduct :
        (0 : Q') < Q'.ofNat
          (slabLinkMultiplicityProductOn K (centralExtent 0)
            (assembleReflectedSlabLabelling 0 source
              zeroEdgeLabelling zeroEdgeLabelling)
            (centralLowerLinks 0)) :=
      q_right_pos_of_mul_pos (Q'.le_of_lt hface) hamplitude
    have hnum := Q'.num_pos_of_pos hqProduct
    change (0 : Int) < Int.ofNat
      (slabLinkMultiplicityProductOn K (centralExtent 0)
        (assembleReflectedSlabLabelling 0 source
          zeroEdgeLabelling zeroEdgeLabelling)
        (centralLowerLinks 0)) at hnum
    exact Int.ofNat_lt.mp hnum
  · intro hproduct
    exact Q'.mul_pos hface (qOfNat_pos_of_pos _ hproduct)

/-! ## 2. Exact finite-sector multiplicity filter -/

def centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun source => decide
      (0 < centralVacuumLowerLinkMultiplicityProduct K
        (centralPhysicalFiniteStateAt w hw K 0 source)))

theorem mem_positiveLowerLinkIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat} :
    source ∈
        centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
          w hw K ↔
      source ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
        0 < centralVacuumLowerLinkMultiplicityProduct K
          (centralPhysicalFiniteStateAt w hw K 0 source) := by
  unfold centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
  simp only [List.mem_filter, decide_eq_true_eq]

theorem centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices_eq_lowerLinkIndices
    {w : Q'} (hw : (0 : Q') ≤ w) (hwpos : (0 : Q') < w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
        w hw K =
      centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
        w hw K := by
  unfold centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
    centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
  apply List.filter_congr
  intro source hsource
  have hsourceState :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralPhysicalFiniteVacuumSectorStates w hw K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w hw K 0 hsource rfl
  have hsourceHalf :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralHalfStates K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_halfStates
      w hw K 0 hsourceState
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact centralHalfAmplitude_vacuum_pos_iff_lowerLinkProduct_pos
    hwpos K (centralPhysicalFiniteStateAt w hw K 0 source) hsourceHalf

/-- At positive coupling, routing-level root predecessors are exactly the
states whose literal lower-link multiplicity product is positive. -/
theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_lowerLinkIndices
    {w : Q'} (hw : (0 : Q') ≤ w) (hwpos : (0 : Q') < w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K =
      centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
        w hw K :=
  Eq.trans
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_amplitudeIndices
      w hw K)
    (centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices_eq_lowerLinkIndices
      hw hwpos K)

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_lowerLinkCount
    {w : Q'} (hw : (0 : Q') ≤ w) (hwpos : (0 : Q') < w)
    (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
        w hw K).length =
      (centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
        w hw K).length :=
  congrArg List.length
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_lowerLinkIndices
      hw hwpos K)

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.centralVacuumLowerFaceFactor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.centralHalfAmplitude_vacuum_pos_iff_lowerLinkProduct_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.mem_positiveLowerLinkIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices_eq_lowerLinkIndices
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_lowerLinkIndices
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_lowerLinkCount
