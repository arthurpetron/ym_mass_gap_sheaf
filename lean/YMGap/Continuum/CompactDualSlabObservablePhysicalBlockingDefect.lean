/-
# Exact physical blocking defect for the literal slab face covariance

The corrected-slab block kernel is stochastic.  Consequently a coarse Boolean
face event pulls back to a `[0,1]`-valued conditional probability on a fine
source, not in general to the original fine Boolean event.  Strict pointwise
event preservation would therefore be an unnecessarily strong RG hypothesis.

This module isolates the exact weaker seam.  For a fine/coarse face pair it
defines three computed local pullback defects (root, target, and joint) and
uses the already-defined physical pushforward remainder for the discrepancy
between the pushed law and the coarse Gibbs law.  Finite probability algebra
then proves

  fine face covariance
    <= coarse contractive rate
       + (root + target + joint pullback defects)
       + three copies of the physical remainder L1 norm.

The coefficient-level paired-support theorem supplies the coarse contractive
rate as soon as the blocked datum enters the residual-coefficient corridor.
The final theorem is specialized to the actual globally link-glued cutoff-one
physical kernel, so no abstract Markov kernel inhabitant is being assumed.

This does not prove that either displayed transport error decays with block
depth or separation.  Those two explicit finite quantities are the remaining
interacting four-dimensional observable-transport producer.

Constructive contract: finite exact-rational probability algebra and the
existing source-indexed physical block kernel only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalRemainderLocality
import YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
import YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem le_add_of_sub_le_local {a b error : Q'}
    (h : a + (-b) <= error) : a <= b + error := by
  have hstep := Q'.add_le_add_right (a + (-b)) error b h
  have hcancel : ((a + (-b)) + b).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a ((-b) + b) 0
        (Q'.neg_add_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hcancel)
    (Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (Q'.add_comm_eqv error b)))

private theorem reassoc_cancel_local (left middle residual : Q') :
    (left + (-middle)) + (middle + residual) ≈ left + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left left
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem productDifference_decompose
    (fineRoot fineTarget coarseRoot coarseTarget : Q') :
    coarseRoot * coarseTarget - fineRoot * fineTarget ≈
      (coarseRoot - fineRoot) * coarseTarget +
        fineRoot * (coarseTarget - fineTarget) := by
  change
    coarseRoot * coarseTarget + (-(fineRoot * fineTarget)) ≈
      (coarseRoot + (-fineRoot)) * coarseTarget +
        fineRoot * (coarseTarget + (-fineTarget))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    ((coarseRoot * coarseTarget + (-(fineRoot * coarseTarget))) +
      (fineRoot * coarseTarget + (-(fineRoot * fineTarget)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv coarseRoot (-fineRoot) coarseTarget)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_mul_eqv fineRoot coarseTarget)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv fineRoot coarseTarget (-fineTarget))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_neg_eqv fineRoot fineTarget)))
  · exact reassoc_cancel_local
      (coarseRoot * coarseTarget) (fineRoot * coarseTarget)
      (-(fineRoot * fineTarget))

private theorem covarianceDifference_decompose
    (fineJoint fineRoot fineTarget coarseJoint coarseRoot coarseTarget : Q') :
    (fineJoint - fineRoot * fineTarget) +
        (-(coarseJoint - coarseRoot * coarseTarget)) ≈
      (fineJoint - coarseJoint) +
        (coarseRoot * coarseTarget - fineRoot * fineTarget) := by
  change
    (fineJoint + (-(fineRoot * fineTarget))) +
        (-(coarseJoint + (-(coarseRoot * coarseTarget)))) ≈
      (fineJoint + (-coarseJoint)) +
        (coarseRoot * coarseTarget + (-(fineRoot * fineTarget)))
  refine Q'.eqv_trans _
    ((fineJoint + (-(fineRoot * fineTarget))) +
      ((-coarseJoint) + (-(-(coarseRoot * coarseTarget))))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv coarseJoint (-(coarseRoot * coarseTarget)))
  refine Q'.eqv_trans _
    ((fineJoint + (-(fineRoot * fineTarget))) +
      ((-coarseJoint) + (coarseRoot * coarseTarget))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left (-coarseJoint) _ _
        (Q'.neg_neg_eqv (coarseRoot * coarseTarget)))
  refine Q'.eqv_trans _
    ((fineJoint + (-coarseJoint)) +
      ((-(fineRoot * fineTarget)) + coarseRoot * coarseTarget)) _ ?_ ?_
  · exact Q'.add_swap_inner fineJoint (-(fineRoot * fineTarget))
      (-coarseJoint) (coarseRoot * coarseTarget)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.add_comm_eqv (-(fineRoot * fineTarget))
      (coarseRoot * coarseTarget))

/-! ## 1. Normalized finite moments of the genuine slab law -/

/-- Event mass under the normalized corrected-slab physical law. -/
def normalizedSlabEventMass
    (D : SlabPhysicalData) (event : EdgeLabelling -> Bool) : Q' :=
  finiteEventMass D.normalizedMass D.physicalLabellings event

/-- Normalizing the summands first gives the same event probability as
normalizing the event numerator after summation. -/
theorem normalizedSlabEventMass_eqv_probability
    (D : SlabPhysicalData) (event : EdgeLabelling -> Bool) :
    normalizedSlabEventMass D event ≈
      finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        event := by
  let partitionPositive :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  let reciprocal := Q'.recipPos D.physicalPartition partitionPositive
  unfold normalizedSlabEventMass finiteEventMass
    finiteWeightedEventProbability finiteWeightedEventMass
    SlabPhysicalData.normalizedMass Q'.divPos
  change
    listQSum
        (fun physical =>
          if event physical then D.physicalTerm physical * reciprocal else 0)
        D.physicalLabellings ≈
      listQSum D.physicalTerm
          (D.physicalLabellings.filter event) * reciprocal
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (if event physical then D.physicalTerm physical else 0) * reciprocal)
      D.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro physical _
    cases hevent : event physical
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.zero_mul_eqv reciprocal)
    · simp only [if_true]
      exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
        (fun physical =>
          if event physical then D.physicalTerm physical else 0)
        D.physicalLabellings * reciprocal) _
    (listQSum_mul_const
      (fun physical =>
        if event physical then D.physicalTerm physical else 0)
      reciprocal D.physicalLabellings) ?_
  exact Q'.mul_eqv_congr_right _ _ reciprocal
    (Q'.eqv_symm
      (listQSum_filter D.physicalTerm event D.physicalLabellings))

/-- Joint positivity of the two named slab faces. -/
def slabPhysicalFacePairPositiveB
    (rootFaceId targetFaceId : Nat) (physical : EdgeLabelling) : Bool :=
  slabPhysicalFacePositiveB rootFaceId physical &&
    slabPhysicalFacePositiveB targetFaceId physical

/-- The same face covariance written directly using the normalized physical
mass that the block kernel pushes forward. -/
def normalizedSlabFaceBooleanCovariance
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  normalizedSlabEventMass D
      (slabPhysicalFacePairPositiveB rootFaceId targetFaceId) -
    normalizedSlabEventMass D (slabPhysicalFacePositiveB rootFaceId) *
      normalizedSlabEventMass D (slabPhysicalFacePositiveB targetFaceId)

/-- Exact bridge from the established physical face covariance to its
normalized-mass presentation used by the stochastic block kernel. -/
theorem slabPhysicalFaceBooleanCovariance_eqv_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabPhysicalFaceBooleanCovariance D rootFaceId targetFaceId ≈
      normalizedSlabFaceBooleanCovariance D rootFaceId targetFaceId := by
  have hjoint := normalizedSlabEventMass_eqv_probability D
    (slabPhysicalFacePairPositiveB rootFaceId targetFaceId)
  have hroot := normalizedSlabEventMass_eqv_probability D
    (slabPhysicalFacePositiveB rootFaceId)
  have htarget := normalizedSlabEventMass_eqv_probability D
    (slabPhysicalFacePositiveB targetFaceId)
  unfold slabPhysicalFaceBooleanCovariance
    normalizedSlabFaceBooleanCovariance
    finiteWeightedBooleanCovariance slabPhysicalFacePairPositiveB at *
  exact sub_eqv_both_local (Q'.eqv_symm hjoint)
    (mul_eqv_both_local (Q'.eqv_symm hroot) (Q'.eqv_symm htarget))

/-! ## 2. A witness-bearing fine/coarse face map and computed defects -/

/-- The four literal face coordinates compared by one slab blocking step.
Membership is carried as data so the final rate is about actual physical
plaquettes at both scales, not default values outside the face carrier. -/
structure SlabFaceBlockMap (S : SlabScalePair) : Type where
  fineRoot : Nat
  fineTarget : Nat
  coarseRoot : Nat
  coarseTarget : Nat
  fineRoot_mem : fineRoot ∈ slabPhysicalFaceEdges S.fine.extent
  fineTarget_mem : fineTarget ∈ slabPhysicalFaceEdges S.fine.extent
  coarseRoot_mem : coarseRoot ∈ slabPhysicalFaceEdges S.coarse.extent
  coarseTarget_mem : coarseTarget ∈ slabPhysicalFaceEdges S.coarse.extent

def fineFaceMoment {S : SlabScalePair}
    (_K : S.FiniteSlabKernel) (faceId : Nat) : Q' :=
  PhysicalKernel.fineCylinderMass _K (slabPhysicalFacePositiveB faceId)

def blockedFaceMoment {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (faceId : Nat) : Q' :=
  PhysicalKernel.blockedCylinderMass K (slabPhysicalFacePositiveB faceId)

def coarseFaceMoment {S : SlabScalePair}
    (_K : S.FiniteSlabKernel) (faceId : Nat) : Q' :=
  PhysicalKernel.coarseCylinderMass _K (slabPhysicalFacePositiveB faceId)

def fineFacePairMoment {S : SlabScalePair}
    (_K : S.FiniteSlabKernel) (rootFaceId targetFaceId : Nat) : Q' :=
  PhysicalKernel.fineCylinderMass _K
    (slabPhysicalFacePairPositiveB rootFaceId targetFaceId)

def blockedFacePairMoment {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (rootFaceId targetFaceId : Nat) : Q' :=
  PhysicalKernel.blockedCylinderMass K
    (slabPhysicalFacePairPositiveB rootFaceId targetFaceId)

def coarseFacePairMoment {S : SlabScalePair}
    (_K : S.FiniteSlabKernel) (rootFaceId targetFaceId : Nat) : Q' :=
  PhysicalKernel.coarseCylinderMass _K
    (slabPhysicalFacePairPositiveB rootFaceId targetFaceId)

/-- Local stochastic distortion of one literal face moment before replacing
the pushed law by the coarse Gibbs law. -/
def facePullbackDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (fineFaceId coarseFaceId : Nat) : Q' :=
  Q'.abs
    (blockedFaceMoment K coarseFaceId - fineFaceMoment K fineFaceId)

/-- Local stochastic distortion of the joint two-face moment. -/
def facePairPullbackDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  Q'.abs
    (blockedFacePairMoment K coarseRoot coarseTarget -
      fineFacePairMoment K fineRoot fineTarget)

/-- Sum of exactly the three local moment distortions consumed by Boolean
covariance. -/
def observablePullbackDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) : Q' :=
  facePairPullbackDefect K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget +
    (facePullbackDefect K M.fineRoot M.coarseRoot +
      facePullbackDefect K M.fineTarget M.coarseTarget)

/-- Full fine/coarse Gibbs moment discrepancy for one face. -/
def faceBlockingMomentDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (fineFaceId coarseFaceId : Nat) : Q' :=
  Q'.abs
    (coarseFaceMoment K coarseFaceId - fineFaceMoment K fineFaceId)

/-- Full fine/coarse Gibbs discrepancy for the joint two-face moment. -/
def facePairBlockingMomentDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  Q'.abs
    (coarseFacePairMoment K coarseRoot coarseTarget -
      fineFacePairMoment K fineRoot fineTarget)

/-- The three fine/coarse moment discrepancies controlling covariance. -/
def observableBlockingMomentDefect {S : SlabScalePair}
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) : Q' :=
  facePairBlockingMomentDefect K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget +
    (faceBlockingMomentDefect K M.fineRoot M.coarseRoot +
      faceBlockingMomentDefect K M.fineTarget M.coarseTarget)

/-- The physical pushforward remainder is tested once for each of the root,
target, and joint moments. -/
def threePhysicalRemainderCost {S : SlabScalePair}
    (K : S.FiniteSlabKernel) : Q' :=
  K.remainderL1 + (K.remainderL1 + K.remainderL1)

/-! ## 3. Exact decomposition: local pullback distortion plus law remainder -/

/-- For any fine/coarse event pair, its direct Gibbs moment discrepancy is at
most the local stochastic pullback defect plus the physical remainder norm. -/
theorem coarseFineCylinderDefect_le_pullback_add_remainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling -> Bool) :
    Q'.abs
        (PhysicalKernel.coarseCylinderMass K coarseEvent -
          PhysicalKernel.fineCylinderMass K fineEvent) <=
      Q'.abs
          (PhysicalKernel.blockedCylinderMass K coarseEvent -
            PhysicalKernel.fineCylinderMass K fineEvent) +
        K.remainderL1 := by
  have hdecomposition :=
    PhysicalKernel.blockedCylinderMass_decomposition K coarseEvent
  have hcoarseBlockedEq :
      PhysicalKernel.coarseCylinderMass K coarseEvent -
          PhysicalKernel.blockedCylinderMass K coarseEvent ≈
        -(PhysicalKernel.cylinderRemainder K coarseEvent) := by
    let coarse := PhysicalKernel.coarseCylinderMass K coarseEvent
    let blocked := PhysicalKernel.blockedCylinderMass K coarseEvent
    let remainder := PhysicalKernel.cylinderRemainder K coarseEvent
    change coarse + (-blocked) ≈ -remainder
    refine Q'.eqv_trans _ (coarse + (-(coarse + remainder))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left
        coarse _ _
        (Q'.neg_eqv_congr _ _ hdecomposition)
    refine Q'.eqv_trans _ (coarse + ((-coarse) + (-remainder))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left coarse _ _
        (Q'.neg_add_eqv coarse remainder)
    refine Q'.eqv_trans _ ((coarse + (-coarse)) + (-remainder)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.add_assoc_eqv coarse (-coarse) (-remainder))
    refine Q'.eqv_trans _ (0 + (-remainder)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ (-remainder)
        (Q'.add_neg_self_eqv coarse)
    exact Q'.eqv_of_eq (Q'.zero_add' (-remainder))
  have hcoarseBlocked :
      Q'.abs
          (PhysicalKernel.coarseCylinderMass K coarseEvent -
            PhysicalKernel.blockedCylinderMass K coarseEvent) <=
        K.remainderL1 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hcoarseBlockedEq))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_neg' (PhysicalKernel.cylinderRemainder K coarseEvent)))
        (PhysicalKernel.cylinderRemainder_abs_le_remainderL1
          K coarseEvent))
  have hsplit :
      PhysicalKernel.coarseCylinderMass K coarseEvent -
          PhysicalKernel.fineCylinderMass K fineEvent ≈
        (PhysicalKernel.coarseCylinderMass K coarseEvent -
            PhysicalKernel.blockedCylinderMass K coarseEvent) +
          (PhysicalKernel.blockedCylinderMass K coarseEvent -
            PhysicalKernel.fineCylinderMass K fineEvent) := by
    exact Q'.eqv_symm
      (reassoc_cancel_local
        (PhysicalKernel.coarseCylinderMass K coarseEvent)
        (PhysicalKernel.blockedCylinderMass K coarseEvent)
        (-(PhysicalKernel.fineCylinderMass K fineEvent)))
  have htriangle := Q'.abs_add_le'
    (PhysicalKernel.coarseCylinderMass K coarseEvent -
      PhysicalKernel.blockedCylinderMass K coarseEvent)
    (PhysicalKernel.blockedCylinderMass K coarseEvent -
      PhysicalKernel.fineCylinderMass K fineEvent)
  have hsum := Q'.add_le_add hcoarseBlocked
    (Q'.le_refl'
      (Q'.abs
        (PhysicalKernel.blockedCylinderMass K coarseEvent -
          PhysicalKernel.fineCylinderMass K fineEvent)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv
          (Q'.add_comm_eqv K.remainderL1
            (Q'.abs
              (PhysicalKernel.blockedCylinderMass K coarseEvent -
                PhysicalKernel.fineCylinderMass K fineEvent))))))

theorem faceBlockingMomentDefect_le_pullback_add_remainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) :
    faceBlockingMomentDefect K fineFaceId coarseFaceId <=
      facePullbackDefect K fineFaceId coarseFaceId + K.remainderL1 := by
  unfold faceBlockingMomentDefect facePullbackDefect
    fineFaceMoment blockedFaceMoment coarseFaceMoment
  exact coarseFineCylinderDefect_le_pullback_add_remainder K
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

theorem facePairBlockingMomentDefect_le_pullback_add_remainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) :
    facePairBlockingMomentDefect K
        fineRoot fineTarget coarseRoot coarseTarget <=
      facePairPullbackDefect K
          fineRoot fineTarget coarseRoot coarseTarget + K.remainderL1 := by
  unfold facePairBlockingMomentDefect facePairPullbackDefect
    fineFacePairMoment blockedFacePairMoment coarseFacePairMoment
  exact coarseFineCylinderDefect_le_pullback_add_remainder K
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- The complete covariance moment defect splits into the three computed
local stochastic distortions plus exactly three remainder tests. -/
theorem observableBlockingMomentDefect_le_transportBudget
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    observableBlockingMomentDefect K M <=
      observablePullbackDefect K M + threePhysicalRemainderCost K := by
  have hjoint := facePairBlockingMomentDefect_le_pullback_add_remainder K
    M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget
  have hroot := faceBlockingMomentDefect_le_pullback_add_remainder K
    M.fineRoot M.coarseRoot
  have htarget := faceBlockingMomentDefect_le_pullback_add_remainder K
    M.fineTarget M.coarseTarget
  have hsum := Q'.add_le_add hjoint (Q'.add_le_add hroot htarget)
  unfold observableBlockingMomentDefect observablePullbackDefect
    threePhysicalRemainderCost at *
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (by ac_qeqv))

/-! ## 4. Three moment errors control Boolean covariance -/

/-- Stability of a Boolean covariance under separately controlled joint,
root, and target moments.  Only the probability bounds actually needed by
the product decomposition are assumed. -/
theorem covariance_le_add_momentDefects
    (fineJoint fineRoot fineTarget coarseJoint coarseRoot coarseTarget : Q')
    (hfineRootNonnegative : (0 : Q') <= fineRoot)
    (hfineRootLeOne : fineRoot <= (1 : Q'))
    (hcoarseTargetNonnegative : (0 : Q') <= coarseTarget)
    (hcoarseTargetLeOne : coarseTarget <= (1 : Q')) :
    fineJoint - fineRoot * fineTarget <=
      coarseJoint - coarseRoot * coarseTarget +
        (Q'.abs (coarseJoint - fineJoint) +
          (Q'.abs (coarseRoot - fineRoot) +
            Q'.abs (coarseTarget - fineTarget))) := by
  have hjoint : fineJoint - coarseJoint <=
      Q'.abs (coarseJoint - fineJoint) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_abs_self (fineJoint - coarseJoint))
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm fineJoint coarseJoint))
  have hroot : coarseRoot - fineRoot <=
      Q'.abs (coarseRoot - fineRoot) :=
    Q'.le_abs_self _
  have htarget : coarseTarget - fineTarget <=
      Q'.abs (coarseTarget - fineTarget) :=
    Q'.le_abs_self _
  have hrootCost :
      (coarseRoot - fineRoot) * coarseTarget <=
        Q'.abs (coarseRoot - fineRoot) := by
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (coarseRoot - fineRoot) (Q'.abs (coarseRoot - fineRoot))
      coarseTarget hroot hcoarseTargetNonnegative
    have hpaid := Q'.mul_le_mul_of_nonneg_left
      coarseTarget (1 : Q') (Q'.abs (coarseRoot - fineRoot))
      hcoarseTargetLeOne (Q'.abs_nonneg (coarseRoot - fineRoot))
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ hpaid
        (Q'.le_of_eqv (Q'.mul_one_eqv
          (Q'.abs (coarseRoot - fineRoot)))))
  have htargetCost :
      fineRoot * (coarseTarget - fineTarget) <=
        Q'.abs (coarseTarget - fineTarget) := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      (coarseTarget - fineTarget) (Q'.abs (coarseTarget - fineTarget))
      fineRoot htarget hfineRootNonnegative
    have hpaid := Q'.mul_le_mul_of_nonneg_right
      fineRoot (1 : Q') (Q'.abs (coarseTarget - fineTarget))
      hfineRootLeOne (Q'.abs_nonneg (coarseTarget - fineTarget))
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ hpaid
        (Q'.le_of_eqv (Q'.one_mul_eqv
          (Q'.abs (coarseTarget - fineTarget)))))
  have hproduct :
      coarseRoot * coarseTarget - fineRoot * fineTarget <=
        Q'.abs (coarseRoot - fineRoot) +
          Q'.abs (coarseTarget - fineTarget) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (productDifference_decompose
          fineRoot fineTarget coarseRoot coarseTarget))
      (Q'.add_le_add hrootCost htargetCost)
  have hcovarianceDifference :
      (fineJoint - fineRoot * fineTarget) +
          (-(coarseJoint - coarseRoot * coarseTarget)) <=
        Q'.abs (coarseJoint - fineJoint) +
          (Q'.abs (coarseRoot - fineRoot) +
            Q'.abs (coarseTarget - fineTarget)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (covarianceDifference_decompose
          fineJoint fineRoot fineTarget
          coarseJoint coarseRoot coarseTarget))
      (Q'.add_le_add hjoint hproduct)
  exact le_add_of_sub_le_local hcovarianceDifference

/-- The literal normalized fine face covariance differs from its coarse
counterpart by no more than the three exact blocking moment defects. -/
theorem normalizedSlabFaceBooleanCovariance_le_add_blockingMomentDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    normalizedSlabFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget <=
      normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget +
        observableBlockingMomentDefect K M := by
  have hfineRootNonnegative :
      (0 : Q') <= fineFaceMoment K M.fineRoot := by
    unfold fineFaceMoment PhysicalKernel.fineCylinderMass
    exact finiteEventMass_nonnegative
      S.fine.normalizedMass S.fine.physicalLabellings
      (slabPhysicalFacePositiveB M.fineRoot)
      (fun physical _ => S.fine.normalizedMass_nonnegative physical)
  have hfineRootLeOne : fineFaceMoment K M.fineRoot <= (1 : Q') := by
    unfold fineFaceMoment PhysicalKernel.fineCylinderMass
    exact finiteEventMass_le_one
      S.fine.normalizedMass S.fine.physicalLabellings
      (slabPhysicalFacePositiveB M.fineRoot)
      (fun physical _ => S.fine.normalizedMass_nonnegative physical)
      S.fine.normalizedMass_total
  have hcoarseTargetNonnegative :
      (0 : Q') <= coarseFaceMoment K M.coarseTarget := by
    unfold coarseFaceMoment PhysicalKernel.coarseCylinderMass
    exact finiteEventMass_nonnegative
      S.coarse.normalizedMass S.coarse.physicalLabellings
      (slabPhysicalFacePositiveB M.coarseTarget)
      (fun physical _ => S.coarse.normalizedMass_nonnegative physical)
  have hcoarseTargetLeOne :
      coarseFaceMoment K M.coarseTarget <= (1 : Q') := by
    unfold coarseFaceMoment PhysicalKernel.coarseCylinderMass
    exact finiteEventMass_le_one
      S.coarse.normalizedMass S.coarse.physicalLabellings
      (slabPhysicalFacePositiveB M.coarseTarget)
      (fun physical _ => S.coarse.normalizedMass_nonnegative physical)
      S.coarse.normalizedMass_total
  exact covariance_le_add_momentDefects
    (fineFacePairMoment K M.fineRoot M.fineTarget)
    (fineFaceMoment K M.fineRoot)
    (fineFaceMoment K M.fineTarget)
    (coarseFacePairMoment K M.coarseRoot M.coarseTarget)
    (coarseFaceMoment K M.coarseRoot)
    (coarseFaceMoment K M.coarseTarget)
    hfineRootNonnegative hfineRootLeOne
    hcoarseTargetNonnegative hcoarseTargetLeOne

/-! ## 5. Coefficient capture plus the physical transport budget -/

/-- A coefficient-captured coarse datum controls the original fine literal
face covariance up to the two exact physical blocking errors: local Markov
observable distortion and the pushed-law remainder. -/
theorem slabPhysicalFaceBooleanCovariance_le_blockedRate_add_transportBudget
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (hcoarsePositive : (0 : Q') < S.coarse.coupling)
    (hcoarseLtOne : S.coarse.coupling < (1 : Q'))
    (hcoefficient :
      exteriorFaceCoefficient S.coarse.coupling 0 <= anchorFaceCoefficient) :
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget <=
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        (observablePullbackDefect K M + threePhysicalRemainderCost K) := by
  have hfine :=
    normalizedSlabFaceBooleanCovariance_le_add_blockingMomentDefect K M
  have hdefect := observableBlockingMomentDefect_le_transportBudget K M
  have hcoarseObservable :=
    slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
      S.coarse hcoarsePositive hcoarseLtOne hcoefficient
      M.coarseRoot M.coarseTarget M.coarseTarget_mem
  have hcoarsePhysical :
      normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget <=
        slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (slabPhysicalFaceBooleanCovariance_eqv_normalized
          S.coarse M.coarseRoot M.coarseTarget))
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (slabObservableFaceBooleanCovariance_eqv_physical
            S.coarse M.coarseRoot M.coarseTarget))
        hcoarseObservable)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabPhysicalFaceBooleanCovariance_eqv_normalized
        S.fine M.fineRoot M.fineTarget))
    (Q'.le_trans' _ _ _ hfine
      (Q'.add_le_add hcoarsePhysical hdefect))

/-- The preceding theorem for the actual globally link-glued cutoff-one
physical slab kernel.  The remaining budget contains only computed finite
quantities of that concrete kernel. -/
theorem cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_transportBudget
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarsePositive : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S)
    (hcoarseLtOne : S.coarse.coupling < (1 : Q'))
    (hcoefficient :
      exteriorFaceCoefficient S.coarse.coupling 0 <= anchorFaceCoefficient) :
    let K := physicalKernel S hfineCutoff hcoarsePositive
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget <=
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        (observablePullbackDefect K M + threePhysicalRemainderCost K) := by
  let K := physicalKernel S hfineCutoff hcoarsePositive
  exact slabPhysicalFaceBooleanCovariance_le_blockedRate_add_transportBudget
    K M hcoarsePositive hcoarseLtOne hcoefficient

#print axioms normalizedSlabEventMass
#print axioms normalizedSlabEventMass_eqv_probability
#print axioms normalizedSlabFaceBooleanCovariance
#print axioms slabPhysicalFaceBooleanCovariance_eqv_normalized
#print axioms observablePullbackDefect
#print axioms observableBlockingMomentDefect
#print axioms coarseFineCylinderDefect_le_pullback_add_remainder
#print axioms observableBlockingMomentDefect_le_transportBudget
#print axioms covariance_le_add_momentDefects
#print axioms normalizedSlabFaceBooleanCovariance_le_add_blockingMomentDefect
#print axioms slabPhysicalFaceBooleanCovariance_le_blockedRate_add_transportBudget
#print axioms cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_transportBudget

end YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
