/-
# Posterior normalization of the cutoff-two support-aware defect

The structural-zero-safe defect from the preceding module is an unnormalised
distance between two positive BF4 boundary-row measures.  This file
normalizes each retained raw row by its explicit positive row mass and proves
the exact identity obtained by choosing the relative scale to be the raw
left/right mass ratio:

  defectMoment = leftRawMass * pairwiseBoundaryPosteriorL1.

Consequently the defect fraction divided by the right raw mass is exactly
the raw mass ratio times that posterior `L1` distance.  This is both a useful
bridge and a diagnostic boundary: posterior mixing controls the shape of the
normalized rows, but the self-normalizing identity still carries the very
mass ratio that the conditional-flow argument must bound independently.

No posterior estimate, uniform ratio bound, payment, completed gap
inhabitant, thermodynamic/continuum construction, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

/-! ## 1. The normalized raw boundary row -/

/-- Boundary law obtained by dividing one literal raw BF4 boundary row by
its constructively positive raw row mass. -/
def cutoffTwoRawBoundaryGivenState
    (later source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (cutoffTwoRawBoundaryMomentTerm later source boundary)
    (cutoffTwoRawStationaryRowMass later source)
    (cutoffTwoRawStationaryRowMass_pos hsource)

theorem cutoffTwoRawBoundaryGivenState_nonnegative_on
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels later 0) :
    (0 : Q') ≤
      cutoffTwoRawBoundaryGivenState
        later source hsource boundary := by
  unfold cutoffTwoRawBoundaryGivenState Q'.divPos
  exact Q'.mul_nonneg _ _
    (cutoffTwoRawBoundaryMomentTerm_nonnegative
      later source hboundary)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Every retained normalized raw boundary row has total mass one. -/
theorem cutoffTwoRawBoundaryGivenState_total_one
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later) :
    listQSum
        (cutoffTwoRawBoundaryGivenState later source hsource)
        (centralBoundaryChannels later 0) ≈
      1 := by
  let mass := cutoffTwoRawStationaryRowMass later source
  let reciprocal := Q'.recipPos mass
    (cutoffTwoRawStationaryRowMass_pos hsource)
  unfold cutoffTwoRawBoundaryGivenState Q'.divPos
  refine Q'.eqv_trans _
    (cutoffTwoRawBoundaryMoment later source * reciprocal) _ ?_ ?_
  · exact listQSum_mul_right
      (cutoffTwoRawBoundaryMomentTerm later source)
      reciprocal (centralBoundaryChannels later 0)
  refine Q'.eqv_trans _ (mass * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal
      (Q'.eqv_symm
        (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hsource))
  exact Q'.mul_recipPos_eqv mass
    (cutoffTwoRawStationaryRowMass_pos hsource)

/-- Multiplying the normalized raw posterior by its row mass recovers the
literal boundary-moment term. -/
theorem cutoffTwoRawBoundaryGivenState_mul_rowMass_eqv_term
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (boundary : EdgeLabelling) :
    cutoffTwoRawStationaryRowMass later source *
        cutoffTwoRawBoundaryGivenState
          later source hsource boundary ≈
      cutoffTwoRawBoundaryMomentTerm later source boundary := by
  refine Q'.eqv_trans _
    (cutoffTwoRawBoundaryGivenState
        later source hsource boundary *
      cutoffTwoRawStationaryRowMass later source) _ ?_ ?_
  · exact Q'.mul_comm_eqv _ _
  unfold cutoffTwoRawBoundaryGivenState
  exact Q'.divPos_mul_eqv _ _ _

/-- The indexed source represented by every retained vacuum-sector index is
a member of the literal positive physical half-state carrier. -/
theorem cutoffTwoIndexedSource_mem_positive
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later) :
    centralPhysicalFiniteStateAt
        cutoffTwoHalfCoupling (by decide) later 0 source ∈
      centralPositiveHalfStates
        cutoffTwoHalfCoupling (by decide) later 0 :=
  centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 hsource)

/-- Opaque indexed presentation of the existing full-carrier physical
source-conditioned boundary posterior. -/
def cutoffTwoCentralBoundaryGivenState
    (later source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (boundary : EdgeLabelling) : Q' :=
  centralBoundaryGivenSource
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 source)
    (cutoffTwoIndexedSource_mem_positive hsource)
    boundary

/-- Opaque cutoff specialization of the existing full physical boundary
prior. -/
def cutoffTwoCentralBoundaryPrior
    (later : Nat) (boundary : EdgeLabelling) : Q' :=
  centralBoundaryPrior cutoffTwoHalfCoupling (by decide) later 0 boundary

/-- The raw-row posterior is not a new probability law: it is exactly the
project's full-positive-carrier source-conditioned boundary posterior, after
the global partition and row marginal are cancelled from the denominator. -/
theorem cutoffTwoRawBoundaryGivenState_eqv_centralBoundaryGivenSource
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (boundary : EdgeLabelling) :
    cutoffTwoRawBoundaryGivenState later source hsource boundary ≈
      cutoffTwoCentralBoundaryGivenState
        later source hsource boundary := by
  let sourceState := centralPhysicalFiniteStateAt
    cutoffTwoHalfCoupling (by decide) later 0 source
  let partition := slabParametricKPhysicalPartition
    cutoffTwoHalfCoupling later (centralExtent 0)
  let marginal := centralPhysicalRowMarginal
    cutoffTwoHalfCoupling (by decide) later 0 sourceState
  have hsourceState : sourceState ∈
      centralPositiveHalfStates
        cutoffTwoHalfCoupling (by decide) later 0 :=
    cutoffTwoIndexedSource_mem_positive hsource
  have hdenPos : (0 : Q') < partition * marginal :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        (by decide) later (centralExtent 0))
      ((mem_centralPositiveHalfStates_iff.mp hsourceState).2)
  have hmoment : cutoffTwoRawBoundaryMoment later source ≈
      partition * marginal := by
    unfold cutoffTwoRawBoundaryMoment
    exact centralBoundaryMoment_eq_partition_mul_marginal hsourceState
  have hden : cutoffTwoRawStationaryRowMass later source ≈
      partition * marginal :=
    Q'.eqv_trans _ _ _
      (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hsource)
      hmoment
  unfold cutoffTwoRawBoundaryGivenState
    cutoffTwoCentralBoundaryGivenState centralBoundaryGivenSource
    cutoffTwoRawBoundaryMomentTerm
  exact divPos_eqv_congr_local
    (cutoffTwoRawStationaryRowMass_pos hsource) hdenPos
    (Q'.eqv_refl _) hden

/-- Pairwise `L1` distance between two normalized literal raw boundary rows.
The project convention omits the probability-theory factor `1/2`. -/
def cutoffTwoRawBoundaryPosteriorL1
    (later left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) : Q' :=
  finiteL1Distance
    (centralBoundaryChannels later 0)
    (cutoffTwoRawBoundaryGivenState later left hleft)
    (cutoffTwoRawBoundaryGivenState later right hright)

/-- Pairwise `L1` distance written directly in the pre-existing physical
boundary-posterior API. -/
def cutoffTwoCentralBoundaryPosteriorL1
    (later left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) : Q' :=
  finiteL1Distance
    (centralBoundaryChannels later 0)
    (cutoffTwoCentralBoundaryGivenState later left hleft)
    (cutoffTwoCentralBoundaryGivenState later right hright)

theorem cutoffTwoRawBoundaryPosteriorL1_eqv_centralBoundaryPosteriorL1
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoRawBoundaryPosteriorL1
        later left right hleft hright ≈
      cutoffTwoCentralBoundaryPosteriorL1
        later left right hleft hright := by
  unfold cutoffTwoRawBoundaryPosteriorL1
    cutoffTwoCentralBoundaryPosteriorL1 finiteL1Distance
  apply listQSum_congr
  intro boundary
  exact Q'.abs_eqv_congr
    (Q'.add_eqv_congr'
      (cutoffTwoRawBoundaryGivenState_eqv_centralBoundaryGivenSource
        hleft boundary)
      (Q'.neg_eqv_congr _ _
        (cutoffTwoRawBoundaryGivenState_eqv_centralBoundaryGivenSource
          hright boundary)))

theorem cutoffTwoRawBoundaryPosteriorL1_nonnegative
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (0 : Q') ≤
      cutoffTwoRawBoundaryPosteriorL1
        later left right hleft hright := by
  unfold cutoffTwoRawBoundaryPosteriorL1 finiteL1Distance
  apply listQSum_nonnegative_on
  intro boundary _hboundary
  exact Q'.abs_nonneg _

/-- Finite `L1` satisfies the triangle inequality in the project's
unnormalized rational setoid. -/
theorem finiteL1Distance_triangle
    {State : Type} (states : List State)
    (left middle right : State → Q') :
    finiteL1Distance states left right ≤
      finiteL1Distance states left middle +
        finiteL1Distance states middle right := by
  unfold finiteL1Distance
  refine Q'.le_trans' _
    (listQSum
      (fun state =>
        Q'.abs (left state + (-middle state)) +
          Q'.abs (middle state + (-right state)))
      states) _ ?_ ?_
  · apply listQSum_mono
    intro state _hstate
    have hdecompose :
        left state + (-right state) ≈
          (left state + (-middle state)) +
            (middle state + (-right state)) := by
      have hinner :
          (-middle state) + (middle state + (-right state)) ≈
            -right state := by
        refine Q'.eqv_trans _
          (((-middle state) + middle state) + (-right state)) _ ?_ ?_
        · exact Q'.eqv_symm
            (Q'.add_assoc_eqv
              (-middle state) (middle state) (-right state))
        refine Q'.eqv_trans _ (0 + (-right state)) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ (-right state)
            (Q'.neg_add_self_eqv (middle state))
        exact Q'.eqv_of_eq (Q'.zero_add' (-right state))
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv
            (left state) (-middle state)
            (middle state + (-right state)))
          (Q'.add_eqv_congr_left
            (left state) _ _ hinner))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose)) ?_
    exact Q'.abs_add_le' _ _
  exact Q'.le_of_eqv
    (listQSum_add
      (fun state => Q'.abs (left state + (-middle state)))
      (fun state => Q'.abs (middle state + (-right state)))
      states)

theorem finiteL1Distance_symm
    {State : Type} (states : List State)
    (left right : State → Q') :
    finiteL1Distance states left right ≈
      finiteL1Distance states right left := by
  unfold finiteL1Distance
  apply listQSum_congr
  intro state
  exact YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
    (left state) (right state)

/-- Existing source-posterior distance from the full physical boundary
prior, specialized to the indexed cutoff-two vacuum carrier. -/
def cutoffTwoCentralBoundaryGivenSourceL1
    (later source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later) : Q' :=
  finiteL1Distance
    (centralBoundaryChannels later 0)
    (cutoffTwoCentralBoundaryGivenState later source hsource)
    (cutoffTwoCentralBoundaryPrior later)

theorem cutoffTwoCentralBoundaryGivenSourceL1_eqv_existing
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoCentralBoundaryGivenSourceL1 later source hsource ≈
      centralBoundaryGivenSourceL1
        cutoffTwoHalfCoupling (by decide) later 0
        (centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) later 0 source)
        (cutoffTwoIndexedSource_mem_positive hsource) := by
  unfold cutoffTwoCentralBoundaryGivenSourceL1
    cutoffTwoCentralBoundaryGivenState cutoffTwoCentralBoundaryPrior
    centralBoundaryGivenSourceL1
  exact Q'.eqv_refl _

/-- Pairwise posterior shape distance is controlled by the two already
defined distances to the common full physical boundary prior. -/
theorem cutoffTwoCentralBoundaryPosteriorL1_le_sourcePriorDistances
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoCentralBoundaryPosteriorL1
        later left right hleft hright ≤
      cutoffTwoCentralBoundaryGivenSourceL1 later left hleft +
        cutoffTwoCentralBoundaryGivenSourceL1 later right hright := by
  unfold cutoffTwoCentralBoundaryPosteriorL1
    cutoffTwoCentralBoundaryGivenSourceL1
  have htriangle := finiteL1Distance_triangle
    (centralBoundaryChannels later 0)
    (cutoffTwoCentralBoundaryGivenState later left hleft)
    (cutoffTwoCentralBoundaryPrior later)
    (cutoffTwoCentralBoundaryGivenState later right hright)
  refine Q'.le_trans' _ _ _ htriangle ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (finiteL1Distance_symm
        (centralBoundaryChannels later 0)
        (cutoffTwoCentralBoundaryPrior later)
        (cutoffTwoCentralBoundaryGivenState later right hright)))

/-! ## 2. Exact relative-defect normalization -/

/-- Positive raw left/right row-mass ratio, with the right-carrier witness
retained in its denominator. -/
def cutoffTwoRawRowMassRatio
    (later left right : Nat)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) : Q' :=
  Q'.divPos
    (cutoffTwoRawStationaryRowMass later left)
    (cutoffTwoRawStationaryRowMass later right)
    (cutoffTwoRawStationaryRowMass_pos hright)

theorem cutoffTwoRawRowMassRatio_mul_rightMass
    {later left right : Nat}
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoRawRowMassRatio later left right hright *
        cutoffTwoRawStationaryRowMass later right ≈
      cutoffTwoRawStationaryRowMass later left := by
  unfold cutoffTwoRawRowMassRatio
  exact Q'.divPos_mul_eqv _ _ _

theorem cutoffTwoRawRowMassRatio_nonnegative
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (0 : Q') ≤ cutoffTwoRawRowMassRatio later left right hright := by
  unfold cutoffTwoRawRowMassRatio Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt (cutoffTwoRawStationaryRowMass_pos hleft))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem weighted_relative_defect_eq_abs_raw_difference
    (weight total left right rho : Q')
    (hweight : (0 : Q') ≤ weight)
    (htotal : (0 : Q') ≤ total) :
    weight * (Q'.abs (left + (-(rho * right))) * total) ≈
      Q'.abs
        (weight * (left * total) +
          -(rho * (weight * (right * total)))) := by
  have hfactor : (0 : Q') ≤ weight * total :=
    Q'.mul_nonneg _ _ hweight htotal
  refine Q'.eqv_trans _
    ((weight * total) * Q'.abs (left + (-(rho * right)))) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _
    (Q'.abs (weight * total) *
      Q'.abs (left + (-(rho * right)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _
      (Q'.abs (left + (-(rho * right))))
      (Q'.eqv_symm
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hfactor))
  refine Q'.eqv_trans _
    (Q'.abs ((weight * total) * (left + (-(rho * right))))) _ ?_ ?_
  · exact Q'.eqv_symm
      (q_abs_mul_eqv (weight * total) (left + (-(rho * right))))
  exact Q'.abs_eqv_congr (by q_ring)

private theorem raw_moment_difference_eq_mass_mul_posterior_difference
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (boundary : EdgeLabelling) :
    cutoffTwoRawBoundaryMomentTerm later left boundary +
        -(cutoffTwoRawRowMassRatio later left right hright *
          cutoffTwoRawBoundaryMomentTerm later right boundary) ≈
      cutoffTwoRawStationaryRowMass later left *
        (cutoffTwoRawBoundaryGivenState
              later left hleft boundary +
          -(cutoffTwoRawBoundaryGivenState
              later right hright boundary)) := by
  let leftMass := cutoffTwoRawStationaryRowMass later left
  let rightMass := cutoffTwoRawStationaryRowMass later right
  let ratio := cutoffTwoRawRowMassRatio later left right hright
  let leftPosterior := cutoffTwoRawBoundaryGivenState
    later left hleft boundary
  let rightPosterior := cutoffTwoRawBoundaryGivenState
    later right hright boundary
  have hleftRecover : leftMass * leftPosterior ≈
      cutoffTwoRawBoundaryMomentTerm later left boundary :=
    cutoffTwoRawBoundaryGivenState_mul_rowMass_eqv_term
      hleft boundary
  have hrightRecover : rightMass * rightPosterior ≈
      cutoffTwoRawBoundaryMomentTerm later right boundary :=
    cutoffTwoRawBoundaryGivenState_mul_rowMass_eqv_term
      hright boundary
  have hratio : ratio * rightMass ≈ leftMass :=
    cutoffTwoRawRowMassRatio_mul_rightMass hright
  refine Q'.eqv_trans _
    (leftMass * leftPosterior +
      -(ratio * (rightMass * rightPosterior))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm hleftRecover)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left ratio _ _
          (Q'.eqv_symm hrightRecover)))
  refine Q'.eqv_trans _
    (leftMass * leftPosterior +
      -((ratio * rightMass) * rightPosterior)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv ratio rightMass rightPosterior)))
  refine Q'.eqv_trans _
    (leftMass * leftPosterior +
      -(leftMass * rightPosterior)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ rightPosterior hratio))
  refine Q'.eqv_trans _
    (leftMass * leftPosterior +
      leftMass * (-rightPosterior)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.mul_neg_eqv leftMass rightPosterior))
  exact Q'.eqv_symm
    (Q'.mul_add_eqv leftMass leftPosterior (-rightPosterior))

/-- At the self-normalizing raw mass ratio, each weighted amplitude defect is
exactly the left raw mass times the pointwise posterior difference. -/
theorem cutoffTwoRelativeDefectMomentTerm_eqv_leftMass_mul_posteriorDifference
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels later 0) :
    cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
        (cutoffTwoRawRowMassRatio later left right hright)
        later left right boundary ≈
      cutoffTwoRawStationaryRowMass later left *
        Q'.abs
          (cutoffTwoRawBoundaryGivenState later left hleft boundary +
            -(cutoffTwoRawBoundaryGivenState
              later right hright boundary)) := by
  let weight := centralBoundaryWeight
    cutoffTwoHalfCoupling later 0 boundary
  let total := centralPositiveBoundaryTotalHalfAmplitude
    cutoffTwoHalfCoupling (by decide) later 0 boundary
  let leftAmplitude := centralHalfAmplitude cutoffTwoHalfCoupling later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 left) boundary
  let rightAmplitude := centralHalfAmplitude cutoffTwoHalfCoupling later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 right) boundary
  let ratio := cutoffTwoRawRowMassRatio later left right hright
  have hweight : (0 : Q') ≤ weight :=
    centralBoundaryWeight_nonnegative_on
      (by decide) boundary hboundary
  have htotal : (0 : Q') ≤ total :=
    cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative
      later boundary
  unfold cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
    cutoffTwoHalfAmplitudeRelativeDefect
  refine Q'.eqv_trans _
    (Q'.abs
      (cutoffTwoRawBoundaryMomentTerm later left boundary +
        -(ratio *
          cutoffTwoRawBoundaryMomentTerm later right boundary))) _ ?_ ?_
  · exact weighted_relative_defect_eq_abs_raw_difference
      weight total leftAmplitude rightAmplitude ratio hweight htotal
  refine Q'.eqv_trans _
    (Q'.abs
      (cutoffTwoRawStationaryRowMass later left *
        (cutoffTwoRawBoundaryGivenState later left hleft boundary +
          -(cutoffTwoRawBoundaryGivenState
            later right hright boundary)))) _ ?_ ?_
  · exact Q'.abs_eqv_congr
      (raw_moment_difference_eq_mass_mul_posterior_difference
        hleft hright boundary)
  refine Q'.eqv_trans _
    (Q'.abs (cutoffTwoRawStationaryRowMass later left) *
      Q'.abs
        (cutoffTwoRawBoundaryGivenState later left hleft boundary +
          -(cutoffTwoRawBoundaryGivenState
            later right hright boundary))) _ ?_ ?_
  · exact q_abs_mul_eqv _ _
  exact Q'.mul_eqv_congr_right _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (Q'.le_of_lt (cutoffTwoRawStationaryRowMass_pos hleft)))

/-! ## 3. The exact pairwise-posterior identity -/

theorem cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_pairwisePosteriorL1
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoHalfAmplitudeRelativeDefectMoment
        (cutoffTwoRawRowMassRatio later left right hright)
        later left right ≈
      cutoffTwoRawStationaryRowMass later left *
        cutoffTwoRawBoundaryPosteriorL1
          later left right hleft hright := by
  unfold cutoffTwoHalfAmplitudeRelativeDefectMoment
    cutoffTwoRawBoundaryPosteriorL1 finiteL1Distance
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        cutoffTwoRawStationaryRowMass later left *
          Q'.abs
            (cutoffTwoRawBoundaryGivenState
                  later left hleft boundary +
              -(cutoffTwoRawBoundaryGivenState
                  later right hright boundary)))
      (centralBoundaryChannels later 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro boundary hboundary
    exact
      cutoffTwoRelativeDefectMomentTerm_eqv_leftMass_mul_posteriorDifference
        hleft hright hboundary
  exact listQSum_mul_left
    (cutoffTwoRawStationaryRowMass later left)
    (fun boundary =>
      Q'.abs
        (cutoffTwoRawBoundaryGivenState later left hleft boundary +
          -(cutoffTwoRawBoundaryGivenState
            later right hright boundary)))
    (centralBoundaryChannels later 0)

/-- The same exact identity, now stated entirely with the repository's
pre-existing source-conditioned physical boundary posterior. -/
theorem cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_centralBoundaryPosteriorL1
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoHalfAmplitudeRelativeDefectMoment
        (cutoffTwoRawRowMassRatio later left right hright)
        later left right ≈
      cutoffTwoRawStationaryRowMass later left *
        cutoffTwoCentralBoundaryPosteriorL1
          later left right hleft hright := by
  exact Q'.eqv_trans _ _ _
    (cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_pairwisePosteriorL1
      hleft hright)
    (Q'.mul_eqv_congr_left
      (cutoffTwoRawStationaryRowMass later left) _ _
      (cutoffTwoRawBoundaryPosteriorL1_eqv_centralBoundaryPosteriorL1
        hleft hright))

/-- Dividing the exact defect identity by the right row mass leaves the raw
mass ratio times the pairwise normalized-posterior `L1` distance. -/
theorem cutoffTwoRelativeDefectFraction_eqv_ratio_mul_pairwisePosteriorL1
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    Q'.divPos
        (cutoffTwoHalfAmplitudeRelativeDefectMoment
          (cutoffTwoRawRowMassRatio later left right hright)
          later left right)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) ≈
      cutoffTwoRawRowMassRatio later left right hright *
        cutoffTwoRawBoundaryPosteriorL1
          later left right hleft hright := by
  let leftMass := cutoffTwoRawStationaryRowMass later left
  let rightMass := cutoffTwoRawStationaryRowMass later right
  let distance := cutoffTwoRawBoundaryPosteriorL1
    later left right hleft hright
  let reciprocal := Q'.recipPos rightMass
    (cutoffTwoRawStationaryRowMass_pos hright)
  unfold cutoffTwoRawRowMassRatio Q'.divPos
  refine Q'.eqv_trans _ ((leftMass * distance) * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal
      (cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_pairwisePosteriorL1
        hleft hright)
  refine Q'.eqv_trans _ (leftMass * (distance * reciprocal)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv leftMass distance reciprocal
  refine Q'.eqv_trans _ (leftMass * (reciprocal * distance)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left leftMass _ _
      (Q'.mul_comm_eqv distance reciprocal)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv leftMass reciprocal distance)

/-- The existing source-to-prior posterior estimates do bound the normalized
shape part of the support-aware defect.  The raw mass ratio remains as an
explicit exterior factor; thus posterior mixing alone does not close the
conditional ratio ceiling. -/
theorem cutoffTwoRelativeDefectFraction_le_ratio_mul_sourcePriorDistances
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    Q'.divPos
        (cutoffTwoHalfAmplitudeRelativeDefectMoment
          (cutoffTwoRawRowMassRatio later left right hright)
          later left right)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) ≤
      cutoffTwoRawRowMassRatio later left right hright *
        (cutoffTwoCentralBoundaryGivenSourceL1 later left hleft +
          cutoffTwoCentralBoundaryGivenSourceL1
            later right hright) := by
  refine Q'.le_trans' _
    (cutoffTwoRawRowMassRatio later left right hright *
      cutoffTwoCentralBoundaryPosteriorL1
        later left right hleft hright) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (cutoffTwoRelativeDefectFraction_eqv_ratio_mul_pairwisePosteriorL1
          hleft hright)
        (Q'.mul_eqv_congr_left
          (cutoffTwoRawRowMassRatio later left right hright) _ _
          (cutoffTwoRawBoundaryPosteriorL1_eqv_centralBoundaryPosteriorL1
            hleft hright)))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (cutoffTwoCentralBoundaryPosteriorL1_le_sourcePriorDistances
      hleft hright)
    (cutoffTwoRawRowMassRatio_nonnegative hleft hright)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRawBoundaryGivenState_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRawBoundaryGivenState_mul_rowMass_eqv_term
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRawBoundaryGivenState_eqv_centralBoundaryGivenSource
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRawBoundaryPosteriorL1_eqv_centralBoundaryPosteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.finiteL1Distance_triangle
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.finiteL1Distance_symm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoCentralBoundaryPosteriorL1_le_sourcePriorDistances
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoCentralBoundaryGivenSourceL1_eqv_existing
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRawRowMassRatio_mul_rightMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRelativeDefectMomentTerm_eqv_leftMass_mul_posteriorDifference
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_pairwisePosteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_centralBoundaryPosteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRelativeDefectFraction_eqv_ratio_mul_pairwisePosteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.cutoffTwoRelativeDefectFraction_le_ratio_mul_sourcePriorDistances
