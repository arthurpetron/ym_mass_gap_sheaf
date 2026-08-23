/-
# Posterior normalization of the BF4 vacuum-sector centered Gram

The two profiles controlling the actual vacuum-sector boundary Gram are
exactly unnormalized conditional-probability distances:

* `target | boundary` versus the sector-conditioned stationary law; and
* `boundary | source` versus the sector square-amplitude boundary prior.

The boundary prior and both conditional laws have total mass one.  Positive
boundary channels give exact target-profile unnormalization; zero channels
are handled constructively from amplitude nonnegativity.  Exact Bayes
algebra gives the source-profile identity with the unconditioned stationary
source weight.  Hence cofinal posterior mixing with product rate below one
compiles to the completed same-object vacuum-sector gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles
import YMGap.Continuum.BF4PhysicalBoundaryPosterior

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
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

/-! ## 1. Generic weighted-Gram channel posteriors -/

/-- The channel prior induced by the weighted square of the total
half-amplitude. -/
def finiteWeightedGramChannelPrior
    {State Channel : Type}
    (states : List State) (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (channel : Channel) : Q' :=
  Q'.divPos
    (weight channel *
      (finiteChannelTotalAmplitude states amplitude channel *
        finiteChannelTotalAmplitude states amplitude channel))
    mass mass_pos

/-- The channel law conditioned on one state, normalized by the exact
weighted-Gram row mass. -/
def finiteWeightedGramChannelGivenState
    {State Channel : Type}
    (states : List State) (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (marginal : State → Q') (state : State)
    (marginal_pos : (0 : Q') < marginal state)
    (channel : Channel) : Q' :=
  Q'.divPos
    (weight channel *
      (amplitude state channel *
        finiteChannelTotalAmplitude states amplitude channel))
    (mass * marginal state)
    (Q'.mul_pos mass_pos marginal_pos)

/-- The square-amplitude channel prior has total mass one whenever its raw
square mass is exactly the supplied positive mass. -/
theorem finiteWeightedGramChannelPrior_total_one
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q') (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (squareMass :
      listQSum
          (fun channel =>
            weight channel *
              (finiteChannelTotalAmplitude states amplitude channel *
                finiteChannelTotalAmplitude states amplitude channel))
          channels ≈ mass) :
    listQSum
        (finiteWeightedGramChannelPrior
          states weight amplitude mass mass_pos)
        channels ≈ 1 := by
  unfold finiteWeightedGramChannelPrior Q'.divPos
  refine Q'.eqv_trans _
    (mass * Q'.recipPos mass mass_pos) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun channel =>
          weight channel *
            (finiteChannelTotalAmplitude states amplitude channel *
              finiteChannelTotalAmplitude states amplitude channel))
        (Q'.recipPos mass mass_pos) channels) ?_
    exact Q'.mul_eqv_congr_right _ _ _ squareMass
  exact Q'.mul_recipPos_eqv mass mass_pos

/-- Every state-conditioned channel posterior has total mass one when the
channel first moment is the supplied row mass. -/
theorem finiteWeightedGramChannelGivenState_total_one
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q') (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (marginal : State → Q') (state : State)
    (marginal_pos : (0 : Q') < marginal state)
    (moment :
      listQSum
          (fun channel =>
            weight channel *
              (amplitude state channel *
                finiteChannelTotalAmplitude states amplitude channel))
          channels ≈ mass * marginal state) :
    listQSum
        (finiteWeightedGramChannelGivenState
          states weight amplitude mass mass_pos marginal state marginal_pos)
        channels ≈ 1 := by
  let rowMass := mass * marginal state
  let rowMass_pos := Q'.mul_pos mass_pos marginal_pos
  unfold finiteWeightedGramChannelGivenState Q'.divPos
  refine Q'.eqv_trans _
    (rowMass * Q'.recipPos rowMass rowMass_pos) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun channel =>
          weight channel *
            (amplitude state channel *
              finiteChannelTotalAmplitude states amplitude channel))
        (Q'.recipPos rowMass rowMass_pos) channels) ?_
    exact Q'.mul_eqv_congr_right _ _ _ moment
  exact Q'.mul_recipPos_eqv rowMass rowMass_pos

/-- Scaling a quotient whose denominator is the left factor cancels that
denominator while retaining an exterior factor. -/
private theorem mul_mul_divPos_eq_factor_mul
    (den factor numerator : Q') (den_pos : (0 : Q') < den) :
    (den * factor) * Q'.divPos numerator den den_pos ≈
      factor * numerator := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((factor * numerator) *
      (den * Q'.recipPos den den_pos)) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _ ((factor * numerator) * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (factor * numerator) _ _
      (Q'.mul_recipPos_eqv den den_pos)
  exact Q'.mul_one_eqv _

/-- Exact Bayes centering: row mass times posterior-minus-prior is the
weighted centered half-amplitude times the channel total. -/
theorem finiteWeightedGramChannelBayesDifference_mul_rowMass
    {State Channel : Type}
    (states : List State) (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (marginal : State → Q') (state : State)
    (marginal_pos : (0 : Q') < marginal state)
    (channel : Channel) :
    (mass * marginal state) *
        (finiteWeightedGramChannelGivenState
              states weight amplitude mass mass_pos marginal
              state marginal_pos channel +
          (-finiteWeightedGramChannelPrior
              states weight amplitude mass mass_pos channel)) ≈
      (weight channel *
        finiteMarginalCenteredAmplitude
          states amplitude marginal state channel) *
        finiteChannelTotalAmplitude states amplitude channel := by
  let total := finiteChannelTotalAmplitude states amplitude channel
  let channelWeight := weight channel
  let rawAmplitude := amplitude state channel
  let centered := finiteMarginalCenteredAmplitude
    states amplitude marginal state channel
  let rowMass := mass * marginal state
  have hrowMass : (0 : Q') < rowMass :=
    Q'.mul_pos mass_pos marginal_pos
  have hposterior :
      rowMass *
          finiteWeightedGramChannelGivenState
            states weight amplitude mass mass_pos marginal
            state marginal_pos channel ≈
        channelWeight * (rawAmplitude * total) := by
    refine Q'.eqv_trans _
      (finiteWeightedGramChannelGivenState
          states weight amplitude mass mass_pos marginal
          state marginal_pos channel * rowMass) _ ?_ ?_
    · exact Q'.mul_comm_eqv _ _
    unfold finiteWeightedGramChannelGivenState
    exact Q'.divPos_mul_eqv
      (channelWeight * (rawAmplitude * total)) rowMass hrowMass
  have hprior :
      rowMass *
          finiteWeightedGramChannelPrior
            states weight amplitude mass mass_pos channel ≈
        marginal state * (channelWeight * (total * total)) := by
    unfold rowMass
    unfold finiteWeightedGramChannelPrior
    exact mul_mul_divPos_eq_factor_mul
      mass (marginal state)
      (channelWeight * (total * total)) mass_pos
  refine Q'.eqv_trans _
    (rowMass *
          finiteWeightedGramChannelGivenState
            states weight amplitude mass mass_pos marginal
            state marginal_pos channel +
      rowMass *
          (-finiteWeightedGramChannelPrior
            states weight amplitude mass mass_pos channel)) _ ?_ ?_
  · exact Q'.mul_add_eqv rowMass _ _
  refine Q'.eqv_trans _
    (channelWeight * (rawAmplitude * total) +
      (-(marginal state *
        (channelWeight * (total * total))))) _ ?_ ?_
  · exact Q'.add_eqv_congr' hposterior
      (Q'.eqv_trans _ _ _
        (Q'.mul_neg_eqv rowMass
          (finiteWeightedGramChannelPrior
            states weight amplitude mass mass_pos channel))
        (Q'.neg_eqv_congr _ _ hprior))
  change
    channelWeight * (rawAmplitude * total) +
        (-(marginal state * (channelWeight * (total * total)))) ≈
      (channelWeight * centered) * total
  have hcentered : centered ≈
      rawAmplitude + (-(marginal state * total)) := by
    unfold centered finiteMarginalCenteredAmplitude
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    ((channelWeight *
      (rawAmplitude + (-(marginal state * total)))) * total) _ ?_ ?_
  · q_ring
  exact Q'.mul_eqv_congr_right _ _ total
    (Q'.mul_eqv_congr_left channelWeight _ _
      (Q'.eqv_symm hcentered))

/-! ## 2. The actual vacuum-sector posterior laws -/

/-- Every indexed physical half-amplitude is nonnegative. -/
theorem centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff half index : Nat)
    (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorGramAmplitude
        w hw cutoff half index boundary := by
  unfold centralPhysicalFiniteVacuumSectorGramAmplitude
  exact centralHalfAmplitude_nonnegative
    hw cutoff half
    (centralPhysicalFiniteStateAt w hw cutoff half index) boundary

/-- Every sector channel total is nonnegative. -/
theorem centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorChannelTotal
        w hw cutoff half boundary := by
  unfold centralPhysicalFiniteVacuumSectorChannelTotal
    finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro index _
  exact centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
    hw cutoff half index boundary

/-- The sector-conditioned stationary weight is positive at every sector
index. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half index := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedWeight
    finiteCarrierMassNormalizedWeight Q'.divPos
  exact Q'.mul_pos
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hindex)
    (Q'.recipPos_pos _
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half))

/-- The sector state law conditioned on one positive boundary channel. -/
def centralPhysicalFiniteVacuumSectorTargetGivenBoundary
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (target : Nat) : Q' :=
  finiteStateGivenChannel
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    boundary channelTotal_pos target

/-- Exact target-posterior `L1` distance from the sector stationary law. -/
def centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) : Q' :=
  finiteL1Distance
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w hw cutoff half boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)

/-- The sector square-amplitude boundary prior. -/
def centralPhysicalFiniteVacuumSectorBoundaryPrior
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  finiteWeightedGramChannelPrior
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    boundary

/-- The physical boundary law conditioned on one sector source. -/
def centralPhysicalFiniteVacuumSectorBoundaryGivenSource
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (boundary : EdgeLabelling) : Q' :=
  finiteWeightedGramChannelGivenState
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    source
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource)
    boundary

/-- Exact source-posterior `L1` distance from the sector boundary prior. -/
def centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) : Q' :=
  finiteL1Distance
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w hw cutoff half)

/-! ## 3. Exact normalization and Bayes identities -/

/-- Every positive-channel target posterior is pointwise nonnegative. -/
theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundary_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (target : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorTargetGivenBoundary
        w hw cutoff half boundary channelTotal_pos target := by
  unfold centralPhysicalFiniteVacuumSectorTargetGivenBoundary
    finiteStateGivenChannel Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
      hw cutoff half target boundary)
    (Q'.le_of_lt (Q'.recipPos_pos _ channelTotal_pos))

/-- The sector square-amplitude boundary prior is pointwise nonnegative on
the literal boundary carrier. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryPrior_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w) {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorBoundaryPrior
        w hw cutoff half boundary := by
  unfold centralPhysicalFiniteVacuumSectorBoundaryPrior
    finiteWeightedGramChannelPrior Q'.divPos
  apply Q'.mul_nonneg
  · apply Q'.mul_nonneg
    · exact centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
        boundary hboundary
    · exact Q'.mul_nonneg _ _
        (centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
          hw cutoff half boundary)
        (centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
          hw cutoff half boundary)
  · exact Q'.le_of_lt (Q'.recipPos_pos _ _)

/-- Every source-conditioned boundary posterior is pointwise nonnegative on
the literal boundary carrier. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSource_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w) {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorBoundaryGivenSource
        w hw cutoff half source hsource boundary := by
  unfold centralPhysicalFiniteVacuumSectorBoundaryGivenSource
    finiteWeightedGramChannelGivenState Q'.divPos
  apply Q'.mul_nonneg
  · apply Q'.mul_nonneg
    · exact centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
        boundary hboundary
    · exact Q'.mul_nonneg _ _
        (centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
          hw cutoff half source boundary)
        (centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
          hw cutoff half boundary)
  · exact Q'.le_of_lt (Q'.recipPos_pos _ _)

/-- Every positive-channel target posterior has total mass one. -/
theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    listQSum
        (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
          w hw cutoff half boundary channelTotal_pos)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) ≈ 1 :=
  finiteStateGivenChannel_total_one
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    boundary channelTotal_pos

/-- The sector square-amplitude boundary prior has total mass one. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    listQSum
        (centralPhysicalFiniteVacuumSectorBoundaryPrior
          w hw cutoff half)
        (centralBoundaryChannels cutoff half) ≈ 1 := by
  exact finiteWeightedGramChannelPrior_total_one
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteVacuumSector_boundaryTotalSquare_eqv_mass
      w hw cutoff half)

/-- Every source-conditioned boundary posterior has total mass one. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    listQSum
        (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
          w hw cutoff half source hsource)
        (centralBoundaryChannels cutoff half) ≈ 1 := by
  exact finiteWeightedGramChannelGivenState_total_one
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    source
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource)
    (centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight
      hsource)

/-- The target profile is exactly channel total times target-posterior `L1`
on every positive boundary channel. -/
theorem centralPhysicalFiniteVacuumSectorTargetProfileDeviation_eq_total_mul_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorTargetProfileDeviation
        w hw cutoff half boundary ≈
      centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary *
        centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
          w hw cutoff half boundary channelTotal_pos := by
  exact finiteCenteredProfile_eq_total_mul_conditionalL1
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    boundary channelTotal_pos

/-- The exact Gram row mass is the unconditioned stationary source weight. -/
theorem centralPhysicalFiniteVacuumSector_mass_mul_normalizedWeight_eqv_weight
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) :
    centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half source ≈
      centralPhysicalFiniteWeight w hw cutoff half source := by
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half source *
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half) _ ?_ ?_
  · exact Q'.mul_comm_eqv _ _
  exact finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    source

/-- The source profile is exactly the unconditioned stationary source
weight times the boundary-posterior `L1` distance. -/
theorem centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_eq_weight_mul_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
        w hw cutoff half source ≈
      centralPhysicalFiniteWeight w hw cutoff half source *
        centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
          w hw cutoff half source hsource := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let channelWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let marginal :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight w hw cutoff half
  let rowMass := mass * marginal source
  let posterior :=
    centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource
  let prior :=
    centralPhysicalFiniteVacuumSectorBoundaryPrior w hw cutoff half
  let distance :=
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
      w hw cutoff half source hsource
  have hmarginalPos : (0 : Q') < marginal source :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource
  have hrowMass : (0 : Q') ≤ rowMass :=
    Q'.le_of_lt
      (Q'.mul_pos
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w hw cutoff half)
        hmarginalPos)
  unfold centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        Q'.abs
          ((channelWeight boundary *
              finiteMarginalCenteredAmplitude
                states amplitude marginal source boundary) *
            finiteChannelTotalAmplitude states amplitude boundary))
      channels) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    exact Q'.eqv_symm
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (channelWeight boundary *
          finiteMarginalCenteredAmplitude
            states amplitude marginal source boundary)
        (centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
          hw cutoff half boundary))
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        Q'.abs
          (rowMass *
            (posterior boundary + (-prior boundary))))
      channels) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    exact Q'.abs_eqv_congr
      (Q'.eqv_symm
        (finiteWeightedGramChannelBayesDifference_mul_rowMass
          states channelWeight amplitude mass
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
          marginal source hmarginalPos boundary))
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        rowMass * Q'.abs
          (posterior boundary + (-prior boundary)))
      channels) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    refine Q'.eqv_trans _
      (Q'.abs rowMass *
        Q'.abs (posterior boundary + (-prior boundary))) _ ?_ ?_
    · exact q_abs_mul_eqv rowMass
        (posterior boundary + (-prior boundary))
    exact Q'.mul_eqv_congr_right _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hrowMass)
  refine Q'.eqv_trans _
    (rowMass * distance) _
    (listQSum_mul_left
      rowMass
      (fun boundary =>
        Q'.abs (posterior boundary + (-prior boundary)))
      channels) ?_
  exact Q'.mul_eqv_congr_right _ _ distance
    (centralPhysicalFiniteVacuumSector_mass_mul_normalizedWeight_eqv_weight
      w hw cutoff half source)

/-! ## 4. Posterior bounds compile to profile bounds -/

private theorem q_nonpos_of_not_pos {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- Every nonnegative member is bounded by its finite total. -/
private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on
            value tail (fun x _ => hvalue x))
      · have ih :=
          listQSum_member_le_nonnegative value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih htailLe

/-- A nonpositive total of nonnegative amplitudes has zero absolute centered
profile. -/
private theorem finiteCenteredProfile_eqv_zero_of_total_nonpos
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q') (channel : Channel)
    (amplitude_nonnegative :
      ∀ state, (0 : Q') ≤ amplitude state channel)
    (total_nonpos :
      finiteChannelTotalAmplitude states amplitude channel ≤ 0) :
    listQSum
        (fun state =>
          Q'.abs
            (finiteMarginalCenteredAmplitude
              states amplitude marginal state channel))
        states ≈ 0 := by
  let total := finiteChannelTotalAmplitude states amplitude channel
  have htotalNonnegative : (0 : Q') ≤ total := by
    unfold total finiteChannelTotalAmplitude
    exact listQSum_nonnegative_on
      (fun state => amplitude state channel) states
      (fun state _ => amplitude_nonnegative state)
  have htotalZero : total ≈ 0 :=
    Q'.eqv_of_le_le total_nonpos htotalNonnegative
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state hstate
    have hamplitudeLe : amplitude state channel ≤ total := by
      unfold total finiteChannelTotalAmplitude
      exact listQSum_member_le_nonnegative
        (fun item => amplitude item channel)
        amplitude_nonnegative states hstate
    have hamplitudeZero : amplitude state channel ≈ 0 := by
      apply Q'.eqv_of_le_le
      · exact Q'.le_trans' _ _ _ hamplitudeLe total_nonpos
      · exact amplitude_nonnegative state
    have hcentered :
        finiteMarginalCenteredAmplitude
            states amplitude marginal state channel ≈ 0 := by
      unfold finiteMarginalCenteredAmplitude
      refine Q'.eqv_trans _
        ((0 : Q') + (-(marginal state * 0))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          hamplitudeZero
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left
              (marginal state) _ _ htotalZero))
      refine Q'.eqv_trans _ ((0 : Q') + (-0)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 0 _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_zero_eqv (marginal state)))
      decide
    refine Q'.eqv_trans _ (Q'.abs (0 : Q')) _
      (Q'.abs_eqv_congr hcentered) ?_
    exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (Q'.le_refl' 0)
  exact listQSum_zero states

/-- A target-posterior bound implies the unnormalized target-profile bound
on every boundary channel, including channels of zero total. -/
theorem centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_of_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling} {targetRate : Q'}
    (targetRate_nonnegative : (0 : Q') ≤ targetRate)
    (hmixing :
      ∀ channelTotal_pos :
          (0 : Q') <
            centralPhysicalFiniteVacuumSectorChannelTotal
              w hw cutoff half boundary,
        centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
            w hw cutoff half boundary channelTotal_pos ≤ targetRate) :
    centralPhysicalFiniteVacuumSectorTargetProfileDeviation
        w hw cutoff half boundary ≤
      targetRate *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary := by
  let total := centralPhysicalFiniteVacuumSectorChannelTotal
    w hw cutoff half boundary
  by_cases htotal : (0 : Q') < total
  · refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorTargetProfileDeviation_eq_total_mul_posteriorL1
          htotal)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (hmixing htotal) (Q'.le_of_lt htotal)) ?_
    exact Q'.le_of_eqv (Q'.mul_comm_eqv total targetRate)
  · have htotalNonpos : total ≤ 0 := q_nonpos_of_not_pos htotal
    have hzero :
        centralPhysicalFiniteVacuumSectorTargetProfileDeviation
            w hw cutoff half boundary ≈ 0 := by
      exact finiteCenteredProfile_eqv_zero_of_total_nonpos
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        boundary
        (fun index =>
          centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
            hw cutoff half index boundary)
        htotalNonpos
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) ?_
    exact Q'.mul_nonneg _ _ targetRate_nonnegative
      (centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
        hw cutoff half boundary)

/-- A source-posterior bound implies the unnormalized source-profile bound
by the exact stationary source weight. -/
theorem centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_of_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    {sourceRate : Q'}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hmixing :
      centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
          w hw cutoff half source hsource ≤ sourceRate) :
    centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
        w hw cutoff half source ≤
      sourceRate *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  have hweight : (0 : Q') ≤
      centralPhysicalFiniteWeight w hw cutoff half source :=
    Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_eq_weight_mul_posteriorL1
        hsource)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hmixing hweight) ?_
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv
      (centralPhysicalFiniteWeight w hw cutoff half source)
      sourceRate)

/-- Cofinal posterior-mixing bounds on the two actual sector conditionals.
Their product, rather than either individual rate, must be uniformly below
one. -/
structure FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (targetRate sourceRate : Q') : Type 1 where
  targetRate_nonnegative : (0 : Q') ≤ targetRate
  sourceRate_nonnegative : (0 : Q') ≤ sourceRate
  rateProduct_lt_one : targetRate * sourceRate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  targetPosteriorBound : ∀ base threshold boundary,
    boundary ∈ centralBoundaryChannels (anchor base threshold) half →
      ∀ channelTotal_pos :
          (0 : Q') <
            centralPhysicalFiniteVacuumSectorChannelTotal
              w hw (anchor base threshold) half boundary,
        centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
            w hw (anchor base threshold) half boundary
            channelTotal_pos ≤ targetRate
  sourcePosteriorBound : ∀ base threshold source,
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w hw (anchor base threshold) half) →
      centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
          w hw (anchor base threshold) half source hsource ≤ sourceRate

namespace FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing

/-- Posterior mixing produces the exact two-profile certificate. -/
def toProfileBounds
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetRate sourceRate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing
      w hw half targetRate sourceRate) :
    FixedNomeCofinalVacuumSectorCenteredGramProfileBounds
      w hw half targetRate sourceRate where
  targetRate_nonnegative := family.targetRate_nonnegative
  sourceRate_nonnegative := family.sourceRate_nonnegative
  rateProduct_lt_one := family.rateProduct_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  targetProfileBound := by
    intro base threshold boundary hboundary
    exact
      centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_of_posteriorL1
        family.targetRate_nonnegative
        (family.targetPosteriorBound base threshold boundary hboundary)
  sourceProfileBound := by
    intro base threshold source hsource
    exact
      centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_of_posteriorL1
        hsource
        (family.sourcePosteriorBound base threshold source hsource)

/-- Cofinal posterior mixing reaches the completed same-object vacuum-sector
strict gap at the product rate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetRate sourceRate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing
      w hw half targetRate sourceRate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (targetRate * sourceRate) :=
  family.toProfileBounds.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.finiteWeightedGramChannelPrior_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.finiteWeightedGramChannelGivenState_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.finiteWeightedGramChannelBayesDifference_mul_rowMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorTargetGivenBoundary_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorBoundaryPrior_nonnegative_on
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorBoundaryGivenSource_nonnegative_on
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorTargetProfileDeviation_eq_total_mul_posteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_eq_weight_mul_posteriorL1
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior.FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing.toVacuumSectorCenteredStrictGap
