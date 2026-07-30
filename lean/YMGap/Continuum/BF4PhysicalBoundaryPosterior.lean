/-
# The physical BF4 interface as two conditional probability laws

The exact boundary-centered Gram is controlled by two profile deviations.
This file normalizes those profiles without changing the carrier:

* `target | boundary`, obtained by dividing a physical half-amplitude by its
  total boundary amplitude; and
* `boundary | source`, obtained by dividing the physical three-factor
  interface weight by its exact row mass.

The corresponding reference boundary law is the square-amplitude marginal.
All three laws have total mass one.  The target profile deviation is exactly
the positive boundary mass times the `L¹` distance of `target | boundary`
from the physical lower-state marginal.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram

namespace YMGap.Continuum.BF4PhysicalBoundaryPosterior

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
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
local macro "ac_qeqv" : tactic =>
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

/-! ## 1. Generic finite conditional laws -/

/-- Exact `L¹` distance on a finite list.  No factor `1/2` is inserted. -/
def finiteL1Distance
    {A : Type} (items : List A)
    (left right : A → Q') : Q' :=
  listQSum
    (fun item => Q'.abs (left item + (-right item)))
    items

/-- A half-amplitude normalized at one channel whose total amplitude is
strictly positive. -/
def finiteStateGivenChannel
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (channel : Channel)
    (total_pos :
      (0 : Q') <
        finiteChannelTotalAmplitude states amplitude channel)
    (state : State) : Q' :=
  Q'.divPos
    (amplitude state channel)
    (finiteChannelTotalAmplitude states amplitude channel)
    total_pos

/-- The conditional state law has exact total mass one. -/
theorem finiteStateGivenChannel_total_one
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (channel : Channel)
    (total_pos :
      (0 : Q') <
        finiteChannelTotalAmplitude states amplitude channel) :
    listQSum
        (finiteStateGivenChannel
          states amplitude channel total_pos)
        states ≈
      1 := by
  unfold finiteStateGivenChannel Q'.divPos
  refine Q'.eqv_trans _
    (finiteChannelTotalAmplitude
        states amplitude channel *
      Q'.recipPos
        (finiteChannelTotalAmplitude
          states amplitude channel)
        total_pos) _ ?_ ?_
  · exact
      listQSum_mul_right
        (fun state => amplitude state channel)
        (Q'.recipPos
          (finiteChannelTotalAmplitude
            states amplitude channel)
          total_pos)
        states
  exact Q'.mul_recipPos_eqv _ total_pos

/-- Entrywise centering is the conditional deviation multiplied by the
positive channel total. -/
theorem finiteMarginalCenteredAmplitude_eq_conditionalDeviation_mul_total
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (state : State) (channel : Channel)
    (total_pos :
      (0 : Q') <
        finiteChannelTotalAmplitude states amplitude channel) :
    finiteMarginalCenteredAmplitude
        states amplitude marginal state channel ≈
      (finiteStateGivenChannel
          states amplitude channel total_pos state +
        (-marginal state)) *
        finiteChannelTotalAmplitude
          states amplitude channel := by
  unfold finiteMarginalCenteredAmplitude finiteStateGivenChannel
  refine Q'.eqv_symm
    (Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv
        (Q'.divPos
          (amplitude state channel)
          (finiteChannelTotalAmplitude states amplitude channel)
          total_pos)
        (-marginal state)
        (finiteChannelTotalAmplitude
          states amplitude channel)) ?_)
  exact Q'.add_eqv_congr'
    (Q'.divPos_mul_eqv
      (amplitude state channel)
      (finiteChannelTotalAmplitude
        states amplitude channel)
      total_pos)
    (Q'.neg_mul_eqv
      (marginal state)
      (finiteChannelTotalAmplitude
        states amplitude channel))

/-- Exact unnormalization of the target-profile `L¹` distance. -/
theorem finiteCenteredProfile_eq_total_mul_conditionalL1
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (channel : Channel)
    (total_pos :
      (0 : Q') <
        finiteChannelTotalAmplitude states amplitude channel) :
    listQSum
        (fun state =>
          Q'.abs
            (finiteMarginalCenteredAmplitude
              states amplitude marginal state channel))
        states ≈
      finiteChannelTotalAmplitude
          states amplitude channel *
        finiteL1Distance
          states
          (finiteStateGivenChannel
            states amplitude channel total_pos)
          marginal := by
  let total :=
    finiteChannelTotalAmplitude states amplitude channel
  let conditional :=
    finiteStateGivenChannel
      states amplitude channel total_pos
  let distance :=
    finiteL1Distance states conditional marginal
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        Q'.abs
          ((conditional state + (-marginal state)) * total))
      states) _ ?_ ?_
  · apply listQSum_congr
    intro state
    exact Q'.abs_eqv_congr
      (finiteMarginalCenteredAmplitude_eq_conditionalDeviation_mul_total
        states amplitude marginal state channel total_pos)
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        Q'.abs (conditional state + (-marginal state)) * total)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro state
    exact
      YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (conditional state + (-marginal state))
        (Q'.le_of_lt total_pos)
  refine Q'.eqv_trans _
    (distance * total) _ ?_ ?_
  · exact
      listQSum_mul_right
        (fun state =>
          Q'.abs (conditional state + (-marginal state)))
        total states
  exact Q'.mul_comm_eqv distance total

/-! ## 2. The genuine BF4 boundary posteriors -/

/-- The physical lower-state law conditioned on one positive interface
labelling. -/
def centralTargetGivenBoundary
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling)
    (boundaryTotal_pos :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
    (target : EdgeLabelling) : Q' :=
  finiteStateGivenChannel
    (centralPositiveHalfStates w hw K half)
    (centralHalfAmplitude w K half)
    boundary boundaryTotal_pos target

/-- Exact target-posterior `L¹` distance from the physical state marginal. -/
def centralTargetGivenBoundaryL1
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling)
    (boundaryTotal_pos :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary) : Q' :=
  finiteL1Distance
    (centralPositiveHalfStates w hw K half)
    (centralTargetGivenBoundary
      w hw K half boundary boundaryTotal_pos)
    (centralPhysicalRowMarginal w hw K half)

/-- Every positive-interface target posterior is a probability law. -/
theorem centralTargetGivenBoundary_total_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {boundary : EdgeLabelling}
    (boundaryTotal_pos :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary) :
    listQSum
        (centralTargetGivenBoundary
          w hw K half boundary boundaryTotal_pos)
        (centralPositiveHalfStates w hw K half) ≈
      1 :=
  finiteStateGivenChannel_total_one
    (centralPositiveHalfStates w hw K half)
    (centralHalfAmplitude w K half)
    boundary boundaryTotal_pos

/-- The first physical quarter-profile obligation is exactly an `L¹`
posterior-mixing obligation after multiplication by the positive interface
mass. -/
theorem centralBoundaryTargetProfileDeviation_eq_total_mul_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {boundary : EdgeLabelling}
    (boundaryTotal_pos :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary) :
    centralBoundaryTargetProfileDeviation
        w hw K half boundary ≈
      centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary *
        centralTargetGivenBoundaryL1
          w hw K half boundary boundaryTotal_pos := by
  exact
    finiteCenteredProfile_eq_total_mul_conditionalL1
      (centralPositiveHalfStates w hw K half)
      (centralHalfAmplitude w K half)
      (centralPhysicalRowMarginal w hw K half)
      boundary boundaryTotal_pos

/-- The square-amplitude interface marginal of the reflected physical
joint law. -/
def centralBoundaryPrior
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralBoundaryWeight w K half boundary *
      (centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary))
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))

/-- The physical interface law conditioned on one retained lower source. -/
def centralBoundaryGivenSource
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralBoundaryWeight w K half boundary *
      (centralHalfAmplitude w K half source boundary *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary))
    (slabParametricKPhysicalPartition
        w K (centralExtent half) *
      centralPhysicalRowMarginal
        w hw K half source)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      ((mem_centralPositiveHalfStates_iff.mp source_mem).2))

/-- The square-amplitude boundary prior has total mass one. -/
theorem centralBoundaryPrior_total_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    listQSum
        (centralBoundaryPrior w hw K half)
        (centralBoundaryChannels K half) ≈
      1 := by
  unfold centralBoundaryPrior Q'.divPos
  refine Q'.eqv_trans _
    (slabParametricKPhysicalPartition
        w K (centralExtent half) *
      Q'.recipPos
        (slabParametricKPhysicalPartition
          w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half))) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun boundary =>
          centralBoundaryWeight w K half boundary *
            (centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary))
        (Q'.recipPos
          (slabParametricKPhysicalPartition
            w K (centralExtent half))
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent half)))
        (centralBoundaryChannels K half)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (centralBoundaryTotalSquareMass_eq_partition
        w hw K half)
  exact Q'.mul_recipPos_eqv _ _

/-- Every retained-source interface posterior has total mass one. -/
theorem centralBoundaryGivenSource_total_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    listQSum
        (centralBoundaryGivenSource
          w hw K half source source_mem)
        (centralBoundaryChannels K half) ≈
      1 := by
  let rowMass :=
    slabParametricKPhysicalPartition
        w K (centralExtent half) *
      centralPhysicalRowMarginal
        w hw K half source
  let rowMass_pos :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      ((mem_centralPositiveHalfStates_iff.mp source_mem).2)
  unfold centralBoundaryGivenSource Q'.divPos
  refine Q'.eqv_trans _
    (rowMass * Q'.recipPos rowMass rowMass_pos) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun boundary =>
          centralBoundaryWeight w K half boundary *
            (centralHalfAmplitude w K half source boundary *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary))
        (Q'.recipPos rowMass rowMass_pos)
        (centralBoundaryChannels K half)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (centralBoundaryMoment_eq_partition_mul_marginal
        source_mem)
  exact Q'.mul_recipPos_eqv _ _

/-- The total physical lower-state amplitude at every interface is
nonnegative. -/
theorem centralPositiveBoundaryTotalHalfAmplitude_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro state _
  exact centralHalfAmplitude_nonnegative
    hw K half state boundary

/-- The target posterior is pointwise nonnegative. -/
theorem centralTargetGivenBoundary_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling)
    (boundaryTotal_pos :
      (0 : Q') <
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
    (target : EdgeLabelling) :
    (0 : Q') ≤
      centralTargetGivenBoundary
        w hw K half boundary boundaryTotal_pos target := by
  unfold centralTargetGivenBoundary finiteStateGivenChannel
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralHalfAmplitude_nonnegative
      hw K half target boundary)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ boundaryTotal_pos))

/-- The square-amplitude boundary prior is pointwise nonnegative on the
literal boundary carrier. -/
theorem centralBoundaryPrior_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {boundary : EdgeLabelling}
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    (0 : Q') ≤
      centralBoundaryPrior w hw K half boundary := by
  unfold centralBoundaryPrior Q'.divPos
  apply Q'.mul_nonneg
  · apply Q'.mul_nonneg
    · exact centralBoundaryWeight_nonnegative_on
        hw boundary boundary_mem
    · exact Q'.mul_nonneg _ _
        (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
          hw K half boundary)
        (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
          hw K half boundary)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _ _)

/-- The source-conditioned boundary posterior is pointwise nonnegative on
the literal boundary carrier. -/
theorem centralBoundaryGivenSource_nonnegative_on
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {source boundary : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem :
      boundary ∈ centralBoundaryChannels K half) :
    (0 : Q') ≤
      centralBoundaryGivenSource
        w hw K half source source_mem boundary := by
  unfold centralBoundaryGivenSource Q'.divPos
  apply Q'.mul_nonneg
  · apply Q'.mul_nonneg
    · exact centralBoundaryWeight_nonnegative_on
        hw boundary boundary_mem
    · exact Q'.mul_nonneg _ _
        (centralHalfAmplitude_nonnegative
          hw K half source boundary)
        (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
          hw K half boundary)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _ _)

/-! ## 3. Exact Bayes `L¹` identities -/

/-- `L¹` distance of the source-conditioned interface posterior from the
square-amplitude boundary marginal. -/
def centralBoundaryGivenSourceL1
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) : Q' :=
  finiteL1Distance
    (centralBoundaryChannels K half)
    (centralBoundaryGivenSource
      w hw K half source source_mem)
    (centralBoundaryPrior w hw K half)

/-- Scaling a quotient whose denominator is the left factor cancels that
denominator while retaining an exterior factor. -/
private theorem mul_mul_divPos_eq_factor_mul
    (den factor numerator : Q')
    (den_pos : (0 : Q') < den) :
    (den * factor) *
        Q'.divPos numerator den den_pos ≈
      factor * numerator := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((factor * numerator) *
      (den * Q'.recipPos den den_pos)) _ ?_ ?_
  · ac_qeqv
  refine Q'.eqv_trans _
    ((factor * numerator) * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (factor * numerator) _ _
      (Q'.mul_recipPos_eqv den den_pos)
  exact Q'.mul_one_eqv _

/-- Before absolute values, the Bayes posterior difference multiplied by
the exact source row mass is the centered interface amplitude. -/
private theorem centralBoundaryBayesDifference_mul_rowMass
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source boundary : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    (slabParametricKPhysicalPartition
          w K (centralExtent half) *
        centralPhysicalRowMarginal
          w hw K half source) *
        (centralBoundaryGivenSource
              w hw K half source source_mem boundary +
          (-centralBoundaryPrior
              w hw K half boundary)) ≈
      (centralBoundaryWeight w K half boundary *
        centralMarginalCenteredHalfAmplitude
          w hw K half source boundary) *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary := by
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let marginal :=
    centralPhysicalRowMarginal w hw K half source
  let total :=
    centralPositiveBoundaryTotalHalfAmplitude
      w hw K half boundary
  let weight :=
    centralBoundaryWeight w K half boundary
  let amplitude :=
    centralHalfAmplitude w K half source boundary
  let centered :=
    centralMarginalCenteredHalfAmplitude
      w hw K half source boundary
  let rowMass := partition * marginal
  have hpartition :
      (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  have hmarginal :
      (0 : Q') < marginal :=
    (mem_centralPositiveHalfStates_iff.mp source_mem).2
  have hrowMass :
      (0 : Q') < rowMass :=
    Q'.mul_pos hpartition hmarginal
  have hposterior :
      rowMass *
          centralBoundaryGivenSource
            w hw K half source source_mem boundary ≈
        weight * (amplitude * total) := by
    refine Q'.eqv_trans _
      (centralBoundaryGivenSource
          w hw K half source source_mem boundary *
        rowMass) _ ?_ ?_
    · exact Q'.mul_comm_eqv _ _
    unfold centralBoundaryGivenSource
    exact Q'.divPos_mul_eqv
      (weight * (amplitude * total))
      rowMass hrowMass
  have hprior :
      rowMass *
          centralBoundaryPrior
            w hw K half boundary ≈
        marginal * (weight * (total * total)) := by
    unfold rowMass
    unfold centralBoundaryPrior
    exact mul_mul_divPos_eq_factor_mul
      partition marginal
      (weight * (total * total))
      hpartition
  refine Q'.eqv_trans _
    ((partition * marginal) *
          centralBoundaryGivenSource
            w hw K half source source_mem boundary +
      (partition * marginal) *
          (-centralBoundaryPrior
            w hw K half boundary)) _ ?_ ?_
  · exact Q'.mul_add_eqv
      (partition * marginal)
      (centralBoundaryGivenSource
        w hw K half source source_mem boundary)
      (-centralBoundaryPrior
        w hw K half boundary)
  refine Q'.eqv_trans _
    ((weight * (amplitude * total)) +
      (-(marginal * (weight * (total * total))))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      hposterior
      (Q'.eqv_trans _ _ _
        (Q'.mul_neg_eqv
          (partition * marginal)
          (centralBoundaryPrior
            w hw K half boundary))
        (Q'.neg_eqv_congr _ _ hprior))
  change
    weight * (amplitude * total) +
        (-(marginal * (weight * (total * total)))) ≈
      (weight * centered) * total
  have hcentered :
      centered ≈
        amplitude + (-(marginal * total)) := by
    unfold centered centralMarginalCenteredHalfAmplitude
      finiteMarginalCenteredAmplitude
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    ((weight *
      (amplitude + (-(marginal * total)))) * total) _ ?_ ?_
  · ac_qeqv
  exact Q'.mul_eqv_congr_right _ _ total
    (Q'.mul_eqv_congr_left weight _ _
      (Q'.eqv_symm hcentered))

/-- The second physical quarter-profile obligation is exactly the source
row mass times a Bayes posterior `L¹` mixing distance. -/
theorem centralSourceBoundaryProfileDeviation_eq_rowMass_mul_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    centralSourceBoundaryProfileDeviation
        w hw K half source ≈
      (slabParametricKPhysicalPartition
          w K (centralExtent half) *
        centralPhysicalRowMarginal
          w hw K half source) *
        centralBoundaryGivenSourceL1
          w hw K half source source_mem := by
  let rowMass :=
    slabParametricKPhysicalPartition
        w K (centralExtent half) *
      centralPhysicalRowMarginal
        w hw K half source
  let posterior :=
    centralBoundaryGivenSource
      w hw K half source source_mem
  let prior :=
    centralBoundaryPrior w hw K half
  let distance :=
    centralBoundaryGivenSourceL1
      w hw K half source source_mem
  have hrowMass :
      (0 : Q') ≤ rowMass := by
    exact Q'.le_of_lt
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half))
        ((mem_centralPositiveHalfStates_iff.mp source_mem).2))
  unfold centralSourceBoundaryProfileDeviation
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        Q'.abs
          ((centralBoundaryWeight w K half boundary *
              centralMarginalCenteredHalfAmplitude
                w hw K half source boundary) *
            centralPositiveBoundaryTotalHalfAmplitude
              w hw K half boundary))
      (centralBoundaryChannels K half)) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    exact Q'.eqv_symm
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (centralBoundaryWeight w K half boundary *
          centralMarginalCenteredHalfAmplitude
            w hw K half source boundary)
        (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
          hw K half boundary))
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        Q'.abs
          (rowMass *
            (posterior boundary + (-prior boundary))))
      (centralBoundaryChannels K half)) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    exact Q'.abs_eqv_congr
      (Q'.eqv_symm
        (centralBoundaryBayesDifference_mul_rowMass
          source_mem))
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        rowMass *
          Q'.abs
            (posterior boundary + (-prior boundary)))
      (centralBoundaryChannels K half)) _ ?_ ?_
  · apply listQSum_congr
    intro boundary
    refine Q'.eqv_trans _
      (Q'.abs rowMass *
        Q'.abs (posterior boundary + (-prior boundary))) _ ?_ ?_
    · exact q_abs_mul_eqv
        rowMass
        (posterior boundary + (-prior boundary))
    exact Q'.mul_eqv_congr_right _ _
      (Q'.abs (posterior boundary + (-prior boundary)))
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
        hrowMass)
  refine Q'.eqv_trans _
    (rowMass *
      listQSum
        (fun boundary =>
          Q'.abs
            (posterior boundary + (-prior boundary)))
        (centralBoundaryChannels K half)) _ ?_ ?_
  · exact listQSum_mul_left
      rowMass
      (fun boundary =>
        Q'.abs
          (posterior boundary + (-prior boundary)))
      (centralBoundaryChannels K half)
  exact Q'.eqv_refl _

/-! ## 4. Posterior quarters imply the physical Gram sixteenth -/

private theorem q_nonpos_of_not_pos {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
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
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on
            value tail (fun x _ => hvalue x))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have h :=
            Q'.add_le_add_right
              (0 : Q') (value head)
              (listQSum value tail)
              (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih htailLe

/-- If a total of nonnegative amplitudes is nonpositive, every centered
entry on that list is rationally zero. -/
private theorem finiteMarginalCenteredAmplitude_eqv_zero_of_total_nonpos
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (state : State) (state_mem : state ∈ states)
    (channel : Channel)
    (amplitude_nonnegative :
      ∀ item, (0 : Q') ≤ amplitude item channel)
    (total_nonpos :
      finiteChannelTotalAmplitude states amplitude channel ≤ 0) :
    finiteMarginalCenteredAmplitude
        states amplitude marginal state channel ≈
      0 := by
  let total :=
    finiteChannelTotalAmplitude
      states amplitude channel
  have htotalNonnegative :
      (0 : Q') ≤ total := by
    unfold total finiteChannelTotalAmplitude
    exact listQSum_nonnegative_on
      (fun item => amplitude item channel) states
      (fun item _ => amplitude_nonnegative item)
  have htotalZero : total ≈ 0 :=
    Q'.eqv_of_le_le total_nonpos htotalNonnegative
  have hamplitudeLe :
      amplitude state channel ≤ total := by
    unfold total finiteChannelTotalAmplitude
    exact listQSum_member_le_nonnegative
      (fun item => amplitude item channel)
      amplitude_nonnegative states state_mem
  have hamplitudeZero :
      amplitude state channel ≈ 0 := by
    apply Q'.eqv_of_le_le
    · exact Q'.le_trans' _ _ _ hamplitudeLe total_nonpos
    · exact amplitude_nonnegative state
  unfold finiteMarginalCenteredAmplitude
  refine Q'.eqv_trans _
    ((0 : Q') + (-(marginal state * 0))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      hamplitudeZero
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left
          (marginal state) _ _ htotalZero))
  refine Q'.eqv_trans _
    ((0 : Q') + (-0)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left
      0 _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_zero_eqv (marginal state)))
  decide

/-- A nonpositive total of nonnegative channel amplitudes has zero absolute
centered profile. -/
private theorem finiteCenteredProfile_eqv_zero_of_total_nonpos
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (channel : Channel)
    (amplitude_nonnegative :
      ∀ state, (0 : Q') ≤ amplitude state channel)
    (total_nonpos :
      finiteChannelTotalAmplitude states amplitude channel ≤ 0) :
    listQSum
        (fun state =>
          Q'.abs
            (finiteMarginalCenteredAmplitude
              states amplitude marginal state channel))
        states ≈
      0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state state_mem
    refine Q'.eqv_trans _
      (Q'.abs (0 : Q')) _ ?_ ?_
    · exact Q'.abs_eqv_congr
        (finiteMarginalCenteredAmplitude_eqv_zero_of_total_nonpos
          states amplitude marginal state state_mem channel
          amplitude_nonnegative total_nonpos)
    exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (Q'.le_refl' 0)
  exact listQSum_zero states

/-- A quarter `L¹` target-posterior estimate on every positive interface
automatically supplies the unnormalized target-profile estimate on every
interface, including zero-mass interfaces. -/
theorem centralBoundaryTargetProfileDeviation_le_quarter_of_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {boundary : EdgeLabelling}
    (hmixing :
      ∀ boundaryTotal_pos :
          (0 : Q') <
            centralPositiveBoundaryTotalHalfAmplitude
              w hw K half boundary,
        centralTargetGivenBoundaryL1
            w hw K half boundary boundaryTotal_pos ≤
          quarter) :
    centralBoundaryTargetProfileDeviation
        w hw K half boundary ≤
      quarter *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary := by
  let total :=
    centralPositiveBoundaryTotalHalfAmplitude
      w hw K half boundary
  by_cases htotal : (0 : Q') < total
  · have hid :=
      centralBoundaryTargetProfileDeviation_eq_total_mul_posteriorL1
        htotal
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hid) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (hmixing htotal)
        (Q'.le_of_lt htotal)) ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv total quarter)
  · have htotalNonpos : total ≤ 0 :=
      q_nonpos_of_not_pos htotal
    have hzero :
        centralBoundaryTargetProfileDeviation
            w hw K half boundary ≈
          0 := by
      exact finiteCenteredProfile_eqv_zero_of_total_nonpos
        (centralPositiveHalfStates w hw K half)
        (centralHalfAmplitude w K half)
        (centralPhysicalRowMarginal w hw K half)
        boundary
        (fun state =>
          centralHalfAmplitude_nonnegative
            hw K half state boundary)
        htotalNonpos
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hzero) ?_
    exact Q'.mul_nonneg _ _
      (by decide)
      (centralPositiveBoundaryTotalHalfAmplitude_nonnegative
        hw K half boundary)

/-- A quarter Bayes-posterior estimate is exactly the second unnormalized
quarter profile estimate. -/
theorem centralSourceBoundaryProfileDeviation_le_quarter_of_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (hmixing :
      centralBoundaryGivenSourceL1
          w hw K half source source_mem ≤
        quarter) :
    centralSourceBoundaryProfileDeviation
        w hw K half source ≤
      quarter *
        (slabParametricKPhysicalPartition
            w K (centralExtent half) *
          centralPhysicalRowMarginal
            w hw K half source) := by
  let rowMass :=
    slabParametricKPhysicalPartition
        w K (centralExtent half) *
      centralPhysicalRowMarginal
        w hw K half source
  have hrowMassNonnegative :
      (0 : Q') ≤ rowMass := by
    exact Q'.le_of_lt
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half))
        ((mem_centralPositiveHalfStates_iff.mp source_mem).2))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralSourceBoundaryProfileDeviation_eq_rowMass_mul_posteriorL1
        source_mem)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hmixing hrowMassNonnegative) ?_
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv rowMass quarter)

/-- The two genuine BF4 posterior-mixing quarters imply the physical
centered-row sixteenth. -/
theorem physicalCenteredPhysicalRowMass_le_sixteenth_of_posteriorL1
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (htarget :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          ∀ boundaryTotal_pos :
              (0 : Q') <
                centralPositiveBoundaryTotalHalfAmplitude
                  w hw K half boundary,
            centralTargetGivenBoundaryL1
                w hw K half boundary boundaryTotal_pos ≤
              quarter)
    (hsource :
      centralBoundaryGivenSourceL1
          w hw K half source source_mem ≤
        quarter) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  apply physicalCenteredPhysicalRowMass_le_sixteenth_of_quarterProfiles
    source_mem
  · intro boundary hboundary
    exact
      centralBoundaryTargetProfileDeviation_le_quarter_of_posteriorL1
        (htarget boundary hboundary)
  · exact
      centralSourceBoundaryProfileDeviation_le_quarter_of_posteriorL1
        source_mem hsource

/-! ## 5. Spacing-uniform AF trajectory consumer -/

/-- The remaining genuine physical estimate, now stated as two
spacing-uniform conditional-probability mixing bounds.

The first field mixes the lower state conditioned on every positive
interface label.  The second mixes the interface conditioned on every
retained lower source.  Their product is the exact boundary-centered Gram
sixteenth. -/
structure MatchedBoundaryPosteriorQuarterRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  target_posterior_quarter :
    ∀ scale boundary,
      boundary ∈
          centralBoundaryChannels
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundaryTotal_pos :
            (0 : Q') <
              centralPositiveBoundaryTotalHalfAmplitude
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) boundary,
          centralTargetGivenBoundaryL1
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) boundary boundaryTotal_pos ≤
            quarter
  source_posterior_quarter :
    ∀ scale source,
      ∀ source_mem :
          source ∈
            centralPositiveHalfStates
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale),
        centralBoundaryGivenSourceL1
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) source source_mem ≤
          quarter

namespace MatchedBoundaryPosteriorQuarterRows

/-- The two posterior quarters produce the exact physical interface
majorant sixteenth. -/
def toBoundaryCenteredGramSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryPosteriorQuarterRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedBoundaryCenteredGramSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.harnack
  boundary_majorant_sixteenth := by
    intro scale source source_mem
    apply
      centralBoundaryCenteredRowMajorant_le_sixteenth_of_quarterProfiles
    · intro boundary boundary_mem
      exact
        centralBoundaryTargetProfileDeviation_le_quarter_of_posteriorL1
          (data.target_posterior_quarter
            scale boundary boundary_mem)
    · exact
        centralSourceBoundaryProfileDeviation_le_quarter_of_posteriorL1
          source_mem
          (data.source_posterior_quarter
            scale source source_mem)

/-- Hence the posterior quarters inhabit both requested rowwise-eighth
fields. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryPosteriorQuarterRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toBoundaryCenteredGramSixteenthRows
    |>.toRowwiseEighthEstimates

end MatchedBoundaryPosteriorQuarterRows

end YMGap.Continuum.BF4PhysicalBoundaryPosterior

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.finiteStateGivenChannel_total_one
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.finiteCenteredProfile_eq_total_mul_conditionalL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralTargetGivenBoundary_total_one
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryTargetProfileDeviation_eq_total_mul_posteriorL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryPrior_total_one
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryGivenSource_total_one
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralTargetGivenBoundary_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryPrior_nonnegative_on
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryGivenSource_nonnegative_on
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralPositiveBoundaryTotalHalfAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralSourceBoundaryProfileDeviation_eq_rowMass_mul_posteriorL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralBoundaryTargetProfileDeviation_le_quarter_of_posteriorL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.centralSourceBoundaryProfileDeviation_le_quarter_of_posteriorL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.physicalCenteredPhysicalRowMass_le_sixteenth_of_posteriorL1
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.MatchedBoundaryPosteriorQuarterRows.toBoundaryCenteredGramSixteenthRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosterior.MatchedBoundaryPosteriorQuarterRows.toRowwiseEighthEstimates
