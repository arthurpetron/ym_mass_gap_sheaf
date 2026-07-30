/-
# Exact conditional integration of the BF4 fixed-magnetic reference carrier

The witness and magnetic labels in
`CentralFixedMagneticIntertwinerChannel` refine the physical boundary label,
but the physical half-amplitude is constant on each such fiber.  Therefore
an arbitrary reference weight contributes to its Gram only through its total
mass on each boundary fiber.

This module proves that conditional integration exactly, before and after
the common physical partition normalization.  It also proves that
nonnegativity and relative weight estimates need only be checked for the
collapsed boundary weights.  Thus redistributing reference mass among
intertwiner/magnetic labels cannot create an artificial analytic
obstruction.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4FixedMagneticActiveRowCore

namespace YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility
open YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SameCarrierRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.BF4SU2FixedIntertwinerPhysicalChoi
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The literal conditional fiber -/

/-- The complete fixed-link-intertwiner and magnetic fiber over one genuine
BF4 boundary label. -/
def centralFixedMagneticIntertwinerFiber
    (K half : Nat) (boundary : EdgeLabelling) :
    List CentralFixedMagneticIntertwinerChannel :=
  (centralFixedFineIntertwinerCarrier K half boundary).flatMap
    (fun witness =>
      (centralFixedMagneticCarrier half boundary).map
        (fun magnetic => (boundary, (witness, magnetic))))

/-- The enlarged carrier is definitionally the disjoint-list union of its
displayed boundary fibers.  No uniqueness assumption is needed for finite
sum regrouping. -/
theorem centralFixedMagneticIntertwinerChannels_eq_flatMap
    (K half : Nat) :
    centralFixedMagneticIntertwinerChannels K half =
      (centralBoundaryChannels K half).flatMap
        (centralFixedMagneticIntertwinerFiber K half) :=
  rfl

/-- Conditional integration of an arbitrary reference weight over all
non-transmitted labels. -/
def centralCollapsedFixedMagneticReferenceWeight
    (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (boundary : EdgeLabelling) : Q' :=
  listQSum referenceWeight
    (centralFixedMagneticIntertwinerFiber K half boundary)

/-! ## 2. Generic exact Gram regrouping -/

/-- A weighted Gram whose half-amplitude is constant on every displayed
fiber depends on the fine weight only through its fiber sums. -/
theorem weightedGram_flatMap_eq_collapsed
    {State Base Channel : Type}
    (bases : List Base)
    (fiber : Base → List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (baseAmplitude : State → Base → Q')
    (hamplitude :
      ∀ state base channel,
        channel ∈ fiber base →
          amplitude state channel ≈
            baseAmplitude state base)
    (left right : State) :
    weightedGram
        (bases.flatMap fiber)
        weight amplitude left right ≈
      weightedGram
        bases
        (fun base => listQSum weight (fiber base))
        baseAmplitude left right := by
  unfold weightedGram
  refine Q'.eqv_trans _
    (listQSum
      (fun base =>
        listQSum
          (fun channel =>
            weight channel *
              (amplitude left channel *
                amplitude right channel))
          (fiber base))
      bases) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr
    intro base
    refine Q'.eqv_trans _
      (listQSum
        (fun channel =>
          weight channel *
            (baseAmplitude left base *
              baseAmplitude right base))
        (fiber base)) _ ?_ ?_
    · apply listQSum_congr_on
      intro channel hchannel
      exact Q'.mul_eqv_congr_left
        (weight channel) _ _
        (q_mul_congr
          (hamplitude left base channel hchannel)
          (hamplitude right base channel hchannel))
    · exact listQSum_mul_right _ _ _

/-! ## 3. BF4 specialization and normalized endpoint identity -/

/-- Exact conditional integration of every non-transmitted fixed-magnetic
label in an arbitrary reference Gram. -/
theorem centralFixedMagneticReferenceGram_eq_collapsed
    (w : Q') (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (left right : EdgeLabelling) :
    weightedGram
        (centralFixedMagneticIntertwinerChannels K half)
        referenceWeight
        (centralFixedMagneticIntertwinerHalfAmplitude
          w K half)
        left right ≈
      weightedGram
        (centralBoundaryChannels K half)
        (centralCollapsedFixedMagneticReferenceWeight
          K half referenceWeight)
        (centralHalfAmplitude w K half)
        left right := by
  rw [centralFixedMagneticIntertwinerChannels_eq_flatMap]
  unfold centralCollapsedFixedMagneticReferenceWeight
  exact weightedGram_flatMap_eq_collapsed
    (centralBoundaryChannels K half)
    (centralFixedMagneticIntertwinerFiber K half)
    referenceWeight
    (centralFixedMagneticIntertwinerHalfAmplitude w K half)
    (centralHalfAmplitude w K half)
    (fun state boundary channel hchannel => by
      unfold centralFixedMagneticIntertwinerFiber at hchannel
      obtain ⟨witness, _hwitness, hmagneticMap⟩ :=
        List.mem_flatMap.mp hchannel
      obtain ⟨magnetic, _hmagnetic, hchannelEq⟩ :=
        List.mem_map.mp hmagneticMap
      rw [← hchannelEq]
      unfold centralFixedMagneticIntertwinerHalfAmplitude
      exact Q'.eqv_refl _)
    left right

/-- The exact fiber collapse survives the common physical partition
normalization. -/
theorem centralNormalizedFixedMagneticReferenceGram_eq_collapsed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (left right : EdgeLabelling) :
    centralNormalizedFixedMagneticReferenceGram
        w hw K half referenceWeight left right ≈
      normalizedWeightedGramJoint
        (centralBoundaryChannels K half)
        (centralCollapsedFixedMagneticReferenceWeight
          K half referenceWeight)
        (centralHalfAmplitude w K half)
        (slabParametricKPhysicalPartition
          w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half))
        left right := by
  unfold centralNormalizedFixedMagneticReferenceGram
    normalizedWeightedGramJoint Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralFixedMagneticReferenceGram_eq_collapsed
      w K half referenceWeight left right)

/-! ## 4. Positivity and the physical collapsed weight -/

/-- A nonnegative fine reference weight has a nonnegative collapsed boundary
weight. -/
theorem centralCollapsedFixedMagneticReferenceWeight_nonnegative
    {K half : Nat}
    {referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q'}
    (hreference :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels K half →
          (0 : Q') ≤ referenceWeight channel)
    {boundary : EdgeLabelling}
    (hboundary :
      boundary ∈ centralBoundaryChannels K half) :
    (0 : Q') ≤
      centralCollapsedFixedMagneticReferenceWeight
        K half referenceWeight boundary := by
  unfold centralCollapsedFixedMagneticReferenceWeight
  apply listQSum_nonnegative_on
  intro channel hchannel
  exact hreference channel
    (List.mem_flatMap.mpr
      ⟨boundary, hboundary, hchannel⟩)

/-- Collapsing the genuine physical enlarged weight reconstructs the
physical BF4 boundary weight exactly. -/
theorem centralCollapsedPhysicalWeight_eqv_boundaryWeight
    (w : Q') (K half : Nat)
    {boundary : EdgeLabelling}
    (hboundary :
      boundary ∈ centralBoundaryChannels K half) :
    centralCollapsedFixedMagneticReferenceWeight
        K half
        (centralFixedMagneticIntertwinerWeight w half)
        boundary ≈
      centralBoundaryWeight w K half boundary := by
  unfold centralCollapsedFixedMagneticReferenceWeight
    centralFixedMagneticIntertwinerFiber
  exact centralFixedMagneticIntertwinerWeight_total
    w K half boundary hboundary

/-! ## 5. Boundary-active row domination -/

/-- The genuine boundary labels visible from one source row.  This is the
fiber quotient of the fine active core: activity depends only on the common
physical half-amplitude. -/
def centralBoundaryActiveCore
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) : Bool :=
  decide
    ((0 : Q') <
      centralHalfAmplitude w K half source boundary)

private theorem q_nonpositive_of_not_positive
    {q : Q'} (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤
    (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_not_positive
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnot : ¬ (0 : Q') < q) :
    q ≈ 0 := by
  have hnonpositive : q ≤ 0 :=
    q_nonpositive_of_not_positive hnot
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

/-- Outside the source-active boundary core the source half-amplitude is
exactly zero. -/
theorem centralHalfAmplitude_eqv_zero_of_boundary_inactive
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (source boundary : EdgeLabelling)
    (hinactive :
      centralBoundaryActiveCore
        w K half source boundary = false) :
    centralHalfAmplitude w K half source boundary ≈
      0 := by
  have hnot :
      ¬ (0 : Q') <
        centralHalfAmplitude w K half source boundary := by
    unfold centralBoundaryActiveCore at hinactive
    simpa only [decide_eq_false_iff_not] using hinactive
  exact q_eqv_zero_of_nonnegative_of_not_positive
    (centralHalfAmplitude_nonnegative
      hw K half source boundary)
    hnot

private theorem neg_zero_eqv :
    (-(0 : Q')) ≈ 0 := by
  decide

private theorem gramIntegrand_relative_of_left_zero
    (physicalWeight referenceWeight
      leftAmplitude rightAmplitude epsilon : Q')
    (hleftZero : leftAmplitude ≈ 0) :
    Q'.abs
        (physicalWeight *
              (leftAmplitude * rightAmplitude) +
          (-(referenceWeight *
              (leftAmplitude * rightAmplitude)))) ≤
      epsilon *
        (physicalWeight *
          (leftAmplitude * rightAmplitude)) := by
  have hproductZero :
      leftAmplitude * rightAmplitude ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        leftAmplitude 0 rightAmplitude hleftZero)
      (Q'.zero_mul_eqv rightAmplitude)
  have hphysicalZero :
      physicalWeight *
          (leftAmplitude * rightAmplitude) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        physicalWeight _ _ hproductZero)
      (Q'.mul_zero_eqv physicalWeight)
  have hreferenceZero :
      referenceWeight *
          (leftAmplitude * rightAmplitude) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        referenceWeight _ _ hproductZero)
      (Q'.mul_zero_eqv referenceWeight)
  have hdifferenceZero :
      physicalWeight *
            (leftAmplitude * rightAmplitude) +
          (-(referenceWeight *
            (leftAmplitude * rightAmplitude))) ≈
        0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        hphysicalZero
        (Q'.eqv_trans _ _ _
          (Q'.neg_eqv_congr _ _ hreferenceZero)
          neg_zero_eqv))
      (Q'.eqv_of_eq (Q'.zero_add' 0))
  have habsZero :
      Q'.abs
          (physicalWeight *
                (leftAmplitude * rightAmplitude) +
            (-(referenceWeight *
                (leftAmplitude * rightAmplitude)))) ≈
        0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr hdifferenceZero)
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
        (Q'.le_refl' 0))
  have hrightZero :
      epsilon *
          (physicalWeight *
            (leftAmplitude * rightAmplitude)) ≈
        0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left epsilon _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            physicalWeight _ _ hproductZero)
          (Q'.mul_zero_eqv physicalWeight)))
      (Q'.mul_zero_eqv epsilon)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ habsZero
      (Q'.eqv_symm hrightZero))

/-- **Conditionally integrated BF4 row CP domination.**

It suffices to compare the physical boundary weight with the total reference
mass of its complete witness/magnetic fiber, and only on boundaries active
from the displayed source.  The inactive complement vanishes exactly. -/
theorem centralNormalizedFixedMagneticReferenceGram_row_error_le_collapsed_active
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (epsilon : Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half)
    (hactive :
      ∀ boundary,
        boundary ∈
            (centralBoundaryChannels K half).filter
              (centralBoundaryActiveCore
                w K half source) →
          Q'.abs
              (centralBoundaryWeight w K half boundary +
                (-centralCollapsedFixedMagneticReferenceWeight
                    K half referenceWeight boundary)) ≤
            epsilon *
              centralBoundaryWeight w K half boundary) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedFixedMagneticReferenceGram
          w hw K half referenceWeight)
        source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K half source := by
  let collapsed :=
    centralCollapsedFixedMagneticReferenceWeight
      K half referenceWeight
  have htransport :
      finiteJointDifferenceAbsRowMass
          (centralPositiveHalfStates w hw K half)
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half referenceWeight)
          source ≈
        finiteJointDifferenceAbsRowMass
          (centralPositiveHalfStates w hw K half)
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedBoundaryReferenceGram
            w hw K half collapsed)
          source := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr
    intro target
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_left
    exact Q'.neg_eqv_congr _ _
      (centralNormalizedFixedMagneticReferenceGram_eq_collapsed
        hw K half referenceWeight source target)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport) ?_
  apply centralNormalizedBoundaryReferenceGram_row_error_le
    collapsed epsilon hsource
  intro target htarget boundary hboundary
  cases hcore :
      centralBoundaryActiveCore
        w K half source boundary with
  | false =>
      exact gramIntegrand_relative_of_left_zero
        (centralBoundaryWeight w K half boundary)
        (collapsed boundary)
        (centralHalfAmplitude w K half source boundary)
        (centralHalfAmplitude w K half target boundary)
        epsilon
        (centralHalfAmplitude_eqv_zero_of_boundary_inactive
          hw K half source boundary hcore)
  | true =>
      exact gramIntegrand_relative_of_weight_relative
        (centralBoundaryWeight w K half boundary)
        (collapsed boundary)
        (centralHalfAmplitude w K half source boundary)
        (centralHalfAmplitude w K half target boundary)
        epsilon
        (centralHalfAmplitude_nonnegative
          hw K half source boundary)
        (centralHalfAmplitude_nonnegative
          hw K half target boundary)
        (hactive boundary
          (List.mem_filter.mpr ⟨hboundary, hcore⟩))

/-- The exact second `1/8` estimate follows from a collapsed relative
`1/8` estimate on the physically active boundary labels. -/
theorem centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth_of_collapsed_active
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half)
    (hactive :
      ∀ boundary,
        boundary ∈
            (centralBoundaryChannels K half).filter
              (centralBoundaryActiveCore
                w K half source) →
          Q'.abs
              (centralBoundaryWeight w K half boundary +
                (-centralCollapsedFixedMagneticReferenceWeight
                    K half referenceWeight boundary)) ≤
            Q'.mkPos 1 8 (by decide) *
              centralBoundaryWeight w K half boundary) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedFixedMagneticReferenceGram
          w hw K half referenceWeight)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source :=
  centralNormalizedFixedMagneticReferenceGram_row_error_le_collapsed_active
    referenceWeight
    (Q'.mkPos 1 8 (by decide))
    hsource hactive

/-! ## 6. Exact endpoint consumer -/

/-- A same-carrier endpoint realization stated only in terms of the
conditionally integrated weight actually visible to the physical Gram.

Unlike `FixedMagneticEndpointRealization`, this structure does not constrain
how reference mass is distributed among witness/magnetic refinements.
Unlike `FixedMagneticCoreTailEndpointRealization`, it has no tail fields:
the boundary-inactive complement is proved to vanish above. -/
structure CollapsedActiveFixedMagneticEndpointRealization
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half) : Type where
  referenceWeight :
    CentralFixedMagneticIntertwinerChannel → Q'
  joint_identification :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K half →
        ∀ right,
          right ∈ centralPositiveHalfStates w hw K half →
            endpoint.joint left right ≈
              centralNormalizedFixedMagneticReferenceGram
                w hw K half referenceWeight left right
  collapsed_active_eighth :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        ∀ boundary,
          boundary ∈
              (centralBoundaryChannels K half).filter
                (centralBoundaryActiveCore
                  w K half source) →
            Q'.abs
                (centralBoundaryWeight w K half boundary +
                  (-centralCollapsedFixedMagneticReferenceWeight
                      K half referenceWeight boundary)) ≤
                Q'.mkPos 1 8 (by decide) *
                  centralBoundaryWeight w K half boundary

/-- Construct a collapsed endpoint realization from the natural
source-active multiplicative window.  This is strictly weaker than a
pointwise window on every fine intertwiner/magnetic label: only the total
conditionally integrated reference mass visible to the displayed row is
constrained. -/
def collapsedActiveFixedMagneticEndpointRealization_of_sevenNineWindow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (joint_identification :
      ∀ left,
        left ∈ centralPositiveHalfStates w hw K half →
          ∀ right,
            right ∈ centralPositiveHalfStates w hw K half →
              endpoint.joint left right ≈
                centralNormalizedFixedMagneticReferenceGram
                  w hw K half referenceWeight left right)
    (lower_window :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈
                (centralBoundaryChannels K half).filter
                  (centralBoundaryActiveCore
                    w K half source) →
              Q'.mkPos 7 8 (by decide) *
                  centralBoundaryWeight w K half boundary ≤
                centralCollapsedFixedMagneticReferenceWeight
                  K half referenceWeight boundary)
    (upper_window :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈
                (centralBoundaryChannels K half).filter
                  (centralBoundaryActiveCore
                    w K half source) →
              centralCollapsedFixedMagneticReferenceWeight
                  K half referenceWeight boundary ≤
                Q'.mkPos 9 8 (by decide) *
                  centralBoundaryWeight w K half boundary) :
    CollapsedActiveFixedMagneticEndpointRealization
      hw K half endpoint where
  referenceWeight := referenceWeight
  joint_identification := joint_identification
  collapsed_active_eighth := by
    intro source hsource boundary hboundary
    exact weightRelativeEighth_of_sevenNineWindow
      (centralBoundaryWeight w K half boundary)
      (centralCollapsedFixedMagneticReferenceWeight
        K half referenceWeight boundary)
      (lower_window source hsource boundary hboundary)
      (upper_window source hsource boundary hboundary)

namespace CollapsedActiveFixedMagneticEndpointRealization

/-- The collapsed endpoint realization proves the literal
physical-minus-endpoint row `1/8` estimate. -/
theorem physicalNormalizedJointRowError_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half}
    (realization :
      CollapsedActiveFixedMagneticEndpointRealization
        hw K half endpoint)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    physicalNormalizedJointRowError endpoint source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  have htransport :
      physicalNormalizedJointRowError endpoint source ≈
        finiteJointDifferenceAbsRowMass
          (centralPositiveHalfStates w hw K half)
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half realization.referenceWeight)
          source := by
    unfold physicalNormalizedJointRowError
      finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_left
    exact Q'.neg_eqv_congr _ _
      (realization.joint_identification
        source hsource target htarget)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport)
    (centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth_of_collapsed_active
      realization.referenceWeight hsource
      (realization.collapsed_active_eighth
        source hsource))

end CollapsedActiveFixedMagneticEndpointRealization

end YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralFixedMagneticIntertwinerChannels_eq_flatMap
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.weightedGram_flatMap_eq_collapsed
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralFixedMagneticReferenceGram_eq_collapsed
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralNormalizedFixedMagneticReferenceGram_eq_collapsed
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralCollapsedFixedMagneticReferenceWeight_nonnegative
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralCollapsedPhysicalWeight_eqv_boundaryWeight
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralHalfAmplitude_eqv_zero_of_boundary_inactive
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralNormalizedFixedMagneticReferenceGram_row_error_le_collapsed_active
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth_of_collapsed_active
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.collapsedActiveFixedMagneticEndpointRealization_of_sevenNineWindow
#print axioms YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse.CollapsedActiveFixedMagneticEndpointRealization.physicalNormalizedJointRowError_le_eighth
