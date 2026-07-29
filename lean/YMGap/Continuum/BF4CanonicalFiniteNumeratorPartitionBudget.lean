/-
# Canonical exact finite BF4 numerator/partition budget

`CentralPhysicalNumeratorPartitionBudget` is the analytic interface used by
the AF-uniform reflected-row comparison.  At one fixed physical BF4 carrier,
all of its raw errors are finite exact rational sums.  This module constructs
those sums and pays them against the located positive physical marginal
floor.

The resulting tolerance is deliberately *computed*, not assumed:

    epsilon =
      |carrier| * (sum of exact entry budgets) / pi_min.

This closes existence of the separated budget at every fixed scale for every
signed symmetric endpoint.  It does not claim that the computed tolerances
are small or bounded uniformly along the AF spacing trajectory.  The
remaining physical theorem is precisely a spacing-uniform upper bound for
this displayed rational sequence (or a sharper analytic budget) strong
enough to fit below the quarter margin.

No extrema or witnesses are hidden in `Prop`: `pi_min` is the explicit
finite minimum already constructed by
`centralPositivePhysicalMarginalFloorData`, and the tolerance and budget are
fields of a Type-valued structure.
-/

import YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint

namespace YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite errors -/

/-- The exact positive-row carrier of an endpoint. -/
def endpointStates
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (_endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    List EdgeLabelling :=
  centralPositiveHalfStates w hw K halfExtent

/-- Sum of the exact physical-minus-endpoint numerator errors in one row.
Using the row sum, rather than a postulated pointwise constant, keeps the
construction fully executable and automatically dominates every retained
entry. -/
def exactNumeratorError
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (centralPhysicalReflectedKernel
              w K halfExtent source target +
          (-endpoint.numerator source target)))
    (endpointStates endpoint)

/-- Sum of absolute endpoint numerators in one row. -/
def exactEndpointNumeratorCeiling
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs (endpoint.numerator source target))
    (endpointStates endpoint)

/-- Exact physical-minus-endpoint partition error. -/
def exactPartitionError
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  Q'.abs
    (slabParametricKPhysicalPartition
          w K (centralExtent halfExtent) +
      (-endpoint.partition))

/-- The positive common denominator in the normalized cross-numerator
estimate. -/
def exactCrossDenominator
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  slabParametricKPhysicalPartition
      w K (centralExtent halfExtent) *
    endpoint.partition

theorem exactCrossDenominator_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') < exactCrossDenominator endpoint := by
  exact Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent))
    endpoint.partition_pos

/-- Exact separated cross-numerator majorant in one source row. -/
def exactCrossMajorant
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  exactNumeratorError endpoint source *
      endpoint.partition +
    exactEndpointNumeratorCeiling endpoint source *
      exactPartitionError endpoint

/-- Exact normalized entry budget obtained by division by the two positive
partitions. -/
def exactEntryBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  Q'.divPos
    (exactCrossMajorant endpoint source)
    (exactCrossDenominator endpoint)
    (exactCrossDenominator_pos endpoint)

private theorem listQSum_member_le_nonnegative
    {A : Type}
    (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head)
            (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

/-! ## 1a. The literal vacuum row -/

theorem zeroEdgeLabelling_mem_centralHalfStates
    (K halfExtent : Nat) :
    zeroEdgeLabelling ∈
      centralHalfStates K halfExtent := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

theorem zeroEdgeLabelling_mem_centralBoundaryChannels
    (K halfExtent : Nat) :
    zeroEdgeLabelling ∈
      centralBoundaryChannels K halfExtent := by
  unfold centralBoundaryChannels
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

theorem assembleReflectedSlabLabelling_zero
    (halfExtent : Nat) :
    assembleReflectedSlabLabelling
        halfExtent zeroEdgeLabelling
        zeroEdgeLabelling zeroEdgeLabelling =
      zeroEdgeLabelling := by
  funext id
  by_cases hid :
      id ∈ slabPhysicalFaceEdges
        (centralExtent halfExtent)
  · unfold assembleReflectedSlabLabelling
    rw [if_pos hid]
    generalize hside :
      plaquetteHalfSide halfExtent
        (slabPlaquetteAt
          (centralExtent halfExtent) id) = side
    cases side <;> rfl
  · exact
      assembleReflectedSlabLabelling_zero_off_physical
        halfExtent zeroEdgeLabelling
        zeroEdgeLabelling zeroEdgeLabelling hid

theorem one_le_centralPhysicalReflectedKernel_vacuum
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (1 : Q') ≤
      centralPhysicalReflectedKernel
        w K halfExtent zeroEdgeLabelling
        zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K
      (centralExtent halfExtent)
      (assembleReflectedSlabLabelling
        halfExtent zeroEdgeLabelling boundary
        zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling ≤
        listQSum value
          (centralBoundaryChannels K halfExtent) :=
    listQSum_member_le_nonnegative
      value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          hw K (centralExtent halfExtent)
          (assembleReflectedSlabLabelling
            halfExtent zeroEdgeLabelling boundary
            zeroEdgeLabelling))
      (centralBoundaryChannels K halfExtent)
      (zeroEdgeLabelling_mem_centralBoundaryChannels
        K halfExtent)
  have hvacuum :
      value zeroEdgeLabelling ≈ 1 := by
    unfold value
    rw [assembleReflectedSlabLabelling_zero]
    exact slabParametricKPhysicalTerm_zero_eqv_one
      w K (centralExtent halfExtent)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hvacuum)
    hmember

theorem centralNormalizedPhysicalReflectedKernel_vacuum_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (0 : Q') <
      centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent zeroEdgeLabelling
        zeroEdgeLabelling := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  apply Q'.mul_pos
  · exact Q'.pos_of_lt_of_le
      (by decide : (0 : Q') < 1)
      (one_le_centralPhysicalReflectedKernel_vacuum
        hw K halfExtent)
  · exact Q'.recipPos_pos _ _

theorem centralPhysicalRowMarginal_vacuum_pos
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (0 : Q') <
      centralPhysicalRowMarginal
        w hw K halfExtent zeroEdgeLabelling := by
  unfold centralPhysicalRowMarginal
  have hmember :=
    listQSum_member_le_nonnegative
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent zeroEdgeLabelling)
      (fun target =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          hw K halfExtent zeroEdgeLabelling target)
      (centralHalfStates K halfExtent)
      (zeroEdgeLabelling_mem_centralHalfStates
        K halfExtent)
  exact Q'.pos_of_lt_of_le
    (centralNormalizedPhysicalReflectedKernel_vacuum_pos
      hw K halfExtent)
    hmember

theorem zeroEdgeLabelling_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    zeroEdgeLabelling ∈
      centralPositiveHalfStates
        w hw K halfExtent := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨zeroEdgeLabelling_mem_centralHalfStates
        K halfExtent,
      centralPhysicalRowMarginal_vacuum_pos
        hw K halfExtent⟩

/-! ## 1b. The canonical order-one rate cannot reach the quarter -/

/-- The constant spin network at the vacuum forces the counting `L²` norm
of the order-zero half-amplitude to be at least one on the physical
carrier. -/
theorem one_le_rankOneAmplitudeL2Sum_centralPositive
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (1 : Q') ≤
      rankOneAmplitudeL2Sum
        (centralPositiveHalfStates
          w hw K halfExtent) := by
  let square := fun state : EdgeLabelling =>
    geometricZerothHalfAmplitude state *
      geometricZerothHalfAmplitude state
  have hmember :
      square zeroEdgeLabelling ≤
        listQSum square
          (centralPositiveHalfStates
            w hw K halfExtent) :=
    listQSum_member_le_nonnegative
      square
      (fun state =>
        YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
          (geometricZerothHalfAmplitude state))
      (centralPositiveHalfStates
        w hw K halfExtent)
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        hw K halfExtent)
  have hvacuum :
      square zeroEdgeLabelling ≈ 1 := by
    unfold square
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        geometricZerothHalfAmplitude_vacuum)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 _ _
          geometricZerothHalfAmplitude_vacuum)
        (Q'.one_mul_eqv 1))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hvacuum) hmember

/-- The located physical marginal floor is at most one because the retained
positive row marginals have total mass exactly one. -/
theorem centralPositivePhysicalMarginalFloor_le_one
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (centralPositivePhysicalMarginalFloorData
        w hw K halfExtent).floor ≤
      1 := by
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  have hfloor :
      floorData.floor ≤
        centralPhysicalRowMarginal
          w hw K halfExtent zeroEdgeLabelling :=
    floorData.floor_le zeroEdgeLabelling
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        hw K halfExtent)
  have hmember :
      centralPhysicalRowMarginal
          w hw K halfExtent zeroEdgeLabelling ≤
        listQSum
          (centralPhysicalRowMarginal
            w hw K halfExtent)
          (centralPositiveHalfStates
            w hw K halfExtent) :=
    listQSum_member_le_nonnegative
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      (fun state =>
        centralPhysicalRowMarginal_nonnegative
          hw K halfExtent state)
      (centralPositiveHalfStates
        w hw K halfExtent)
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        hw K halfExtent)
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ hmember
      (Q'.le_of_eqv
        (centralPositiveRowMarginal_total_one
          w hw K halfExtent)))

/-- Consequently the explicit Cauchy--Schwarz/marginal-floor rate attached
to the order-one rank-one endpoint is at least one.  This is a theorem about
the *canonical coarse bound*, not a no-gap theorem for the physical Markov
operator. -/
theorem one_le_canonicalRankOneRate
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    (1 : Q') ≤
      (canonicalRankOneGeometricTaylorEndpointSpectralData
        w hw K halfExtent).rate := by
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  have hfloor :
      floorData.floor ≤ (1 : Q') :=
    centralPositivePhysicalMarginalFloor_le_one
      hw K halfExtent
  have hamplitude :
      (1 : Q') ≤
        rankOneAmplitudeL2Sum
          (centralPositiveHalfStates
            w hw K halfExtent) :=
    one_le_rankOneAmplitudeL2Sum_centralPositive
      hw K halfExtent
  have hmul :
      (1 : Q') * floorData.floor ≤
        rankOneAmplitudeL2Sum
          (centralPositiveHalfStates
            w hw K halfExtent) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv floorData.floor))
      (Q'.le_trans' _ _ _ hfloor hamplitude)
  change (1 : Q') ≤
    Q'.divPos
      (rankOneAmplitudeL2Sum
        (centralPositiveHalfStates
          w hw K halfExtent))
      floorData.floor floorData.floor_pos
  exact Q'.le_divPos_of_mul_le _ _
    floorData.floor_pos hmul

theorem exactNumeratorError_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤ exactNumeratorError endpoint source := by
  unfold exactNumeratorError
  exact listQSum_nonnegative_on _ _
    (fun target _ => Q'.abs_nonneg _)

theorem exactEndpointNumeratorCeiling_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      exactEndpointNumeratorCeiling endpoint source := by
  unfold exactEndpointNumeratorCeiling
  exact listQSum_nonnegative_on _ _
    (fun target _ => Q'.abs_nonneg _)

theorem exactPartitionError_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') ≤ exactPartitionError endpoint :=
  Q'.abs_nonneg _

theorem exactCrossMajorant_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤ exactCrossMajorant endpoint source := by
  unfold exactCrossMajorant
  exact Q'.add_le_add
    (Q'.mul_nonneg _ _
      (exactNumeratorError_nonnegative endpoint source)
      (Q'.le_of_lt endpoint.partition_pos))
    (Q'.mul_nonneg _ _
      (exactEndpointNumeratorCeiling_nonnegative
        endpoint source)
      (exactPartitionError_nonnegative endpoint))

theorem exactEntryBudget_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤ exactEntryBudget endpoint source := by
  unfold exactEntryBudget Q'.divPos
  exact Q'.mul_nonneg _ _
    (exactCrossMajorant_nonnegative endpoint source)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (exactCrossDenominator_pos endpoint)))

theorem exactNumeratorError_bounds_entry
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {source target : EdgeLabelling}
    (htarget :
      target ∈ endpointStates endpoint) :
    Q'.abs
        (centralPhysicalReflectedKernel
              w K halfExtent source target +
          (-endpoint.numerator source target)) ≤
      exactNumeratorError endpoint source := by
  exact listQSum_member_le_nonnegative
    (fun state =>
      Q'.abs
        (centralPhysicalReflectedKernel
              w K halfExtent source state +
          (-endpoint.numerator source state)))
    (fun state => Q'.abs_nonneg _)
    (endpointStates endpoint)
    htarget

theorem exactEndpointNumeratorCeiling_bounds_entry
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {source target : EdgeLabelling}
    (htarget :
      target ∈ endpointStates endpoint) :
    Q'.abs (endpoint.numerator source target) ≤
      exactEndpointNumeratorCeiling endpoint source := by
  exact listQSum_member_le_nonnegative
    (fun state => Q'.abs (endpoint.numerator source state))
    (fun state => Q'.abs_nonneg _)
    (endpointStates endpoint)
    htarget

/-! ## 2. Located marginal payment and the canonical tolerance -/

/-- Sum of the exact normalized entry budgets over retained source rows. -/
def exactEntryBudgetSum
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  listQSum
    (exactEntryBudget endpoint)
    (endpointStates endpoint)

theorem exactEntryBudgetSum_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') ≤ exactEntryBudgetSum endpoint := by
  unfold exactEntryBudgetSum
  exact listQSum_nonnegative_on _ _
    (fun source _ =>
      exactEntryBudget_nonnegative endpoint source)

/-- Canonical exact tolerance at a fixed BF4 carrier. -/
def exactFiniteEpsilon
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  Q'.divPos
    (Q'.ofNat (endpointStates endpoint).length *
      exactEntryBudgetSum endpoint)
    floorData.floor floorData.floor_pos

theorem exactFiniteEpsilon_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') ≤ exactFiniteEpsilon endpoint := by
  unfold exactFiniteEpsilon Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.ofNat_nonneg _)
      (exactEntryBudgetSum_nonnegative endpoint))
    (Q'.le_of_lt
      (Q'.recipPos_pos _ _))

/-- The explicit order-one rank-one endpoint cannot satisfy the quarter
premise, even before any AF limit is taken: its coarse rate is already at
least one and the exact comparison tolerance is nonnegative.  Hence the
next endpoint must exploit centered cancellation (for example a higher
positive Gram partial), rather than merely sharpen the spacing estimate
for this canonical Cauchy--Schwarz bound. -/
theorem canonicalRankOne_exactQuarterPremise_impossible
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) :
    ¬
      ((canonicalRankOneGeometricTaylorEndpointSpectralData
          w hw K halfExtent).toRawEndpoint.rate +
          exactFiniteEpsilon
            (canonicalRankOneGeometricTaylorEndpointSpectralData
              w hw K halfExtent).toRawEndpoint ≤
        Q'.mkPos 1 4 (by decide)) := by
  let spectral :=
    canonicalRankOneGeometricTaylorEndpointSpectralData
      w hw K halfExtent
  let endpoint := spectral.toRawEndpoint
  intro hquarter
  have hrate : (1 : Q') ≤ endpoint.rate := by
    exact one_le_canonicalRankOneRate
      hw K halfExtent
  have hepsilon :
      (0 : Q') ≤ exactFiniteEpsilon endpoint :=
    exactFiniteEpsilon_nonnegative endpoint
  have hsum :
      (1 : Q') ≤
        endpoint.rate + exactFiniteEpsilon endpoint :=
    Q'.le_trans' _ _ _ hrate
      (Q'.add_le_self_of_nonneg
        endpoint.rate
        (exactFiniteEpsilon endpoint)
        hepsilon)
  have himpossible :
      (1 : Q') ≤ Q'.mkPos 1 4 (by decide) :=
    Q'.le_trans' _ _ _ hsum hquarter
  exact
    (by decide :
      ¬ ((1 : Q') ≤ Q'.mkPos 1 4 (by decide)))
      himpossible

/-! ## 3. The exact Type-valued inhabitant -/

/-- Computed fixed-scale data: the rational tolerance and the complete
separated numerator/partition/marginal budget which it pays. -/
structure ExactFiniteBudgetData
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Type where
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  budget :
    CentralPhysicalNumeratorPartitionBudget
      endpoint epsilon

/-- Every finite physical BF4 carrier and every signed symmetric endpoint
have a canonical exact numerator/partition budget. -/
def exactFiniteBudgetData
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    ExactFiniteBudgetData endpoint := by
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  let states := endpointStates endpoint
  let numeratorError := exactNumeratorError endpoint
  let endpointCeiling :=
    exactEndpointNumeratorCeiling endpoint
  let partitionError := exactPartitionError endpoint
  let entryBudget := exactEntryBudget endpoint
  let epsilon := exactFiniteEpsilon endpoint
  have hphysicalPartition :
      (0 : Q') <
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent) :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent)
  exact
    { epsilon := epsilon
      epsilon_nonnegative :=
        exactFiniteEpsilon_nonnegative endpoint
      budget :=
        { numeratorError := numeratorError
          endpointNumeratorCeiling := endpointCeiling
          partitionError := partitionError
          entryBudget := entryBudget
          numeratorError_nonnegative := by
            intro source _
            exact exactNumeratorError_nonnegative
              endpoint source
          endpointNumeratorCeiling_nonnegative := by
            intro source _
            exact
              exactEndpointNumeratorCeiling_nonnegative
                endpoint source
          partitionError_nonnegative :=
            exactPartitionError_nonnegative endpoint
          entryBudget_nonnegative := by
            intro source _
            exact exactEntryBudget_nonnegative
              endpoint source
          numerator_error := by
            intro source _ target htarget
            exact exactNumeratorError_bounds_entry
              endpoint htarget
          endpoint_numerator_ceiling := by
            intro source _ target htarget
            exact
              exactEndpointNumeratorCeiling_bounds_entry
                endpoint htarget
          partition_error :=
            Q'.le_refl' _
          normalized_entry_payment := by
            intro source _
            exact Q'.le_of_eqv
              (Q'.eqv_symm
                (Q'.divPos_mul_eqv
                  (exactCrossMajorant endpoint source)
                  (exactCrossDenominator endpoint)
                  (exactCrossDenominator_pos endpoint)))
          marginalBudget :=
            { marginalFloor := fun _ => floorData.floor
              epsilon_nonnegative :=
                exactFiniteEpsilon_nonnegative endpoint
              marginalFloor_nonnegative := by
                intro source _
                exact Q'.le_of_lt floorData.floor_pos
              marginalFloor_le_physical := by
                intro source hsource
                exact floorData.floor_le source hsource
              carrier_payment := by
                intro source hsource
                have hentry :
                    entryBudget source ≤
                      exactEntryBudgetSum endpoint := by
                  exact listQSum_member_le_nonnegative
                    entryBudget
                    (fun state =>
                      exactEntryBudget_nonnegative
                        endpoint state)
                    states hsource
                have hscaled :
                    Q'.ofNat states.length *
                        entryBudget source ≤
                      Q'.ofNat states.length *
                        exactEntryBudgetSum endpoint :=
                  Q'.mul_le_mul_of_nonneg_left _ _ _
                    hentry (Q'.ofNat_nonneg _)
                exact Q'.le_trans' _ _ _ hscaled
                  (Q'.le_of_eqv
                    (Q'.eqv_symm
                      (Q'.divPos_mul_eqv
                        (Q'.ofNat states.length *
                          exactEntryBudgetSum endpoint)
                        floorData.floor
                        floorData.floor_pos))) } } }

theorem exactFiniteBudgetData_epsilon
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (exactFiniteBudgetData endpoint).epsilon =
      exactFiniteEpsilon endpoint :=
  rfl

/-! ## 4. Direct physical consequences and the exact quarter test -/

/-- The canonical exact budget gives a literal fixed-scale row-relative
comparison, with no analytic hypothesis.  The price is the computed
`exactFiniteEpsilon endpoint`; uniform smallness of that value is the
remaining AF theorem. -/
theorem exactFinite_row_relative_error
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralNormalizedPhysicalReflectedKernel
          w hw K halfExtent)
        endpoint.joint source ≤
      exactFiniteEpsilon endpoint *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact
    (exactFiniteBudgetData endpoint).budget.row_relative_error
      endpoint hsource

/-- Exact signed symmetric-reference comparison at one physical BF4 scale. -/
def exactFiniteComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalSymmetricReferenceComparison
      w hw K halfExtent :=
  (exactFiniteBudgetData endpoint).budget.toSymmetricReferenceComparison
    endpoint
    (exactFiniteEpsilon endpoint)
    (exactFiniteEpsilon_nonnegative endpoint)

/-- The genuine fixed-scale quarter theorem now has one fully executable
rational premise: the endpoint rate plus the exact computed physical
comparison tolerance must fit below `1/4`. -/
theorem exactFinite_physical_markov_quadratic_abs_le_quarter
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (hquarter :
      endpoint.rate + exactFiniteEpsilon endpoint ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K halfExtent
          observable observable := by
  exact
    CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le_quarter
      (exactFiniteComparison endpoint)
      hquarter observable hmean

end YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget

#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactCrossDenominator_pos
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.zeroEdgeLabelling_mem_centralHalfStates
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.zeroEdgeLabelling_mem_centralBoundaryChannels
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.assembleReflectedSlabLabelling_zero
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.one_le_centralPhysicalReflectedKernel_vacuum
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.centralNormalizedPhysicalReflectedKernel_vacuum_pos
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.centralPhysicalRowMarginal_vacuum_pos
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.zeroEdgeLabelling_mem_centralPositiveHalfStates
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.one_le_rankOneAmplitudeL2Sum_centralPositive
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.centralPositivePhysicalMarginalFloor_le_one
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.one_le_canonicalRankOneRate
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactNumeratorError_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactEndpointNumeratorCeiling_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactPartitionError_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactCrossMajorant_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactEntryBudget_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactNumeratorError_bounds_entry
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactEndpointNumeratorCeiling_bounds_entry
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactEntryBudgetSum_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactFiniteEpsilon_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.canonicalRankOne_exactQuarterPremise_impossible
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactFiniteBudgetData
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactFinite_row_relative_error
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactFiniteComparison
#print axioms YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.exactFinite_physical_markov_quadratic_abs_le_quarter
