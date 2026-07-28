/-
# Outer-cutoff transport through the deterministic BF4 U(1) block

The finite BF4 block map is written with a cutoff-dependent bounded wrapper
so that it is total on arbitrary charge labellings.  On every state in the
physical cutoff carrier, however, that wrapper is exactly the direct signed
sum of the four fine charges.  This module removes the apparent dependence
on the cutoff by naming that direct block state.

Consequently every blocked exponent-Gram coordinate is the probability of
one cutoff-independent Boolean event under the canonical normalized fine
U(1) slab law.  The outer-cutoff normalized-event estimate therefore passes
through the deterministic block exactly, giving a bound uniform in every
later cutoff and an explicit modulus.

This is a fixed-nome, fixed-geometry statement.  It neither constructs a
constructive-real limit object nor supplies uniformity as the nome tends to
one or the slab volume grows.

All constructions are finite and exact over `Q'`.  There is no
`Classical.*`, `Real`, `native_decide`, custom axiom, noncomputable
declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff
import YMGap.Continuum.BF4U1ActualExponentGramScoreTube

namespace YMGap.Continuum.BF4U1OuterCutoffBlockGramTransport

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1BlockReflectionCP
open YMGap.Continuum.BF4U1ActualExponentGramScoreTube
open YMGap.Continuum.BF4U1ExponentGramPositivity
open YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff
open YMGap.Continuum.BF4U1OuterCutoffNesting
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BF4U1OuterCutoffTensorTailModulus
open YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1TwistedPhysicalReindex
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A cutoff-independent direct block -/

/-- Direct dyadic signed-charge block on the physical coarse face list.
Unlike `u1BlockState`, this definition does not contain a carrier cutoff.
The value outside the physical face list is zero. -/
def u1DirectBlockState
    (G : CutoffOneGeometry)
    (fineState : ChargeLabelling) : ChargeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges
        (centralExtent G.coarseHalf) then
      encodeCharge
        (dyadicFaceChargeSum
          (centralExtent G.fineHalf) fineState
          (slabPlaquetteAt
            (centralExtent G.coarseHalf) id))
    else 0

/-- On a listed fine state, the total bounded BF4 block agrees pointwise
with the cutoff-independent direct block.  The pointwise formulation avoids
functional extensionality and is exactly what the exponent sums consume. -/
theorem u1BlockState_eq_direct_at
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states)
    (id : Nat) :
    u1BlockState G fineChargeCutoff fineState id =
      u1DirectBlockState G fineState id := by
  by_cases hid :
      id ∈ slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)
  · unfold u1DirectBlockState
    rw [if_pos hid]
    exact
      u1BlockState_eq_direct_on_physical
        G g hg fineChargeCutoff hfine hid
  · unfold u1DirectBlockState u1BlockState
    rw [if_neg hid, if_neg hid]

/-! ## 2. Exponent coordinates as fixed Boolean events -/

/-- The blocked exponent-Gram coordinate viewed as a Boolean event on a fine
state.  It is independent of every outer charge cutoff and of the candidate
coarse coupling. -/
def u1DirectBlockExponentGramEvent
    (G : CutoffOneGeometry)
    (coordinate : ExponentGramCoordinate)
    (fineState : ChargeLabelling) : Bool :=
  decide
    (u1LowerHeatExponent G.coarseHalf
        (centralLowerRestriction G.coarseHalf
          (u1DirectBlockState G fineState)) =
        coordinate.leftExponent ∧
      u1LowerHeatExponent G.coarseHalf
        (u1ReflectedUpperRestriction G.coarseHalf
          (u1DirectBlockState G fineState)) =
        coordinate.rightExponent)

private theorem u1HeatExponentOn_eq_of_pointwise
    (left right : ChargeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id = right id) →
      u1HeatExponentOn ids left =
        u1HeatExponentOn ids right
  | [], _ => rfl
  | id :: tail, hpoint => by
      simp only [u1HeatExponentOn]
      rw [hpoint id List.mem_cons_self]
      exact congrArg
        (fun value =>
          chargeMagnitude (right id) *
              chargeMagnitude (right id) +
            value)
        (u1HeatExponentOn_eq_of_pointwise
          left right tail
          (fun item hitem =>
            hpoint item
              (List.mem_cons_of_mem id hitem)))

private theorem u1BlockLowerExponentCoefficient_eq_direct
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff exponent : Nat)
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states) :
    u1ExponentCoefficient G.coarseHalf exponent
        (centralLowerRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) =
      u1ExponentCoefficient G.coarseHalf exponent
        (centralLowerRestriction G.coarseHalf
          (u1DirectBlockState G fineState)) := by
  unfold u1ExponentCoefficient u1LowerHeatExponent
  rw [u1HeatExponentOn_eq_of_pointwise]
  intro id hid
  simp only [centralLowerRestriction, if_pos hid]
  exact
    u1BlockState_eq_direct_at
      G g hg fineChargeCutoff hfine id

private theorem u1BlockUpperExponentCoefficient_eq_direct
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff exponent : Nat)
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states) :
    u1ExponentCoefficient G.coarseHalf exponent
        (u1ReflectedUpperRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) =
      u1ExponentCoefficient G.coarseHalf exponent
        (u1ReflectedUpperRestriction G.coarseHalf
          (u1DirectBlockState G fineState)) := by
  unfold u1ExponentCoefficient u1LowerHeatExponent
  rw [u1HeatExponentOn_eq_of_pointwise]
  intro id hid
  simp only [u1ReflectedUpperRestriction, if_pos hid]
  rw [u1BlockState_eq_direct_at
    G g hg fineChargeCutoff hfine
    (slabFaceReflectId
      (centralExtent G.coarseHalf) id)]

private theorem exponentCoefficient_product_eq_eventIndicator
    (G : CutoffOneGeometry)
    (coordinate : ExponentGramCoordinate)
    (fineState : ChargeLabelling) :
    u1ExponentCoefficient G.coarseHalf
          coordinate.leftExponent
          (centralLowerRestriction G.coarseHalf
            (u1DirectBlockState G fineState)) *
        u1ExponentCoefficient G.coarseHalf
          coordinate.rightExponent
          (u1ReflectedUpperRestriction G.coarseHalf
            (u1DirectBlockState G fineState)) ≈
      if u1DirectBlockExponentGramEvent
          G coordinate fineState then 1 else 0 := by
  unfold u1DirectBlockExponentGramEvent
    u1ExponentCoefficient
  by_cases hleft :
      u1LowerHeatExponent G.coarseHalf
          (centralLowerRestriction G.coarseHalf
            (u1DirectBlockState G fineState)) =
        coordinate.leftExponent
  · by_cases hright :
      u1LowerHeatExponent G.coarseHalf
          (u1ReflectedUpperRestriction G.coarseHalf
            (u1DirectBlockState G fineState)) =
        coordinate.rightExponent
    · simp [hleft, hright]
      exact Q'.mul_one_eqv 1
    · simp [hleft, hright]
      exact Q'.mul_zero_eqv 1
  · simp [hleft]
    exact Q'.zero_mul_eqv _

/-! ## 3. Normalized Boolean-event identification -/

private theorem canonicalEventProbability_eq_normalizedIndicator
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (event : ChargeLabelling → Bool) :
    canonicalU1SlabEventProbability
        w hw half K event ≈
      listQSum
        (fun state =>
          if event state then
            (canonicalU1Slab w hw half K).normalizedMass state
          else 0)
        (canonicalU1Slab w hw half K).states := by
  let D := canonicalU1Slab w hw half K
  unfold canonicalU1SlabEventProbability
    canonicalU1SlabEventNumerator
    U1SlabData.normalizedMass Q'.divPos
  refine Q'.eqv_symm
    (Q'.eqv_trans _
      (listQSum
        (fun state =>
          (if event state then D.physicalTerm state else 0) *
            Q'.recipPos D.partition D.partition_pos)
        D.states) _ ?_ ?_)
  · apply listQSum_congr_on
    intro state _
    by_cases hevent : event state
    · rw [if_pos hevent, if_pos hevent]
      exact Q'.eqv_refl _
    · rw [if_neg hevent, if_neg hevent]
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv
          (Q'.recipPos D.partition D.partition_pos))
  · exact listQSum_mul_right
      (fun state =>
        if event state then D.physicalTerm state else 0)
      (Q'.recipPos D.partition D.partition_pos)
      D.states

private theorem blockedEntry_eq_normalizedDirectIndicator
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) :
    u1BlockedExponentGramEntry
        G g hg candidate hcandidate
          fineChargeCutoff coordinate ≈
      listQSum
        (fun fineState =>
          if u1DirectBlockExponentGramEvent
              G coordinate fineState then
            (fineU1Data G g hg
              fineChargeCutoff).normalizedMass fineState
          else 0)
        (fineU1Data G g hg
          fineChargeCutoff).states := by
  let observable : ChargeLabelling → Q' :=
    fun coarseState =>
      u1ExponentCoefficient G.coarseHalf
          coordinate.leftExponent
          (centralLowerRestriction
            G.coarseHalf coarseState) *
        u1ExponentCoefficient G.coarseHalf
          coordinate.rightExponent
          (u1ReflectedUpperRestriction
            G.coarseHalf coarseState)
  refine Q'.eqv_trans _
    (u1BlockedObservableExpectation
      G g hg candidate hcandidate
        fineChargeCutoff observable) _ ?_ ?_
  · unfold u1BlockedExponentGramEntry
      u1ExponentGramEntry reflectedLawBilinear
      u1BlockedObservableExpectation observable
    apply listQSum_congr_on
    intro coarseState _
    rw [u1ExponentCoefficient_reflectedRestrictions]
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _ _ _
      (u1BlockedObservableExpectation_eq_pullback
        G g hg candidate hcandidate
          fineChargeCutoff observable) ?_
    apply listQSum_congr_on
    intro fineState hfine
    unfold observable
    rw [
      u1BlockLowerExponentCoefficient_eq_direct
        G g hg fineChargeCutoff
        coordinate.leftExponent hfine,
      u1BlockUpperExponentCoefficient_eq_direct
        G g hg fineChargeCutoff
        coordinate.rightExponent hfine]
    have hindicator :=
      exponentCoefficient_product_eq_eventIndicator
        G coordinate fineState
    by_cases hevent :
        u1DirectBlockExponentGramEvent
          G coordinate fineState
    · rw [if_pos hevent] at hindicator
      rw [if_pos hevent]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          ((fineU1Data G g hg
            fineChargeCutoff).normalizedMass fineState)
          _ _ hindicator)
        (Q'.mul_one_eqv _)
    · rw [if_neg hevent] at hindicator
      rw [if_neg hevent]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          ((fineU1Data G g hg
            fineChargeCutoff).normalizedMass fineState)
          _ _ hindicator)
        (Q'.mul_zero_eqv _)

/-- Exact identification of an actual blocked coordinate with one canonical
fine-slab event probability.  In particular the value is independent of the
candidate coarse coupling, even though the finite pushed carrier used to
define it depends on that candidate. -/
theorem u1BlockedExponentGramEntry_eq_outerEventProbability
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) :
    u1BlockedExponentGramEntry
        G g hg candidate hcandidate
          fineChargeCutoff coordinate ≈
      canonicalU1SlabEventProbability
        g hg G.fineHalf fineChargeCutoff
        (u1DirectBlockExponentGramEvent G coordinate) := by
  refine Q'.eqv_trans _ _ _
    (blockedEntry_eq_normalizedDirectIndicator
      G g hg candidate hcandidate
        fineChargeCutoff coordinate) ?_
  exact Q'.eqv_symm
    (canonicalEventProbability_eq_normalizedIndicator
      g hg G.fineHalf fineChargeCutoff
      (u1DirectBlockExponentGramEvent G coordinate))

/-! ## 4. The unblocked coarse coordinate as an event -/

/-- Cutoff-independent Boolean event representing one ordinary U(1)
exponent-Gram coordinate. -/
def u1ExponentGramEvent
    (half : Nat)
    (coordinate : ExponentGramCoordinate)
    (state : ChargeLabelling) : Bool :=
  decide
    (u1LowerHeatExponent half
        (centralLowerRestriction half state) =
        coordinate.leftExponent ∧
      u1LowerHeatExponent half
        (u1ReflectedUpperRestriction half state) =
        coordinate.rightExponent)

private theorem exponentCoefficient_product_eq_plainEventIndicator
    (half : Nat)
    (coordinate : ExponentGramCoordinate)
    (state : ChargeLabelling) :
    u1ExponentCoefficient half coordinate.leftExponent
          (centralLowerRestriction half state) *
        u1ExponentCoefficient half coordinate.rightExponent
          (u1ReflectedUpperRestriction half state) ≈
      if u1ExponentGramEvent half coordinate state
        then 1 else 0 := by
  unfold u1ExponentGramEvent u1ExponentCoefficient
  by_cases hleft :
      u1LowerHeatExponent half
          (centralLowerRestriction half state) =
        coordinate.leftExponent
  · by_cases hright :
      u1LowerHeatExponent half
          (u1ReflectedUpperRestriction half state) =
        coordinate.rightExponent
    · simp [hleft, hright]
      exact Q'.mul_one_eqv 1
    · simp [hleft, hright]
      exact Q'.mul_zero_eqv 1
  · simp [hleft]
    exact Q'.zero_mul_eqv _

/-- An ordinary canonical U(1) exponent-Gram entry is exactly one normalized
Boolean-event probability. -/
theorem u1ExponentGramEntry_eq_outerEventProbability
    (w : Q') (hw : (0 : Q') ≤ w)
    (half K : Nat)
    (coordinate : ExponentGramCoordinate) :
    u1ExponentGramEntry half
        (canonicalU1Slab w hw half K).states
        (canonicalU1Slab w hw half K).normalizedMass
    coordinate ≈
      canonicalU1SlabEventProbability
        w hw half K
        (u1ExponentGramEvent half coordinate) := by
  let D := canonicalU1Slab w hw half K
  change
    u1ExponentGramEntry half D.states
        D.normalizedMass coordinate ≈
      canonicalU1SlabEventProbability
        w hw half K
        (u1ExponentGramEvent half coordinate)
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        if u1ExponentGramEvent half coordinate state then
          D.normalizedMass state
        else 0)
      D.states) _ ?_ ?_
  · refine Q'.eqv_trans _
      (u1FullNormalizedMassReflectionBilinear D
        (u1ExponentCoefficient half
          coordinate.leftExponent)
        (u1ExponentCoefficient half
          coordinate.rightExponent)) _ ?_ ?_
    · exact
        u1ExponentGramEntry_eq_fullBilinear
          D coordinate
    · unfold u1FullNormalizedMassReflectionBilinear
      apply listQSum_congr_on
      intro state _
      have hindicator :=
        exponentCoefficient_product_eq_plainEventIndicator
          half coordinate state
      by_cases hevent :
          u1ExponentGramEvent half coordinate state
      · rw [if_pos hevent] at hindicator
        rw [if_pos hevent]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            _ _ (D.normalizedMass state) hindicator)
          (Q'.one_mul_eqv _)
      · rw [if_neg hevent] at hindicator
        rw [if_neg hevent]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            _ _ (D.normalizedMass state) hindicator)
          (Q'.zero_mul_eqv _)
  · exact Q'.eqv_symm
      (canonicalEventProbability_eq_normalizedIndicator
        w hw half K
        (u1ExponentGramEvent half coordinate))

/-- The literal candidate coarse entry is the corresponding canonical
coarse-slab event probability at outer charge cutoff `4K`. -/
theorem u1CoarseExponentGramEntry_eq_outerEventProbability
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) :
    u1CoarseExponentGramEntry
        G candidate hcandidate fineChargeCutoff coordinate ≈
      canonicalU1SlabEventProbability
        candidate (Q'.le_of_lt hcandidate)
        G.coarseHalf (4 * fineChargeCutoff)
        (u1ExponentGramEvent G.coarseHalf coordinate) := by
  unfold u1CoarseExponentGramEntry coarseU1Data
  exact
    u1ExponentGramEntry_eq_outerEventProbability
      candidate (Q'.le_of_lt hcandidate)
      G.coarseHalf (4 * fineChargeCutoff) coordinate

/-! ## 5. Uniform outer-cutoff transport -/

/-- The deterministic BF4 block preserves the outer tensor-envelope bound.
Both candidate couplings may be chosen independently because the blocked
coordinate is represented by the same fine-state event at both cutoffs. -/
theorem u1BlockedExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {K L : Nat} (hKL : K ≤ L)
    (candidateK : Q') (hcandidateK : (0 : Q') < candidateK)
    (candidateL : Q') (hcandidateL : (0 : Q') < candidateL)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (u1BlockedExponentGramEntry
            G g (Q'.le_of_lt hg0)
              candidateK hcandidateK K coordinate +
          -u1BlockedExponentGramEntry
            G g (Q'.le_of_lt hg0)
              candidateL hcandidateL L coordinate) ≤
      signedChargeTensorTailEnvelope g K
        (slabPhysicalFaceEdges
          (centralExtent G.fineHalf)).length := by
  have hK :=
    u1BlockedExponentGramEntry_eq_outerEventProbability
      G g (Q'.le_of_lt hg0)
      candidateK hcandidateK K coordinate
  have hL :=
    u1BlockedExponentGramEntry_eq_outerEventProbability
      G g (Q'.le_of_lt hg0)
      candidateL hcandidateL L coordinate
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (absQ_eqv_congr
        (Q'.add_eqv_congr'
          hK (Q'.neg_eqv_congr _ _ hL)))) ?_
  exact
    canonicalU1SlabEventProbability_outerCutoff_abs_le_tensorEnvelope
      hg0 hg1 G.fineHalf hKL
      (u1DirectBlockExponentGramEvent G coordinate)

/-- Explicit outer-cutoff modulus for every actual blocked exponent-Gram
coordinate, uniform in the later cutoff and in both candidate couplings. -/
theorem u1BlockedExponentGramEntry_outerCutoff_abs_le_of_cutoff
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat} (hKL : K ≤ L)
    (hK :
      signedChargeTensorTailCutoff g ε
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length ≤ K)
    (candidateK : Q') (hcandidateK : (0 : Q') < candidateK)
    (candidateL : Q') (hcandidateL : (0 : Q') < candidateL)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (u1BlockedExponentGramEntry
            G g (Q'.le_of_lt hg0)
              candidateK hcandidateK K coordinate +
          -u1BlockedExponentGramEntry
            G g (Q'.le_of_lt hg0)
              candidateL hcandidateL L coordinate) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (u1BlockedExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
      G hg0 hg1 hKL
      candidateK hcandidateK candidateL hcandidateL coordinate)
    (signedChargeTensorTailEnvelope_le_of_cutoff
      hg0 hg1 hε
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf)).length K hK)

/-- A fixed candidate coarse coordinate obeys the same outer-cutoff estimate,
with the physical coarse carrier cutoff `4K`. -/
theorem u1CoarseExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
    (G : CutoffOneGeometry)
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {K L : Nat} (hKL : K ≤ L)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (u1CoarseExponentGramEntry
            G candidate hcandidate0 K coordinate +
          -u1CoarseExponentGramEntry
            G candidate hcandidate0 L coordinate) ≤
      signedChargeTensorTailEnvelope candidate (4 * K)
        (slabPhysicalFaceEdges
          (centralExtent G.coarseHalf)).length := by
  have hK :=
    u1CoarseExponentGramEntry_eq_outerEventProbability
      G candidate hcandidate0 K coordinate
  have hL :=
    u1CoarseExponentGramEntry_eq_outerEventProbability
      G candidate hcandidate0 L coordinate
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (absQ_eqv_congr
        (Q'.add_eqv_congr'
          hK (Q'.neg_eqv_congr _ _ hL)))) ?_
  exact
    canonicalU1SlabEventProbability_outerCutoff_abs_le_tensorEnvelope
      hcandidate0 hcandidate1 G.coarseHalf
      (by omega : 4 * K ≤ 4 * L)
      (u1ExponentGramEvent G.coarseHalf coordinate)

/-- Explicit coarse-coordinate modulus, uniform in every later fine cutoff.
The cutoff hypothesis is naturally stated for the induced coarse cutoff
`4K`. -/
theorem u1CoarseExponentGramEntry_outerCutoff_abs_le_of_cutoff
    (G : CutoffOneGeometry)
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat} (hKL : K ≤ L)
    (hK :
      signedChargeTensorTailCutoff candidate ε
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        4 * K)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (u1CoarseExponentGramEntry
            G candidate hcandidate0 K coordinate +
          -u1CoarseExponentGramEntry
            G candidate hcandidate0 L coordinate) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (u1CoarseExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
      G hcandidate0 hcandidate1 hKL coordinate)
    (signedChargeTensorTailEnvelope_le_of_cutoff
      hcandidate0 hcandidate1 hε
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)).length
      (4 * K) hK)

/-! ## 6. Finite-coordinate and atlas-score transport -/

/-- The sum of the fine blocked-event envelope and the candidate coarse-event
envelope.  This bound contains no dependence on the later outer cutoff. -/
def u1ExponentGramOuterScoreCoordinateEnvelope
    (G : CutoffOneGeometry)
    (g candidate : Q') (K : Nat) : Q' :=
  signedChargeTensorTailEnvelope g K
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf)).length +
    signedChargeTensorTailEnvelope candidate (4 * K)
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)).length

theorem u1ExponentGramOuterScoreCoordinateEnvelope_nonnegative
    (G : CutoffOneGeometry)
    {g candidate : Q'}
    (hg0 : (0 : Q') < g)
    (hcandidate0 : (0 : Q') < candidate)
    (K : Nat) :
    (0 : Q') ≤
      u1ExponentGramOuterScoreCoordinateEnvelope
        G g candidate K := by
  unfold u1ExponentGramOuterScoreCoordinateEnvelope
  exact Q'.zero_le_add _ _
    (signedChargeTensorTailEnvelope_nonnegative
      hg0 K
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf)).length)
    (signedChargeTensorTailEnvelope_nonnegative
      hcandidate0 (4 * K)
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)).length)

/-- One absolute blocked-versus-coarse Gram discrepancy is Lipschitz under
outer-cutoff growth, with one fine and one coarse tensor envelope. -/
theorem u1ExponentGramCoordinateDistance_outerCutoff_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {K L : Nat} (hKL : K ≤ L)
    (coordinate : ExponentGramCoordinate) :
    Q'.abs
        (Q'.abs
            (u1BlockedExponentGramEntry
                G g (Q'.le_of_lt hg0)
                  candidate hcandidate0 L coordinate +
              -u1CoarseExponentGramEntry
                G candidate hcandidate0 L coordinate) +
          -Q'.abs
            (u1BlockedExponentGramEntry
                G g (Q'.le_of_lt hg0)
                  candidate hcandidate0 K coordinate +
              -u1CoarseExponentGramEntry
                G candidate hcandidate0 K coordinate)) ≤
      u1ExponentGramOuterScoreCoordinateEnvelope
        G g candidate K := by
  have hlipschitz :=
    abs_gram_discrepancy_lipschitz
      (u1BlockedExponentGramEntry
        G g (Q'.le_of_lt hg0)
          candidate hcandidate0 K coordinate)
      (u1CoarseExponentGramEntry
        G candidate hcandidate0 K coordinate)
      (u1BlockedExponentGramEntry
        G g (Q'.le_of_lt hg0)
          candidate hcandidate0 L coordinate)
      (u1CoarseExponentGramEntry
        G candidate hcandidate0 L coordinate)
  have hblocked :
      Q'.abs
          (u1BlockedExponentGramEntry
              G g (Q'.le_of_lt hg0)
                candidate hcandidate0 K coordinate +
            -u1BlockedExponentGramEntry
              G g (Q'.le_of_lt hg0)
                candidate hcandidate0 L coordinate) ≤
        signedChargeTensorTailEnvelope g K
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (absQ_eqv_abs
            (u1BlockedExponentGramEntry
                G g (Q'.le_of_lt hg0)
                  candidate hcandidate0 K coordinate +
              -u1BlockedExponentGramEntry
                G g (Q'.le_of_lt hg0)
                  candidate hcandidate0 L coordinate))))
      (u1BlockedExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
        G hg0 hg1 hKL
        candidate hcandidate0 candidate hcandidate0 coordinate)
  have hcoarse :
      Q'.abs
          (u1CoarseExponentGramEntry
              G candidate hcandidate0 K coordinate +
            -u1CoarseExponentGramEntry
              G candidate hcandidate0 L coordinate) ≤
        signedChargeTensorTailEnvelope candidate (4 * K)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (absQ_eqv_abs
            (u1CoarseExponentGramEntry
                G candidate hcandidate0 K coordinate +
              -u1CoarseExponentGramEntry
                G candidate hcandidate0 L coordinate))))
      (u1CoarseExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
        G hcandidate0 hcandidate1 hKL coordinate)
  exact Q'.le_trans' _ _ _ hlipschitz
    (Q'.add_le_add hblocked hcoarse)

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤
        Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead :=
        hbound head List.mem_cons_self
      have htail :=
        listQSum_le_length_mul_local
          value hbound0 tail
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value tail ≤
            bound + Q'.ofNat tail.length * bound :=
        Q'.add_le_add hhead htail
      have htarget :
          bound + Q'.ofNat tail.length * bound ≈
            Q'.ofNat (head :: tail).length * bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound ((1 : Q') * bound)
            (Q'.ofNat tail.length * bound)
            (Q'.eqv_symm
              (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              1 (Q'.ofNat tail.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv
            1 (Q'.ofNat tail.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv
              tail.length))
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv htarget)

/-- The literal finite exponent-Gram score at cutoff `L` differs from its
cutoff-`K` value by at most the coordinate count times the two-event
envelope. -/
theorem u1ExponentGramDistance_outerCutoff_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {K L : Nat} (hKL : K ≤ L)
    (coordinates : List ExponentGramCoordinate) :
    Q'.abs
        (u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
              candidate hcandidate0 L coordinates +
          -u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
              candidate hcandidate0 K coordinates) ≤
      Q'.ofNat coordinates.length *
        u1ExponentGramOuterScoreCoordinateEnvelope
          G g candidate K := by
  have hsum :=
    YMGap.Continuum.Z4FiniteCylinderQuadraticStability.abs_listQSum_sub_le
      (fun coordinate =>
        Q'.abs
          (u1BlockedExponentGramEntry
              G g (Q'.le_of_lt hg0)
                candidate hcandidate0 L coordinate +
            -u1CoarseExponentGramEntry
              G candidate hcandidate0 L coordinate))
      (fun coordinate =>
        Q'.abs
          (u1BlockedExponentGramEntry
              G g (Q'.le_of_lt hg0)
                candidate hcandidate0 K coordinate +
            -u1CoarseExponentGramEntry
              G candidate hcandidate0 K coordinate))
      coordinates
  refine Q'.le_trans' _ _ _ hsum ?_
  apply listQSum_le_length_mul_local
    _
    (u1ExponentGramOuterScoreCoordinateEnvelope_nonnegative
      G hg0 hcandidate0 K)
  intro coordinate _
  exact
    u1ExponentGramCoordinateDistance_outerCutoff_abs_le
      G hg0 hg1 hcandidate0 hcandidate1 hKL coordinate

/-- Explicit fixed-candidate modulus for the complete finite-coordinate
score.  The fine threshold is paid at `K`; the coarse threshold is paid at
the physically induced cutoff `4K`.  Both are independent of the later
outer cutoff `L`. -/
theorem u1ExponentGramDistance_outerCutoff_abs_le_of_cutoffs
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat} (hKL : K ≤ L)
    (coordinates : List ExponentGramCoordinate)
    (hFine :
      signedChargeTensorTailCutoff g
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length ≤
        K)
    (hCoarse :
      signedChargeTensorTailCutoff candidate
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        4 * K) :
    Q'.abs
        (u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
              candidate hcandidate0 L coordinates +
          -u1ExponentGramDistance
            G g (Q'.le_of_lt hg0)
              candidate hcandidate0 K coordinates) ≤
      ε := by
  let δ := twoEntryCoordinateTolerance coordinates ε
  have hδpos : (0 : Q') < δ :=
    twoEntryCoordinateTolerance_pos coordinates hε
  have hbase :=
    u1ExponentGramDistance_outerCutoff_abs_le
      G hg0 hg1 hcandidate0 hcandidate1 hKL coordinates
  have hfine :
      signedChargeTensorTailEnvelope g K
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length ≤
        δ :=
    signedChargeTensorTailEnvelope_le_of_cutoff
      hg0 hg1 hδpos
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf)).length
      K hFine
  have hcoarse :
      signedChargeTensorTailEnvelope candidate (4 * K)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        δ :=
    signedChargeTensorTailEnvelope_le_of_cutoff
      hcandidate0 hcandidate1 hδpos
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf)).length
      (4 * K) hCoarse
  have henvelope :
      u1ExponentGramOuterScoreCoordinateEnvelope
          G g candidate K ≤
        δ + δ := by
    unfold u1ExponentGramOuterScoreCoordinateEnvelope
    exact Q'.add_le_add hfine hcoarse
  have hscaled :
      Q'.ofNat coordinates.length *
          u1ExponentGramOuterScoreCoordinateEnvelope
            G g candidate K ≤
        Q'.ofNat coordinates.length * (δ + δ) := by
    exact Q'.mul_le_mul_of_nonneg_left
      _ _ _ henvelope
      (YMGap.Constructive.ExpNeg.ofNat_nonneg'
        coordinates.length)
  have hcountEqv :
      Q'.ofNat coordinates.length * (δ + δ) ≈
        Q'.ofNat
            (coordinates.length + coordinates.length) *
          δ := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv
        (Q'.ofNat coordinates.length) δ δ) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (Q'.ofNat coordinates.length)
          (Q'.ofNat coordinates.length) δ)) ?_
    exact Q'.mul_eqv_congr_right _ _ δ
      (Q'.eqv_symm
        (Q'.ofNat_add_eqv
          coordinates.length coordinates.length))
  have hcount :
      Q'.ofNat
            (coordinates.length + coordinates.length) *
          δ ≤
        Q'.ofNat
            (2 * (coordinates.length + 1)) *
          δ := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (CReal.ofNat_le_ofNat (by omega))
      (Q'.le_of_lt hδpos)
  have hpay :
      Q'.ofNat coordinates.length * (δ + δ) ≤
        ε := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcountEqv)
      (Q'.le_trans' _ _ _ hcount
        (Q'.le_of_eqv
          (twoEntryCoordinateScale_mul_tolerance_eqv
            coordinates ε)))
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ hscaled hpay)

/-- Finite-atlas wrapper of the score transport.  Membership makes both
conditional score definitions reduce to the same fixed candidate distance. -/
theorem atlasU1ExponentGramScore_outerCutoff_abs_le
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates)
    (hcandidate1 : candidate < (1 : Q'))
    {K L : Nat} (hKL : K ≤ L)
    (coordinates : List ExponentGramCoordinate) :
    Q'.abs
        (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate +
          -atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas K
              coordinates candidate) ≤
      Q'.ofNat coordinates.length *
        u1ExponentGramOuterScoreCoordinateEnvelope
          G g candidate K := by
  rw [
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas L
      coordinates candidate hcandidate,
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas K
      coordinates candidate hcandidate]
  exact
    u1ExponentGramDistance_outerCutoff_abs_le
      G hg0 hg1
      (atlas.candidate_pos hcandidate)
      hcandidate1 hKL coordinates

/-- Atlas-score form of the explicit fixed-candidate modulus.  The theorem is
uniform in the later cutoff `L`; only the named candidate's two explicit
tensor thresholds must be paid at the retained cutoff `K`. -/
theorem atlasU1ExponentGramScore_outerCutoff_abs_le_of_cutoffs
    (G : CutoffOneGeometry)
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (atlas : PositiveCouplingAtlas)
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates)
    (hcandidate1 : candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    {K L : Nat} (hKL : K ≤ L)
    (coordinates : List ExponentGramCoordinate)
    (hFine :
      signedChargeTensorTailCutoff g
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.fineHalf)).length ≤
        K)
    (hCoarse :
      signedChargeTensorTailCutoff candidate
          (twoEntryCoordinateTolerance coordinates ε)
          (slabPhysicalFaceEdges
            (centralExtent G.coarseHalf)).length ≤
        4 * K) :
    Q'.abs
        (atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas L
              coordinates candidate +
          -atlasU1ExponentGramScore
            G g (Q'.le_of_lt hg0) atlas K
              coordinates candidate) ≤
      ε := by
  rw [
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas L
      coordinates candidate hcandidate,
    atlasU1ExponentGramScore_of_mem
      G g (Q'.le_of_lt hg0) atlas K
      coordinates candidate hcandidate]
  exact
    u1ExponentGramDistance_outerCutoff_abs_le_of_cutoffs
      G hg0 hg1
      (atlas.candidate_pos hcandidate)
      hcandidate1 hε hKL coordinates
      hFine hCoarse

#print axioms u1BlockState_eq_direct_at
#print axioms u1BlockedExponentGramEntry_eq_outerEventProbability
#print axioms u1BlockedExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
#print axioms u1BlockedExponentGramEntry_outerCutoff_abs_le_of_cutoff
#print axioms u1ExponentGramEntry_eq_outerEventProbability
#print axioms u1CoarseExponentGramEntry_outerCutoff_abs_le_tensorEnvelope
#print axioms u1CoarseExponentGramEntry_outerCutoff_abs_le_of_cutoff
#print axioms u1ExponentGramCoordinateDistance_outerCutoff_abs_le
#print axioms u1ExponentGramDistance_outerCutoff_abs_le
#print axioms u1ExponentGramDistance_outerCutoff_abs_le_of_cutoffs
#print axioms atlasU1ExponentGramScore_outerCutoff_abs_le
#print axioms atlasU1ExponentGramScore_outerCutoff_abs_le_of_cutoffs

end YMGap.Continuum.BF4U1OuterCutoffBlockGramTransport
