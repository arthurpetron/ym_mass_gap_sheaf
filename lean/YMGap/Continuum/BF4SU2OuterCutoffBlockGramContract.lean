/-
# K-parametric SU(2) slab Gram family and block-pushforward interface/fence

The current physical BF4 kernel is hard-wired to fine cutoff one and coarse
cutoff four.  Nevertheless `SlabPhysicalData` itself supports an honest
outer family with fine cutoff `K` and coarse cutoff `4K`.  This module names
that family, its normalized exponent-Gram entries, and proves exact recovery
of the existing data at `K = 1`.

No parametric physical block kernel is invented.  Instead a Type-level
interface/fence records an additional deterministic block map, supported
carrier theorem, normalized pushforward identity, and cutoff-one *blocked
marginal* recovery.

This does **not** by itself connect the outer family to the available
`SU2PhysicalOuterCutoffNormalizedEventTail`: that theorem controls
`parametricKPhysicalPartition` on the box carrier
`List.range (plaquetteEdgeCount n)`, whereas this file uses
`slabParametricKPhysicalPartition` on the corrected-slab carrier
`slabPhysicalFaceEdges`.  A corrected-slab normalized-event tail theorem, or
a proved measure-preserving bridge between those two laws, remains a separate
analytic input.  The exact pullback theorem below deliberately stops at the
corrected-slab event probability.  Convergence of the full
blocked-versus-coarse score additionally needs the analogous normalized
corrected-slab tail at the candidate coarse coupling and induced cutoff
`4K`.
-/

import YMGap.Continuum.BF4ExponentGramMatchedOneStep
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

namespace YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract

set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

abbrev OuterSlabLabelling :=
  YMGap.Continuum.BF4ExponentGramMatchedOneStep.SlabLabelling

/-! ## 1. Honest outer slab family -/

/-- Fine SU(2) corrected slab at arbitrary spin cutoff `K`. -/
def su2FineOuterData
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat) : SlabPhysicalData where
  coupling := g
  coupling_nonnegative := hg
  cutoff := K
  half := G.fineHalf

/-- Coarse SU(2) corrected slab at the lossless induced cutoff `4K`. -/
def su2CoarseOuterData
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat) : SlabPhysicalData where
  coupling := candidate
  coupling_nonnegative := Q'.le_of_lt hcandidate
  cutoff := 4 * K
  half := G.coarseHalf

theorem su2FineOuterData_one
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g) :
    su2FineOuterData G g hg 1 = G.fineData g hg :=
  rfl

theorem su2CoarseOuterData_one
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    su2CoarseOuterData G candidate hcandidate 1 =
      G.coarseData candidate hcandidate := by
  rfl

/-- Normalized fine exponent-Gram coordinate on the outer family. -/
def su2FineOuterExponentGramEntry
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let fine := su2FineOuterData G g hg K
  exponentGramEntry G.fineHalf
    fine.physicalLabellings fine.normalizedMass coordinate

/-- Normalized coarse exponent-Gram coordinate on the induced `4K` family. -/
def su2CoarseOuterExponentGramEntry
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let coarse := su2CoarseOuterData G candidate hcandidate K
  exponentGramEntry G.coarseHalf
    coarse.physicalLabellings coarse.normalizedMass coordinate

/-- At `K=1`, the parametric coarse Gram is definitionally the existing
cutoff-four coarse discriminator entry. -/
theorem su2CoarseOuterExponentGramEntry_one
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coordinate : ExponentGramCoordinate) :
    su2CoarseOuterExponentGramEntry
        G candidate hcandidate 1 coordinate =
      coarseExponentGramEntry
        G candidate hcandidate coordinate := by
  rfl

/-! ## 2. The exact corrected-slab Boolean-event law -/

/-- Probability of a Boolean event under the normalized fine
corrected-slab law.  This is intentionally a finite sum of normalized slab
masses, not the box probability from
`SU2PhysicalOuterCutoffNormalizedEventTail`. -/
def su2FineOuterEventProbability
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) : Q' :=
  let fine := su2FineOuterData G g hg K
  listQSum
    (fun source =>
      if event source then fine.normalizedMass source else 0)
    fine.physicalLabellings

/-- Probability of a Boolean event under the normalized coarse
corrected-slab law at the induced cutoff `4K`. -/
def su2CoarseOuterEventProbability
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) : Q' :=
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  listQSum
    (fun target =>
      if event target then coarse.normalizedMass target else 0)
    coarse.physicalLabellings

private theorem listQSum_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _
        (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_mask_le_total_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item)
    (event : A → Bool) :
    ∀ items : List A,
      listQSum
          (fun item =>
            if event item then weight item else 0)
          items ≤
        listQSum weight items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      cases hevent : event head
      · simp only [listQSum, hevent, Bool.false_eq_true,
          ↓reduceIte]
        exact Q'.add_le_add
          (hweight head)
          (listQSum_mask_le_total_local
            weight hweight event tail)
      · simp only [listQSum, hevent, ↓reduceIte]
        exact Q'.add_le_add
          (Q'.le_refl' (weight head))
          (listQSum_mask_le_total_local
            weight hweight event tail)

private theorem listQSum_mask_le_total_on_local
    {A : Type} (weight : A → Q')
    (event : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        (0 : Q') ≤ weight item) →
      listQSum
          (fun item =>
            if event item then weight item else 0)
          items ≤
        listQSum weight items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hweight => by
      have htail :
          ∀ item, item ∈ tail →
            (0 : Q') ≤ weight item :=
        fun item hitem =>
          hweight item (List.mem_cons_of_mem head hitem)
      cases hevent : event head
      · simp only [listQSum, hevent, Bool.false_eq_true,
          ↓reduceIte]
        exact Q'.add_le_add
          (hweight head List.mem_cons_self)
          (listQSum_mask_le_total_on_local
            weight event tail htail)
      · simp only [listQSum, hevent, ↓reduceIte]
        exact Q'.add_le_add
          (Q'.le_refl' (weight head))
          (listQSum_mask_le_total_on_local
            weight event tail htail)

/-- The exact corrected-slab event law is nonnegative at every cutoff. -/
theorem su2FineOuterEventProbability_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) :
    (0 : Q') ≤
      su2FineOuterEventProbability G g hg K event := by
  unfold su2FineOuterEventProbability
  apply listQSum_nonnegative_local
  intro source
  by_cases hevent : event source = true
  · rw [if_pos hevent]
    exact
      (su2FineOuterData G g hg K).normalizedMass_nonnegative
        source
  · rw [if_neg hevent]
    exact Q'.le_refl' 0

/-- The exact corrected-slab event law is at most one at every cutoff. -/
theorem su2FineOuterEventProbability_le_one
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) :
    su2FineOuterEventProbability G g hg K event ≤
      (1 : Q') := by
  let fine := su2FineOuterData G g hg K
  have hmask :
      listQSum
          (fun source =>
            if event source then
              fine.normalizedMass source
            else 0)
          fine.physicalLabellings ≤
        listQSum fine.normalizedMass
          fine.physicalLabellings :=
    listQSum_mask_le_total_local
      fine.normalizedMass
      fine.normalizedMass_nonnegative
      event fine.physicalLabellings
  exact Q'.le_trans' _ _ _ hmask
    (Q'.le_of_eqv fine.normalizedMass_total)

/-- The exact coarse corrected-slab event law is nonnegative. -/
theorem su2CoarseOuterEventProbability_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) :
    (0 : Q') ≤
      su2CoarseOuterEventProbability
        G candidate hcandidate K event := by
  unfold su2CoarseOuterEventProbability
  apply listQSum_nonnegative_local
  intro target
  by_cases hevent : event target = true
  · rw [if_pos hevent]
    exact
      (su2CoarseOuterData
        G candidate hcandidate K).normalizedMass_nonnegative
        target
  · rw [if_neg hevent]
    exact Q'.le_refl' 0

/-- The exact coarse corrected-slab event law is at most one. -/
theorem su2CoarseOuterEventProbability_le_one
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) :
    su2CoarseOuterEventProbability
        G candidate hcandidate K event ≤
      (1 : Q') := by
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  have hmask :
      listQSum
          (fun target =>
            if event target then
              coarse.normalizedMass target
            else 0)
          coarse.physicalLabellings ≤
        listQSum coarse.normalizedMass
          coarse.physicalLabellings :=
    listQSum_mask_le_total_local
      coarse.normalizedMass
      coarse.normalizedMass_nonnegative
      event coarse.physicalLabellings
  exact Q'.le_trans' _ _ _ hmask
    (Q'.le_of_eqv coarse.normalizedMass_total)

/-- Boolean events agreeing on the actual finite corrected-slab carrier have
exactly the same normalized probability. -/
theorem su2FineOuterEventProbability_congr_on
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (K : Nat)
    (first second : OuterSlabLabelling → Bool)
    (hagrees :
      ∀ source,
        source ∈
            (su2FineOuterData G g hg K).physicalLabellings →
          first source = second source) :
    su2FineOuterEventProbability G g hg K first ≈
      su2FineOuterEventProbability G g hg K second := by
  unfold su2FineOuterEventProbability
  apply listQSum_congr_on
  intro source hsource
  rw [hagrees source hsource]
  exact Q'.eqv_refl _

/-- Cutoff-independent Boolean event for an ordinary corrected-slab
exponent-Gram coordinate. -/
def su2ExponentGramEvent
    (half : Nat)
    (coordinate : ExponentGramCoordinate)
    (state : OuterSlabLabelling) : Bool :=
  decide
    (lowerHeatExponent half
          (centralLowerRestriction half state) =
        coordinate.leftExponent ∧
      lowerHeatExponent half
          (centralReflectedUpperRestriction half state) =
        coordinate.rightExponent)

private theorem
    exponentCoefficient_product_eq_plainEventIndicator
    (half : Nat)
    (coordinate : ExponentGramCoordinate)
    (state : OuterSlabLabelling) :
    exponentCoefficient half coordinate.leftExponent
          (centralLowerRestriction half state) *
        exponentCoefficient half coordinate.rightExponent
          (centralReflectedUpperRestriction half state) ≈
      if su2ExponentGramEvent half coordinate state
        then 1 else 0 := by
  unfold su2ExponentGramEvent exponentCoefficient
  by_cases hleft :
      lowerHeatExponent half
          (centralLowerRestriction half state) =
        coordinate.leftExponent
  · by_cases hright :
      lowerHeatExponent half
          (centralReflectedUpperRestriction half state) =
        coordinate.rightExponent
    · simp [hleft, hright]
      exact Q'.mul_one_eqv 1
    · simp [hleft, hright]
      exact Q'.mul_zero_eqv 1
  · simp [hleft]
    exact Q'.zero_mul_eqv _

/-- Every ordinary coarse exponent-Gram coordinate is exactly a Boolean
event probability under the normalized coarse corrected-slab law. -/
theorem su2CoarseOuterExponentGramEntry_eq_eventProbability
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    su2CoarseOuterExponentGramEntry
        G candidate hcandidate K coordinate ≈
      su2CoarseOuterEventProbability
        G candidate hcandidate K
        (su2ExponentGramEvent G.coarseHalf coordinate) := by
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  unfold su2CoarseOuterExponentGramEntry
    su2CoarseOuterEventProbability
    exponentGramEntry reflectedLawBilinear
  apply listQSum_congr_on
  intro state _
  have hindicator :=
    exponentCoefficient_product_eq_plainEventIndicator
      G.coarseHalf coordinate state
  by_cases hevent :
      su2ExponentGramEvent G.coarseHalf coordinate state
  · rw [if_pos hevent] at hindicator
    rw [if_pos hevent]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        _ _ (coarse.normalizedMass state) hindicator)
      (Q'.one_mul_eqv _)
  · rw [if_neg hevent] at hindicator
    rw [if_neg hevent]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        _ _ (coarse.normalizedMass state) hindicator)
      (Q'.zero_mul_eqv _)

/-! ## 3. Stronger deterministic marginal surrogate -/

/-- **STRONGER DETERMINISTIC SURROGATE (not constructed here).** A
deterministic realization of the normalized outer slab marginal.

This is not the physically correct source-indexed SU(2) target: the existing
cutoff-one recoupling block is a stochastic Markov kernel.  The stochastic
contract in the final section is the honest physical interface.  This
deterministic structure remains useful as a strictly stronger surrogate
because it converts a blocked coordinate to a Boolean source event.

The `cutoff_one_mass` field recovers the existing physical kernel's blocked
marginal exactly at the only cutoff where that kernel is currently defined.
It does not recover the existing source-indexed stochastic conditional
kernel: `blockState` is a proposed deterministic realization of the same
marginal, not an identification with that conditional kernel.  The
pushforward identity is quantified over every rational observable and is
therefore strong enough to recover every exponent-Gram coordinate of the
blocked marginal.

The structure is still insufficient for outer-cutoff convergence without a
corrected-slab event-tail theorem (or a proved bridge to the box event law).
No value of this structure is constructed here, and this declaration is not
a new frontier enumeration or a discharge of any existing frontier atom. -/
structure SU2OuterPhysicalBlockContract
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  blockState :
    Nat → OuterSlabLabelling → OuterSlabLabelling
  blockedMass : Nat → OuterSlabLabelling → Q'
  blockState_mem :
    ∀ K source,
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
        blockState K source ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings
  pushforward_identity :
    ∀ K (observable : OuterSlabLabelling → Q'),
      listQSum
          (fun target =>
            observable target * blockedMass K target)
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings ≈
        listQSum
          (fun source =>
            (su2FineOuterData G g hg K).normalizedMass source *
              observable (blockState K source))
          (su2FineOuterData
            G g hg K).physicalLabellings
  blockedMass_nonnegative :
    ∀ K target,
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        (0 : Q') ≤ blockedMass K target
  blockState_cutoff_stable :
    ∀ K L source,
      K ≤ L →
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
        ∀ faceId,
          blockState K source faceId =
            blockState L source faceId
  cutoff_one_mass :
    ∀ target,
      blockedMass 1 target ≈
        let S :=
          G.candidateScalePair g hg candidate hcandidate
        let kernel := physicalKernel S rfl hcandidate
        kernel.blockedMass target

/-- Unit mass is not an extra field: it follows from the all-observable
pushforward identity by taking the constant-one observable. -/
theorem contractBlockedMass_total
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat) :
    listQSum
        (contract.blockedMass K)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      1 := by
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  let fine := su2FineOuterData G g hg K
  refine Q'.eqv_trans _
    (listQSum
      (fun target => (1 : Q') * contract.blockedMass K target)
      coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  refine Q'.eqv_trans _
    (listQSum
      (fun source => fine.normalizedMass source * (1 : Q'))
      fine.physicalLabellings) _ ?_ ?_
  · exact contract.pushforward_identity K (fun _ => 1)
  refine Q'.eqv_trans _
    (listQSum fine.normalizedMass fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    exact Q'.mul_one_eqv _
  · exact fine.normalizedMass_total

/-- At cutoff one, every expectation of the contract's blocked marginal
agrees with the existing physical kernel's blocked marginal.  This is the
strongest recovery furnished by `cutoff_one_mass`; it does not identify a
source-indexed deterministic block with the existing stochastic conditional
kernel. -/
theorem contractCutoffOneExpectation_eq_physicalKernel
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (observable : OuterSlabLabelling → Q') :
    listQSum
        (fun target =>
          observable target * contract.blockedMass 1 target)
        (su2CoarseOuterData
          G candidate hcandidate 1).physicalLabellings ≈
      listQSum
        (fun target =>
          observable target *
            let S :=
              G.candidateScalePair g hg candidate hcandidate
            let kernel := physicalKernel S rfl hcandidate
            kernel.blockedMass target)
        (su2CoarseOuterData
          G candidate hcandidate 1).physicalLabellings := by
  apply listQSum_congr_on
  intro target _
  exact Q'.mul_eqv_congr_left
    (observable target) _ _
    (contract.cutoff_one_mass target)

/-- The two exponents that determine a pulled-back blocked Gram event. -/
def contractBlockedExponentPair
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat) (source : OuterSlabLabelling) : Nat × Nat :=
  ( lowerHeatExponent G.coarseHalf
      (centralLowerRestriction G.coarseHalf
        (contract.blockState K source)),
    lowerHeatExponent G.coarseHalf
      (centralReflectedUpperRestriction G.coarseHalf
        (contract.blockState K source)) )

private theorem heatExponentOn_eq_of_pointwise
    (left right : OuterSlabLabelling)
    (hpoint : ∀ faceId, left faceId = right faceId) :
    ∀ ids, heatExponentOn ids left = heatExponentOn ids right
  | [] => rfl
  | faceId :: tail => by
      simp only [heatExponentOn]
      rw [hpoint faceId]
      exact congrArg
        (fun value => c4 (right faceId) + value)
        (heatExponentOn_eq_of_pointwise left right hpoint tail)

/-- On every old supported source, the pulled-back Boolean-event label is
independent of all later outer cutoffs.  This is the exact stability needed
before a finite-coordinate tail estimate can be transported through the
physical block interface. -/
theorem contractBlockedExponentPair_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    {K L : Nat} {source : OuterSlabLabelling}
    (hKL : K ≤ L)
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    contractBlockedExponentPair contract K source =
      contractBlockedExponentPair contract L source := by
  have hblock :
      ∀ faceId,
        contract.blockState K source faceId =
          contract.blockState L source faceId :=
    contract.blockState_cutoff_stable K L source hKL hsource
  apply Prod.ext
  · unfold contractBlockedExponentPair lowerHeatExponent
    apply heatExponentOn_eq_of_pointwise
    intro faceId
    simp only [centralLowerRestriction]
    split
    · exact hblock faceId
    · rfl
  · unfold contractBlockedExponentPair lowerHeatExponent
    apply heatExponentOn_eq_of_pointwise
    intro faceId
    simp only [centralReflectedUpperRestriction]
    split
    · exact hblock
        (slabFaceReflectId
          (centralExtent G.coarseHalf) faceId)
    · rfl

/-- The pulled-back Boolean event for one exponent-Gram coordinate.  It is
defined on the fine corrected-slab carrier. -/
def contractBlockedExponentGramEvent
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    (source : OuterSlabLabelling) : Bool :=
  decide
    (contractBlockedExponentPair contract K source =
      (coordinate.leftExponent, coordinate.rightExponent))

/-- On every old supported source, the pulled-back Boolean event is exactly
stable under every later cutoff.  This is enough to use one later-cutoff
event in a pairwise tail comparison once a corrected-slab event tail is
available. -/
theorem contractBlockedExponentGramEvent_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    {K L : Nat} {source : OuterSlabLabelling}
    (hKL : K ≤ L)
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (coordinate : ExponentGramCoordinate) :
    contractBlockedExponentGramEvent
        contract K coordinate source =
      contractBlockedExponentGramEvent
        contract L coordinate source := by
  unfold contractBlockedExponentGramEvent
  rw [
    contractBlockedExponentPair_cutoff_stable
      contract hKL hsource]

/-- At the old cutoff law, the old- and later-cutoff block events have equal
probability.  Thus a pairwise cutoff estimate can use the *single* later
event on both laws; no illicit equality of cutoff-dependent predicates is
needed outside the old supported carrier. -/
theorem contractBlockedExponentGramEventProbability_align
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    (coordinate : ExponentGramCoordinate) :
    su2FineOuterEventProbability G g hg K
        (contractBlockedExponentGramEvent
          contract K coordinate) ≈
      su2FineOuterEventProbability G g hg K
        (contractBlockedExponentGramEvent
          contract L coordinate) := by
  apply su2FineOuterEventProbability_congr_on
  intro source hsource
  exact contractBlockedExponentGramEvent_cutoff_stable
    contract hKL hsource coordinate

/-- Exponent-Gram entry of any supplied parametric physical block contract. -/
def contractBlockedExponentGramEntry
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  exponentGramEntry G.coarseHalf
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings
    (contract.blockedMass K) coordinate

private theorem exponentCoefficient_product_eq_eventIndicator
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    (source : OuterSlabLabelling) :
    exponentCoefficient G.coarseHalf
          coordinate.leftExponent
          (centralLowerRestriction G.coarseHalf
            (contract.blockState K source)) *
        exponentCoefficient G.coarseHalf
          coordinate.rightExponent
          (centralReflectedUpperRestriction G.coarseHalf
            (contract.blockState K source)) ≈
      if contractBlockedExponentGramEvent
          contract K coordinate source then 1 else 0 := by
  unfold contractBlockedExponentGramEvent
    contractBlockedExponentPair exponentCoefficient
  by_cases hleft :
      lowerHeatExponent G.coarseHalf
          (centralLowerRestriction G.coarseHalf
            (contract.blockState K source)) =
        coordinate.leftExponent
  · by_cases hright :
      lowerHeatExponent G.coarseHalf
          (centralReflectedUpperRestriction G.coarseHalf
            (contract.blockState K source)) =
        coordinate.rightExponent
    · simp [hleft, hright]
      exact Q'.mul_one_eqv 1
    · simp [hleft, hright]
      exact Q'.mul_zero_eqv 1
  · simp [hleft]
    exact Q'.zero_mul_eqv _

/-- Exact transport endpoint: every contract-blocked exponent-Gram
coordinate is one Boolean-event probability under the normalized fine
corrected-slab law.

This theorem does not invoke the box normalized-event tail.  Its right-hand
side uses `slabParametricKPhysicalPartition`; establishing a cutoff modulus
for this exact law is the remaining geometry-specific analytic input. -/
theorem contractBlockedExponentGramEntry_eq_fineEventProbability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    contractBlockedExponentGramEntry contract K coordinate ≈
      su2FineOuterEventProbability G g hg K
        (contractBlockedExponentGramEvent
          contract K coordinate) := by
  let observable : OuterSlabLabelling → Q' :=
    fun target =>
      exponentCoefficient G.coarseHalf
          coordinate.leftExponent
          (centralLowerRestriction
            G.coarseHalf target) *
        exponentCoefficient G.coarseHalf
          coordinate.rightExponent
          (centralReflectedUpperRestriction
            G.coarseHalf target)
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        observable target * contract.blockedMass K target)
      (su2CoarseOuterData
        G candidate hcandidate K).physicalLabellings) _ ?_ ?_
  · unfold contractBlockedExponentGramEntry
      exponentGramEntry reflectedLawBilinear observable
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (su2FineOuterData G g hg K).normalizedMass source *
          observable (contract.blockState K source))
      (su2FineOuterData G g hg K).physicalLabellings) _ ?_ ?_
  · exact contract.pushforward_identity K observable
  · unfold su2FineOuterEventProbability
    apply listQSum_congr_on
    intro source _
    have hindicator :=
      exponentCoefficient_product_eq_eventIndicator
        contract K coordinate source
    by_cases hevent :
        contractBlockedExponentGramEvent
          contract K coordinate source
    · rw [if_pos hevent] at hindicator
      rw [if_pos hevent]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          ((su2FineOuterData G g hg K).normalizedMass
            source)
          _ _ hindicator)
        (Q'.mul_one_eqv _)
    · rw [if_neg hevent] at hindicator
      rw [if_neg hevent]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          ((su2FineOuterData G g hg K).normalizedMass
            source)
          _ _ hindicator)
        (Q'.mul_zero_eqv _)

private theorem exponentGramEntry_mass_congr
    (half : Nat) (states : List OuterSlabLabelling)
    (leftMass rightMass : OuterSlabLabelling → Q')
    (coordinate : ExponentGramCoordinate)
    (hmass :
      ∀ state, state ∈ states →
        leftMass state ≈ rightMass state) :
    exponentGramEntry half states leftMass coordinate ≈
      exponentGramEntry half states rightMass coordinate := by
  unfold exponentGramEntry reflectedLawBilinear
  apply listQSum_congr_on
  intro state hstate
  exact Q'.mul_eqv_congr_left _ _ _
    (hmass state hstate)

/-- The contract's cutoff-one Gram recovers the existing physical blocked
entry.  This proves that the contract has the correct anchor interface
without asserting that such a contract has been constructed. -/
theorem contractBlockedExponentGramEntry_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalBlockContract
        G g hg candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    contractBlockedExponentGramEntry contract 1 coordinate ≈
      blockedExponentGramEntry
        G g hg candidate hcandidate coordinate := by
  unfold contractBlockedExponentGramEntry
    blockedExponentGramEntry
  apply exponentGramEntry_mass_congr
  intro target _
  exact contract.cutoff_one_mass target

/-! ## 4. The physically pinned source-indexed stochastic contract -/

/-- **OPEN PHYSICAL INTERFACE/FENCE (not constructed here).** A
K-parametric source-indexed Markov kernel on the actual fine and coarse
corrected-slab carriers.

Unlike `SU2OuterPhysicalBlockContract`, this structure has the same
source/target semantics as the existing cutoff-one SU(2) recoupling kernel.
Its cutoff-one field recovers every entry of that kernel, not merely its
blocked marginal.  No value is constructed here.

This is still not an outer-cutoff convergence theorem.  Pulling back a target
event through a Markov kernel produces a rational observable in `[0,1]`, not
a Boolean event.  A corrected-slab bounded-observable tail theorem is the
remaining analytic input. -/
structure SU2OuterPhysicalMarkovContract
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  kernelEntry :
    Nat → OuterSlabLabelling → OuterSlabLabelling → Q'
  nonnegative :
    ∀ K source target,
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
        target ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        (0 : Q') ≤ kernelEntry K source target
  row_total :
    ∀ K source,
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
        listQSum
            (kernelEntry K source)
            (su2CoarseOuterData
              G candidate hcandidate K).physicalLabellings ≈
          1
  cutoff_stable :
    ∀ K L source target,
      K ≤ L →
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        kernelEntry K source target ≈
          kernelEntry L source target
  /-- **OPEN LOSSLESS-SUPPORT INPUT.** Enlarging the outer cutoff from
  `K` to `L` creates no transition from an old fine source into a genuinely
  new coarse target.  This is the source-indexed form of the lossless
  induced `4K` carrier property that a physical recoupling constructor must
  prove. -/
  old_source_no_new_target :
    ∀ K L source target,
      K ≤ L →
      source ∈
          (su2FineOuterData G g hg K).physicalLabellings →
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate L).physicalLabellings →
      target ∉
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        kernelEntry L source target ≈ 0
  cutoff_one_entry :
    ∀ source target,
      kernelEntry 1 source target ≈
        let S :=
          G.candidateScalePair g hg candidate hcandidate
        let kernel := physicalKernel S rfl hcandidate
        kernel.kernel source target

private theorem outer_range_nodup :
    ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨outer_range_nodup N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

private theorem outer_slabPhysicalFaceEdges_nodup
    (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact outer_range_nodup _

private theorem outer_listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ states : List A,
      (∀ state, state ∈ states →
        lower state ≤ upper state) →
      listQSum lower states ≤
        listQSum upper states
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (outer_listQSum_mono_on lower upper tail
          (fun state hstate =>
            hpointwise state
              (List.mem_cons_of_mem head hstate)))

/-- The physical blocked marginal is defined, not assumed: sum the
source-indexed Markov kernel against the exact normalized fine law. -/
def stochasticContractBlockedMass
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat) (target : OuterSlabLabelling) : Q' :=
  listQSum
    (fun source =>
      (su2FineOuterData G g hg K).normalizedMass source *
        contract.kernelEntry K source target)
    (su2FineOuterData G g hg K).physicalLabellings

/-- The defined stochastic blocked marginal is nonnegative on the supported
coarse carrier. -/
theorem stochasticContractBlockedMass_nonnegative
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat) {target : OuterSlabLabelling}
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    (0 : Q') ≤
      stochasticContractBlockedMass contract K target := by
  unfold stochasticContractBlockedMass
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    ((su2FineOuterData G g hg K).normalizedMass_nonnegative
      source)
    (contract.nonnegative K source target
      hsource
      htarget)

/-- Every stochastic blocked marginal has total mass one. -/
theorem stochasticContractBlockedMass_total
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat) :
    listQSum
        (stochasticContractBlockedMass contract K)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      1 := by
  let fine := su2FineOuterData G g hg K
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            fine.normalizedMass source *
              contract.kernelEntry K source target)
          coarse.physicalLabellings)
      fine.physicalLabellings) _ ?_ ?_
  · unfold stochasticContractBlockedMass
    exact listQSum_swap
      (fun source target =>
        fine.normalizedMass source *
          contract.kernelEntry K source target)
      fine.physicalLabellings coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun source => fine.normalizedMass source * 1)
      fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (fine.normalizedMass source)
        (contract.kernelEntry K source)
        coarse.physicalLabellings)
      (Q'.mul_eqv_congr_left
        (fine.normalizedMass source) _ _
        (contract.row_total K source hsource))
  · refine Q'.eqv_trans _ _ _
      (listQSum_congr_on
        (fun source => fine.normalizedMass source * 1)
        fine.normalizedMass fine.physicalLabellings
        (fun source _ => Q'.mul_one_eqv _)) ?_
    exact fine.normalizedMass_total

/-- Exact cutoff-one recovery of the existing physical blocked marginal. -/
theorem stochasticContractBlockedMass_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (target : OuterSlabLabelling) :
    stochasticContractBlockedMass contract 1 target ≈
      let S :=
        G.candidateScalePair g hg candidate hcandidate
      let kernel := physicalKernel S rfl hcandidate
      kernel.blockedMass target := by
  unfold stochasticContractBlockedMass
    SlabScalePair.FiniteSlabKernel.blockedMass
  apply listQSum_congr_on
  intro source _
  exact Q'.mul_eqv_congr_left
    ((su2FineOuterData G g hg 1).normalizedMass source)
    _ _ (contract.cutoff_one_entry source target)

/-- Exponent-Gram entry of the physically source-indexed stochastic
contract. -/
def stochasticContractBlockedExponentGramEntry
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  exponentGramEntry G.coarseHalf
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings
    (stochasticContractBlockedMass contract K)
    coordinate

/-- Exact cutoff-one recovery of every existing physical blocked
exponent-Gram entry. -/
theorem stochasticContractBlockedExponentGramEntry_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramEntry
        contract 1 coordinate ≈
      blockedExponentGramEntry
        G g hg candidate hcandidate coordinate := by
  unfold stochasticContractBlockedExponentGramEntry
    blockedExponentGramEntry
  apply exponentGramEntry_mass_congr
  intro target _
  exact stochasticContractBlockedMass_one contract target

private theorem mul_swap_first_two
    (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right
      (a * b) (b * a) c
      (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-- Pull a rational coarse observable backward through one row of the
source-indexed physical Markov contract.  Unlike the Boolean event wrapper
below, this carrier also covers continuous finite-cutoff backward messages. -/
def stochasticContractPulledObservable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (observable : OuterSlabLabelling → Q')
    (source : OuterSlabLabelling) : Q' :=
  listQSum
    (fun target =>
      observable target *
        contract.kernelEntry K source target)
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings

/-- A nonnegative coarse observable has a nonnegative backward message on
every supported source. -/
theorem stochasticContractPulledObservable_nonnegative
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (observable : OuterSlabLabelling → Q')
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (hobservable :
      ∀ target,
        target ∈
            (su2CoarseOuterData
              G candidate hcandidate K).physicalLabellings →
          (0 : Q') ≤ observable target) :
    (0 : Q') ≤
      stochasticContractPulledObservable
        contract K observable source := by
  unfold stochasticContractPulledObservable
  apply listQSum_nonnegative_on
  intro target htarget
  exact Q'.mul_nonneg _ _
    (hobservable target htarget)
    (contract.nonnegative K source target
      hsource htarget)

/-- A coarse observable bounded above by one has a backward message bounded
above by one on every supported source. -/
theorem stochasticContractPulledObservable_le_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (observable : OuterSlabLabelling → Q')
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (hobservable :
      ∀ target,
        target ∈
            (su2CoarseOuterData
              G candidate hcandidate K).physicalLabellings →
          observable target ≤ (1 : Q')) :
    stochasticContractPulledObservable
        contract K observable source ≤
      (1 : Q') := by
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  have hsum :
      listQSum
          (fun target =>
            observable target *
              contract.kernelEntry K source target)
          coarse.physicalLabellings ≤
        listQSum
          (contract.kernelEntry K source)
          coarse.physicalLabellings := by
    apply outer_listQSum_mono_on
    intro target htarget
    refine Q'.le_trans' _
      (1 * contract.kernelEntry K source target) _
      (Q'.mul_le_mul_of_nonneg_right
        (observable target) 1
        (contract.kernelEntry K source target)
        (hobservable target htarget)
        (contract.nonnegative K source target
          hsource htarget)) ?_
    exact Q'.le_of_eqv
      (Q'.one_mul_eqv
        (contract.kernelEntry K source target))
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (contract.row_total K source hsource))

/-- Conditional probability, given a fine source, that the stochastic
coarse target lies in one exponent-Gram event.  This is the true Markov
pullback observable. -/
def stochasticContractExponentEventProbability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    (source : OuterSlabLabelling) : Q' :=
  listQSum
    (fun target =>
      if su2ExponentGramEvent
          G.coarseHalf coordinate target then
        contract.kernelEntry K source target
      else 0)
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings

/-- The pulled-back Markov event probability is nonnegative on supported
fine sources. -/
theorem stochasticContractExponentEventProbability_nonnegative
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    (0 : Q') ≤
      stochasticContractExponentEventProbability
        contract K coordinate source := by
  unfold stochasticContractExponentEventProbability
  apply listQSum_nonnegative_on
  intro target htarget
  by_cases hevent :
      su2ExponentGramEvent
        G.coarseHalf coordinate target = true
  · rw [if_pos hevent]
    exact contract.nonnegative K source target hsource
      htarget
  · rw [if_neg hevent]
    exact Q'.le_refl' 0

/-- The pulled-back Markov event probability is at most one on supported
fine sources. -/
theorem stochasticContractExponentEventProbability_le_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    stochasticContractExponentEventProbability
        contract K coordinate source ≤
      (1 : Q') := by
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  have hmask :
      listQSum
          (fun target =>
            if su2ExponentGramEvent
                G.coarseHalf coordinate target then
              contract.kernelEntry K source target
            else 0)
          coarse.physicalLabellings ≤
        listQSum
          (contract.kernelEntry K source)
          coarse.physicalLabellings :=
    listQSum_mask_le_total_on_local
      (contract.kernelEntry K source)
      (su2ExponentGramEvent G.coarseHalf coordinate)
      coarse.physicalLabellings
      (fun target htarget =>
        contract.nonnegative K source target hsource
          htarget)
  exact Q'.le_trans' _ _ _ hmask
    (Q'.le_of_eqv
      (contract.row_total K source hsource))

/-- The pulled-back exponent event is exactly cutoff-stable on every old
fine source.  The proof partitions the `4L` target carrier into the old
`4K` sector and its complement.  Pointwise kernel stability identifies the
old sector, while `old_source_no_new_target` kills the new sector. -/
theorem stochasticContractExponentEventProbability_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    (coordinate : ExponentGramCoordinate)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    stochasticContractExponentEventProbability
        contract K coordinate source ≈
      stochasticContractExponentEventProbability
        contract L coordinate source := by
  let edges :=
    slabPhysicalFaceEdges
      (centralExtent G.coarseHalf)
  let smallSupport :=
    boundedEdgeLabellings (4 * K) edges
  let largeSupport :=
    boundedEdgeLabellings (4 * L) edges
  let oldTest :=
    labelWithinB (4 * K) edges
  let event :=
    su2ExponentGramEvent G.coarseHalf coordinate
  let weightK : OuterSlabLabelling → Q' :=
    fun target =>
      if event target then
        contract.kernelEntry K source target
      else 0
  let weightL : OuterSlabLabelling → Q' :=
    fun target =>
      if event target then
        contract.kernelEntry L source target
      else 0
  change
    listQSum weightK smallSupport ≈
      listQSum weightL largeSupport
  have h4KL : 4 * K ≤ 4 * L := by omega
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff
      h4KL _
      (outer_slabPhysicalFaceEdges_nodup
        (centralExtent G.coarseHalf))
  have hold :
      listQSum weightL
          (largeSupport.filter oldTest) ≈
        listQSum weightK smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro target htarget
    dsimp only [weightK, weightL]
    by_cases hevent : event target = true
    · rw [if_pos hevent, if_pos hevent]
      exact Q'.eqv_symm
        (contract.cutoff_stable
          K L source target hKL hsource htarget)
    · rw [if_neg hevent, if_neg hevent]
      exact Q'.eqv_refl 0
  have hnew :
      listQSum weightL
          (largeSupport.filter
            (fun target => !(oldTest target))) ≈
        0 := by
    refine Q'.eqv_trans _
      (listQSum
        (fun _ : OuterSlabLabelling => (0 : Q'))
        (largeSupport.filter
          (fun target => !(oldTest target)))) _ ?_ ?_
    · apply listQSum_congr_on
      intro target htarget
      have htargetParts := List.mem_filter.mp htarget
      have htargetLarge : target ∈ largeSupport :=
        htargetParts.1
      have htargetNotSmall : target ∉ smallSupport := by
        intro htargetSmall
        have htargetOldFiltered :
            target ∈ largeSupport.filter oldTest := by
          rw [hfilter]
          exact htargetSmall
        have holdTrue :=
          (List.mem_filter.mp htargetOldFiltered).2
        have hnewTrue := htargetParts.2
        rw [holdTrue] at hnewTrue
        cases hnewTrue
      have hzero :
          contract.kernelEntry L source target ≈ 0 := by
        apply contract.old_source_no_new_target
          K L source target hKL hsource
        · exact htargetLarge
        · exact htargetNotSmall
      dsimp only [weightL]
      by_cases hevent : event target = true
      · rw [if_pos hevent]
        exact hzero
      · rw [if_neg hevent]
        exact Q'.eqv_refl 0
    · exact listQSum_zero _
  have hsplit :
      listQSum weightL largeSupport ≈
        listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun target => !(oldTest target))) :=
    listQSum_filter_partition weightL oldTest largeSupport
  have hparts :
      listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun target => !(oldTest target))) ≈
        listQSum weightK smallSupport := by
    refine Q'.eqv_trans _
      (listQSum weightK smallSupport + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr' hold hnew
    · exact Q'.eqv_of_eq
        (Q'.add_zero' (listQSum weightK smallSupport))
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hsplit hparts)

/-- Every fixed rational coarse observable has an exactly cutoff-stable
backward message on old sources.  No positivity or boundedness assumption is
needed for stability itself; those order properties are supplied separately
by `stochasticContractPulledObservable_nonnegative` and
`stochasticContractPulledObservable_le_one`. -/
theorem stochasticContractPulledObservable_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    (observable : OuterSlabLabelling → Q')
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    stochasticContractPulledObservable
        contract K observable source ≈
      stochasticContractPulledObservable
        contract L observable source := by
  let edges :=
    slabPhysicalFaceEdges
      (centralExtent G.coarseHalf)
  let smallSupport :=
    boundedEdgeLabellings (4 * K) edges
  let largeSupport :=
    boundedEdgeLabellings (4 * L) edges
  let oldTest :=
    labelWithinB (4 * K) edges
  let weightK : OuterSlabLabelling → Q' :=
    fun target =>
      observable target *
        contract.kernelEntry K source target
  let weightL : OuterSlabLabelling → Q' :=
    fun target =>
      observable target *
        contract.kernelEntry L source target
  change
    listQSum weightK smallSupport ≈
      listQSum weightL largeSupport
  have h4KL : 4 * K ≤ 4 * L := by omega
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff
      h4KL _
      (outer_slabPhysicalFaceEdges_nodup
        (centralExtent G.coarseHalf))
  have hold :
      listQSum weightL
          (largeSupport.filter oldTest) ≈
        listQSum weightK smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro target htarget
    dsimp only [weightK, weightL]
    exact Q'.mul_eqv_congr_left
      (observable target) _ _
      (Q'.eqv_symm
        (contract.cutoff_stable
          K L source target hKL hsource htarget))
  have hnew :
      listQSum weightL
          (largeSupport.filter
            (fun target => !(oldTest target))) ≈
        0 := by
    refine Q'.eqv_trans _
      (listQSum
        (fun _ : OuterSlabLabelling => (0 : Q'))
        (largeSupport.filter
          (fun target => !(oldTest target)))) _ ?_ ?_
    · apply listQSum_congr_on
      intro target htarget
      have htargetParts := List.mem_filter.mp htarget
      have htargetLarge : target ∈ largeSupport :=
        htargetParts.1
      have htargetNotSmall : target ∉ smallSupport := by
        intro htargetSmall
        have htargetOldFiltered :
            target ∈ largeSupport.filter oldTest := by
          rw [hfilter]
          exact htargetSmall
        have holdTrue :=
          (List.mem_filter.mp htargetOldFiltered).2
        have hnewTrue := htargetParts.2
        rw [holdTrue] at hnewTrue
        cases hnewTrue
      have hzero :
          contract.kernelEntry L source target ≈ 0 := by
        apply contract.old_source_no_new_target
          K L source target hKL hsource
        · exact htargetLarge
        · exact htargetNotSmall
      dsimp only [weightL]
      exact Q'.eqv_trans _
        (observable target * 0) _
        (Q'.mul_eqv_congr_left
          (observable target) _ _ hzero)
        (Q'.mul_zero_eqv (observable target))
    · exact listQSum_zero _
  have hsplit :
      listQSum weightL largeSupport ≈
        listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun target => !(oldTest target))) :=
    listQSum_filter_partition weightL oldTest largeSupport
  have hparts :
      listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun target => !(oldTest target))) ≈
        listQSum weightK smallSupport := by
    refine Q'.eqv_trans _
      (listQSum weightK smallSupport + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr' hold hnew
    · exact Q'.eqv_of_eq
        (Q'.add_zero' (listQSum weightK smallSupport))
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hsplit hparts)

/-- Expectation under the stochastic blocked marginal equals expectation of
the sourcewise Markov pullback under the normalized fine law. -/
theorem stochasticContractBlockedObservableExpectation_eq_pullback
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (observable : OuterSlabLabelling → Q') :
    listQSum
        (fun target =>
          observable target *
            stochasticContractBlockedMass contract K target)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      listQSum
        (fun source =>
          (su2FineOuterData G g hg K).normalizedMass source *
            listQSum
              (fun target =>
                observable target *
                  contract.kernelEntry K source target)
              (su2CoarseOuterData
                G candidate hcandidate K).physicalLabellings)
        (su2FineOuterData
          G g hg K).physicalLabellings := by
  let fine := su2FineOuterData G g hg K
  let coarse :=
    su2CoarseOuterData G candidate hcandidate K
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            observable target *
              (fine.normalizedMass source *
                contract.kernelEntry K source target))
          fine.physicalLabellings)
      coarse.physicalLabellings) _ ?_ ?_
  · unfold stochasticContractBlockedMass
    apply listQSum_congr_on
    intro target _
    exact Q'.eqv_symm
      (listQSum_mul_left
        (observable target)
        (fun source =>
          fine.normalizedMass source *
            contract.kernelEntry K source target)
        fine.physicalLabellings)
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            observable target *
              (fine.normalizedMass source *
                contract.kernelEntry K source target))
          coarse.physicalLabellings)
      fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        observable target *
          (fine.normalizedMass source *
            contract.kernelEntry K source target))
      fine.physicalLabellings coarse.physicalLabellings
  · apply listQSum_congr_on
    intro source _
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          fine.normalizedMass source *
            (observable target *
              contract.kernelEntry K source target))
        coarse.physicalLabellings) _ ?_ ?_
    · apply listQSum_congr_on
      intro target _
      exact mul_swap_first_two
        (observable target)
        (fine.normalizedMass source)
        (contract.kernelEntry K source target)
    · exact listQSum_mul_left
        (fine.normalizedMass source)
        (fun target =>
          observable target *
            contract.kernelEntry K source target)
        coarse.physicalLabellings

private theorem stochasticExponentObservable_eq_eventProbability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate)
    (source : OuterSlabLabelling) :
    listQSum
        (fun target =>
          (exponentCoefficient G.coarseHalf
              coordinate.leftExponent
              (centralLowerRestriction
                G.coarseHalf target) *
            exponentCoefficient G.coarseHalf
              coordinate.rightExponent
              (centralReflectedUpperRestriction
                G.coarseHalf target)) *
            contract.kernelEntry K source target)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      stochasticContractExponentEventProbability
        contract K coordinate source := by
  unfold stochasticContractExponentEventProbability
  apply listQSum_congr_on
  intro target _
  have hindicator :=
    exponentCoefficient_product_eq_plainEventIndicator
      G.coarseHalf coordinate target
  by_cases hevent :
      su2ExponentGramEvent G.coarseHalf coordinate target
  · rw [if_pos hevent] at hindicator
    rw [if_pos hevent]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _
        (contract.kernelEntry K source target)
        hindicator)
      (Q'.one_mul_eqv _)
  · rw [if_neg hevent] at hindicator
    rw [if_neg hevent]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _
        (contract.kernelEntry K source target)
        hindicator)
      (Q'.zero_mul_eqv _)

/-- The honest stochastic transport identity.  A blocked exponent-Gram
coordinate is the fine-law expectation of a `[0,1]`-valued conditional
kernel probability.  Consequently Boolean-event tails alone do not close
the stochastic SU(2) transport. -/
theorem
    stochasticContractBlockedExponentGramEntry_eq_fineBoundedExpectation
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramEntry
        contract K coordinate ≈
      listQSum
        (fun source =>
          (su2FineOuterData G g hg K).normalizedMass source *
            stochasticContractExponentEventProbability
              contract K coordinate source)
        (su2FineOuterData
          G g hg K).physicalLabellings := by
  let observable : OuterSlabLabelling → Q' :=
    fun target =>
      exponentCoefficient G.coarseHalf
          coordinate.leftExponent
          (centralLowerRestriction G.coarseHalf target) *
        exponentCoefficient G.coarseHalf
          coordinate.rightExponent
          (centralReflectedUpperRestriction
            G.coarseHalf target)
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        observable target *
          stochasticContractBlockedMass contract K target)
      (su2CoarseOuterData
        G candidate hcandidate K).physicalLabellings) _ ?_ ?_
  · unfold stochasticContractBlockedExponentGramEntry
      exponentGramEntry reflectedLawBilinear observable
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (su2FineOuterData G g hg K).normalizedMass source *
          listQSum
            (fun target =>
              observable target *
                contract.kernelEntry K source target)
            (su2CoarseOuterData
              G candidate hcandidate K).physicalLabellings)
      (su2FineOuterData
        G g hg K).physicalLabellings) _ ?_ ?_
  · exact
      stochasticContractBlockedObservableExpectation_eq_pullback
        contract K observable
  · apply listQSum_congr_on
    intro source _
    exact Q'.mul_eqv_congr_left
      ((su2FineOuterData G g hg K).normalizedMass source)
      _ _
      (stochasticExponentObservable_eq_eventProbability
        contract K coordinate source)

#print axioms su2FineOuterData_one
#print axioms su2CoarseOuterData_one
#print axioms su2CoarseOuterExponentGramEntry_one
#print axioms su2FineOuterEventProbability_nonnegative
#print axioms su2FineOuterEventProbability_le_one
#print axioms su2FineOuterEventProbability_congr_on
#print axioms su2CoarseOuterEventProbability_nonnegative
#print axioms su2CoarseOuterEventProbability_le_one
#print axioms su2CoarseOuterExponentGramEntry_eq_eventProbability
#print axioms SU2OuterPhysicalBlockContract
#print axioms SU2OuterPhysicalMarkovContract
#print axioms contractBlockedMass_total
#print axioms contractCutoffOneExpectation_eq_physicalKernel
#print axioms contractBlockedExponentPair_cutoff_stable
#print axioms contractBlockedExponentGramEvent_cutoff_stable
#print axioms contractBlockedExponentGramEventProbability_align
#print axioms contractBlockedExponentGramEntry_eq_fineEventProbability
#print axioms contractBlockedExponentGramEntry_one
#print axioms stochasticContractBlockedMass_nonnegative
#print axioms stochasticContractBlockedMass_total
#print axioms stochasticContractBlockedMass_one
#print axioms stochasticContractBlockedExponentGramEntry_one
#print axioms stochasticContractPulledObservable_nonnegative
#print axioms stochasticContractPulledObservable_le_one
#print axioms stochasticContractExponentEventProbability_nonnegative
#print axioms stochasticContractExponentEventProbability_le_one
#print axioms
  stochasticContractExponentEventProbability_cutoff_stable
#print axioms
  stochasticContractPulledObservable_cutoff_stable
#print axioms
  stochasticContractBlockedObservableExpectation_eq_pullback
#print axioms
  stochasticContractBlockedExponentGramEntry_eq_fineBoundedExpectation

end YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
