/-
# Marked-pair difference form of the cutoff-one centered coupling score

The symmetric occupied-face recoding leaves one centered kernel-row response
at each marked source.  This module expands that centering exactly over a
second fine physical source:

  Z_actual * F(x) - sum_y a(y) * F(y)
    = sum_y a(y) * (F(x) - F(y)).

Consequently the complete cutoff-one centered score-event moment is a finite
sum over a marked occupied source-face `(x,p)` and an actual source `y`, with
term

  markedMarginMass(x,p) * (actualMass(y) * (F(x) - F(y))).

This is the first exact carrier on which a two-source switching or
antisymmetrization argument can act while retaining the occupied insertion
anchor.  No switch invariance is asserted here: the marked mass is at
coupling one, whereas the second-source mass is at the actual coupling.

The result is finite exact rational algebra.  It proves no local covariance
estimate, cutoff- or volume-uniform bound, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: finite sums and rational setoid algebra only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginMarkedPairDifference

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum left items - listQSum right items ≈
      listQSum (fun item => left item - right item) items := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (listQSum left items +
        listQSum (fun item => -(right item)) items) _
      (listQSum_add left (fun item => -(right item)) items)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_neg_local right items)))

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 1. A volume-independent bound on one symmetric face share -/

/-- Every symmetric occupied-face share is nonnegative when the heat nome
is nonnegative. -/
theorem slabCutoffOneSymmetricMarginShare_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (physical : EdgeLabelling) (faces : List Nat) :
    (0 : Q') ≤
      slabCutoffOneSymmetricMarginShare w physical faces := by
  unfold slabCutoffOneSymmetricMarginShare
  cases hoccupied : slabCutoffOneOccupiedFaces physical faces with
  | nil =>
      change (0 : Q') ≤ 0
      exact Q'.le_refl' 0
  | cons first rest =>
      change (0 : Q') ≤
        Q'.divPos
          (geomSum w (3 * (rest.length + 1)))
          (Q'.ofNat (rest.length + 1))
          (Q'.ofNat_succ_pos rest.length)
      unfold Q'.divPos
      exact Q'.mul_nonneg _ _
        (geomSum_nonneg hw0 (3 * (rest.length + 1)))
        (Q'.le_of_lt
          (Q'.recipPos_pos
            (Q'.ofNat (rest.length + 1))
            (Q'.ofNat_succ_pos rest.length)))

/-- **Uniform local coefficient bound.**  On `0 ≤ w ≤ 1`, every symmetric
occupied-face share is at most three, independently of the source, face
count, and slab volume.  It is `geomSum(w,3n)/n ≤ 3n/n = 3` in the nonempty
branch. -/
theorem slabCutoffOneSymmetricMarginShare_le_three
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (physical : EdgeLabelling) (faces : List Nat) :
    slabCutoffOneSymmetricMarginShare w physical faces ≤ (3 : Q') := by
  unfold slabCutoffOneSymmetricMarginShare
  cases hoccupied : slabCutoffOneOccupiedFaces physical faces with
  | nil =>
      change (0 : Q') ≤ 3
      decide
  | cons first rest =>
      change
        Q'.divPos
          (geomSum w (3 * (rest.length + 1)))
          (Q'.ofNat (rest.length + 1))
          (Q'.ofNat_succ_pos rest.length) ≤ (3 : Q')
      apply Q'.divPos_le_of_le_mul
      have hgeom := geomSum_le hw0 hw1 (3 * (rest.length + 1))
      exact Q'.le_trans' _ _ _ hgeom
        (Q'.le_of_eqv (by
          simpa using
            (ofNat_mul_eqv 3 (rest.length + 1))))

/-! ## 2. Center one kernel row against an explicit second source -/

/-- One centered kernel-row response is exactly its pairwise difference
against all actual fine-source masses. -/
theorem fineCouplingPhysicalCenteredEventResponse_eqv_sourceDifferenceSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (source : EdgeLabelling) :
    fineCouplingPhysicalCenteredEventResponse K event source ≈
      listQSum
        (fun other =>
          S.fine.physicalTerm other *
            (fineCouplingKernelOutputEventMass K source event -
              fineCouplingKernelOutputEventMass K other event))
        S.fine.physicalLabellings := by
  let sourceEvent := fineCouplingKernelOutputEventMass K source event
  let actualEvent := fun other =>
    S.fine.physicalTerm other *
      fineCouplingKernelOutputEventMass K other event
  let constantEvent := fun other =>
    S.fine.physicalTerm other * sourceEvent
  refine Q'.eqv_trans _
    (listQSum S.fine.physicalTerm S.fine.physicalLabellings * sourceEvent -
      listQSum actualEvent S.fine.physicalLabellings) _ ?_ ?_
  · unfold fineCouplingPhysicalCenteredEventResponse
      fineCouplingPhysicalActualKernelEventRawMass
      fineCouplingPhysicalSourceKernelEventMoment
      SlabPhysicalData.physicalPartition
      slabParametricKPhysicalPartition
      SlabPhysicalData.physicalTerm
      SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum constantEvent S.fine.physicalLabellings -
      listQSum actualEvent S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _
      (-(listQSum actualEvent S.fine.physicalLabellings))
      (Q'.eqv_symm
        (listQSum_mul_right S.fine.physicalTerm sourceEvent
          S.fine.physicalLabellings))
  refine Q'.eqv_trans _
    (listQSum
      (fun other => constantEvent other - actualEvent other)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_sub_local constantEvent actualEvent
      S.fine.physicalLabellings
  apply listQSum_congr
  intro other
  exact Q'.eqv_symm
    (mul_sub_expand_local (S.fine.physicalTerm other)
      sourceEvent (fineCouplingKernelOutputEventMass K other event))

/-! ## 3. The marked occupied-face source-pair carrier -/

/-- A symmetric occupied source-face entry paired with a second fine
physical source. -/
abbrev FineCouplingPhysicalMarkedSourcePair :=
  FineCouplingPhysicalSourceFaceContribution × EdgeLabelling

/-- Cartesian carrier of marked occupied source-faces and actual fine
physical sources. -/
def fineCouplingPhysicalSymmetricMarkedSourcePairCarrier
    (S : SlabScalePair) :
    List FineCouplingPhysicalMarkedSourcePair :=
  cartesian
    (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier S)
    S.fine.physicalLabellings

/-- The difference between the two kernel-row event masses in a marked
source pair. -/
def fineCouplingPhysicalMarkedSourcePairEventDifference
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalMarkedSourcePair) : Q' :=
  fineCouplingKernelOutputEventMass K pair.1.1 event -
    fineCouplingKernelOutputEventMass K pair.2 event

/-- One marked-pair term: symmetric occupied-face margin mass on the first
source, actual mass on the second source, and their kernel-row event
difference. -/
def fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalMarkedSourcePair) : Q' :=
  fineCouplingPhysicalSourceFaceMarginRawMass S pair.1 *
    (S.fine.physicalTerm pair.2 *
      fineCouplingPhysicalMarkedSourcePairEventDifference K event pair)

/-- Sum of all symmetric marked-pair difference terms. -/
def fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm K event)
    (fineCouplingPhysicalSymmetricMarkedSourcePairCarrier S)

/-- Membership in the marked-pair carrier certifies an actual occupied
insertion face and physical membership of both sources. -/
theorem fineCouplingPhysicalSymmetricMarkedSourcePairCarrier_mem
    (S : SlabScalePair) (pair : FineCouplingPhysicalMarkedSourcePair)
    (hpair : pair ∈
      fineCouplingPhysicalSymmetricMarkedSourcePairCarrier S) :
    pair.1.1 ∈ S.fine.physicalLabellings ∧
      pair.1.1 pair.1.2.1 = 1 ∧
      pair.2 ∈ S.fine.physicalLabellings := by
  unfold fineCouplingPhysicalSymmetricMarkedSourcePairCarrier at hpair
  have hparts := (mem_cartesian_iff _ _ pair).mp hpair
  exact ⟨
    (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier_mem
      S pair.1 hparts.1).1,
    (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier_mem
      S pair.1 hparts.1).2,
    hparts.2⟩

/-! ## 4. Flatten the centered insertion onto marked source pairs -/

/-- One symmetric occupied-face insertion is exactly the sum of its marked
pair differences against all actual fine sources. -/
theorem fineCouplingPhysicalSymmetricSourceFaceInsertion_eqv_pairDifferenceSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (marked : FineCouplingPhysicalSourceFaceContribution) :
    fineCouplingPhysicalSourceFaceCenteredEventInsertion K event marked ≈
      listQSum
        (fun other =>
          fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm
            K event (marked, other))
        S.fine.physicalLabellings := by
  refine Q'.eqv_trans _
    (fineCouplingPhysicalSourceFaceMarginRawMass S marked *
      fineCouplingPhysicalCenteredEventResponse K event marked.1) _ ?_ ?_
  · exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (fineCouplingPhysicalSourceFaceMarginRawMass S marked *
      listQSum
        (fun other =>
          S.fine.physicalTerm other *
            (fineCouplingKernelOutputEventMass K marked.1 event -
              fineCouplingKernelOutputEventMass K other event))
        S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (fineCouplingPhysicalCenteredEventResponse_eqv_sourceDifferenceSum
        K event marked.1)
  · exact Q'.eqv_symm
      (listQSum_mul_left
        (fineCouplingPhysicalSourceFaceMarginRawMass S marked)
        (fun other =>
          S.fine.physicalTerm other *
            (fineCouplingKernelOutputEventMass K marked.1 event -
              fineCouplingKernelOutputEventMass K other event))
        S.fine.physicalLabellings)

/-- The complete symmetric centered insertion sum is exactly the marked
two-source difference sum. -/
theorem fineCouplingPhysicalCenteredMarginSymmetricInsertionSum_eqv_markedPairDifference
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalCenteredMarginSymmetricInsertionSum K event ≈
      fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum K event := by
  unfold fineCouplingPhysicalCenteredMarginSymmetricInsertionSum
    fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum
    fineCouplingPhysicalSymmetricMarkedSourcePairCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun marked =>
        listQSum
          (fun other =>
            fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm
              K event (marked, other))
          S.fine.physicalLabellings)
      (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier S)) _ ?_ ?_
  · apply listQSum_congr
    intro marked
    exact
      fineCouplingPhysicalSymmetricSourceFaceInsertion_eqv_pairDifferenceSum
        K event marked
  · exact Q'.eqv_symm
      (listQSum_cartesian_eq_nested_local
        (fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm K event)
        (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier S)
        S.fine.physicalLabellings)

/-- At cutoff one, the original centered score-event moment is exactly a
marked occupied-face two-source difference sum. -/
theorem fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_markedPairDifference
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event ≈
      fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum K event := by
  exact Q'.eqv_trans _ _ _
    (fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_symmetric
      hfineCutoff K event)
    (fineCouplingPhysicalCenteredMarginSymmetricInsertionSum_eqv_markedPairDifference
      K event)

#print axioms slabCutoffOneSymmetricMarginShare_nonnegative
#print axioms slabCutoffOneSymmetricMarginShare_le_three
#print axioms fineCouplingPhysicalCenteredEventResponse_eqv_sourceDifferenceSum
#print axioms FineCouplingPhysicalMarkedSourcePair
#print axioms fineCouplingPhysicalSymmetricMarkedSourcePairCarrier
#print axioms fineCouplingPhysicalMarkedSourcePairEventDifference
#print axioms fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceTerm
#print axioms fineCouplingPhysicalSymmetricMarkedSourcePairDifferenceSum
#print axioms fineCouplingPhysicalSymmetricMarkedSourcePairCarrier_mem
#print axioms fineCouplingPhysicalSymmetricSourceFaceInsertion_eqv_pairDifferenceSum
#print axioms fineCouplingPhysicalCenteredMarginSymmetricInsertionSum_eqv_markedPairDifference
#print axioms fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_markedPairDifference

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginMarkedPairDifference
