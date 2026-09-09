/-
# Local face-insertion expansion of the centered coupling score

The one-replica reduction leaves centered moments of the global geometric
coupling quotient.  This module telescopes that quotient over the literal
ordered slab-face list.

For every fine physical source it constructs a finite list of face-labelled
contributions.  Their coefficients sum exactly to the global geometric
quotient.  Flattening these lists gives a source--face carrier whose raw mass
sums to the fine coupling-margin partition.  Most importantly, a centered
score-event moment is exactly the sum over that carrier of

  localFaceMarginMass *
    (Z_actual * rowEventMass(source) - actualEventRawMass).

Thus the analytic frontier is a sum of local action insertions against a
centered event response, with the physical face identifier retained for a
future distance decomposition.  No estimate is proved here.

In particular, this module does not establish cutoff- or volume-uniform
control, all-cutoff persistence, a continuum measure, OS/GNS
reconstruction, a Hamiltonian gap, or the Yang--Mills mass gap.

Constructive contract: structural recursion, exact finite sums, and rational
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion

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
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

private theorem sub_mul_expand_local (left right factor : Q') :
    (left - right) * factor ≈
      left * factor - right * factor := by
  refine Q'.eqv_trans _
    (factor * (left - right)) _
    (Q'.mul_comm_eqv (left - right) factor) ?_
  refine Q'.eqv_trans _
    (factor * left - factor * right) _
    (mul_sub_expand_local factor left right) ?_
  exact sub_eqv_both_local
    (Q'.mul_comm_eqv factor left)
    (Q'.mul_comm_eqv factor right)

private theorem mul_swap_tail_local (first middle last : Q') :
    (first * middle) * last ≈
      (first * last) * middle := by
  refine Q'.eqv_trans _
    (first * (middle * last)) _
    (Q'.mul_assoc_eqv first middle last) ?_
  refine Q'.eqv_trans _
    (first * (last * middle)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left first _ _
      (Q'.mul_comm_eqv middle last)
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv first last middle)

private theorem mul_swap_inner_local (first middle last : Q') :
    first * (middle * last) ≈
      (first * last) * middle := by
  refine Q'.eqv_trans _
    (first * (last * middle)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left first _ _
      (Q'.mul_comm_eqv middle last)
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv first last middle)

/-! ## 1. Telescope a geometric quotient over additive exponents -/

/-- Additive decomposition of the finite geometric quotient. -/
theorem geomSum_add_eqv (w : Q') (left : Nat) : ∀ right : Nat,
    geomSum w (left + right) ≈
      geomSum w left + qpow w left * geomSum w right
  | 0 => by
      rw [Nat.add_zero, geomSum_zero]
      refine Q'.eqv_trans _ (geomSum w left + 0) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.eqv_of_eq (Q'.add_zero' (geomSum w left)))
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_zero_eqv (qpow w left)))
  | right + 1 => by
      change
        geomSum w (left + right) + qpow w (left + right) ≈
          geomSum w left +
            qpow w left *
              (geomSum w right + qpow w right)
      refine Q'.eqv_trans _
        (geomSum w left + qpow w left * geomSum w right +
          qpow w left * qpow w right) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (geomSum_add_eqv w left right)
          (qpow_add w left right)
      refine Q'.eqv_trans _
        (geomSum w left +
          (qpow w left * geomSum w right +
            qpow w left * qpow w right)) _ ?_ ?_
      · exact Q'.add_assoc_eqv _ _ _
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (Q'.mul_add_eqv (qpow w left)
              (geomSum w right) (qpow w right)))

/-- A face identifier paired with its prefix-weighted local geometric
quotient. -/
abbrev PhysicalMarginFaceContribution := Nat × Q'

/-- Ordered local-face expansion of the geometric quotient.  Contributions
from the tail are multiplied by the heat power of the head face. -/
def slabPhysicalMarginFaceContributions
    (w : Q') (physical : EdgeLabelling) :
    List Nat → List PhysicalMarginFaceContribution
  | [] => []
  | faceId :: rest =>
      (faceId, geomSum w (c4 (physical faceId))) ::
        (slabPhysicalMarginFaceContributions w physical rest).map
          (fun contribution =>
            (contribution.1,
              qpow w (c4 (physical faceId)) * contribution.2))

/-- The face-labelled local coefficients sum exactly to the global
geometric quotient of the total face Casimir. -/
theorem slabPhysicalMarginFaceContributions_sum_eqv_geomSum
    (w : Q') (physical : EdgeLabelling) : ∀ faces : List Nat,
    listQSum (fun contribution : PhysicalMarginFaceContribution =>
        contribution.2)
        (slabPhysicalMarginFaceContributions w physical faces) ≈
      geomSum w (slabPhysicalCasimirExponentOn physical faces)
  | [] => Q'.eqv_refl 0
  | faceId :: rest => by
      let exponent := c4 (physical faceId)
      let tail := slabPhysicalMarginFaceContributions w physical rest
      have hscaled :
          listQSum
              (fun contribution : PhysicalMarginFaceContribution =>
                qpow w exponent * contribution.2) tail ≈
            qpow w exponent *
              listQSum
                (fun contribution : PhysicalMarginFaceContribution =>
                  contribution.2) tail :=
        listQSum_mul_left _ _ _
      simp only [slabPhysicalMarginFaceContributions, listQSum,
        listQSum_map]
      change
        geomSum w exponent +
            listQSum
              (fun contribution : PhysicalMarginFaceContribution =>
                qpow w exponent * contribution.2) tail ≈
          geomSum w
            (exponent + slabPhysicalCasimirExponentOn physical rest)
      refine Q'.eqv_trans _
        (geomSum w exponent +
          qpow w exponent *
            listQSum
              (fun contribution : PhysicalMarginFaceContribution =>
                contribution.2) tail) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ hscaled
      refine Q'.eqv_trans _
        (geomSum w exponent +
          qpow w exponent *
            geomSum w
              (slabPhysicalCasimirExponentOn physical rest)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left (qpow w exponent) _ _
            (slabPhysicalMarginFaceContributions_sum_eqv_geomSum
              w physical rest))
      · exact Q'.eqv_symm
          (geomSum_add_eqv w exponent
            (slabPhysicalCasimirExponentOn physical rest))

/-! ## 2. The physical source--face carrier -/

/-- A fine physical source together with one face-labelled local quotient
coefficient. -/
abbrev FineCouplingPhysicalSourceFaceContribution :=
  EdgeLabelling × PhysicalMarginFaceContribution

def fineCouplingPhysicalSourceFaceContributionCarrier
    (S : SlabScalePair) :
    List FineCouplingPhysicalSourceFaceContribution :=
  S.fine.physicalLabellings.flatMap fun source =>
    (slabPhysicalMarginFaceContributions S.fine.coupling source
      (slabPhysicalFaceEdges S.fine.extent)).map fun contribution =>
        (source, contribution)

/-- Raw coupling-margin mass of one source--face contribution. -/
def fineCouplingPhysicalSourceFaceMarginRawMass
    (S : SlabScalePair)
    (contribution : FineCouplingPhysicalSourceFaceContribution) : Q' :=
  contribution.2.2 * fineUnitCouplingPhysicalTerm S contribution.1

/-- For one source, its local face contributions recover its global
geometric-quotient mass. -/
theorem fineCouplingPhysicalSourceFaceMarginRawMass_sum_eqv_marginTerm
    (S : SlabScalePair) (source : EdgeLabelling) :
    listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2 * fineUnitCouplingPhysicalTerm S source)
        (slabPhysicalMarginFaceContributions S.fine.coupling source
          (slabPhysicalFaceEdges S.fine.extent)) ≈
      fineCouplingPhysicalMarginTerm S source := by
  refine Q'.eqv_trans _
    (listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2)
        (slabPhysicalMarginFaceContributions S.fine.coupling source
          (slabPhysicalFaceEdges S.fine.extent)) *
      fineUnitCouplingPhysicalTerm S source) _ ?_ ?_
  · exact listQSum_mul_right _ _ _
  refine Q'.eqv_trans _
    (geomSum S.fine.coupling
        (slabPhysicalCasimirExponentOn source
          (slabPhysicalFaceEdges S.fine.extent)) *
      fineUnitCouplingPhysicalTerm S source) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (slabPhysicalMarginFaceContributions_sum_eqv_geomSum
        S.fine.coupling source
        (slabPhysicalFaceEdges S.fine.extent))
  · unfold fineCouplingPhysicalMarginTerm slabPhysicalCasimirExponent
    exact Q'.eqv_refl _

/-- The flattened source--face carrier has total mass equal to the global
fine coupling-margin partition. -/
theorem fineCouplingPhysicalSourceFaceMarginRawMass_total
    (S : SlabScalePair) :
    listQSum (fineCouplingPhysicalSourceFaceMarginRawMass S)
        (fineCouplingPhysicalSourceFaceContributionCarrier S) ≈
      fineCouplingPhysicalPartitionMarginSum S := by
  unfold fineCouplingPhysicalSourceFaceContributionCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceMarginRawMass S)
          ((slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
              (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  unfold fineCouplingPhysicalPartitionMarginSum
  apply listQSum_congr
  intro source
  rw [listQSum_map]
  simpa only [fineCouplingPhysicalSourceFaceMarginRawMass] using
    (fineCouplingPhysicalSourceFaceMarginRawMass_sum_eqv_marginTerm
      S source)

/-! ## 3. Centered event moments as local insertions -/

/-- Actual unnormalized fine-source mass of a coarse-output event. -/
def fineCouplingPhysicalActualKernelEventRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  fineCouplingPhysicalSourceKernelEventMoment K
    S.fine.physicalTerm event

/-- One local face-margin insertion against the centered coarse-output event
response. -/
def fineCouplingPhysicalSourceFaceCenteredEventInsertion
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (contribution : FineCouplingPhysicalSourceFaceContribution) : Q' :=
  fineCouplingPhysicalSourceFaceMarginRawMass S contribution *
    (S.fine.physicalPartition *
        fineCouplingKernelOutputEventMass K contribution.1 event -
      fineCouplingPhysicalActualKernelEventRawMass K event)

/-- The total of the local source--face insertions. -/
def fineCouplingPhysicalCenteredMarginLocalInsertionSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
    (fineCouplingPhysicalSourceFaceContributionCarrier S)

private theorem centeredScoreEventMoment_eqv_commonForm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event ≈
      listQSum
          (fun source =>
            fineCouplingPhysicalMarginTerm S source *
              fineCouplingKernelOutputEventMass K source event)
          S.fine.physicalLabellings * S.fine.physicalPartition -
        fineCouplingPhysicalActualKernelEventRawMass K event *
          fineCouplingPhysicalPartitionMarginSum S := by
  let marginEvent := fun source =>
    fineCouplingPhysicalMarginTerm S source *
      fineCouplingKernelOutputEventMass K source event
  let actualEvent := fun source =>
    S.fine.physicalTerm source *
      fineCouplingKernelOutputEventMass K source event
  unfold fineCouplingPhysicalSourceKernelEventMoment
    fineCouplingPhysicalSourceCenteredMarginRawDebt
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        marginEvent source * S.fine.physicalPartition -
          actualEvent source *
            fineCouplingPhysicalPartitionMarginSum S)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    simp only [marginEvent, actualEvent]
    refine Q'.eqv_trans _
      ((fineCouplingPhysicalMarginTerm S source *
            S.fine.physicalPartition) *
          fineCouplingKernelOutputEventMass K source event -
        (S.fine.physicalTerm source *
            fineCouplingPhysicalPartitionMarginSum S) *
          fineCouplingKernelOutputEventMass K source event) _ ?_ ?_
    · exact sub_mul_expand_local _ _ _
    · exact sub_eqv_both_local
        (mul_swap_tail_local _ _ _)
        (mul_swap_tail_local _ _ _)
  refine Q'.eqv_trans _
    (listQSum
          (fun source => marginEvent source * S.fine.physicalPartition)
          S.fine.physicalLabellings -
      listQSum
          (fun source => actualEvent source *
            fineCouplingPhysicalPartitionMarginSum S)
          S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ _)
  refine sub_eqv_both_local
    (listQSum_mul_right marginEvent S.fine.physicalPartition
      S.fine.physicalLabellings)
    (listQSum_mul_right actualEvent
      (fineCouplingPhysicalPartitionMarginSum S)
      S.fine.physicalLabellings)

private theorem localInsertionSum_eqv_commonForm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalCenteredMarginLocalInsertionSum K event ≈
      listQSum
          (fun source =>
            fineCouplingPhysicalMarginTerm S source *
              fineCouplingKernelOutputEventMass K source event)
          S.fine.physicalLabellings * S.fine.physicalPartition -
        fineCouplingPhysicalActualKernelEventRawMass K event *
          fineCouplingPhysicalPartitionMarginSum S := by
  let centeredResponse := fun source =>
    S.fine.physicalPartition *
        fineCouplingKernelOutputEventMass K source event -
      fineCouplingPhysicalActualKernelEventRawMass K event
  unfold fineCouplingPhysicalCenteredMarginLocalInsertionSum
    fineCouplingPhysicalSourceFaceContributionCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
          ((slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
              (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        fineCouplingPhysicalMarginTerm S source *
          centeredResponse source)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro source
    rw [listQSum_map]
    refine Q'.eqv_trans _
      (listQSum
          (fun contribution : PhysicalMarginFaceContribution =>
            (contribution.2 * fineUnitCouplingPhysicalTerm S source) *
              centeredResponse source)
          (slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent))) _ ?_ ?_
    · apply listQSum_congr
      intro contribution
      unfold fineCouplingPhysicalSourceFaceCenteredEventInsertion
        fineCouplingPhysicalSourceFaceMarginRawMass
      exact Q'.eqv_refl _
    refine Q'.eqv_trans _
      (listQSum
          (fun contribution : PhysicalMarginFaceContribution =>
            contribution.2 * fineUnitCouplingPhysicalTerm S source)
          (slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)) *
        centeredResponse source) _ ?_ ?_
    · exact listQSum_mul_right _ _ _
    · exact Q'.mul_eqv_congr_right _ _ _
        (fineCouplingPhysicalSourceFaceMarginRawMass_sum_eqv_marginTerm
          S source)
  let marginEvent := fun source =>
    fineCouplingPhysicalMarginTerm S source *
      fineCouplingKernelOutputEventMass K source event
  let constantMargin := fun source =>
    fineCouplingPhysicalMarginTerm S source *
      fineCouplingPhysicalActualKernelEventRawMass K event
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        marginEvent source * S.fine.physicalPartition -
          constantMargin source)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    unfold centeredResponse marginEvent constantMargin
    refine Q'.eqv_trans _
      (fineCouplingPhysicalMarginTerm S source *
          (S.fine.physicalPartition *
            fineCouplingKernelOutputEventMass K source event) -
        fineCouplingPhysicalMarginTerm S source *
          fineCouplingPhysicalActualKernelEventRawMass K event) _ ?_ ?_
    · exact mul_sub_expand_local _ _ _
    · exact sub_eqv_both_local
        (mul_swap_inner_local _ _ _)
        (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum
          (fun source => marginEvent source * S.fine.physicalPartition)
          S.fine.physicalLabellings -
      listQSum constantMargin S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ _)
  refine Q'.eqv_trans _
    (listQSum marginEvent S.fine.physicalLabellings *
          S.fine.physicalPartition -
      listQSum (fineCouplingPhysicalMarginTerm S)
          S.fine.physicalLabellings *
        fineCouplingPhysicalActualKernelEventRawMass K event) _ ?_ ?_
  · exact sub_eqv_both_local
      (listQSum_mul_right marginEvent S.fine.physicalPartition _)
      (by
        unfold constantMargin
        exact listQSum_mul_right _ _ _)
  refine sub_eqv_both_local (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    (fineCouplingPhysicalPartitionMarginSum S *
      fineCouplingPhysicalActualKernelEventRawMass K event) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by
      unfold fineCouplingPhysicalPartitionMarginSum
      exact Q'.eqv_refl _)
  · exact Q'.mul_comm_eqv _ _

/-- Every centered one-replica score-event moment is exactly a sum of local
face insertions on a carrier retaining the inserted physical face. -/
theorem fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_localInsertions
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event ≈
      fineCouplingPhysicalCenteredMarginLocalInsertionSum K event := by
  exact Q'.eqv_trans _ _ _
    (centeredScoreEventMoment_eqv_commonForm K event)
    (Q'.eqv_symm (localInsertionSum_eqv_commonForm K event))

#print axioms geomSum_add_eqv
#print axioms slabPhysicalMarginFaceContributions
#print axioms slabPhysicalMarginFaceContributions_sum_eqv_geomSum
#print axioms fineCouplingPhysicalSourceFaceContributionCarrier
#print axioms fineCouplingPhysicalSourceFaceMarginRawMass
#print axioms fineCouplingPhysicalSourceFaceMarginRawMass_sum_eqv_marginTerm
#print axioms fineCouplingPhysicalSourceFaceMarginRawMass_total
#print axioms fineCouplingPhysicalActualKernelEventRawMass
#print axioms fineCouplingPhysicalSourceFaceCenteredEventInsertion
#print axioms fineCouplingPhysicalCenteredMarginLocalInsertionSum
#print axioms fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_localInsertions

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
