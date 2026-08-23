/-
# Support-compatible overlap control of the BF4 sector posteriors

The cutoff-two vacuum row has genuine zeros, so a finite global projective
diameter cannot control the actual posterior laws.  Total overlap does not
require common support.  For two normalized finite laws `p` and `q`, the
canonical common submass `min p q` leaves two nonnegative residuals and gives

    ||p - q||_1 <= 2 * (1 - sum_x min (p x) (q x)).

This module proves that estimate over the repository's exact rational setoid,
specializes it to both physical vacuum-sector posteriors, and compiles cofinal
overlap floors whose residual-rate product is below one to the completed
same-object vacuum-sector strict gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
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
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item + (-right item)) items ≈
      listQSum left items + (-listQSum right items) := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _) (listQSum_neg_local right items)

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Generic finite common-submass estimate -/

/-- The largest pointwise common submass of two finite weights. -/
def finiteProbabilityOverlap {State : Type}
    (states : List State) (left right : State → Q') : Q' :=
  listQSum (fun state => Q'.min' (left state) (right state)) states

/-- A common submass removes from both laws before the triangle inequality.
This is the pointwise mechanism that permits incompatible support. -/
theorem qAbs_sub_le_common_residuals
    {left right common : Q'}
    (common_le_left : common ≤ left)
    (common_le_right : common ≤ right) :
    Q'.abs (left + (-right)) ≤
      (left + (-common)) + (right + (-common)) := by
  have hleftResidual : (0 : Q') ≤ left + (-common) :=
    Q'.sub_nonneg_of_le common_le_left
  have hrightResidual : (0 : Q') ≤ right + (-common) :=
    Q'.sub_nonneg_of_le common_le_right
  have hdifference :
      left + (-right) ≈
        (left + (-common)) + (-(right + (-common))) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      ((left + (-common)) + ((-right) + common)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (left + (-common)) _ _
        (Q'.eqv_trans _ ((-right) + (-(-common))) _
          (Q'.neg_add_eqv right (-common))
          (Q'.add_eqv_congr_left (-right) _ _
            (Q'.neg_neg_eqv common)))
    refine Q'.eqv_trans _
      ((left + (-right)) + ((-common) + common)) _
      (Q'.add_swap_inner left (-common) (-right) common) ?_
    refine Q'.eqv_trans _ ((left + (-right)) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (left + (-right)) _ _
        (Q'.neg_add_self_eqv common)
    exact Q'.eqv_of_eq (Q'.add_zero' (left + (-right)))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (left + (-common)) (-(right + (-common)))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr'
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hleftResidual)
      (Q'.eqv_trans _ _ _
        (Q'.abs_neg' (right + (-common)))
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
          hrightResidual)))

/-- Summed common-submass estimate before normalization. -/
theorem finiteL1Distance_le_commonResidualMass
    {State : Type} (states : List State)
    (left right common : State → Q')
    (common_le_left : ∀ state, state ∈ states → common state ≤ left state)
    (common_le_right : ∀ state, state ∈ states → common state ≤ right state) :
    finiteL1Distance states left right ≤
      (finiteMass states left + (-finiteMass states common)) +
        (finiteMass states right + (-finiteMass states common)) := by
  unfold finiteL1Distance finiteMass
  have hsum := listQSum_le_termwise_local
    (fun state => Q'.abs (left state + (-right state)))
    (fun state =>
      (left state + (-common state)) +
        (right state + (-common state)))
    states
    (fun state hstate =>
      qAbs_sub_le_common_residuals
        (common_le_left state hstate)
        (common_le_right state hstate))
  refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _
    (listQSum (fun state => left state + (-common state)) states +
      listQSum (fun state => right state + (-common state)) states) _ ?_ ?_
  · exact listQSum_add
      (fun state => left state + (-common state))
      (fun state => right state + (-common state)) states
  exact Q'.add_eqv_congr'
    (listQSum_sub_local left common states)
    (listQSum_sub_local right common states)

/-- For normalized finite laws, a lower bound on canonical overlap gives an
explicit `L1` contraction rate. -/
theorem finiteL1Distance_le_two_mul_one_sub_overlap
    {State : Type} (states : List State)
    (left right : State → Q')
    (left_total_one : finiteMass states left ≈ 1)
    (right_total_one : finiteMass states right ≈ 1)
    (overlapFloor : Q')
    (overlapFloor_le :
      overlapFloor ≤ finiteProbabilityOverlap states left right) :
    finiteL1Distance states left right ≤
      (2 : Q') * (1 + (-overlapFloor)) := by
  let overlap := finiteProbabilityOverlap states left right
  let common := fun state => Q'.min' (left state) (right state)
  have hresidual := finiteL1Distance_le_commonResidualMass
    states left right common
    (fun state _ => Q'.min_le_left' (left state) (right state))
    (fun state _ => Q'.min_le_right' (left state) (right state))
  have hoverlap : finiteMass states common ≈ overlap :=
    Q'.eqv_refl _
  have hnormalized :
      (finiteMass states left + (-finiteMass states common)) +
          (finiteMass states right + (-finiteMass states common)) ≈
        (1 + (-overlap)) + (1 + (-overlap)) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' left_total_one
        (Q'.neg_eqv_congr _ _ hoverlap))
      (Q'.add_eqv_congr' right_total_one
        (Q'.neg_eqv_congr _ _ hoverlap))
  refine Q'.le_trans' _ _ _ hresidual ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalized) ?_
  have hsingle : 1 + (-overlap) ≤ 1 + (-overlapFloor) :=
    Q'.add_le_add_left 1 (-overlap) (-overlapFloor)
      (Q'.neg_le_neg overlapFloor_le)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add hsingle hsingle) (Q'.le_of_eqv ?_)
  exact Q'.eqv_symm
    (YMGap.Constructive.ExpNeg.two_mul_eqv
      (1 + (-overlapFloor)))

/-- Overlap is nonnegative for pointwise nonnegative laws. -/
theorem finiteProbabilityOverlap_nonnegative
    {State : Type} (states : List State)
    (left right : State → Q')
    (left_nonnegative : ∀ state, state ∈ states → (0 : Q') ≤ left state)
    (right_nonnegative : ∀ state, state ∈ states → (0 : Q') ≤ right state) :
    (0 : Q') ≤ finiteProbabilityOverlap states left right := by
  unfold finiteProbabilityOverlap
  apply listQSum_nonnegative_on
  intro state hstate
  exact Q'.zero_le_min _ _
    (left_nonnegative state hstate)
    (right_nonnegative state hstate)

/-! ## 2. The two actual sector overlaps -/

/-- Common mass between `target | boundary` and the sector stationary law. -/
def centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) : Q' :=
  finiteProbabilityOverlap
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w hw cutoff half boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)

/-- Common mass between `boundary | source` and the square-amplitude prior. -/
def centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) : Q' :=
  finiteProbabilityOverlap
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w hw cutoff half)

/-- A target-posterior overlap floor implies its exact support-compatible
`L1` rate. -/
theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_of_overlap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (overlapFloor : Q')
    (overlapFloor_le :
      overlapFloor ≤
        centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
          w hw cutoff half boundary channelTotal_pos) :
    centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
        w hw cutoff half boundary channelTotal_pos ≤
      (2 : Q') * (1 + (-overlapFloor)) := by
  exact finiteL1Distance_le_two_mul_one_sub_overlap
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w hw cutoff half boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
      channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half)
    overlapFloor overlapFloor_le

/-- A source-posterior overlap floor implies its exact support-compatible
`L1` rate. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_of_overlap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (overlapFloor : Q')
    (overlapFloor_le :
      overlapFloor ≤
        centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
          w hw cutoff half source hsource) :
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
        w hw cutoff half source hsource ≤
      (2 : Q') * (1 + (-overlapFloor)) := by
  exact finiteL1Distance_le_two_mul_one_sub_overlap
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one
      hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one
      w hw cutoff half)
    overlapFloor overlapFloor_le

/-! ## 3. Cofinal overlap floors compile to the completed gap -/

/-- Cofinal lower bounds on the two actual posterior overlaps.  Their
residual `L1` rate product, not a pointwise positive-support ratio, must be
strictly below one. -/
structure FixedNomeCofinalVacuumSectorPosteriorOverlap
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (targetOverlapFloor sourceOverlapFloor : Q') : Type 1 where
  targetOverlapFloor_nonnegative : (0 : Q') ≤ targetOverlapFloor
  sourceOverlapFloor_nonnegative : (0 : Q') ≤ sourceOverlapFloor
  targetOverlapFloor_le_one : targetOverlapFloor ≤ (1 : Q')
  sourceOverlapFloor_le_one : sourceOverlapFloor ≤ (1 : Q')
  residualRateProduct_lt_one :
    ((2 : Q') * (1 + (-targetOverlapFloor))) *
        ((2 : Q') * (1 + (-sourceOverlapFloor))) < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  targetOverlapBound : ∀ base threshold boundary,
    boundary ∈ centralBoundaryChannels (anchor base threshold) half →
      ∀ channelTotal_pos :
          (0 : Q') <
            centralPhysicalFiniteVacuumSectorChannelTotal
              w hw (anchor base threshold) half boundary,
        targetOverlapFloor ≤
          centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
            w hw (anchor base threshold) half boundary channelTotal_pos
  sourceOverlapBound : ∀ base threshold source,
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w hw (anchor base threshold) half) →
      sourceOverlapFloor ≤
        centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
          w hw (anchor base threshold) half source hsource

namespace FixedNomeCofinalVacuumSectorPosteriorOverlap

/-- Overlap floors produce the exact posterior-mixing certificate. -/
def toPosteriorMixing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetOverlapFloor sourceOverlapFloor : Q'}
    (family : FixedNomeCofinalVacuumSectorPosteriorOverlap
      w hw half targetOverlapFloor sourceOverlapFloor) :
    FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing
      w hw half
      ((2 : Q') * (1 + (-targetOverlapFloor)))
      ((2 : Q') * (1 + (-sourceOverlapFloor))) where
  targetRate_nonnegative :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.sub_nonneg_of_le family.targetOverlapFloor_le_one)
  sourceRate_nonnegative :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.sub_nonneg_of_le family.sourceOverlapFloor_le_one)
  rateProduct_lt_one := family.residualRateProduct_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  targetPosteriorBound := by
    intro base threshold boundary hboundary channelTotal_pos
    exact
      centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_of_overlap
        channelTotal_pos targetOverlapFloor
        (family.targetOverlapBound
          base threshold boundary hboundary channelTotal_pos)
  sourcePosteriorBound := by
    intro base threshold source hsource
    exact
      centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_of_overlap
        hsource sourceOverlapFloor
        (family.sourceOverlapBound base threshold source hsource)

/-- Cofinal posterior overlap reaches the completed same-object vacuum-sector
strict gap at the product of the two residual rates. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetOverlapFloor sourceOverlapFloor : Q'}
    (family : FixedNomeCofinalVacuumSectorPosteriorOverlap
      w hw half targetOverlapFloor sourceOverlapFloor) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half
      (((2 : Q') * (1 + (-targetOverlapFloor))) *
        ((2 : Q') * (1 + (-sourceOverlapFloor)))) :=
  family.toPosteriorMixing.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorPosteriorOverlap

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.qAbs_sub_le_common_residuals
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.finiteL1Distance_le_commonResidualMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.finiteL1Distance_le_two_mul_one_sub_overlap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.finiteProbabilityOverlap_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_of_overlap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_of_overlap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap.FixedNomeCofinalVacuumSectorPosteriorOverlap.toVacuumSectorCenteredStrictGap
