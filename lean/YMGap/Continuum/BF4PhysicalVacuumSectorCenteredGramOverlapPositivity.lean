/-
# Finite positivity of the two BF4 vacuum-sector posterior overlaps

The support-compatible overlap compiler still needs an inhabited common-mass
statement.  At every fixed finite cutoff, normalization supplies a positive
atom of the conditioned law.  For the target posterior, the sector stationary
law is positive at every canonical sector index.  For the source posterior,
the exact Bayes factors show that every positive conditioned boundary channel
also has positive square-amplitude prior mass.

Consequently both canonical overlaps are strictly positive and at most one at
every fixed cutoff.  This is not a cutoff-uniform lower bound: the positive
rational may shrink along a cofinal sequence, so no completed or continuum gap
is claimed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

private theorem q_left_pos_of_mul_pos
    {left right : Q'}
    (right_nonnegative : (0 : Q') ≤ right)
    (product_pos : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos product_pos
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp right_nonnegative
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  exact (Int.not_lt_of_ge
    (Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum))
    hproductNum

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (left_nonnegative : (0 : Q') ≤ left)
    (product_pos : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos product_pos
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp left_nonnegative
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  exact (Int.not_lt_of_ge
    (Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos))
    hproductNum

private theorem q_min_pos {left right : Q'}
    (left_pos : (0 : Q') < left)
    (right_pos : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases hle : left ≤ right
  · rw [if_pos hle]
    exact left_pos
  · rw [if_neg hle]
    exact right_pos

private theorem listQSum_pos_exists_of_nonnegative
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      (0 : Q') < listQSum value items →
      ∃ item, item ∈ items ∧ (0 : Q') < value item
  | [], _, hsum => by
      exact absurd hsum (Int.not_lt_of_ge (Q'.le_refl' 0))
  | head :: tail, hnonnegative, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have hheadNonpos : value head ≤ 0 :=
          q_nonpos_of_not_pos hhead
        have hheadZero : value head ≈ 0 :=
          Q'.eqv_of_le_le hheadNonpos
            (hnonnegative head List.mem_cons_self)
        have hsumEqTail :
            listQSum value (head :: tail) ≈ listQSum value tail := by
          refine Q'.eqv_trans _ (0 + listQSum value tail) _ ?_ ?_
          · exact Q'.add_eqv_congr' hheadZero (Q'.eqv_refl _)
          exact Q'.eqv_of_eq (Q'.zero_add' (listQSum value tail))
        have htailPos : (0 : Q') < listQSum value tail :=
          Q'.pos_of_lt_of_le hsum (Q'.le_of_eqv hsumEqTail)
        rcases listQSum_pos_exists_of_nonnegative value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htailPos with ⟨item, hitem, hitemPos⟩
        exact ⟨item, List.mem_cons_of_mem head hitem, hitemPos⟩

private theorem listQSum_pos_of_member
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      (0 : Q') < value witness →
      (0 : Q') < listQSum value items
  | [], _, _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, witness, hnonnegative, hmem, hwitness => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.pos_of_lt_of_le hwitness
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun item hitem =>
                hnonnegative item
                  (List.mem_cons_of_mem head hitem))))
      · have htailPos := listQSum_pos_of_member
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail hwitness
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le htailPos htailLe

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

/-! ## 1. Generic support-compatible finite positivity -/

/-- A normalized nonnegative finite law has positive overlap with any
nonnegative reference law that is positive on its positive support. -/
theorem finiteProbabilityOverlap_pos_of_support
    {State : Type} (states : List State)
    (left right : State → Q')
    (left_nonnegative :
      ∀ state, state ∈ states → (0 : Q') ≤ left state)
    (right_nonnegative :
      ∀ state, state ∈ states → (0 : Q') ≤ right state)
    (left_total_one : finiteMass states left ≈ 1)
    (support_inclusion :
      ∀ state, state ∈ states →
        (0 : Q') < left state → (0 : Q') < right state) :
    (0 : Q') < finiteProbabilityOverlap states left right := by
  have hmassPos : (0 : Q') < finiteMass states left :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.ge_of_eqv left_total_one)
  rcases listQSum_pos_exists_of_nonnegative left states
      left_nonnegative hmassPos with
    ⟨witness, hwitness, hleftPos⟩
  have hrightPos := support_inclusion witness hwitness hleftPos
  unfold finiteProbabilityOverlap
  exact listQSum_pos_of_member
    (fun state => Q'.min' (left state) (right state))
    states
    (fun state hstate =>
      Q'.zero_le_min _ _
        (left_nonnegative state hstate)
        (right_nonnegative state hstate))
    hwitness (q_min_pos hleftPos hrightPos)

/-- Canonical overlap never exceeds the total mass of either input law. -/
theorem finiteProbabilityOverlap_le_leftMass
    {State : Type} (states : List State)
    (left right : State → Q') :
    finiteProbabilityOverlap states left right ≤ finiteMass states left := by
  unfold finiteProbabilityOverlap finiteMass
  exact listQSum_le_termwise_local
    (fun state => Q'.min' (left state) (right state))
    left states
    (fun state _ => Q'.min_le_left' (left state) (right state))

/-! ## 2. Exact physical support inclusion -/

/-- A positive source-conditioned boundary atom forces positive prior mass
at the same channel.  This is the physical Bayes support inclusion needed by
the overlap argument; no full-support assumption is introduced. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryPrior_pos_of_givenSource_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half)
    (hposterior :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorBoundaryGivenSource
          w hw cutoff half source hsource boundary) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorBoundaryPrior
        w hw cutoff half boundary := by
  let channelWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half boundary
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude
      w hw cutoff half source boundary
  let total :=
    centralPhysicalFiniteVacuumSectorChannelTotal
      w hw cutoff half boundary
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let marginal :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half source
  have hweightNonnegative : (0 : Q') ≤ channelWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
      boundary hboundary
  have hamplitudeNonnegative : (0 : Q') ≤ amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude_nonnegative
      hw cutoff half source boundary
  have htotalNonnegative : (0 : Q') ≤ total :=
    centralPhysicalFiniteVacuumSectorChannelTotal_nonnegative
      hw cutoff half boundary
  have hmarginalPos : (0 : Q') < marginal :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource
  have hrowMassPos : (0 : Q') < mass * marginal :=
    Q'.mul_pos
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      hmarginalPos
  unfold centralPhysicalFiniteVacuumSectorBoundaryGivenSource
    finiteWeightedGramChannelGivenState Q'.divPos at hposterior
  change (0 : Q') <
      (channelWeight * (amplitude * total)) *
        Q'.recipPos (mass * marginal) hrowMassPos at hposterior
  have hnumeratorPos :
      (0 : Q') < channelWeight * (amplitude * total) :=
    q_left_pos_of_mul_pos
      (Q'.le_of_lt (Q'.recipPos_pos _ hrowMassPos)) hposterior
  have hweightPos : (0 : Q') < channelWeight :=
    q_left_pos_of_mul_pos
      (Q'.mul_nonneg _ _ hamplitudeNonnegative htotalNonnegative)
      hnumeratorPos
  have hampTotalPos : (0 : Q') < amplitude * total :=
    q_right_pos_of_mul_pos hweightNonnegative hnumeratorPos
  have htotalPos : (0 : Q') < total :=
    q_right_pos_of_mul_pos hamplitudeNonnegative hampTotalPos
  unfold centralPhysicalFiniteVacuumSectorBoundaryPrior
    finiteWeightedGramChannelPrior Q'.divPos
  change (0 : Q') <
      (channelWeight * (total * total)) *
        Q'.recipPos mass
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)
  exact Q'.mul_pos
    (Q'.mul_pos hweightPos (Q'.mul_pos htotalPos htotalPos))
    (Q'.recipPos_pos _
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half))

/-! ## 3. Both actual finite overlaps lie in `(0,1]` -/

/-- Every positive boundary channel has strictly positive overlap between its
target posterior and the sector stationary law. -/
theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
        w hw cutoff half boundary channelTotal_pos := by
  exact finiteProbabilityOverlap_pos_of_support
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w hw cutoff half boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half)
    (fun state hstate =>
      centralPhysicalFiniteVacuumSectorTargetGivenBoundary_nonnegative
        hw cutoff half boundary channelTotal_pos state)
    (fun state hstate => Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hstate))
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
      channelTotal_pos)
    (fun state hstate _ =>
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hstate)

/-- Every canonical sector source has strictly positive overlap between its
boundary posterior and the square-amplitude boundary prior. -/
theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
        w hw cutoff half source hsource := by
  exact finiteProbabilityOverlap_pos_of_support
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w hw cutoff half source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w hw cutoff half)
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorBoundaryGivenSource_nonnegative_on
        hw hsource hboundary)
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorBoundaryPrior_nonnegative_on
        hw hboundary)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one hsource)
    (fun boundary hboundary hposterior =>
      centralPhysicalFiniteVacuumSectorBoundaryPrior_pos_of_givenSource_pos
        hsource hboundary hposterior)

/-- The target posterior overlap is at most one. -/
theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
        w hw cutoff half boundary channelTotal_pos ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _
    (finiteProbabilityOverlap_le_leftMass
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
        w hw cutoff half boundary channelTotal_pos)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half))
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one
        channelTotal_pos))

/-- The source posterior overlap is at most one. -/
theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
        w hw cutoff half source hsource ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _
    (finiteProbabilityOverlap_le_leftMass
      (centralBoundaryChannels cutoff half)
      (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
        w hw cutoff half source hsource)
      (centralPhysicalFiniteVacuumSectorBoundaryPrior
        w hw cutoff half))
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one
        hsource))

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.finiteProbabilityOverlap_pos_of_support
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.finiteProbabilityOverlap_le_leftMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.centralPhysicalFiniteVacuumSectorBoundaryPrior_pos_of_givenSource_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_le_one
