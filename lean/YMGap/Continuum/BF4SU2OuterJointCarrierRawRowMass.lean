/-
# Joint-carrier nonemptiness as strict raw-row mass

The finite joint carrier and the explicit whole-slab raw kernel were
previously connected only in the easy direction: a retained carrier code
gives one strictly positive raw entry.  This module proves the converse
constructively.

For a fixed fine state, sum the nonnegative whole-slab recoupling weights
over the literal coarse physical carrier.  If that finite raw-row mass is
strictly positive, finite recursion selects:

* one coarse target of positive raw weight;
* at every coarse face, one pair channel of positive fixed-final weight; and
* at every coarse link, one fusion witness from the positive link product.

These data form a `WholeSlabJointChannelSelection`, hence an actual member
of `wholeSlabJointCarrierCodes`.  Consequently positive length of the
enumerated joint carrier is equivalent to strict positivity of the explicit
raw-row mass.

The all-positive-row obstruction is therefore restated without a hidden
choice or routing oracle as one scalar nonvanishing theorem for the genuine
BF4 recoupling row.  This module does not prove that nonvanishing from the
fine physical term.

## Axiom gate

Finite list recursion and exact `Nat`/`Int`/`Q'` order only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction

namespace YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Constructive positive-member extraction -/

/-- A literal positive member of a finite weighted list. -/
structure PositiveListMember {A : Type}
    (value : A → Q') (items : List A) : Type where
  item : A
  item_mem : item ∈ items
  item_positive : (0 : Q') < value item

private theorem q_nonpos_of_not_pos {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- A strictly positive finite sum of nonnegative rational terms
constructively returns one positive summand. -/
def positiveListMemberOfSumPositive {A : Type}
    (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      (0 : Q') < listQSum value items →
        PositiveListMember value items
  | [], hsum => by
      have hnum := Q'.num_pos_of_pos hsum
      simp only [listQSum] at hnum
      exact False.elim (Int.lt_irrefl 0 hnum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact
          { item := head
            item_mem := List.mem_cons_self
            item_positive := hhead }
      · have hheadLe : value head ≤ 0 :=
          q_nonpos_of_not_pos hhead
        have hsumLe :
            value head + listQSum value tail ≤
              listQSum value tail := by
          have hadd :=
            Q'.add_le_add_right
              (value head) 0 (listQSum value tail) hheadLe
          simpa only [Q'.zero_add'] using hadd
        have htail :
            (0 : Q') < listQSum value tail := by
          change (0 : Q') <
            value head + listQSum value tail at hsum
          exact Q'.pos_of_lt_of_le hsum hsumLe
        let selected :=
          positiveListMemberOfSumPositive value hvalue tail htail
        exact
          { item := selected.item
            item_mem :=
              List.mem_cons_of_mem head selected.item_mem
            item_positive := selected.item_positive }

private theorem listQSum_member_le_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
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
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

/-! ## 2. Strict factors of positive finite products -/

private theorem q_left_pos_of_mul_pos
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum :
      (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos :
      left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg
      hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum :
      (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos :
      left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos
      hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem wholeSlabFiniteQProduct_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      (0 : Q') ≤ wholeSlabFiniteQProduct value items
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _
        (hvalue head)
        (wholeSlabFiniteQProduct_nonnegative_local
          value hvalue tail)

private theorem wholeSlabFiniteQProduct_factor_pos
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A),
      (0 : Q') < wholeSlabFiniteQProduct value items →
      ∀ item, item ∈ items →
        (0 : Q') < value item
  | [], _, item, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: tail, hproduct, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact q_left_pos_of_mul_pos
          (wholeSlabFiniteQProduct_nonnegative_local
            value hvalue tail)
          hproduct
      · have htailProduct :
            (0 : Q') <
              wholeSlabFiniteQProduct value tail :=
          q_right_pos_of_mul_pos
            (hvalue head) hproduct
        exact wholeSlabFiniteQProduct_factor_pos
          value hvalue tail htailProduct item htail

private theorem natListProduct_factor_pos_local {A : Type}
    (value : A → Nat) :
    ∀ (items : List A),
      0 < natListProduct value items →
      ∀ item, item ∈ items → 0 < value item
  | [], _, item, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: tail, hproduct, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        have hne : value head ≠ 0 := by
          intro hzero
          rw [natListProduct, hzero, Nat.zero_mul] at hproduct
          exact Nat.not_lt_zero 0 hproduct
        omega
      · have htailProduct :
            0 < natListProduct value tail := by
          have hne :
              natListProduct value tail ≠ 0 := by
            intro hzero
            rw [natListProduct, hzero, Nat.mul_zero] at hproduct
            exact Nat.not_lt_zero 0 hproduct
          omega
        exact natListProduct_factor_pos_local
          value tail htailProduct item htail

private theorem nat_pos_of_qOfNat_pos
    (value : Nat)
    (hvalue : (0 : Q') < Q'.ofNat value) :
    0 < value := by
  have hnum := Q'.num_pos_of_pos hvalue
  rw [Q'.ofNat_num_cast] at hnum
  exact Int.ofNat_lt.mp hnum

/-! ## 3. The scalar raw-row mass and one positive target -/

/-- The literal unnormalised whole-slab BF4 row sum. -/
def wholeSlabJointRawRowMass
    (S : SlabScalePair) (fineState : EdgeLabelling) : Q' :=
  listQSum
    (wholeSlabRecouplingRawWeight S fineState)
    S.coarse.physicalLabellings

theorem wholeSlabJointRawRowMass_nonnegative
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (0 : Q') ≤ wholeSlabJointRawRowMass S fineState := by
  unfold wholeSlabJointRawRowMass
  exact listQSum_nonnegative_on
    (wholeSlabRecouplingRawWeight S fineState)
    S.coarse.physicalLabellings
    (fun coarseState _ =>
      wholeSlabRecouplingRawWeight_nonnegative
        S fineState coarseState)

/-- One coarse state selected constructively from positive total raw mass. -/
structure PositiveWholeSlabRawTarget
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  coarseTarget : EdgeLabelling
  coarseTarget_mem :
    coarseTarget ∈ S.coarse.physicalLabellings
  rawWeight_pos :
    (0 : Q') <
      wholeSlabRecouplingRawWeight
        S fineState coarseTarget

def positiveWholeSlabRawTargetOfRowMass
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    PositiveWholeSlabRawTarget S fineState := by
  let selected :=
    positiveListMemberOfSumPositive
      (wholeSlabRecouplingRawWeight S fineState)
      (fun coarseState =>
        wholeSlabRecouplingRawWeight_nonnegative
          S fineState coarseState)
      S.coarse.physicalLabellings
      (by simpa only [wholeSlabJointRawRowMass] using hmass)
  exact
    { coarseTarget := selected.item
      coarseTarget_mem := selected.item_mem
      rawWeight_pos := selected.item_positive }

/-! ### The exact normalized BF4 row supplied by positive raw mass -/

/-- Positive raw-row mass, together with physical source membership,
constructs the pre-existing exact whole-slab normalization datum.  Thus the
scalar frontier is not merely a support surrogate: it gives the literal
globally link-glued conditional BF4 row. -/
def coherentSlabRecouplingSourceOfRawRowMassPositive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (fine_mem : fineState ∈ S.fine.physicalLabellings)
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    CoherentSlabRecouplingSource S :=
  let target := positiveWholeSlabRawTargetOfRowMass hmass
  { fineState := fineState
    fine_mem := fine_mem
    coarseWitness := target.coarseTarget
    coarseWitness_mem := target.coarseTarget_mem
    coarseWitness_positive := target.rawWeight_pos }

/-- The partition function of the constructed conditional row is exactly
the scalar raw-row mass, not a comparison or a new normalization. -/
theorem coherentSource_partition_eq_rawRowMass
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (fine_mem : fineState ∈ S.fine.physicalLabellings)
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    wholeSlabRecouplingPartition
        (coherentSlabRecouplingSourceOfRawRowMassPositive
          fine_mem hmass) =
      wholeSlabJointRawRowMass S fineState :=
  rfl

/-- The selected entry of the exact normalized BF4 row is strictly
positive. -/
theorem coherentSource_conditionalKernel_witness_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (fine_mem : fineState ∈ S.fine.physicalLabellings)
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    let source :=
      coherentSlabRecouplingSourceOfRawRowMassPositive
        fine_mem hmass
    (0 : Q') <
      wholeSlabRecouplingConditionalKernel
        source source.coarseWitness := by
  let source :=
    coherentSlabRecouplingSourceOfRawRowMassPositive
      fine_mem hmass
  exact Q'.divPos_pos _ _
    (wholeSlabRecouplingPartition_pos source)
    source.coarseWitness_positive

/-- Transfer an unnormalised entry floor and a partition ceiling to the
normalized BF4 row.  This is the division-safe order lemma needed for
spacing-uniform Harnack estimates: the analytic work may bound numerator
and partition separately. -/
theorem wholeSlabConditionalKernel_ge_of_raw_floor
    {S : SlabScalePair}
    (source : CoherentSlabRecouplingSource S)
    (coarseState : EdgeLabelling)
    (floor partitionCeiling : Q')
    (floor_nonnegative : (0 : Q') ≤ floor)
    (partition_le :
      wholeSlabRecouplingPartition source ≤ partitionCeiling)
    (raw_floor :
      floor * partitionCeiling ≤
        wholeSlabRecouplingRawWeight
          S source.fineState coarseState) :
    floor ≤
      wholeSlabRecouplingConditionalKernel
        source coarseState := by
  unfold wholeSlabRecouplingConditionalKernel
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left
      (wholeSlabRecouplingPartition source)
      partitionCeiling floor
      partition_le floor_nonnegative)
    raw_floor

/-- Dually, an unnormalised entry ceiling proportional to the exact
partition gives the same ceiling after row normalization. -/
theorem wholeSlabConditionalKernel_le_of_raw_ceiling
    {S : SlabScalePair}
    (source : CoherentSlabRecouplingSource S)
    (coarseState : EdgeLabelling)
    (ceiling : Q')
    (raw_ceiling :
      wholeSlabRecouplingRawWeight
          S source.fineState coarseState ≤
        ceiling * wholeSlabRecouplingPartition source) :
    wholeSlabRecouplingConditionalKernel
        source coarseState ≤ ceiling := by
  unfold wholeSlabRecouplingConditionalKernel
  exact Q'.divPos_le_of_le_mul _ _
    (wholeSlabRecouplingPartition_pos source)
    raw_ceiling

/-! ## 4. Positive target entries expose all face and link data -/

private def fixedFinalFaceChannelTerm
    (S : SlabScalePair) (fineState coarseTarget : EdgeLabelling)
    (faceId : Nat) (channel : PairChannelState) : Q' :=
  if channel.2 = coarseTarget faceId then
    packetPairChannelRawWeight S.coarse.coupling
      (wholeSlabFinePacket S fineState faceId) channel
  else 0

private theorem fixedFinalFaceChannelTerm_nonnegative
    (S : SlabScalePair) (fineState coarseTarget : EdgeLabelling)
    (faceId : Nat) (channel : PairChannelState) :
    (0 : Q') ≤
      fixedFinalFaceChannelTerm
        S fineState coarseTarget faceId channel := by
  unfold fixedFinalFaceChannelTerm
  by_cases hfinal : channel.2 = coarseTarget faceId
  · rw [if_pos hfinal]
    exact packetPairChannelRawWeight_nonnegative
      S.coarse.coupling_nonnegative _ _
  · rw [if_neg hfinal]
    exact Q'.le_refl' 0

private theorem PositiveWholeSlabRawTarget.faceProduct_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState) :
    (0 : Q') <
      wholeSlabFaceRawProduct
        S fineState target.coarseTarget := by
  have hraw := target.rawWeight_pos
  unfold wholeSlabRecouplingRawWeight at hraw
  exact q_left_pos_of_mul_pos
    (by
      rw [Q'.zero_le_iff_num_nonneg]
      exact Int.natCast_nonneg _)
    target.rawWeight_pos

private theorem PositiveWholeSlabRawTarget.linkProduct_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState) :
    0 <
      slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent
        target.coarseTarget := by
  have hraw := target.rawWeight_pos
  unfold wholeSlabRecouplingRawWeight at hraw
  have hq :
      (0 : Q') <
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct
            S.coarse.cutoff S.coarse.extent
            target.coarseTarget) :=
    q_right_pos_of_mul_pos
      (wholeSlabFaceRawProduct_nonnegative
        S fineState target.coarseTarget)
      hraw
  exact nat_pos_of_qOfNat_pos _ hq

private theorem PositiveWholeSlabRawTarget.faceRawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    (0 : Q') <
      wholeSlabFaceRawWeight
        S fineState target.coarseTarget faceId := by
  have hfinite :
      (0 : Q') <
        wholeSlabFiniteQProduct
          (wholeSlabFaceRawWeight
            S fineState target.coarseTarget)
          S.coarse.faceEdges :=
    Q'.pos_of_lt_of_le
      target.faceProduct_pos
      (Q'.le_of_eqv
        (wholeSlabFaceRawProduct_eqv_finiteQProduct
          S fineState target.coarseTarget))
  exact wholeSlabFiniteQProduct_factor_pos
    (wholeSlabFaceRawWeight
      S fineState target.coarseTarget)
    (fun id =>
      wholeSlabFaceRawWeight_nonnegative
        S fineState target.coarseTarget id)
    S.coarse.faceEdges hfinite faceId hface

private structure PositiveFaceChannelWitness
    (S : SlabScalePair) (fineState coarseTarget : EdgeLabelling)
    (faceId : Nat) : Type where
  channel : PairChannelState
  channel_mem :
    channel ∈ pairChannelStateSpace S.fine.cutoff
  channel_final :
    channel.2 = coarseTarget faceId
  channel_positive :
    (0 : Q') <
      packetPairChannelRawWeight S.coarse.coupling
        (wholeSlabFinePacket S fineState faceId) channel

private def PositiveWholeSlabRawTarget.positiveFaceChannel
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    PositiveFaceChannelWitness
      S fineState target.coarseTarget faceId := by
  let selected :=
    positiveListMemberOfSumPositive
      (fixedFinalFaceChannelTerm
        S fineState target.coarseTarget faceId)
      (fixedFinalFaceChannelTerm_nonnegative
        S fineState target.coarseTarget faceId)
      (pairChannelStateSpace S.fine.cutoff)
      (by
        have hfacePos :=
          target.faceRawWeight_pos faceId hface
        unfold wholeSlabFaceRawWeight at hfacePos
        exact hfacePos)
  have hfinal :
      selected.item.2 =
        target.coarseTarget faceId := by
    by_cases h :
        selected.item.2 =
          target.coarseTarget faceId
    · exact h
    · have hzero :
          fixedFinalFaceChannelTerm
              S fineState target.coarseTarget faceId
              selected.item = 0 := by
        unfold fixedFinalFaceChannelTerm
        rw [if_neg h]
      have hselectedPos := selected.item_positive
      rw [hzero] at hselectedPos
      exact False.elim
        ((by decide : ¬ (0 : Q') < 0) hselectedPos)
  have hpositive :
      (0 : Q') <
        packetPairChannelRawWeight S.coarse.coupling
          (wholeSlabFinePacket S fineState faceId)
          selected.item := by
    simpa only [fixedFinalFaceChannelTerm, hfinal, if_true] using
      selected.item_positive
  exact
    { channel := selected.item
      channel_mem := selected.item_mem
      channel_final := hfinal
      channel_positive := hpositive }

private def PositiveWholeSlabRawTarget.faceChannel
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState)
    (faceId : Nat) : PairChannelState :=
  if hface : faceId ∈ S.coarse.faceEdges then
    (target.positiveFaceChannel faceId hface).channel
  else ((0, 0), 0)

/-- Strict raw mass constructs the full semantic joint carrier. -/
def PositiveWholeSlabRawTarget.toJointChannelSelection
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState) :
    WholeSlabJointChannelSelection S fineState where
  coarseTarget := target.coarseTarget
  coarseTarget_mem := target.coarseTarget_mem
  faceChannel := target.faceChannel
  faceChannel_mem := by
    intro faceId hface
    unfold PositiveWholeSlabRawTarget.faceChannel
    rw [dif_pos hface]
    exact
      (target.positiveFaceChannel faceId hface).channel_mem
  faceChannel_final := by
    intro faceId hface
    unfold PositiveWholeSlabRawTarget.faceChannel
    rw [dif_pos hface]
    exact
      (target.positiveFaceChannel faceId hface).channel_final
  faceChannel_positive := by
    intro faceId hface
    unfold PositiveWholeSlabRawTarget.faceChannel
    rw [dif_pos hface]
    exact
      (target.positiveFaceChannel faceId hface).channel_positive
  coarseLink_positive := by
    intro link hlink
    have hlinkProduct := target.linkProduct_pos
    unfold slabExplicitLinkMultiplicityProduct at hlinkProduct
    exact natListProduct_factor_pos_local
      (slabExplicitLinkMultiplicity
        S.coarse.cutoff S.coarse.extent target.coarseTarget)
      (boundaryCompleteSlabLinks S.coarse.extent)
      hlinkProduct link hlink

/-! ## 5. Exact equivalence with the enumerated joint carrier -/

def jointCarrierNonemptyOfRawRowMassPositive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    WholeSlabJointCarrierNonempty S fineState :=
  jointSelectionToCarrierNonempty
    (positiveWholeSlabRawTargetOfRowMass hmass).toJointChannelSelection

theorem rawRowMass_pos_of_jointCarrierNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (nonempty : WholeSlabJointCarrierNonempty S fineState) :
    (0 : Q') < wholeSlabJointRawRowMass S fineState := by
  let selection := nonempty.toSelection
  have hentry :
      (0 : Q') <
        wholeSlabRecouplingRawWeight
          S fineState selection.coarseTarget :=
    selection.rawWeight_pos
  have hle :
      wholeSlabRecouplingRawWeight
          S fineState selection.coarseTarget ≤
        wholeSlabJointRawRowMass S fineState := by
    unfold wholeSlabJointRawRowMass
    exact listQSum_member_le_nonnegative
      (wholeSlabRecouplingRawWeight S fineState)
      (fun coarseState =>
        wholeSlabRecouplingRawWeight_nonnegative
          S fineState coarseState)
      S.coarse.physicalLabellings
      selection.coarseTarget_mem
  exact Q'.pos_of_lt_of_le hentry hle

/-- **Exact finite support theorem.**  The literal global joint carrier is
inhabited exactly when the explicit unnormalised BF4 recoupling row has
strictly positive total mass. -/
theorem jointCarrierCodes_length_pos_iff_rawRowMass_pos
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    0 < (wholeSlabJointCarrierCodes S fineState).length ↔
      (0 : Q') < wholeSlabJointRawRowMass S fineState := by
  constructor
  · intro hlength
    exact rawRowMass_pos_of_jointCarrierNonempty
      { candidates_positive := hlength }
  · intro hmass
    exact
      (jointCarrierNonemptyOfRawRowMassPositive
        hmass).candidates_positive

/-! ## 6. All-row scalar frontier and equivalence -/

/-- Scalar form of the genuine all-positive-row BF4 obstruction. -/
structure SU2OuterRawRowMassPositive
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  positive :
    ∀ K source,
      K ≠ 1 →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
      (0 : Q') <
        wholeSlabJointRawRowMass
          (su2OuterScalePair
            G g hg candidate hcandidate K) source

def SU2OuterRawRowMassPositive.toJointCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (mass :
      SU2OuterRawRowMassPositive
        G g hg candidate hcandidate) :
    SU2OuterJointCarrierNonempty
      G g hg candidate hcandidate where
  nonempty := by
    intro K source hK hsource hpositive
    exact jointCarrierNonemptyOfRawRowMassPositive
      (mass.positive K source hK hsource hpositive)

/-- Every positive physical row in the all-cutoff scalar frontier yields
the genuine normalized whole-slab conditional row. -/
def SU2OuterRawRowMassPositive.coherentSource
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (mass :
      SU2OuterRawRowMassPositive
        G g hg candidate hcandidate)
    (K : Nat) (source : EdgeLabelling)
    (hK : K ≠ 1)
    (hsource :
      source ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalTerm source) :
    CoherentSlabRecouplingSource
      (su2OuterScalePair
        G g hg candidate hcandidate K) :=
  coherentSlabRecouplingSourceOfRawRowMassPositive
    hsource
    (mass.positive K source hK hsource hpositive)

def rawRowMassPositiveOfJointCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (carrier :
      SU2OuterJointCarrierNonempty
        G g hg candidate hcandidate) :
    SU2OuterRawRowMassPositive
      G g hg candidate hcandidate where
  positive := by
    intro K source hK hsource hpositive
    exact rawRowMass_pos_of_jointCarrierNonempty
      (carrier.nonempty K source hK hsource hpositive)

/-- The scalar nonvanishing frontier is already sufficient for the exact
physical positive-row closure; no separate routing oracle is needed after
the positive coarse summand and its local factors have been extracted. -/
def SU2OuterRawRowMassPositive.toPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (mass :
      SU2OuterRawRowMassPositive
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate :=
  mass.toJointCarrierNonempty.toPositiveRowClosure

/-- Equivalently, positive raw mass constructs the former fine-witness
routing interface by using the selected positive joint carrier member as a
constant route. -/
def SU2OuterRawRowMassPositive.toFineWitnessRouting
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (mass :
      SU2OuterRawRowMassPositive
        G g hg candidate hcandidate) :
    SU2OuterFineWitnessRouting
      G g hg candidate hcandidate :=
  fineWitnessRoutingOfJointCarrierNonempty
    mass.toJointCarrierNonempty

#print axioms PositiveListMember
#print axioms positiveListMemberOfSumPositive
#print axioms wholeSlabJointRawRowMass_nonnegative
#print axioms positiveWholeSlabRawTargetOfRowMass
#print axioms coherentSlabRecouplingSourceOfRawRowMassPositive
#print axioms coherentSource_partition_eq_rawRowMass
#print axioms coherentSource_conditionalKernel_witness_pos
#print axioms wholeSlabConditionalKernel_ge_of_raw_floor
#print axioms wholeSlabConditionalKernel_le_of_raw_ceiling
#print axioms PositiveWholeSlabRawTarget.toJointChannelSelection
#print axioms jointCarrierNonemptyOfRawRowMassPositive
#print axioms rawRowMass_pos_of_jointCarrierNonempty
#print axioms jointCarrierCodes_length_pos_iff_rawRowMass_pos
#print axioms SU2OuterRawRowMassPositive
#print axioms SU2OuterRawRowMassPositive.toJointCarrierNonempty
#print axioms SU2OuterRawRowMassPositive.coherentSource
#print axioms rawRowMassPositiveOfJointCarrierNonempty
#print axioms SU2OuterRawRowMassPositive.toPositiveRowClosure
#print axioms SU2OuterRawRowMassPositive.toFineWitnessRouting

end YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
