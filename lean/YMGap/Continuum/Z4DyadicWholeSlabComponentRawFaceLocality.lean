/-
# Component locality for the whole-slab dyadic raw row

One coarse-face factor in the globally glued recoupling row reads exactly the
four fine plaquettes in that face's dyadic fibre.  A rooted strand-component
peel which selects no strand at those four fine face identifiers therefore
leaves the packet and its complete local raw factor unchanged.

The result is lifted through the finite face product, raw event sums, and
normalization when a component avoids every coarse face in the selected
scope.  The remaining mathematical frontier is now local and explicit:
evaluate the finitely many affected coarse-face factors of a closed component
as one target-independent scalar.  No such bubble evaluation or aggregate
RG estimate is asserted here.

Constructive contract: finite lists, explicit dyadic fibres, and rational
setoid algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
import YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
import YMGap.Continuum.Z4DyadicClosedPairBubble

namespace YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_congr_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSum_congr_local left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem)))

private theorem wholeSlabFiniteQProduct_congr_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      wholeSlabFiniteQProduct left items ≈
        wholeSlabFiniteQProduct right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree =>
      Q'.eqv_trans _
        (right head * wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_local left right tail
            (fun item hitem =>
              hagree item (List.mem_cons_of_mem head hitem))))

private theorem wholeSlabFiniteQProduct_filter_partition_local {A : Type}
    (value : A → Q') (test : A → Bool) : ∀ items : List A,
    wholeSlabFiniteQProduct value items ≈
      wholeSlabFiniteQProduct value (items.filter test) *
        wholeSlabFiniteQProduct value
          (items.filter (fun item => !(test item)))
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | head :: tail => by
      have htail :=
        wholeSlabFiniteQProduct_filter_partition_local value test tail
      cases hhead : test head with
      | false =>
          simp only [wholeSlabFiniteQProduct, List.filter_cons, hhead,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _
            (value head *
              (wholeSlabFiniteQProduct value (tail.filter test) *
                wholeSlabFiniteQProduct value
                  (tail.filter (fun item => !(test item))))) _ ?_ ?_
          · exact Q'.mul_eqv_congr_left (value head) _ _ htail
          · refine Q'.eqv_trans _
              ((value head *
                  wholeSlabFiniteQProduct value (tail.filter test)) *
                wholeSlabFiniteQProduct value
                  (tail.filter (fun item => !(test item)))) _
              (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
            refine Q'.eqv_trans _
              ((wholeSlabFiniteQProduct value (tail.filter test) *
                  value head) *
                wholeSlabFiniteQProduct value
                  (tail.filter (fun item => !(test item)))) _ ?_ ?_
            · exact Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_comm_eqv _ _)
            · exact Q'.mul_assoc_eqv _ _ _
      | true =>
          simp only [wholeSlabFiniteQProduct, List.filter_cons, hhead,
            ↓reduceIte, Bool.not_true, Bool.false_eq_true]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (value head) _ _ htail)
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b')
    (hpositive : (0 : Q') < b) (hpositive' : (0 : Q') < b') :
    Q'.divPos a b hpositive ≈ Q'.divPos a' b' hpositive' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hpositive'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hpositive) b' b
          (Q'.eqv_symm hb))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hpositive) ha))
  · apply Q'.le_divPos_of_mul_le a b hpositive
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hpositive') b b' hb)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hpositive')
          (Q'.eqv_symm ha)))

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_eqv_divPos_of_cross_local
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul_local hq hcancel

/-! ## 1. Locality of the four-spin packet -/

/-- Two fine spin fields which agree on the four explicit dyadic preimages
produce exactly the same packet. -/
theorem dyadicFaceSpinPacket_eq_of_local
    (first second : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq)
    (hlocal : ∀ finePlaquette,
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette →
        first finePlaquette = second finePlaquette) :
    dyadicFaceSpinPacket first coarsePlaquette =
      dyadicFaceSpinPacket second coarsePlaquette := by
  have hslots := dyadicFacePreimage_slots_mem coarsePlaquette
  simp only [dyadicFaceSpinPacket]
  rw [hlocal _ hslots.1,
    hlocal _ hslots.2.1,
    hlocal _ hslots.2.2.1,
    hlocal _ hslots.2.2.2]

/-- Fine face identifiers read by one literal coarse-face packet. -/
def dyadicCoarseFaceFineFaceIds
    (S : SlabScalePair) (coarseFaceId : Nat) : List Nat :=
  (dyadicFacePreimages
      (slabPlaquetteAt S.coarse.extent coarseFaceId)).map
    (slabFaceIdOfPlaquette S.fine.extent)

/-- A rooted strand component is invisible to one coarse-face packet when it
selects zero copies at all four fine preimage identifiers. -/
def componentAvoidsDyadicCoarseFace
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat) : Prop :=
  componentAvoidsFaces seed
    (dyadicCoarseFaceFineFaceIds S coarseFaceId)

/-- Avoidance makes the lowered and source spin fields agree on every fine
plaquette read by the selected coarse packet. -/
theorem lowerSlabSpinAtPlaquette_eq_of_componentAvoidsDyadicCoarseFace
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : componentAvoidsDyadicCoarseFace seed coarseFaceId)
    (finePlaquette : Z4Plaq)
    (hpreimage : finePlaquette ∈ dyadicFacePreimages
      (slabPlaquetteAt S.coarse.extent coarseFaceId)) :
    slabSpinAtPlaquette S.fine.extent
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
        finePlaquette =
      slabSpinAtPlaquette S.fine.extent physical finePlaquette := by
  have hcoarsePlaquette :
      slabPlaquetteAt S.coarse.extent coarseFaceId ∈
        boundaryCompleteSlabPlaquettes S.coarse.extent :=
    slabPlaquetteAt_mem hcoarse
  have hfineDyadic := dyadicFacePreimage_mem_boundaryCompleteFineSlab
    hcoarsePlaquette hpreimage
  have hfine : finePlaquette ∈
      boundaryCompleteSlabPlaquettes S.fine.extent := by
    rw [S.fine_extent]
    exact hfineDyadic
  have hfaceId : slabFaceIdOfPlaquette S.fine.extent finePlaquette ∈
      dyadicCoarseFaceFineFaceIds S coarseFaceId := by
    unfold dyadicCoarseFaceFineFaceIds
    exact List.mem_map.mpr ⟨finePlaquette, hpreimage, rfl⟩
  have hagree :=
    (componentAvoidsFaces_iff_lowerPhysical_agrees seed
      (dyadicCoarseFaceFineFaceIds S coarseFaceId)).mp havoid
      (slabFaceIdOfPlaquette S.fine.extent finePlaquette) hfaceId
  rw [slabSpinAtPlaquette_eq_of_mem hfine,
    slabSpinAtPlaquette_eq_of_mem hfine]
  simpa only [slabFaceIdOfPlaquette] using hagree

/-- Component avoidance is exactly enough to preserve the whole local
four-spin packet. -/
theorem wholeSlabFinePacket_lowerPhysical_eq_of_componentAvoids
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : componentAvoidsDyadicCoarseFace seed coarseFaceId) :
    wholeSlabFinePacket S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
        coarseFaceId =
      wholeSlabFinePacket S physical coarseFaceId := by
  unfold wholeSlabFinePacket
  apply dyadicFaceSpinPacket_eq_of_local
  intro finePlaquette hpreimage
  exact lowerSlabSpinAtPlaquette_eq_of_componentAvoidsDyadicCoarseFace
    seed coarseFaceId hcoarse havoid finePlaquette hpreimage

/-! ## 2. Locality of the actual raw face factor -/

/-- Every coarse target label receives the same local raw face factor after
peeling a component invisible to that coarse face. -/
theorem wholeSlabFaceRawWeight_lowerPhysical_eqv_of_componentAvoids
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseState : EdgeLabelling) (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : componentAvoidsDyadicCoarseFace seed coarseFaceId) :
    wholeSlabFaceRawWeight S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
        coarseState coarseFaceId ≈
      wholeSlabFaceRawWeight S physical coarseState coarseFaceId := by
  unfold wholeSlabFaceRawWeight
  rw [wholeSlabFinePacket_lowerPhysical_eq_of_componentAvoids
    seed coarseFaceId hcoarse havoid]
  exact Q'.eqv_refl _

/-! ## 3. The finite carrier of touched coarse faces -/

/-- Decidable test that the component selects at least one strand among the
four fine faces read by a coarse-face packet. -/
def componentTouchesDyadicCoarseFaceB
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat) : Bool :=
  (dyadicCoarseFaceFineFaceIds S coarseFaceId).any
    (fun fineFaceId =>
      decide (0 < slabFaceStrandSelectionCount seed.selected fineFaceId))

/-- The Boolean touch test is false exactly when the component is invisible
to the four-face packet. -/
theorem componentTouchesDyadicCoarseFaceB_eq_false_iff
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat) :
    componentTouchesDyadicCoarseFaceB seed coarseFaceId = false ↔
      componentAvoidsDyadicCoarseFace seed coarseFaceId := by
  unfold componentTouchesDyadicCoarseFaceB
    componentAvoidsDyadicCoarseFace componentAvoidsFaces
  constructor
  · intro hfalse fineFaceId hfine
    have hterm := List.any_eq_false.mp hfalse fineFaceId hfine
    have hnotPositive :
        ¬ 0 < slabFaceStrandSelectionCount seed.selected fineFaceId := by
      intro hpositive
      exact hterm (decide_eq_true hpositive)
    omega
  · intro havoid
    apply List.any_eq_false.mpr
    intro fineFaceId hfine
    intro hdecision
    have hpositive := of_decide_eq_true hdecision
    rw [havoid fineFaceId hfine] at hpositive
    omega

/-- Literal finite carrier of coarse faces whose four-face packets are touched
by the component. -/
def componentTouchedDyadicCoarseFaceIds
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment) : List Nat :=
  S.coarse.faceEdges.filter (componentTouchesDyadicCoarseFaceB seed)

/-- Complementary finite carrier of coarse faces untouched by the component. -/
def componentUntouchedDyadicCoarseFaceIds
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment) : List Nat :=
  S.coarse.faceEdges.filter
    (fun coarseFaceId => !(componentTouchesDyadicCoarseFaceB seed coarseFaceId))

theorem componentAvoidsDyadicCoarseFace_of_mem_untouched
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseFaceId : Nat)
    (hmem : coarseFaceId ∈ componentUntouchedDyadicCoarseFaceIds seed) :
    componentAvoidsDyadicCoarseFace seed coarseFaceId := by
  have hparts := List.mem_filter.mp hmem
  have hfalse :
      componentTouchesDyadicCoarseFaceB seed coarseFaceId = false := by
    cases htest : componentTouchesDyadicCoarseFaceB seed coarseFaceId with
    | false => rfl
    | true =>
        have hcontra : false = true := by
          simpa only [htest, Bool.not_true] using hparts.2
        exact Bool.noConfusion hcontra
  exact (componentTouchesDyadicCoarseFaceB_eq_false_iff
    seed coarseFaceId).mp hfalse

/-- Product of precisely the local raw factors touched by the component. -/
def wholeSlabComponentTouchedFaceRawProduct
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (fineState coarseState : EdgeLabelling) : Q' :=
  wholeSlabFiniteQProduct
    (wholeSlabFaceRawWeight S fineState coarseState)
    (componentTouchedDyadicCoarseFaceIds seed)

/-- Product of the complementary local raw factors untouched by the
component. -/
def wholeSlabComponentUntouchedFaceRawProduct
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (fineState coarseState : EdgeLabelling) : Q' :=
  wholeSlabFiniteQProduct
    (wholeSlabFaceRawWeight S fineState coarseState)
    (componentUntouchedDyadicCoarseFaceIds seed)

/-- The complete face product factors into the finite touched carrier and its
untouched complement. -/
theorem wholeSlabFaceRawProduct_eqv_componentTouched_mul_untouched
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (fineState coarseState : EdgeLabelling) :
    wholeSlabFaceRawProduct S fineState coarseState ≈
      wholeSlabComponentTouchedFaceRawProduct seed fineState coarseState *
        wholeSlabComponentUntouchedFaceRawProduct
          seed fineState coarseState := by
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight S fineState coarseState)
      S.coarse.faceEdges) _
    (wholeSlabFaceRawProduct_eqv_finiteQProduct S fineState coarseState) ?_
  exact wholeSlabFiniteQProduct_filter_partition_local
    (wholeSlabFaceRawWeight S fineState coarseState)
    (componentTouchesDyadicCoarseFaceB seed)
    S.coarse.faceEdges

/-- The entire untouched factor is identical before and after the component
peel. -/
theorem wholeSlabComponentUntouchedFaceRawProduct_lowerPhysical_eqv
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseState : EdgeLabelling) :
    wholeSlabComponentUntouchedFaceRawProduct seed
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
      wholeSlabComponentUntouchedFaceRawProduct
        seed physical coarseState := by
  unfold wholeSlabComponentUntouchedFaceRawProduct
  exact wholeSlabFiniteQProduct_congr_local _ _ _
    (fun coarseFaceId hmem =>
      wholeSlabFaceRawWeight_lowerPhysical_eqv_of_componentAvoids
        seed coarseState coarseFaceId
        (List.mem_filter.mp hmem).1
        (componentAvoidsDyadicCoarseFace_of_mem_untouched
          seed coarseFaceId hmem))

/-! ## 4. Lift locality through the complete raw row -/

/-- A component avoids every coarse-face packet in the globally glued row. -/
def componentAvoidsAllDyadicCoarseFaces
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment) : Prop :=
  ∀ coarseFaceId, coarseFaceId ∈ S.coarse.faceEdges →
    componentAvoidsDyadicCoarseFace seed coarseFaceId

/-- If all coarse-face packets are avoided, their complete finite product is
unchanged for every globally glued coarse target. -/
theorem wholeSlabFaceRawProduct_lowerPhysical_eqv_of_componentAvoidsAll
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseState : EdgeLabelling)
    (havoid : componentAvoidsAllDyadicCoarseFaces seed) :
    wholeSlabFaceRawProduct S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
      wholeSlabFaceRawProduct S physical coarseState := by
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState)
      S.coarse.faceEdges) _
    (wholeSlabFaceRawProduct_eqv_finiteQProduct S _ _) ?_
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight S physical coarseState)
      S.coarse.faceEdges) _ ?_ ?_
  · exact wholeSlabFiniteQProduct_congr_local _ _ _
      (fun coarseFaceId hcoarse =>
        wholeSlabFaceRawWeight_lowerPhysical_eqv_of_componentAvoids
          seed coarseState coarseFaceId hcoarse
          (havoid coarseFaceId hcoarse))
  · exact Q'.eqv_symm
      (wholeSlabFaceRawProduct_eqv_finiteQProduct S _ _)

/-- The complete globally link-glued raw row is unchanged: its coarse-link
multiplicity depends only on the target and is common to the two rows. -/
theorem wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_componentAvoidsAll
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (coarseState : EdgeLabelling)
    (havoid : componentAvoidsAllDyadicCoarseFaces seed) :
    wholeSlabRecouplingRawWeight S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
      wholeSlabRecouplingRawWeight S physical coarseState := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.mul_eqv_congr_right _ _ _
    (wholeSlabFaceRawProduct_lowerPhysical_eqv_of_componentAvoidsAll
      seed coarseState havoid)

/-- Raw mass of an arbitrary Boolean coarse event before row normalization. -/
def wholeSlabRawEventMass
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum (wholeSlabRecouplingRawWeight S fineState)
    (S.coarse.physicalLabellings.filter event)

/-- Complete raw row mass, without packaging a positive witness. -/
def wholeSlabRawRowMass
    (S : SlabScalePair) (fineState : EdgeLabelling) : Q' :=
  listQSum (wholeSlabRecouplingRawWeight S fineState)
    S.coarse.physicalLabellings

theorem wholeSlabRawEventMass_lowerPhysical_eqv_of_componentAvoidsAll
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (event : EdgeLabelling → Bool)
    (havoid : componentAvoidsAllDyadicCoarseFaces seed) :
    wholeSlabRawEventMass S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) event ≈
      wholeSlabRawEventMass S physical event := by
  unfold wholeSlabRawEventMass
  exact listQSum_congr_local _ _ _
    (fun coarseState _ =>
      wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_componentAvoidsAll
        seed coarseState havoid)

theorem wholeSlabRawRowMass_lowerPhysical_eqv_of_componentAvoidsAll
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (havoid : componentAvoidsAllDyadicCoarseFaces seed) :
    wholeSlabRawRowMass S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) ≈
      wholeSlabRawRowMass S physical := by
  unfold wholeSlabRawRowMass
  exact listQSum_congr_local _ _ _
    (fun coarseState _ =>
      wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_componentAvoidsAll
        seed coarseState havoid)

/-- Normalized event responses are identical once the complete raw row is
invisible to the component peel. -/
theorem wholeSlabRawEventRatio_lowerPhysical_eqv_of_componentAvoidsAll
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (event : EdgeLabelling → Bool)
    (havoid : componentAvoidsAllDyadicCoarseFaces seed)
    (hlowerPositive : (0 : Q') < wholeSlabRawRowMass S
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed))
    (hsourcePositive : (0 : Q') < wholeSlabRawRowMass S physical) :
    Q'.divPos
        (wholeSlabRawEventMass S
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) event)
        (wholeSlabRawRowMass S
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed))
        hlowerPositive ≈
      Q'.divPos (wholeSlabRawEventMass S physical event)
        (wholeSlabRawRowMass S physical) hsourcePositive := by
  exact divPos_eqv_congr_local
    (wholeSlabRawEventMass_lowerPhysical_eqv_of_componentAvoidsAll
      seed event havoid)
    (wholeSlabRawRowMass_lowerPhysical_eqv_of_componentAvoidsAll
      seed havoid)
    hlowerPositive hsourcePositive

/-! ## 5. Compiler from one touched-bubble scalar to normalized cancellation -/

/-- If the finite touched-face product changes by one target-independent
scalar, then the complete face product changes by that same scalar.  The
untouched factors have already been proved identical. -/
theorem wholeSlabFaceRawProduct_lowerPhysical_eqv_of_touchedScalar
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (bubble : Q')
    (hbubble : ∀ coarseState : EdgeLabelling,
      wholeSlabComponentTouchedFaceRawProduct seed
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
        bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState)
    (coarseState : EdgeLabelling) :
    wholeSlabFaceRawProduct S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
      bubble * wholeSlabFaceRawProduct S physical coarseState := by
  refine Q'.eqv_trans _
    (wholeSlabComponentTouchedFaceRawProduct seed
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState *
      wholeSlabComponentUntouchedFaceRawProduct seed
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState) _
    (wholeSlabFaceRawProduct_eqv_componentTouched_mul_untouched
      seed _ coarseState) ?_
  refine Q'.eqv_trans _
    ((bubble * wholeSlabComponentTouchedFaceRawProduct
        seed physical coarseState) *
      wholeSlabComponentUntouchedFaceRawProduct seed
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (hbubble coarseState)
  · refine Q'.eqv_trans _
      ((bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState) *
        wholeSlabComponentUntouchedFaceRawProduct
          seed physical coarseState) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (wholeSlabComponentUntouchedFaceRawProduct_lowerPhysical_eqv
          seed coarseState)
    · refine Q'.eqv_trans _
        (bubble *
          (wholeSlabComponentTouchedFaceRawProduct seed physical coarseState *
            wholeSlabComponentUntouchedFaceRawProduct
              seed physical coarseState)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left bubble _ _
        (Q'.eqv_symm
          (wholeSlabFaceRawProduct_eqv_componentTouched_mul_untouched
            seed physical coarseState))

/-- The target-link multiplicity is common to both rows, so the same scalar
relation lifts from the face product to the globally glued raw kernel. -/
theorem wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_touchedScalar
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (bubble : Q')
    (hbubble : ∀ coarseState : EdgeLabelling,
      wholeSlabComponentTouchedFaceRawProduct seed
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
        bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState)
    (coarseState : EdgeLabelling) :
    wholeSlabRecouplingRawWeight S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
      bubble * wholeSlabRecouplingRawWeight S physical coarseState := by
  unfold wholeSlabRecouplingRawWeight
  refine Q'.eqv_trans _
    ((bubble * wholeSlabFaceRawProduct S physical coarseState) *
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct
          S.coarse.cutoff S.coarse.extent coarseState)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (wholeSlabFaceRawProduct_lowerPhysical_eqv_of_touchedScalar
        seed bubble hbubble coarseState)
  · exact Q'.mul_assoc_eqv _ _ _

theorem wholeSlabRawEventMass_lowerPhysical_eqv_of_touchedScalar
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (bubble : Q')
    (hbubble : ∀ coarseState : EdgeLabelling,
      wholeSlabComponentTouchedFaceRawProduct seed
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
        bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState)
    (event : EdgeLabelling → Bool) :
    wholeSlabRawEventMass S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) event ≈
      bubble * wholeSlabRawEventMass S physical event := by
  unfold wholeSlabRawEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        bubble * wholeSlabRecouplingRawWeight S physical coarseState)
      (S.coarse.physicalLabellings.filter event)) _ ?_ ?_
  · exact listQSum_congr_local _ _ _
      (fun coarseState _ =>
        wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_touchedScalar
          seed bubble hbubble coarseState)
  · exact listQSum_mul_left bubble _ _

theorem wholeSlabRawRowMass_lowerPhysical_eqv_of_touchedScalar
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (bubble : Q')
    (hbubble : ∀ coarseState : EdgeLabelling,
      wholeSlabComponentTouchedFaceRawProduct seed
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
        bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState) :
    wholeSlabRawRowMass S
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) ≈
      bubble * wholeSlabRawRowMass S physical := by
  unfold wholeSlabRawRowMass
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        bubble * wholeSlabRecouplingRawWeight S physical coarseState)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_local _ _ _
      (fun coarseState _ =>
        wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_touchedScalar
          seed bubble hbubble coarseState)
  · exact listQSum_mul_left bubble _ _

/-- The target-independent scalar cancels exactly between every raw event mass
and the complete raw row mass.  This is the normalization compiler consumed by
the still-open touched closed-bubble evaluation. -/
theorem wholeSlabRawEventRatio_lowerPhysical_eqv_of_touchedScalar
    {S : SlabScalePair} {physical : EdgeLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈ slabFusionWitnessAssignmentsOn
      S.fine.cutoff S.fine.extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed S.fine.cutoff S.fine.extent
      physical links assignment hassignment)
    (bubble : Q')
    (hbubble : ∀ coarseState : EdgeLabelling,
      wholeSlabComponentTouchedFaceRawProduct seed
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) coarseState ≈
        bubble * wholeSlabComponentTouchedFaceRawProduct
          seed physical coarseState)
    (event : EdgeLabelling → Bool)
    (hlowerPositive : (0 : Q') < wholeSlabRawRowMass S
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed))
    (hsourcePositive : (0 : Q') < wholeSlabRawRowMass S physical) :
    Q'.divPos
        (wholeSlabRawEventMass S
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) event)
        (wholeSlabRawRowMass S
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed))
        hlowerPositive ≈
      Q'.divPos (wholeSlabRawEventMass S physical event)
        (wholeSlabRawRowMass S physical) hsourcePositive := by
  apply divPos_eqv_divPos_of_cross_local hlowerPositive hsourcePositive
  refine Q'.eqv_trans _
    ((bubble * wholeSlabRawEventMass S physical event) *
      wholeSlabRawRowMass S physical) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (wholeSlabRawEventMass_lowerPhysical_eqv_of_touchedScalar
        seed bubble hbubble event)
  · refine Q'.eqv_trans _
      ((wholeSlabRawEventMass S physical event * bubble) *
        wholeSlabRawRowMass S physical) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
    · refine Q'.eqv_trans _
        (wholeSlabRawEventMass S physical event *
          (bubble * wholeSlabRawRowMass S physical)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (wholeSlabRawRowMass_lowerPhysical_eqv_of_touchedScalar
            seed bubble hbubble))

#print axioms dyadicFaceSpinPacket_eq_of_local
#print axioms lowerSlabSpinAtPlaquette_eq_of_componentAvoidsDyadicCoarseFace
#print axioms wholeSlabFinePacket_lowerPhysical_eq_of_componentAvoids
#print axioms wholeSlabFaceRawWeight_lowerPhysical_eqv_of_componentAvoids
#print axioms componentTouchesDyadicCoarseFaceB_eq_false_iff
#print axioms wholeSlabFaceRawProduct_eqv_componentTouched_mul_untouched
#print axioms wholeSlabComponentUntouchedFaceRawProduct_lowerPhysical_eqv
#print axioms wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_componentAvoidsAll
#print axioms wholeSlabRawEventRatio_lowerPhysical_eqv_of_componentAvoidsAll
#print axioms wholeSlabRecouplingRawWeight_lowerPhysical_eqv_of_touchedScalar
#print axioms wholeSlabRawEventRatio_lowerPhysical_eqv_of_touchedScalar

end YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
