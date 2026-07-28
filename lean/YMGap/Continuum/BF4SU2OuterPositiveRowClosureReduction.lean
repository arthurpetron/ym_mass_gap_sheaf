/-
# Joint-channel reduction of the SU(2) outer positive-row closure

The whole-slab raw recoupling weight is not signed: every fixed-final face
sum is nonnegative, the face product is nonnegative, and the coarse link
multiplicity is a natural number.  Its possible zeros therefore come from
fusion incompatibility, never cancellation.

For every bounded fine labelling this module constructs one canonical coarse
labelling.  On each coarse face it uses the stretched (highest-spin) channel:
the final label is the sum of the four fine twice-spins in that dyadic face
fibre.  The lossless coarse cutoff `4 * K` contains this label.  The stretched
channel has strictly positive local character/fusion weight, so every face
factor, and hence the complete face product, is strictly positive.

The canonical target is a diagnostic, not the solution: the pinned
single-cube counterexample in `notes/all-cutoff-coherence-counterexample.md`
has positive fine link multiplicities but makes this independently stretched
coarse target link-inadmissible.  This module therefore records the stretched
construction as an exact fence and then isolates the viable residual datum:
one *joint* choice of the coarse labelling, a positive face channel at every
coarse face, and a positive intertwiner multiplicity at every shared coarse
link.  That joint channel/intertwiner selection constructively yields the
original positive-row closure.

## Axiom gate

Finite exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier

namespace YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Uniform fine-face bounds -/

/-- A bounded whole-slab labelling remains bounded after it is read as a
geometric plaquette field and extended by zero outside the slab. -/
theorem slabSpinAtPlaquette_le_cutoff
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (plaquette : Z4Plaq) :
    slabSpinAtPlaquette S.fine.extent fineState plaquette ≤
      S.fine.cutoff := by
  by_cases hslab :
      plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hidLt :=
      listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes S.fine.extent) hslab
    have hidMem : listIndexOf plaquette
        (boundaryCompleteSlabPlaquettes S.fine.extent) ∈
          S.fine.faceEdges := by
      unfold SlabPhysicalData.faceEdges slabPhysicalFaceEdges
      exact List.mem_range.mpr hidLt
    have hbound :=
      (boundedEdgeLabellings_sound
        S.fine.cutoff S.fine.faceEdges fineState hfineMem).1
        (listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes S.fine.extent))
        hidMem
    omega
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    omega

theorem wholeSlabFinePacket_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (coarseFaceId : Nat) :
    wholeSlabFinePacket S fineState coarseFaceId ∈
      faceSpinPacketStateSpace S.fine.cutoff := by
  exact dyadicFaceSpinPacket_mem_stateSpace
    S.fine.cutoff
    (slabSpinAtPlaquette S.fine.extent fineState)
    (slabSpinAtPlaquette_le_cutoff hfineMem)
    (slabPlaquetteAt S.coarse.extent coarseFaceId)

/-! ## 2. The canonical stretched coarse labelling -/

def stretchedPacketFinal (packet : FaceSpinPacket) : Nat :=
  packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3

def wholeSlabStretchedTarget
    (S : SlabScalePair) (fineState : EdgeLabelling) : EdgeLabelling :=
  fun coarseFaceId =>
    if coarseFaceId ∈ S.coarse.faceEdges then
      stretchedPacketFinal
        (wholeSlabFinePacket S fineState coarseFaceId)
    else 0

theorem wholeSlabStretchedTarget_eq_of_mem
    (S : SlabScalePair) (fineState : EdgeLabelling)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    wholeSlabStretchedTarget S fineState coarseFaceId =
      stretchedPacketFinal
        (wholeSlabFinePacket S fineState coarseFaceId) := by
  unfold wholeSlabStretchedTarget
  rw [if_pos hface]

theorem wholeSlabStretchedTarget_eq_zero_of_not_mem
    (S : SlabScalePair) (fineState : EdgeLabelling)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∉ S.coarse.faceEdges) :
    wholeSlabStretchedTarget S fineState coarseFaceId = 0 := by
  unfold wholeSlabStretchedTarget
  rw [if_neg hface]

theorem wholeSlabStretchedTarget_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    wholeSlabStretchedTarget S fineState ∈
      S.coarse.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro coarseFaceId hface
    rw [wholeSlabStretchedTarget_eq_of_mem S fineState hface]
    have hchannel :=
      stretchedPairChannel_mem S.fine.cutoff
        (wholeSlabFinePacket S fineState coarseFaceId)
        (wholeSlabFinePacket_mem hfineMem coarseFaceId)
    have hfinal :=
      (mem_pairChannelStateSpace_iff S.fine.cutoff _).mp hchannel
    unfold stretchedPacketFinal
    rw [S.coarse_cutoff]
    omega
  · intro coarseFaceId hface
    exact wholeSlabStretchedTarget_eq_zero_of_not_mem
      S fineState hface

/-! ## 3. Strict positivity of every stretched face -/

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

theorem wholeSlabStretchedTarget_faceRawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    (0 : Q') <
      wholeSlabFaceRawWeight S fineState
        (wholeSlabStretchedTarget S fineState) coarseFaceId := by
  let packet := wholeSlabFinePacket S fineState coarseFaceId
  let channel : PairChannelState :=
    ((packet.spin0 + packet.spin1, packet.spin2 + packet.spin3),
      stretchedPacketFinal packet)
  have hchannelMem :
      channel ∈ pairChannelStateSpace S.fine.cutoff := by
    exact stretchedPairChannel_mem S.fine.cutoff packet
      (wholeSlabFinePacket_mem hfineMem coarseFaceId)
  have hfinal :
      channel.2 =
        wholeSlabStretchedTarget S fineState coarseFaceId := by
    rw [wholeSlabStretchedTarget_eq_of_mem S fineState hface]
  have hselected :
      (0 : Q') <
        (if channel.2 =
              wholeSlabStretchedTarget S fineState coarseFaceId then
            packetPairChannelRawWeight S.coarse.coupling packet channel
          else 0) := by
    rw [if_pos hfinal]
    exact stretchedPairChannelRawWeight_pos hcoarseCoupling packet
  have hle :
      (if channel.2 =
            wholeSlabStretchedTarget S fineState coarseFaceId then
          packetPairChannelRawWeight S.coarse.coupling packet channel
        else 0) ≤
        wholeSlabFaceRawWeight S fineState
          (wholeSlabStretchedTarget S fineState) coarseFaceId := by
    unfold wholeSlabFaceRawWeight
    apply listQSum_member_le_local
    · intro state
      by_cases hstate :
          state.2 =
            wholeSlabStretchedTarget S fineState coarseFaceId
      · rw [if_pos hstate]
        exact packetPairChannelRawWeight_nonnegative
          S.coarse.coupling_nonnegative _ _
      · rw [if_neg hstate]
        exact Q'.le_refl' 0
    · exact hchannelMem
  exact Q'.pos_of_lt_of_le hselected hle

theorem wholeSlabStretchedTarget_faceProduct_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    (0 : Q') <
      wholeSlabFaceRawProduct S fineState
        (wholeSlabStretchedTarget S fineState) := by
  apply wholeSlabFaceRawProduct_pos_of_pointwise
  intro coarseFaceId hface
  exact wholeSlabStretchedTarget_faceRawWeight_pos
    hfineMem hcoarseCoupling hface

private theorem ofNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

theorem wholeSlabStretchedTarget_rawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hlink :
      0 < slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent
        (wholeSlabStretchedTarget S fineState)) :
    (0 : Q') <
      wholeSlabRecouplingRawWeight S fineState
        (wholeSlabStretchedTarget S fineState) := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.mul_pos
    (wholeSlabStretchedTarget_faceProduct_pos
      hfineMem hcoarseCoupling)
    (ofNat_pos_of_pos_local hlink)

/-! ## 4. Exact closed counterexample to independent stretched coherence -/

/-- The six doubled-spin-one faces of the pinned fine unit-cube boundary
from `notes/all-cutoff-coherence-counterexample.md`. -/
def stretchedFenceFineSupport : List Z4Plaq :=
  [((0, 0, 1, 1), .p02), ((0, 0, 1, 2), .p02),
   ((0, 0, 1, 1), .p03), ((0, 0, 2, 1), .p03),
   ((0, 0, 1, 1), .p23), ((1, 0, 1, 1), .p23)]

def stretchedFenceFineState : EdgeLabelling :=
  slabBinarySupportLabelling 3 stretchedFenceFineSupport

def stretchedFenceGeometry :
    YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry :=
  ⟨0⟩

theorem stretchedFence_one_nonnegative : (0 : Q') ≤ 1 := by
  decide

theorem stretchedFence_one_positive : (0 : Q') < 1 := by
  decide

/-- Ambient cutoff two makes the cutoff-one-valued fine counterexample a
literal instance of the still-open `K ≥ 2` sector. -/
def stretchedFenceScalePair : SlabScalePair :=
  su2OuterScalePair stretchedFenceGeometry
    1 stretchedFence_one_nonnegative
    1 stretchedFence_one_positive 2

def stretchedFenceBadCoarseLink : Z4Link :=
  ((0, 0, 0, 0), .x2)

/-- Kernel-checked global obstruction.  The fine cube boundary stretches to
one isolated coarse `p23` face of label two, so this displayed boundary link
has no invariant tensor. -/
theorem stretchedFence_badCoarseLink_multiplicity_zero :
    slabExplicitLinkMultiplicity
        stretchedFenceScalePair.coarse.cutoff
        stretchedFenceScalePair.coarse.extent
        (wholeSlabStretchedTarget
          stretchedFenceScalePair stretchedFenceFineState)
        stretchedFenceBadCoarseLink = 0 := by
  decide

theorem stretchedFenceFineState_mem :
    stretchedFenceFineState ∈
      stretchedFenceScalePair.fine.physicalLabellings := by
  exact slabBinarySupportLabelling_mem
    (K := 2) (extent := 3) (by omega) stretchedFenceFineSupport

private theorem natListProduct_eq_zero_of_member {A : Type}
    (value : A → Nat) :
    ∀ (xs : List A) {x : A},
      x ∈ xs → value x = 0 →
      natListProduct value xs = 0
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem, hzero => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp [natListProduct, hzero]
      · rw [natListProduct]
        rw [natListProduct_eq_zero_of_member value tail htail hzero]
        omega

theorem stretchedFence_stretchedTarget_linkProduct_zero :
    slabExplicitLinkMultiplicityProduct
        stretchedFenceScalePair.coarse.cutoff
        stretchedFenceScalePair.coarse.extent
        (wholeSlabStretchedTarget
          stretchedFenceScalePair stretchedFenceFineState) = 0 := by
  unfold slabExplicitLinkMultiplicityProduct
  apply natListProduct_eq_zero_of_member
    (slabExplicitLinkMultiplicity
      stretchedFenceScalePair.coarse.cutoff
      stretchedFenceScalePair.coarse.extent
      (wholeSlabStretchedTarget
        stretchedFenceScalePair stretchedFenceFineState))
    (boundaryCompleteSlabLinks stretchedFenceScalePair.coarse.extent)
    (x := stretchedFenceBadCoarseLink)
  · decide
  · exact stretchedFence_badCoarseLink_multiplicity_zero

/-! ## 5. Cutoff zero is already closed -/

theorem wholeSlabStretchedTarget_eq_zero_of_fine_cutoff_zero
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 0)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (coarseFaceId : Nat) :
    wholeSlabStretchedTarget S fineState coarseFaceId = 0 := by
  by_cases hface : coarseFaceId ∈ S.coarse.faceEdges
  · have htargetMem :=
      wholeSlabStretchedTarget_mem hfineMem
    have hbound :=
      (boundedEdgeLabellings_sound
        S.coarse.cutoff S.coarse.faceEdges
        (wholeSlabStretchedTarget S fineState) htargetMem).1
        coarseFaceId hface
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    omega
  · exact wholeSlabStretchedTarget_eq_zero_of_not_mem
      S fineState hface

private theorem listMap_eq_of_pointwise {A B : Type}
    (left right : A → B) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → left x = right x) →
      xs.map left = xs.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self]
      rw [listMap_eq_of_pointwise left right tail
        (fun x hmem =>
          hagree x (List.mem_cons_of_mem head hmem))]

theorem wholeSlabStretchedTarget_linkMultiplicity_eq_one_of_fine_cutoff_zero
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 0)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (link : Z4Link) :
    slabExplicitLinkMultiplicity
        S.coarse.cutoff S.coarse.extent
        (wholeSlabStretchedTarget S fineState) link = 1 := by
  have hmap :
      (slabIncidentPlaqIds S.coarse.extent link).map
          (wholeSlabStretchedTarget S fineState) =
        (slabIncidentPlaqIds S.coarse.extent link).map
          zeroEdgeLabelling := by
    apply listMap_eq_of_pointwise
    intro coarseFaceId _
    exact wholeSlabStretchedTarget_eq_zero_of_fine_cutoff_zero
      hfineCutoff hfineMem coarseFaceId
  unfold slabExplicitLinkMultiplicity
  rw [hmap]
  exact slabExplicitLinkMultiplicity_zero_eq_one
    S.coarse.cutoff S.coarse.extent link

theorem wholeSlabStretchedTarget_linkProduct_eq_one_of_fine_cutoff_zero
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 0)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent
        (wholeSlabStretchedTarget S fineState) = 1 := by
  unfold slabExplicitLinkMultiplicityProduct
  generalize boundaryCompleteSlabLinks S.coarse.extent = links
  induction links with
  | nil => rfl
  | cons head tail ih =>
      simp only [natListProduct]
      rw [
        wholeSlabStretchedTarget_linkMultiplicity_eq_one_of_fine_cutoff_zero
          hfineCutoff hfineMem head,
        ih]

/-! ## 6. Positive fine mass exposes pointwise fine-link admissibility -/

private theorem positive_not_eqv_zero {a : Q'}
    (ha : (0 : Q') < a) : ¬ a ≈ 0 := by
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) ha

theorem fineLinkProduct_ne_zero_of_physicalTerm_pos
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical) :
    slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent physical ≠ 0 := by
  intro hzero
  have htermZero : D.physicalTerm physical ≈ 0 := by
    unfold SlabPhysicalData.physicalTerm
      slabParametricKPhysicalTerm
    rw [hzero]
    exact Q'.mul_zero_eqv _
  exact (positive_not_eqv_zero hpositive) htermZero

private theorem natListProduct_factor_ne_zero {A : Type}
    (value : A → Nat) :
    ∀ xs : List A,
      natListProduct value xs ≠ 0 →
      ∀ x, x ∈ xs → value x ≠ 0
  | [], _, x, hmem => absurd hmem List.not_mem_nil
  | head :: tail, hproduct, x, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · intro hzero
        apply hproduct
        simp [natListProduct, hzero]
      · have htailProduct :
            natListProduct value tail ≠ 0 := by
          intro hzero
          apply hproduct
          simp [natListProduct, hzero]
        exact natListProduct_factor_ne_zero
          value tail htailProduct x htail

theorem fineLinkMultiplicity_pos_of_physicalTerm_pos
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical)
    (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks D.extent) :
    0 < slabExplicitLinkMultiplicity
      D.cutoff D.extent physical link := by
  have hproduct :
      natListProduct
          (slabExplicitLinkMultiplicity
            D.cutoff D.extent physical)
          (boundaryCompleteSlabLinks D.extent) ≠ 0 := by
    exact fineLinkProduct_ne_zero_of_physicalTerm_pos
      D physical hpositive
  have hfactor :=
    natListProduct_factor_ne_zero
      (slabExplicitLinkMultiplicity
        D.cutoff D.extent physical)
      (boundaryCompleteSlabLinks D.extent)
      hproduct link hlink
  omega

private theorem natListProduct_pos_on {A : Type}
    (value : A → Nat) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → 0 < value x) →
      0 < natListProduct value xs
  | [], _ => by
      change 0 < 1
      omega
  | head :: tail, hvalue => by
      simp only [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_on value tail
          (fun x hmem =>
            hvalue x (List.mem_cons_of_mem head hmem)))

/-! ## 7. The independently stretched route is an exact fence -/

/-- A sufficient stretched-link condition.  It is intentionally retained as
a diagnostic interface: the independent-face counterexample shows that this
condition is false for the intended all-source geometry, even though all the
local face theorems above are true. -/
structure SU2OuterStretchedLinkClosure
    (G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  linkProduct_positive :
    ∀ K source,
      2 ≤ K →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
      0 < slabExplicitLinkMultiplicityProduct
        (su2OuterScalePair
          G g hg candidate hcandidate K).coarse.cutoff
        (su2OuterScalePair
          G g hg candidate hcandidate K).coarse.extent
        (wholeSlabStretchedTarget
          (su2OuterScalePair
            G g hg candidate hcandidate K) source)

/-- If the falsified stretched-link condition were available, it would imply
the genuine raw-weight positive-row closure.  This theorem identifies the
failure exactly at the shared-link factor. -/
def SU2OuterStretchedLinkClosure.toPositiveRowClosure
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterStretchedLinkClosure
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate where
  coarseWitness := fun K source _ _ _ =>
    wholeSlabStretchedTarget
      (su2OuterScalePair
        G g hg candidate hcandidate K) source
  coarseWitness_mem := by
    intro K source hK hsource hpositive
    exact wholeSlabStretchedTarget_mem hsource
  coarseWitness_positive := by
    intro K source hK hsource hpositive
    have hlink :
        0 < slabExplicitLinkMultiplicityProduct
          (su2OuterScalePair
            G g hg candidate hcandidate K).coarse.cutoff
          (su2OuterScalePair
            G g hg candidate hcandidate K).coarse.extent
          (wholeSlabStretchedTarget
            (su2OuterScalePair
              G g hg candidate hcandidate K) source) := by
      by_cases hKzero : K = 0
      · subst K
        rw [
          wholeSlabStretchedTarget_linkProduct_eq_one_of_fine_cutoff_zero
            rfl hsource]
        omega
      · exact closure.linkProduct_positive
          K source (by omega) hsource hpositive
    exact wholeSlabStretchedTarget_rawWeight_pos
      hsource hcandidate
      hlink

/-! ## 8. Viable joint face-channel/intertwiner selection -/

/-- Constructive data for one genuinely coherent whole-slab row.

Unlike the stretched candidate, the target and all face channels are chosen
jointly.  The same target is read by every face and every coarse link.
Pointwise positive coarse-link multiplicities are carried as data, so no
global nonvanishing is hidden in a scalar product hypothesis. -/
structure WholeSlabJointChannelSelection
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  coarseTarget : EdgeLabelling
  coarseTarget_mem :
    coarseTarget ∈ S.coarse.physicalLabellings
  faceChannel : Nat → PairChannelState
  faceChannel_mem :
    ∀ coarseFaceId,
      coarseFaceId ∈ S.coarse.faceEdges →
      faceChannel coarseFaceId ∈
        pairChannelStateSpace S.fine.cutoff
  faceChannel_final :
    ∀ coarseFaceId,
      coarseFaceId ∈ S.coarse.faceEdges →
      (faceChannel coarseFaceId).2 =
        coarseTarget coarseFaceId
  faceChannel_positive :
    ∀ coarseFaceId,
      coarseFaceId ∈ S.coarse.faceEdges →
      (0 : Q') <
        packetPairChannelRawWeight S.coarse.coupling
          (wholeSlabFinePacket S fineState coarseFaceId)
          (faceChannel coarseFaceId)
  coarseLink_positive :
    ∀ coarseLink,
      coarseLink ∈ boundaryCompleteSlabLinks S.coarse.extent →
      0 < slabExplicitLinkMultiplicity
        S.coarse.cutoff S.coarse.extent coarseTarget coarseLink

namespace WholeSlabJointChannelSelection

theorem faceRawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    (0 : Q') <
      wholeSlabFaceRawWeight S fineState
        selection.coarseTarget coarseFaceId := by
  let channel := selection.faceChannel coarseFaceId
  have hselected :
      (0 : Q') <
        (if channel.2 =
              selection.coarseTarget coarseFaceId then
            packetPairChannelRawWeight S.coarse.coupling
              (wholeSlabFinePacket S fineState coarseFaceId)
              channel
          else 0) := by
    rw [if_pos (selection.faceChannel_final coarseFaceId hface)]
    exact selection.faceChannel_positive coarseFaceId hface
  have hle :
      (if channel.2 =
            selection.coarseTarget coarseFaceId then
          packetPairChannelRawWeight S.coarse.coupling
            (wholeSlabFinePacket S fineState coarseFaceId)
            channel
        else 0) ≤
        wholeSlabFaceRawWeight S fineState
          selection.coarseTarget coarseFaceId := by
    unfold wholeSlabFaceRawWeight
    apply listQSum_member_le_local
    · intro state
      by_cases hstate :
          state.2 = selection.coarseTarget coarseFaceId
      · rw [if_pos hstate]
        exact packetPairChannelRawWeight_nonnegative
          S.coarse.coupling_nonnegative _ _
      · rw [if_neg hstate]
        exact Q'.le_refl' 0
    · exact selection.faceChannel_mem coarseFaceId hface
  exact Q'.pos_of_lt_of_le hselected hle

theorem faceProduct_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    (0 : Q') <
      wholeSlabFaceRawProduct S fineState
        selection.coarseTarget := by
  apply wholeSlabFaceRawProduct_pos_of_pointwise
  intro coarseFaceId hface
  exact selection.faceRawWeight_pos hface

theorem linkProduct_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    0 < slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent selection.coarseTarget := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_on
    (slabExplicitLinkMultiplicity
      S.coarse.cutoff S.coarse.extent selection.coarseTarget)
    (boundaryCompleteSlabLinks S.coarse.extent)
    selection.coarseLink_positive

theorem rawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    (0 : Q') <
      wholeSlabRecouplingRawWeight
        S fineState selection.coarseTarget := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.mul_pos selection.faceProduct_pos
    (ofNat_pos_of_pos_local selection.linkProduct_pos)

end WholeSlabJointChannelSelection

/-- The genuine residual constructor: every positive higher-cutoff fine row
returns one joint target/channel/intertwiner selection as `Type`-level data. -/
structure SU2OuterJointChannelSelection
    (G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  select :
    ∀ K source,
      K ≠ 1 →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
      WholeSlabJointChannelSelection
        (su2OuterScalePair
          G g hg candidate hcandidate K) source

def SU2OuterJointChannelSelection.toPositiveRowClosure
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (joint :
      SU2OuterJointChannelSelection
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate where
  coarseWitness := fun K source hK hsource hpositive =>
    (joint.select K source hK hsource hpositive).coarseTarget
  coarseWitness_mem := by
    intro K source hK hsource hpositive
    exact (joint.select K source hK hsource hpositive).coarseTarget_mem
  coarseWitness_positive := by
    intro K source hK hsource hpositive
    exact (joint.select K source hK hsource hpositive).rawWeight_pos

#print axioms slabSpinAtPlaquette_le_cutoff
#print axioms wholeSlabFinePacket_mem
#print axioms wholeSlabStretchedTarget_mem
#print axioms wholeSlabStretchedTarget_faceRawWeight_pos
#print axioms wholeSlabStretchedTarget_faceProduct_pos
#print axioms wholeSlabStretchedTarget_rawWeight_pos
#print axioms stretchedFence_badCoarseLink_multiplicity_zero
#print axioms stretchedFenceFineState_mem
#print axioms stretchedFence_stretchedTarget_linkProduct_zero
#print axioms wholeSlabStretchedTarget_linkProduct_eq_one_of_fine_cutoff_zero
#print axioms fineLinkMultiplicity_pos_of_physicalTerm_pos
#print axioms SU2OuterStretchedLinkClosure.toPositiveRowClosure
#print axioms WholeSlabJointChannelSelection.faceRawWeight_pos
#print axioms WholeSlabJointChannelSelection.faceProduct_pos
#print axioms WholeSlabJointChannelSelection.linkProduct_pos
#print axioms WholeSlabJointChannelSelection.rawWeight_pos
#print axioms SU2OuterJointChannelSelection.toPositiveRowClosure

end YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
