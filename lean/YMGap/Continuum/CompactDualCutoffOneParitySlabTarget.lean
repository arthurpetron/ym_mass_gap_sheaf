/-
# Cutoff-one cellular parity target on the corrected slab

This module assembles the local cutoff-one face and link doors into one
globally shared coarse target.

The odd-label support of a fine corrected-slab state is pushed through the
global F2 cellular dyadic map.  The affine fine extent ensures that the
finite box output is again contained in the corrected coarse slab.  If the
fine odd support has even incidence, the existing chain-map theorem makes
the coarse support even.  Encoding that one geometric support by the
corrected-slab binary support bridge gives a literal member of the coarse
Cartesian labelling list and a strictly positive complete coarse link
product.

The second half identifies its label on every coarse face with the canonical
binary parity fusion channel.  With positive coarse coupling, every face
factor is strictly positive, hence so is the whole globally link-glued raw
weight.  This constructs a `CoherentSlabRecouplingSource` at cutoff one from
an even fine odd support.  The next gate is to derive that evenness directly
from positivity of the fine physical Gibbs summand.
-/

import YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
import YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
import YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

namespace YMGap.Continuum.CompactDualCutoffOneParitySlabTarget

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fine odd support and the finite cellular image -/

def fineOddSlabSupport
    (S : SlabScalePair) (fineState : EdgeLabelling) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes S.fine.extent).filter fun plaquette =>
    decide (slabSpinAtPlaquette S.fine.extent fineState plaquette % 2 = 1)

theorem fineOddSlabSupport_nodup
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (fineOddSlabSupport S fineState).Nodup := by
  unfold fineOddSlabSupport
  exact List.filter_sublist.nodup
    (boundaryCompleteSlabPlaquettes_nodup S.fine.extent)

theorem fineOddSlabSupport_subset
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈ fineOddSlabSupport S fineState) :
    plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent := by
  exact (List.mem_filter.mp hmem).1

theorem fineOddSlabSupport_mem_doubled_box
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈ fineOddSlabSupport S fineState) :
    plaquette ∈ boxPlaquettes (2 * (S.coarse.extent + 1)) := by
  have hbox :=
    ((mem_boundaryCompleteSlabPlaquettes S.fine.extent plaquette).mp
      (fineOddSlabSupport_subset hmem)).1
  rw [S.fine_extent] at hbox
  unfold dyadicSlabFineExtent at hbox
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hbox

/-- The global finite F2 image, retained in canonical coarse-box order. -/
def cutoffOneCoarseParitySupport
    (S : SlabScalePair) (fineState : EdgeLabelling) : List Z4Plaq :=
  dyadicModTwoPushforwardSupport
    (S.coarse.extent + 1) (fineOddSlabSupport S fineState)

private theorem xorList_true_exists_local {A : Type}
    (coefficient : A → Bool) :
    ∀ entries : List A, xorList coefficient entries = true →
      ∃ entry, entry ∈ entries ∧ coefficient entry = true
  | [], htrue => by cases htrue
  | head :: tail, htrue => by
      cases hhead : coefficient head with
      | false =>
          have htail : xorList coefficient tail = true := by
            simpa [xorList, hhead] using htrue
          obtain ⟨entry, hmem, hentry⟩ :=
            xorList_true_exists_local coefficient tail htail
          exact ⟨entry, List.mem_cons_of_mem head hmem, hentry⟩
      | true => exact ⟨head, List.mem_cons_self, hhead⟩

private theorem coarse_time_admissible_of_preimage
    {extent : Nat} {coarsePlaquette finePlaquette : Z4Plaq}
    (hpreimage : finePlaquette ∈
      dyadicFacePreimages coarsePlaquette)
    (hfine :
      plaquetteTimeAdmissible (dyadicSlabFineExtent extent) finePlaquette) :
    plaquetteTimeAdmissible extent coarsePlaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane <;>
    simp only [dyadicFacePreimages, List.mem_cons, List.not_mem_nil,
      or_false] at hpreimage <;>
    rcases hpreimage with h | h | h | h <;>
    subst finePlaquette <;>
    simp only [plaquetteTimeAdmissible, dyadicSlabFineExtent] at hfine ⊢ <;>
    omega

theorem cutoffOneCoarseParitySupport_subset_slab
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈ cutoffOneCoarseParitySupport S fineState) :
    plaquette ∈ boundaryCompleteSlabPlaquettes S.coarse.extent := by
  have hparts :=
    (mem_dyadicModTwoPushforwardSupport_iff
      (S.coarse.extent + 1) (fineOddSlabSupport S fineState)
      plaquette).mp hmem
  apply (mem_boundaryCompleteSlabPlaquettes S.coarse.extent plaquette).mpr
  refine ⟨hparts.1, ?_⟩
  unfold dyadicFacePushforward at hparts
  obtain ⟨finePlaquette, hpreimage, hfineCoefficient⟩ :=
    xorList_true_exists_local
      (supportCoefficient (fineOddSlabSupport S fineState))
      (dyadicFacePreimages plaquette) hparts.2
  have hfineMem : finePlaquette ∈ fineOddSlabSupport S fineState := by
    simpa [supportCoefficient] using hfineCoefficient
  have hfineTime :=
    ((mem_boundaryCompleteSlabPlaquettes S.fine.extent finePlaquette).mp
      (fineOddSlabSupport_subset hfineMem)).2
  rw [S.fine_extent] at hfineTime
  exact coarse_time_admissible_of_preimage hpreimage hfineTime

theorem cutoffOneCoarseParitySupport_nodup
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    (cutoffOneCoarseParitySupport S fineState).Nodup := by
  exact dyadicModTwoPushforwardSupport_nodup
    (S.coarse.extent + 1) (fineOddSlabSupport S fineState)

theorem cutoffOneCoarseParitySupport_even
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineEven : EvenFaceIncidence (fineOddSlabSupport S fineState)) :
    EvenFaceIncidence (cutoffOneCoarseParitySupport S fineState) := by
  exact dyadicModTwoPushforwardSupport_preserves_evenFaceIncidence
    (fun _ hmem => fineOddSlabSupport_mem_doubled_box hmem)
    (fineOddSlabSupport_nodup S fineState)
    hfineEven

/-! ## 2. One actual coarse labelling and its link product -/

def cutoffOneCoarseParityState
    (S : SlabScalePair) (fineState : EdgeLabelling) : EdgeLabelling :=
  slabBinarySupportLabelling S.coarse.extent
    (cutoffOneCoarseParitySupport S fineState)

theorem cutoffOneCoarseParityState_mem
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (fineState : EdgeLabelling) :
    cutoffOneCoarseParityState S fineState ∈
      S.coarse.physicalLabellings := by
  unfold cutoffOneCoarseParityState
    SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  apply slabBinarySupportLabelling_mem
  rw [S.coarse_cutoff, hfineCutoff]
  omega

theorem cutoffOneCoarseParityState_linkProduct_pos
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineEven : EvenFaceIncidence (fineOddSlabSupport S fineState)) :
    0 < slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent
      (cutoffOneCoarseParityState S fineState) := by
  unfold cutoffOneCoarseParityState
  apply slabBinarySupport_linkMultiplicityProduct_pos
  · rw [S.coarse_cutoff, hfineCutoff]
    omega
  · intro plaquette hmem
    exact cutoffOneCoarseParitySupport_subset_slab hmem
  · exact cutoffOneCoarseParitySupport_nodup S fineState
  · exact cutoffOneCoarseParitySupport_even hfineEven

/-! ## 3. The same global state is the positive face channel -/

theorem fineOddSlabSupport_coefficient
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (plaquette : Z4Plaq) :
    supportCoefficient (fineOddSlabSupport S fineState) plaquette =
      decide
        (slabSpinAtPlaquette S.fine.extent fineState plaquette % 2 = 1) := by
  by_cases hslab :
      plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent
  · simp [supportCoefficient, fineOddSlabSupport, hslab]
  · have hnot : plaquette ∉ fineOddSlabSupport S fineState := by
      intro hmem
      exact hslab (fineOddSlabSupport_subset hmem)
    rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    simp [supportCoefficient, hnot]

theorem fineSlabSpin_le_one
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (plaquette : Z4Plaq) :
    slabSpinAtPlaquette S.fine.extent fineState plaquette ≤ 1 := by
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
    rw [hfineCutoff] at hbound
    omega
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    omega

theorem wholeSlabFinePacket_binary
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (coarseFaceId : Nat) :
    PacketBinary (wholeSlabFinePacket S fineState coarseFaceId) := by
  have hmem := dyadicFaceSpinPacket_mem_stateSpace
    1
    (slabSpinAtPlaquette S.fine.extent fineState)
    (fineSlabSpin_le_one hfineCutoff hfineMem)
    (slabPlaquetteAt S.coarse.extent coarseFaceId)
  exact (mem_faceSpinPacketStateSpace_iff 1 _).mp hmem

theorem binaryPacketParityChannel_final_eq_packetParity
    (packet : FaceSpinPacket) (hbinary : PacketBinary packet) :
    (binaryPacketParityChannel packet).2 =
      (faceSpinPacketParity packet).toNat := by
  obtain ⟨spin0, spin1, spin2, spin3⟩ := packet
  rcases hbinary with ⟨h0, h1, h2, h3⟩
  change spin0 ≤ 1 at h0
  change spin1 ≤ 1 at h1
  change spin2 ≤ 1 at h2
  change spin3 ≤ 1 at h3
  have hc0 : spin0 = 0 ∨ spin0 = 1 := by omega
  have hc1 : spin1 = 0 ∨ spin1 = 1 := by omega
  have hc2 : spin2 = 0 ∨ spin2 = 1 := by omega
  have hc3 : spin3 = 0 ∨ spin3 = 1 := by omega
  rcases hc0 with rfl | rfl <;>
    rcases hc1 with rfl | rfl <;>
    rcases hc2 with rfl | rfl <;>
    rcases hc3 with rfl | rfl <;> decide

theorem cutoffOneCoarseParityState_face_eq_channel
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    cutoffOneCoarseParityState S fineState coarseFaceId =
      (binaryPacketParityChannel
        (wholeSlabFinePacket S fineState coarseFaceId)).2 := by
  let packet := wholeSlabFinePacket S fineState coarseFaceId
  let coarsePlaquette :=
    slabPlaquetteAt S.coarse.extent coarseFaceId
  have hindicator :
      cutoffOneCoarseParityState S fineState coarseFaceId =
        (supportCoefficient
          (cutoffOneCoarseParitySupport S fineState)
          coarsePlaquette).toNat := by
    unfold cutoffOneCoarseParityState
    rw [slabBinarySupportLabelling_eq_indicator hface]
    by_cases hmem :
        coarsePlaquette ∈ cutoffOneCoarseParitySupport S fineState
    · change slabPlaquetteAt S.coarse.extent coarseFaceId ∈
        cutoffOneCoarseParitySupport S fineState at hmem
      simp [coarsePlaquette, supportCoefficient, hmem]
    · change slabPlaquetteAt S.coarse.extent coarseFaceId ∉
        cutoffOneCoarseParitySupport S fineState at hmem
      simp [coarsePlaquette, supportCoefficient, hmem]
  have hbox : ∀ finePlaquette,
      finePlaquette ∈ fineOddSlabSupport S fineState →
        finePlaquette ∈ boxPlaquettes
          (2 * (S.coarse.extent + 1)) :=
    fun _ hmem => fineOddSlabSupport_mem_doubled_box hmem
  have hcoefficient :=
    supportCoefficient_dyadicModTwoPushforwardSupport
      hbox coarsePlaquette
  change supportCoefficient
      (cutoffOneCoarseParitySupport S fineState) coarsePlaquette =
    dyadicFacePushforward
      (supportCoefficient (fineOddSlabSupport S fineState))
      coarsePlaquette at hcoefficient
  have hfineCoefficient :
      supportCoefficient (fineOddSlabSupport S fineState) =
        fun plaquette =>
          decide
            (slabSpinAtPlaquette S.fine.extent fineState plaquette % 2 = 1) := by
    funext plaquette
    exact fineOddSlabSupport_coefficient S fineState plaquette
  rw [hfineCoefficient] at hcoefficient
  have hrefines :=
    dyadicFaceSpinPacket_refines_parity
      (slabSpinAtPlaquette S.fine.extent fineState)
      coarsePlaquette
  have hpacketParity :
      faceSpinPacketParity packet =
        supportCoefficient
          (cutoffOneCoarseParitySupport S fineState)
          coarsePlaquette := by
    exact hrefines.trans hcoefficient.symm
  rw [hindicator, ← hpacketParity]
  exact (binaryPacketParityChannel_final_eq_packetParity packet
    (wholeSlabFinePacket_binary hfineCutoff hfineMem coarseFaceId)).symm

theorem cutoffOneCoarseParityState_faceRawWeight_pos
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    (0 : Q') <
      wholeSlabFaceRawWeight S fineState
        (cutoffOneCoarseParityState S fineState) coarseFaceId := by
  have hstate :=
    cutoffOneCoarseParityState_face_eq_channel
      hfineCutoff hfineMem hface
  have hbinary :=
    wholeSlabFinePacket_binary hfineCutoff hfineMem coarseFaceId
  unfold wholeSlabFaceRawWeight
  rw [hfineCutoff, hstate]
  exact fixedFinalFaceRawWeight_parity_pos
    hcoarseCoupling (wholeSlabFinePacket S fineState coarseFaceId) hbinary

private theorem wholeSlabFaceRawProduct_pos
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    (0 : Q') <
      wholeSlabFaceRawProduct S fineState
        (cutoffOneCoarseParityState S fineState) := by
  apply wholeSlabFaceRawProduct_pos_of_pointwise
  intro faceId hface
  exact cutoffOneCoarseParityState_faceRawWeight_pos
    hfineCutoff hfineMem hcoarseCoupling hface

private theorem ofNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

theorem cutoffOneCoarseParityState_rawWeight_pos
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hfineEven : EvenFaceIncidence (fineOddSlabSupport S fineState))
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    (0 : Q') <
      wholeSlabRecouplingRawWeight S fineState
        (cutoffOneCoarseParityState S fineState) := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.mul_pos
    (wholeSlabFaceRawProduct_pos
      hfineCutoff hfineMem hcoarseCoupling)
    (ofNat_pos_of_pos_local
      (cutoffOneCoarseParityState_linkProduct_pos
        hfineCutoff hfineEven))

/-! ## 4. A coherent whole-slab source at cutoff one -/

structure CutoffOneEvenSlabSource (S : SlabScalePair) : Type where
  fineState : EdgeLabelling
  fine_mem : fineState ∈ S.fine.physicalLabellings
  fine_cutoff : S.fine.cutoff = 1
  fineOddSupport_even :
    EvenFaceIncidence (fineOddSlabSupport S fineState)
  coarse_coupling_positive : (0 : Q') < S.coarse.coupling

def CutoffOneEvenSlabSource.toCoherentSlabRecouplingSource
    {S : SlabScalePair} (source : CutoffOneEvenSlabSource S) :
    CoherentSlabRecouplingSource S where
  fineState := source.fineState
  fine_mem := source.fine_mem
  coarseWitness := cutoffOneCoarseParityState S source.fineState
  coarseWitness_mem :=
    cutoffOneCoarseParityState_mem source.fine_cutoff source.fineState
  coarseWitness_positive :=
    cutoffOneCoarseParityState_rawWeight_pos
      source.fine_cutoff source.fine_mem source.fineOddSupport_even
      source.coarse_coupling_positive

theorem cutoffOneWholeSlabConditionalKernel_row_normalized
    {S : SlabScalePair} (source : CutoffOneEvenSlabSource S) :
    listQSum
        (wholeSlabRecouplingConditionalKernel
          source.toCoherentSlabRecouplingSource)
        S.coarse.physicalLabellings ≈ 1 := by
  exact wholeSlabRecouplingConditionalKernel_row_normalized
    source.toCoherentSlabRecouplingSource

#print axioms cutoffOneCoarseParitySupport_subset_slab
#print axioms cutoffOneCoarseParitySupport_even
#print axioms cutoffOneCoarseParityState_mem
#print axioms cutoffOneCoarseParityState_linkProduct_pos
#print axioms cutoffOneCoarseParityState_face_eq_channel
#print axioms cutoffOneCoarseParityState_rawWeight_pos
#print axioms CutoffOneEvenSlabSource.toCoherentSlabRecouplingSource
#print axioms cutoffOneWholeSlabConditionalKernel_row_normalized

end YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
