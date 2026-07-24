/-
# Whole corrected-slab recoupling raw kernel

Pairwise adjacent-cube rows do not by themselves ensure that a coarse face
or link reused by several blocks receives one common channel.  This module
therefore defines the whole-slab raw row directly on the actual corrected-
slab fine and coarse physical labelling lists.

For every coarse face, the four geometric fine preimages form the exact
`FaceSpinPacket`.  All two-pair fusion states with the prescribed final
coarse character are summed.  These face-fiber sums are multiplied over the
entire coarse slab and then multiplied by the complete coarse
link-multiplicity product.  Thus every coarse face label is shared globally
and every coarse link sees the same incident labels.

A `CoherentSlabRecouplingSource` retains one coarse physical target with
strictly positive raw mass.  From that witness the complete row is
nonnegative and normalized by a single denominator over the literal coarse
physical labelling space.

This constructs the exact global raw carrier and its normalization algebra.
The load-bearing remaining theorem is physical coherence: every positive
fine Gibbs summand must supply such a coarse witness, compatibly with
reflection.  That theorem is not assumed here.

## Axiom gate

Finite exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualFiniteBlockRemainder

namespace YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

abbrev SlabLabelling := EdgeLabelling

/-! ## 1. Whole-slab geometric face fibers -/

/-- Read a corrected-slab numerical labelling at a geometric plaquette,
extended by spin zero outside the selected slab.  Every dyadic preimage used
by the raw kernel is inside, while the explicit zero extension makes the
function safe for later global cellular-boundary arguments. -/
def slabSpinAtPlaquette
    (extent : Nat) (physical : SlabLabelling)
    (plaquette :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) : Nat :=
  if plaquette ∈ boundaryCompleteSlabPlaquettes extent then
    physical
      (listIndexOf plaquette
        (boundaryCompleteSlabPlaquettes extent))
  else 0

theorem slabSpinAtPlaquette_eq_of_mem
    {extent : Nat} {physical : SlabLabelling}
    {plaquette :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent physical plaquette =
      physical
        (listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes extent)) := by
  unfold slabSpinAtPlaquette
  rw [if_pos hplaquette]

theorem slabSpinAtPlaquette_eq_zero_of_not_mem
    {extent : Nat} {physical : SlabLabelling}
    {plaquette :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hplaquette :
      plaquette ∉ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent physical plaquette = 0 := by
  unfold slabSpinAtPlaquette
  rw [if_neg hplaquette]

def wholeSlabFinePacket
    (S : SlabScalePair) (fineState : SlabLabelling)
    (coarseFaceId : Nat) : FaceSpinPacket :=
  dyadicFaceSpinPacket
    (slabSpinAtPlaquette S.fine.extent fineState)
    (slabPlaquetteAt S.coarse.extent coarseFaceId)

/-- The exact character/fusion mass on one coarse face after fixing only its
final coarse character and summing both internal pair channels. -/
def wholeSlabFaceRawWeight
    (S : SlabScalePair) (fineState coarseState : SlabLabelling)
    (coarseFaceId : Nat) : Q' :=
  listQSum
    (fun channel =>
      if channel.2 = coarseState coarseFaceId then
        packetPairChannelRawWeight S.coarse.coupling
          (wholeSlabFinePacket S fineState coarseFaceId) channel
      else 0)
    (pairChannelStateSpace S.fine.cutoff)

theorem wholeSlabFaceRawWeight_nonnegative
    (S : SlabScalePair) (fineState coarseState : SlabLabelling)
    (coarseFaceId : Nat) :
    (0 : Q') ≤
      wholeSlabFaceRawWeight S fineState coarseState coarseFaceId := by
  unfold wholeSlabFaceRawWeight
  apply listQSum_nonnegative_on
  intro channel _
  by_cases hfinal : channel.2 = coarseState coarseFaceId
  · rw [if_pos hfinal]
    exact packetPairChannelRawWeight_nonnegative
      S.coarse.coupling_nonnegative _ _
  · rw [if_neg hfinal]
    exact Q'.le_refl' 0

private def wholeSlabQProduct {A : Type}
    (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => value head * wholeSlabQProduct value tail

private theorem wholeSlabQProduct_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs, (0 : Q') ≤ wholeSlabQProduct value xs
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (wholeSlabQProduct_nonnegative value hvalue tail)

private theorem wholeSlabQProduct_pos_on {A : Type}
    (value : A → Q') :
    ∀ xs, (∀ x, x ∈ xs → (0 : Q') < value x) →
      (0 : Q') < wholeSlabQProduct value xs
  | [], _ => by
      change (0 : Q') < 1
      decide
  | head :: tail, hvalue =>
      Q'.mul_pos
        (hvalue head List.mem_cons_self)
        (wholeSlabQProduct_pos_on value tail
          (fun x hmem =>
            hvalue x (List.mem_cons_of_mem head hmem)))

def wholeSlabFaceRawProduct
    (S : SlabScalePair) (fineState coarseState : SlabLabelling) : Q' :=
  wholeSlabQProduct
    (wholeSlabFaceRawWeight S fineState coarseState)
    S.coarse.faceEdges

theorem wholeSlabFaceRawProduct_nonnegative
    (S : SlabScalePair) (fineState coarseState : SlabLabelling) :
    (0 : Q') ≤ wholeSlabFaceRawProduct S fineState coarseState := by
  unfold wholeSlabFaceRawProduct
  apply wholeSlabQProduct_nonnegative
  intro coarseFaceId
  exact wholeSlabFaceRawWeight_nonnegative
    S fineState coarseState coarseFaceId

/-- Pointwise strict positivity on every geometric coarse face makes the
complete whole-slab face product strictly positive. -/
theorem wholeSlabFaceRawProduct_pos_of_pointwise
    (S : SlabScalePair) (fineState coarseState : SlabLabelling)
    (hvalue : ∀ coarseFaceId, coarseFaceId ∈ S.coarse.faceEdges →
      (0 : Q') <
        wholeSlabFaceRawWeight S fineState coarseState coarseFaceId) :
    (0 : Q') < wholeSlabFaceRawProduct S fineState coarseState := by
  unfold wholeSlabFaceRawProduct
  exact wholeSlabQProduct_pos_on
    (wholeSlabFaceRawWeight S fineState coarseState)
    S.coarse.faceEdges hvalue

/-! ## 2. Complete globally link-glued raw row -/

def wholeSlabRecouplingRawWeight
    (S : SlabScalePair) (fineState coarseState : SlabLabelling) : Q' :=
  wholeSlabFaceRawProduct S fineState coarseState *
    Q'.ofNat
      (slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent coarseState)

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

theorem wholeSlabRecouplingRawWeight_nonnegative
    (S : SlabScalePair) (fineState coarseState : SlabLabelling) :
    (0 : Q') ≤
      wholeSlabRecouplingRawWeight S fineState coarseState := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.mul_nonneg _ _
    (wholeSlabFaceRawProduct_nonnegative S fineState coarseState)
    (ofNat_nonnegative_local _)

/-! ## 3. One globally coherent witness and one denominator -/

structure CoherentSlabRecouplingSource (S : SlabScalePair) : Type where
  fineState : SlabLabelling
  fine_mem : fineState ∈ S.fine.physicalLabellings
  coarseWitness : SlabLabelling
  coarseWitness_mem : coarseWitness ∈ S.coarse.physicalLabellings
  coarseWitness_positive :
    (0 : Q') <
      wholeSlabRecouplingRawWeight S fineState coarseWitness

def wholeSlabRecouplingPartition
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) : Q' :=
  listQSum
    (wholeSlabRecouplingRawWeight S source.fineState)
    S.coarse.physicalLabellings

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

theorem wholeSlabRecouplingPartition_pos
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) :
    (0 : Q') < wholeSlabRecouplingPartition source := by
  have hle := listQSum_member_le_local
    (wholeSlabRecouplingRawWeight S source.fineState)
    (wholeSlabRecouplingRawWeight_nonnegative S source.fineState)
    S.coarse.physicalLabellings
    source.coarseWitness_mem
  exact Q'.pos_of_lt_of_le source.coarseWitness_positive hle

def wholeSlabRecouplingConditionalKernel
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (coarseState : SlabLabelling) : Q' :=
  Q'.divPos
    (wholeSlabRecouplingRawWeight S source.fineState coarseState)
    (wholeSlabRecouplingPartition source)
    (wholeSlabRecouplingPartition_pos source)

theorem wholeSlabRecouplingConditionalKernel_nonnegative
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (coarseState : SlabLabelling) :
    (0 : Q') ≤
      wholeSlabRecouplingConditionalKernel source coarseState := by
  unfold wholeSlabRecouplingConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (wholeSlabRecouplingRawWeight_nonnegative
      S source.fineState coarseState)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem wholeSlabRecouplingConditionalKernel_row_normalized
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) :
    listQSum
        (wholeSlabRecouplingConditionalKernel source)
        S.coarse.physicalLabellings ≈ 1 := by
  unfold wholeSlabRecouplingConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (wholeSlabRecouplingPartition source *
      Q'.recipPos (wholeSlabRecouplingPartition source)
        (wholeSlabRecouplingPartition_pos source)) _
    (listQSum_mul_right
      (wholeSlabRecouplingRawWeight S source.fineState)
      (Q'.recipPos (wholeSlabRecouplingPartition source)
        (wholeSlabRecouplingPartition_pos source))
      S.coarse.physicalLabellings)
    (Q'.mul_recipPos_eqv _
      (wholeSlabRecouplingPartition_pos source))

#print axioms wholeSlabFaceRawWeight_nonnegative
#print axioms slabSpinAtPlaquette_eq_of_mem
#print axioms slabSpinAtPlaquette_eq_zero_of_not_mem
#print axioms wholeSlabFaceRawProduct_nonnegative
#print axioms wholeSlabFaceRawProduct_pos_of_pointwise
#print axioms wholeSlabRecouplingRawWeight_nonnegative
#print axioms wholeSlabRecouplingPartition_pos
#print axioms wholeSlabRecouplingConditionalKernel_nonnegative
#print axioms wholeSlabRecouplingConditionalKernel_row_normalized

end YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
