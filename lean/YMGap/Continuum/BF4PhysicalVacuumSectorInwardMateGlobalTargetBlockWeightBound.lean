/-
# Weighted capacity of one global target/root/size block

Inside a fixed global coarse block, every distinct realized representative
has the same peel rate and the same lowered physical target atom.  The global
residual-code injection bounds the number of such representatives by the
genuine SU(2) target-tuple multiplicity.  Multiplying these two facts gives the
weighted block contraction needed for the geometric size/root/target sums.

No size tail, root union, physical-target sum, total-mass normalization,
conditional, posterior, operator, or continuum claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockWeightBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Small exact finite-sum lemmas -/

private theorem listQSum_le_length_mul_local {A : Type}
    (value : A -> Q') (bound : Q') : ∀ items : List A,
    (0 : Q') ≤ bound ->
    (∀ item, item ∈ items -> value item ≤ bound) ->
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _, _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound0, hvalue => by
      have htail := listQSum_le_length_mul_local value bound tail hbound0
        (fun item hitem => hvalue item (List.mem_cons_of_mem head hitem))
      have hadd := Q'.add_le_add
        (hvalue head List.mem_cons_self) htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ bound
              (Q'.ofNat_add_eqv tail.length 1)
          refine Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
            (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
          exact Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + bound) _
            (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
            (Q'.add_comm_eqv
              (Q'.ofNat tail.length * bound) bound)))

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _
        (Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

/-! ## 2. The common target atom in one global block -/

/-- A global representative in one coarse block has exactly the common peel
rate times the selected physical target atom. -/
theorem globalCubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hrepresentative : representative ∈
      globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize) :
    globalCubeInwardMateFullPeelRepresentativeTargetWeight K representative ≈
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockEntryWeight
          anchorCoupling K target := by
  have hspec :=
    globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec
      representative hrepresentative
  have htargetEq :=
    globalCubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
      htarget representative hrepresentative
  have hatom :=
    EnumeratedCubeInwardMateFullSource.presentedTargetWeight_eqv_fixedOrderAtom
      representative.entry
  unfold globalCubeInwardMateFullPeelRepresentativeTargetWeight
  dsimp only
  refine Q'.eqv_trans _
    (componentAdaptiveEntropyAnchorRatio ^
        representative.adaptiveInverseData.peelSize *
      cubeInwardMateFixedOrderTargetBlockEntryWeight anchorCoupling K
        representative.adaptiveInverseData.lowerPhysical) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (componentAdaptiveEntropyAnchorRatio ^
        representative.adaptiveInverseData.peelSize) _ _ hatom
  · rw [hspec.2.1, htargetEq]
    exact Q'.eqv_refl _

/-! ## 3. Weighted global block capacity -/

private theorem blockCardinalityWeight_eqv_physicalBlock
    (K : Nat) (target : EdgeLabelling) (peelSize : Nat) :
    Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length *
        (componentAdaptiveEntropyAnchorRatio ^ peelSize *
          cubeInwardMateFixedOrderTargetBlockEntryWeight
            anchorCoupling K target) ≈
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let rate := componentAdaptiveEntropyAnchorRatio ^ peelSize
  let atom := cubeInwardMateFixedOrderTargetBlockEntryWeight
    anchorCoupling K target
  let tuples := cubeInwardMateFixedOrderTargetTuples K target
  refine Q'.eqv_trans _ ((Q'.ofNat tuples.length * rate) * atom) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat tuples.length) rate atom)) ?_
  refine Q'.eqv_trans _ ((rate * Q'.ofNat tuples.length) * atom) _
    (Q'.mul_eqv_congr_right _ _ atom
      (Q'.mul_comm_eqv (Q'.ofNat tuples.length) rate)) ?_
  refine Q'.eqv_trans _ (rate * (Q'.ofNat tuples.length * atom)) _
    (Q'.mul_assoc_eqv rate (Q'.ofNat tuples.length) atom) ?_
  apply Q'.mul_eqv_congr_left rate
  unfold cubeInwardMateFixedOrderTargetBlockWeight tuples atom
  exact Q'.eqv_symm (listQSum_const_local
    (cubeInwardMateFixedOrderTargetBlockEntryWeight anchorCoupling K target)
    (cubeInwardMateFixedOrderTargetTuples K target))

/-- **Weighted global fixed-block capacity.**  One all-physical
target/root/size block costs at most its geometric rate times the exact genuine
SU(2) physical target block. -/
theorem globalCubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock
    {K : Nat} {hK : 1 ≤ K}
    (target : EdgeLabelling) (rootFaceId peelSize : Nat)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    globalCubeInwardMateFullPeelTargetBlockWeight
        (globalCubeInwardMateFullPeelRepresentativeTargetWeight
          K (hK := hK))
        (target, (rootFaceId, peelSize)) ≤
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let block := globalCubeInwardMateFullPeelTargetBlockRepresentatives
    K hK target rootFaceId peelSize
  let rate := componentAdaptiveEntropyAnchorRatio ^ peelSize
  let atom := cubeInwardMateFixedOrderTargetBlockEntryWeight
    anchorCoupling K target
  let bound := rate * atom
  have hrate0 : (0 : Q') ≤ rate :=
    Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) peelSize
  have hatom0 : (0 : Q') ≤ atom :=
    cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative K target
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _ hrate0 hatom0
  have hsum :
      listQSum
          (globalCubeInwardMateFullPeelRepresentativeTargetWeight K) block ≤
        Q'.ofNat block.length * bound := by
    apply listQSum_le_length_mul_local
    · exact hbound0
    · intro representative hrepresentative
      exact Q'.le_of_eqv
        (globalCubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
          htarget representative hrepresentative)
  have hlength :=
    globalCubeInwardMateFullPeelTargetBlock_length_le_targetTuples
      (K := K) (hK := hK) (target := target)
      (rootFaceId := rootFaceId) (peelSize := peelSize) htarget
  have hlengthQ : Q'.ofNat block.length ≤
      Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length :=
    CReal.ofNat_le_ofNat hlength
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ bound hlengthQ hbound0
  unfold globalCubeInwardMateFullPeelTargetBlockWeight
  change
    listQSum
        (globalCubeInwardMateFullPeelRepresentativeTargetWeight K) block ≤
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K target
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (blockCardinalityWeight_eqv_physicalBlock K target peelSize)))

#print axioms globalCubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
#print axioms globalCubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockWeightBound
