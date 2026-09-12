/-
# The first-stretched contraction retains every nonnegative target observable

The `384/425` estimate is a bound on each physical target, not merely on the
total partition.  An arbitrary nonnegative function of the lowered physical
target is constant on the exact target fibers and on the coarse target/root/
size blocks.  It therefore passes through both finite Fubini identities.

The result is domination of the pushed-forward first-stretched mass by
`384/425` times the genuine physical mass, tested against any such function.
In particular this permits a vacuum-sector indicator.  No assertion that
every source in the vacuum sector has its target there is made here.

Fixed anchor coupling and extent one, arbitrary spin cutoff K >= 1.
No new analytic input, sorry, classical axiom, or enlarged proof budget.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetCongestion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetRootSum
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem sum_le_on {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le_on f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem sum_cartesian {A B : Type} (f : A × B → Q')
    (xs : List A) (ys : List B) :
    listQSum f (cartesian xs ys) ≈
      listQSum (fun x => listQSum (fun y => f (x, y)) ys) xs := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr_on
  intro x _
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- A nonnegative physical target observable passes through the exact
presented-target inverse-fiber contraction without any additional factor. -/
theorem targetWeightedSourceMass_le_representatives
    (K : Nat) (hK : 1 ≤ K) (f : EdgeLabelling → Q')
    (hf : ∀ target, (0 : Q') ≤ f target) :
    listQSum
        (fun source => f source.adaptiveInverseData.lowerPhysical *
          GlobalEnumeratedCubeInwardMateFullSource.weight source)
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      listQSum
        (fun representative => f representative.adaptiveInverseData.lowerPhysical *
          globalCubeInwardMateFullPeelRepresentativeTargetWeight K representative)
        (globalCubeInwardMateFullPeelTargetRepresentatives K hK) := by
  let weighted : GlobalEnumeratedCubeInwardMateFullSource K hK → Q' :=
    fun source => f source.adaptiveInverseData.lowerPhysical * source.weight
  have hpartition := keyRepresentativeFibers_weight_total
    (globalEnumeratedCubeInwardMateFullSources K hK) weighted
    GlobalEnumeratedCubeInwardMateFullSource.targetKey
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpartition) ?_
  apply sum_le_on
  intro representative _
  have hfactor : listQSum weighted
        (globalCubeInwardMateFullPeelTargetFiber representative) ≈
      f representative.adaptiveInverseData.lowerPhysical *
        listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
          (globalCubeInwardMateFullPeelTargetFiber representative) := by
    refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
    apply listQSum_congr_on
    intro source hsource
    have hkey : representative.targetKey = source.targetKey :=
      of_decide_eq_true (List.mem_filter.mp hsource).2
    have hphysical := (GlobalEnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
      representative source hkey).2.2.1
    unfold weighted
    rw [← hphysical]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (globalCubeInwardMateFullPeelTargetFiber_weight_sum_le representative)
      (hf representative.adaptiveInverseData.lowerPhysical))

/-- Exact coarse-block Fubini also holds for arbitrary representative weights. -/
theorem representativeWeightedBlocks_total
    (K : Nat) (hK : 1 ≤ K)
    (weight : GlobalEnumeratedCubeInwardMateFullSource K hK → Q') :
    globalCubeInwardMateFullPeelTargetBlocksWeight weight ≈
      globalCubeInwardMateFullPeelRepresentativesWeight weight := by
  apply finiteCoordinateFiberWeight_total
    (globalCubeInwardMateFullPeelTargetRepresentatives K hK)
    weight (cubeInwardMateFullPeelBlockCoordinates K)
    globalCubeInwardMateFullPeelRepresentativeBlockKey
    cubeInwardMateFullPeelBlockCoordinateKey
    (globalCubeInwardMateFullPeelTargetBlockWeight weight)
  · exact cubeInwardMateFullPeelBlockCoordinateKeys_nodup K
  · exact fun representative _ =>
      globalCubeInwardMateFullPeelRepresentativeBlockKey_mem representative
  · intro coordinate _
    exact Q'.eqv_of_eq
      (globalCubeInwardMateFullPeelBlock_fiberWeight_eq
        weight coordinate.1 coordinate.2.1 coordinate.2.2).symm

/-- Target observables factor through the full root/size sum exactly. -/
theorem targetWeightedRepresentatives_eqv_physicalTargetSum
    (K : Nat) (hK : 1 ≤ K) (f : EdgeLabelling → Q') :
    listQSum
        (fun representative => f representative.adaptiveInverseData.lowerPhysical *
          globalCubeInwardMateFullPeelRepresentativeTargetWeight K representative)
        (globalCubeInwardMateFullPeelTargetRepresentatives K hK) ≈
      listQSum
        (fun target => f target *
          globalCubeInwardMateFullPeelTargetRootsStrictRateWeight K hK target)
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) := by
  let weight := globalCubeInwardMateFullPeelRepresentativeTargetWeight K (hK := hK)
  let weighted : GlobalEnumeratedCubeInwardMateFullSource K hK → Q' :=
    fun representative => f representative.adaptiveInverseData.lowerPhysical *
      weight representative
  let targets := boundedEdgeLabellings K (slabPhysicalFaceEdges 1)
  let roots := centralLowerCubeFaceIds
  let sizes := List.range (cubeInwardMateFullPeelMaxSize K + 1)
  have hblocks := representativeWeightedBlocks_total K hK weighted
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hblocks) ?_
  unfold globalCubeInwardMateFullPeelTargetBlocksWeight
    cubeInwardMateFullPeelBlockCoordinates
  refine Q'.eqv_trans _ _ _
    (sum_cartesian (globalCubeInwardMateFullPeelTargetBlockWeight weighted)
      targets (cartesian roots sizes)) ?_
  apply listQSum_congr_on
  intro target htarget
  refine Q'.eqv_trans _ _ _
    (sum_cartesian
      (fun rootSize => globalCubeInwardMateFullPeelTargetBlockWeight weighted
        (target, rootSize)) roots sizes) ?_
  change listQSum
      (fun root => listQSum
        (fun size => globalCubeInwardMateFullPeelTargetBlockWeight weighted
          (target, (root, size))) sizes) roots ≈
    f target * listQSum
      (fun root => listQSum
        (fun size => globalCubeInwardMateFullPeelTargetBlockWeight weight
          (target, (root, size))) sizes) roots
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
  apply listQSum_congr_on
  intro root _
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
  apply listQSum_congr_on
  intro size _
  unfold globalCubeInwardMateFullPeelTargetBlockWeight
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
  apply listQSum_congr_on
  intro representative hrepresentative
  have hphysical :=
    globalCubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
      htarget representative hrepresentative
  unfold weighted
  rw [hphysical]
  exact Q'.eqv_refl _

private theorem mul_swap_middle (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- **Physical target-measure domination.**  The full first-stretched mass,
pushed to its actual lowered physical target, is dominated by `384/425`
times the genuine BF4 physical mass, against every nonnegative target test.
The constant is uniform in K at the fixed anchor coupling and extent one. -/
theorem targetWeightedFirstStretchedMass_le_physicalMass
    (K : Nat) (hK : 1 ≤ K) (f : EdgeLabelling → Q')
    (hf : ∀ target, (0 : Q') ≤ f target) :
    listQSum
        (fun source => f source.adaptiveInverseData.lowerPhysical *
          GlobalEnumeratedCubeInwardMateFullSource.weight source)
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      Q'.mkPos 384 425 (by decide) *
        listQSum
          (fun target => f target *
            slabParametricKPhysicalTerm anchorCoupling K 1 target)
          (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) := by
  have hsource := targetWeightedSourceMass_le_representatives K hK f hf
  have htargets := targetWeightedRepresentatives_eqv_physicalTargetSum K hK f
  refine Q'.le_trans' _ _ _ hsource
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets) ?_)
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (listQSum_mul_left _ _ _))
  apply sum_le_on
  intro target htarget
  have hroot := globalCubeInwardMateFullPeelTargetRootsStrictRateWeight_le
    (K := K) (hK := hK) target htarget
  have hphysical := cubeInwardMateFixedOrderTargetTuples_weight_total
    anchorCoupling K target (cubeInwardMatePhysicalBoundedOfMem K target htarget)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (f target) hroot (hf target)
  refine Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (mul_swap_middle _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hphysical)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.targetWeightedSourceMass_le_representatives
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.representativeWeightedBlocks_total
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.targetWeightedRepresentatives_eqv_physicalTargetSum
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.targetWeightedFirstStretchedMass_le_physicalMass
