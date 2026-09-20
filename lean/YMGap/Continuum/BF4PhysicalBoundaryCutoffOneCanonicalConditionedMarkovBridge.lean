/-
# Positive-cutoff canonical conditioned/Markov bridge

At cutoff `K = 1` and half extent zero, the canonical vacuum component is
the explicit vacuum/cube block.  The physical conditional kernel is the
partition-normalized reflected Gram divided by its physical row marginal;
the already checked Gram-Markov rows divide the same raw row by its raw row
mass.  This file proves that the two normalizations coincide and contracts
the weighted-entry bridge to an exact zero centered-row residual.

This is a non-vacuous finite SU(2) result.  It is not a cutoff-uniform
contraction, a cofinal family, a completed spectral gap, a continuum limit,
or a Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge

set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
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

private theorem scaled_divPos_eqv_raw_divPos
    {raw reciprocal rawMass : Q'}
    (hrawMass : (0 : Q') < rawMass)
    (hscaled : (0 : Q') < rawMass * reciprocal) :
    Q'.divPos (raw * reciprocal) (rawMass * reciprocal) hscaled ≈
      Q'.divPos raw rawMass hrawMass := by
  apply divPos_eqv_of_eqv_mul_local hscaled
  refine Q'.eqv_trans _
    ((Q'.divPos raw rawMass hrawMass * rawMass) * reciprocal) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_eqv_congr_right
        (Q'.divPos raw rawMass hrawMass * rawMass)
        raw reciprocal
        (Q'.divPos_mul_eqv raw rawMass hrawMass))
  exact Q'.mul_assoc_eqv _ _ _

private theorem conditionalKernel_eqv_raw_divPos
    {w : Q'} (hw : (0 : Q') < w)
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffOneVacuumColumnCarrier w hw)
    (rawMass : Q') (hrawMass : (0 : Q') < rawMass)
    (hrowMarginal :
      centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0 source ≈
        rawMass *
          centralPhysicalFiniteVacuumSectorPartitionReciprocal
            w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalConditionalKernel w (Q'.le_of_lt hw) 1 0 source target ≈
      Q'.divPos
        (centralPhysicalReflectedKernel w 1 0 source target)
        rawMass hrawMass := by
  have hsourceRaw :=
    (mem_centralPositiveHalfStates_iff.mp hsource)
  have hsourceMarginal :
      (0 : Q') <
        centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0 source :=
    hsourceRaw.2
  have hpartition :
      (0 : Q') <
        slabParametricKPhysicalPartition w 1 (centralExtent 0) :=
    slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) 1 (centralExtent 0)
  have hreciprocal :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw) 1 0 := by
    unfold centralPhysicalFiniteVacuumSectorPartitionReciprocal
    exact Q'.recipPos_pos _ hpartition
  have hscaled :
      (0 : Q') < rawMass *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw) 1 0 :=
    Q'.mul_pos hrawMass hreciprocal
  rw [centralPhysicalConditionalKernel_eq_divPos hsourceMarginal]
  unfold centralNormalizedPhysicalReflectedKernel
  refine Q'.eqv_trans _ _ _
      (divPos_eqv_congr_local hsourceMarginal hscaled
      (Q'.eqv_refl _)
      hrowMarginal) ?_
  exact scaled_divPos_eqv_raw_divPos hrawMass hscaled

/-! ## 1. The physical conditional kernel is the exact K=1 Gram-Markov row -/

/-- On the explicit cutoff-one vacuum/cube component, the physical
conditional kernel and the row-normalized genuine Gram block are the same
kernel. -/
theorem cutoffOneCanonicalConditionalKernel_eqv_gramMarkov
    {w : Q'} (hw : (0 : Q') < w)
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw) :
    centralPhysicalConditionalKernel w (Q'.le_of_lt hw) 1 0 source target ≈
      cutoffOneVacuumCubePhysicalGramMarkov w hw source target := by
  have hsourceCarrier :=
    cutoffOneVacuumCubePhysicalSources_subset_carrier hw source hsource
  have hconditional :
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw) 1 0 source target ≈
        cutoffOneVacuumCubePhysicalGramMarkov w hw source target := by
    simp only [cutoffOneVacuumCubePhysicalSources,
      List.mem_cons, List.not_mem_nil, or_false] at hsource
    rcases hsource with hsource | hsource
    · subst source
      have hrowMarginal :=
        centralPhysicalRowMarginal_cutoffOne_vacuum_eqv hw
      have hrawMass := cutoffOneVacuumPhysicalGramRowMass_pos hw
      have hraw := conditionalKernel_eqv_raw_divPos
        (target := target) hw hsourceCarrier
        (cutoffOneVacuumPhysicalGramRowMass w hw)
        hrawMass hrowMarginal
      unfold cutoffOneVacuumCubePhysicalGramMarkov
      rw [if_neg cutoffOne_vacuum_cube_code_ne]
      unfold cutoffOneVacuumPhysicalGramMarkov
      exact Q'.eqv_trans _ _ _ hraw (Q'.eqv_refl _)
    · subst source
      have hrowMarginal :=
        centralPhysicalRowMarginal_cutoffOne_cube_eqv hw
      have hrawMass := cutoffOneCubePhysicalGramRowMass_pos hw
      have hraw := conditionalKernel_eqv_raw_divPos
        (target := target) hw hsourceCarrier
        (cutoffOneCubePhysicalGramRowMass w hw)
        hrawMass hrowMarginal
      unfold cutoffOneVacuumCubePhysicalGramMarkov
      rw [if_pos rfl]
      unfold cutoffOneCubePhysicalGramMarkov
      exact Q'.eqv_trans _ _ _ hraw (Q'.eqv_refl _)
  exact hconditional

/-! ## 2. Pointwise centered-entry annihilation -/

/-- Every canonical vacuum/cube source-target entry has zero centered
conditioned transition.  This is the pointwise form needed before attempting
to recurse the finite weighted density power. -/
theorem cutoffOneCanonicalConditionedCenteredEntry_eqv_zero
    {w : Q'} (hw : (0 : Q') < w)
    {source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0) :
    finiteWeightedCenteredTransition
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w (Q'.le_of_lt hw) 1 0)
        (centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w (Q'.le_of_lt hw) 1 0
          (canonicalFullDensityOneStepIndex
            w (Q'.le_of_lt hw) 1 0))
        source target ≈ 0 := by
  have hsourceStateMem :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 hsource rfl
  have hsourceBlock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)).mp hsourceStateMem
  have htargetStateMem :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 htarget rfl
  have htargetBlock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)).mp htargetStateMem
  have htargetCarrier :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 target ∈
        cutoffOneVacuumColumnCarrier w hw :=
    cutoffOneVacuumCubePhysicalSources_subset_carrier hw
      (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 target)
      htargetBlock
  have hkernel :=
    cutoffOneCanonicalConditionalKernel_eqv_gramMarkov
      hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)
      hsourceBlock htargetCarrier
  have hrefresh :=
    cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)
      hsourceBlock
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)
      htargetCarrier
  have hweight :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior
      hw htarget
  refine Q'.eqv_trans _ _ _
    (canonicalConditionedCenteredTransition_eqv_conditionalKernel_sub_weight
      hsource htarget) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ hkernel hrefresh)
      (Q'.neg_eqv_congr _ _ hweight)) ?_
  unfold cutoffOneVacuumColumnRefreshKernel
  exact Q'.add_neg_self_eqv _

private theorem listQSum_eqv_zero_of_pointwise_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-! ## 3. Exact zero centered row on the positive-cutoff canonical sector -/

/-- The canonical conditioned one-step has zero centered row residual on the
entire non-vacuous cutoff-one vacuum/cube sector.  This is exact finite
refresh behavior, not a uniform or continuum gap. -/
theorem cutoffOneCanonicalConditionedCenteredRowMass_eqv_zero
    {w : Q'} (hw : (0 : Q') < w)
    {source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) 1 0)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w (Q'.le_of_lt hw) 1 0)
        (centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w (Q'.le_of_lt hw) 1 0
          (canonicalFullDensityOneStepIndex
            w (Q'.le_of_lt hw) 1 0))
        source ≈ 0 := by
  have hrow :=
    canonicalConditionedCenteredRowMass_eqv_conditionalResidualL1
      hsource
  refine Q'.eqv_trans _ _ _ hrow ?_
  unfold finiteL1Norm
  apply listQSum_eqv_zero_of_pointwise_local
  intro target htarget
  have hsourceStateMem :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 hsource rfl
  have hsourceBlock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)).mp hsourceStateMem
  have htargetStateMem :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 htarget rfl
  have htargetBlock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)).mp htargetStateMem
  have htargetCarrier :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 target ∈
        cutoffOneVacuumColumnCarrier w hw :=
    cutoffOneVacuumCubePhysicalSources_subset_carrier hw
      (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 target)
      htargetBlock
  have hkernel :=
    cutoffOneCanonicalConditionalKernel_eqv_gramMarkov
      hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)
      hsourceBlock htargetCarrier
  have hrefresh :=
    cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 source)
      hsourceBlock
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 target)
      htargetCarrier
  have hweight :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior
      hw htarget
  have hresidual :
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw) 1 0
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) 1 0 source)
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) 1 0 target) +
        (-(centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w (Q'.le_of_lt hw) 1 0 target)) ≈ 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ hkernel hrefresh)
        (Q'.neg_eqv_congr _ _ hweight)) ?_
    unfold cutoffOneVacuumColumnRefreshKernel
    exact Q'.add_neg_self_eqv _
  exact Q'.abs_eqv_congr hresidual

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge.cutoffOneCanonicalConditionalKernel_eqv_gramMarkov
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge.cutoffOneCanonicalConditionedCenteredEntry_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge.cutoffOneCanonicalConditionedCenteredRowMass_eqv_zero
