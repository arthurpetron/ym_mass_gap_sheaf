/-
# A shell-linear analytic bound for the cutoff-two novel edge load

The novel endpoint list is duplicate-free and embeds by the identity map into
the full ordered endpoint square.  Since every one-path directed-edge load is
nonnegative, the novel simple-flow load on any fixed directed edge is bounded
by the corresponding full simple-flow load.  The existing stationary-mass
argument bounds that full load by carrier size.

Combining this domination with the exact carrier decomposition gives

  novelEdgeLoad(later, source, target) <= ofNat (65 + n),

where `n` is the classifier-reject shell length.  This replaces the cubic
occurrence-count ceiling by a linear analytic load ceiling: stationary weights
absorb the endpoint multiplicity.

This does not compare the load to the possibly small conditional transition
on the selected edge.  It therefore proves no cutoff-uniform capacity,
completed contraction, thermodynamic/continuum construction, or Clay gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The classifier-normal endpoint list is duplicate-free -/

private theorem cutoffTwoClassifierAcceptedIndices_nodup (later : Nat) :
    (cutoffTwoClassifierAcceptedIndices later).Nodup := by
  unfold cutoffTwoClassifierAcceptedIndices cutoffTwoEdgeLoadFullStates
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) later 0)

private theorem cutoffTwoClassifierRejectedIndices_nodup (later : Nat) :
    (cutoffTwoClassifierRejectedIndices later).Nodup := by
  unfold cutoffTwoClassifierRejectedIndices cutoffTwoEdgeLoadFullStates
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) later 0)

private theorem cutoffTwoClassifierAccepted_ne_rejected
    {later accepted rejected : Nat}
    (haccepted : accepted ∈ cutoffTwoClassifierAcceptedIndices later)
    (hrejected : rejected ∈ cutoffTwoClassifierRejectedIndices later) :
    accepted ≠ rejected := by
  intro heq
  subst rejected
  unfold cutoffTwoClassifierAcceptedIndices at haccepted
  unfold cutoffTwoClassifierRejectedIndices at hrejected
  have haccept := (List.mem_filter.mp haccepted).2
  have hreject := (List.mem_filter.mp hrejected).2
  cases hclassifier :
      cutoffTwoCubeSectorStateB
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 accepted) with
  | false => simp [hclassifier] at haccept
  | true => simp [hclassifier] at hreject

private theorem cutoffTwoClassifierNovelEndpointPairs_nodup
    (later : Nat) :
    (cutoffTwoClassifierNovelEndpointPairs later).Nodup := by
  let accepted := cutoffTwoClassifierAcceptedIndices later
  let rejected := cutoffTwoClassifierRejectedIndices later
  have haccepted : accepted.Nodup :=
    cutoffTwoClassifierAcceptedIndices_nodup later
  have hrejected : rejected.Nodup :=
    cutoffTwoClassifierRejectedIndices_nodup later
  have hrr : (cartesian rejected rejected).Nodup :=
    cartesian_nodup rejected rejected hrejected hrejected
  have har : (cartesian accepted rejected).Nodup :=
    cartesian_nodup accepted rejected haccepted hrejected
  have hra : (cartesian rejected accepted).Nodup :=
    cartesian_nodup rejected accepted hrejected haccepted
  unfold cutoffTwoClassifierNovelEndpointPairs
  apply List.nodup_append.mpr
  refine ⟨hrr, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨har, hra, ?_⟩
    intro left hleft right hright heq
    have hleftParts := (mem_cartesian_iff accepted rejected left).mp hleft
    have hrightParts := (mem_cartesian_iff rejected accepted right).mp hright
    exact (cutoffTwoClassifierAccepted_ne_rejected
      hleftParts.1 hrightParts.1) (congrArg Prod.fst heq)
  · intro left hleft right hright heq
    have hleftParts := (mem_cartesian_iff rejected rejected left).mp hleft
    rcases List.mem_append.mp hright with hrightAR | hrightRA
    · have hrightParts :=
        (mem_cartesian_iff accepted rejected right).mp hrightAR
      exact (cutoffTwoClassifierAccepted_ne_rejected
        hrightParts.1 hleftParts.1) (congrArg Prod.fst heq).symm
    · have hrightParts :=
        (mem_cartesian_iff rejected accepted right).mp hrightRA
      exact (cutoffTwoClassifierAccepted_ne_rejected
        hrightParts.2 hleftParts.2) (congrArg Prod.snd heq).symm

theorem cutoffTwoNovelEndpointPairs_nodup
    {later : Nat} (hcutoff : 2 ≤ later) :
    (cutoffTwoNovelEndpointPairs later).Nodup := by
  rw [cutoffTwoNovelEndpointPairs_eq_classifierPairs hcutoff]
  exact cutoffTwoClassifierNovelEndpointPairs_nodup later

/-! ## 2. Novel traffic is a nonnegative subflow of full traffic -/

private theorem cutoffTwoWeight_nonnegative_local
    (later state : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadWeight later state := by
  unfold cutoffTwoEdgeLoadWeight
  exact centralPhysicalRowMarginal_nonnegative
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 state)

theorem cutoffTwoSimpleWeightedPathEdgeLoad_nonnegative
    (later left right source target : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (0 : Q') ≤ weightedDirectedEdgeLoad
      (cutoffTwoSimpleWeightedPathOccurrences later left right)
      source target := by
  unfold cutoffTwoSimpleWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  apply weightedDirectedEdgeLoad_nonnegative
  intro occurrence hoccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hoccurrence
  subst occurrence
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (cutoffTwoWeight_nonnegative_local later left)
      (cutoffTwoWeight_nonnegative_local later right))
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem cutoffTwoNovelSimpleEdgeLoad_le_fullSimpleEdgeLoad
    {later : Nat} (hcutoff : 2 ≤ later)
    (source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≤
      cutoffTwoSimpleFullEdgeLoad later source target := by
  let pathLoad : Nat × Nat → Q' := fun pair =>
    weightedDirectedEdgeLoad
      (cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)
      source target
  have hsum :
      listQSum pathLoad (cutoffTwoNovelEndpointPairs later) ≤
        listQSum pathLoad (cutoffTwoCanonicalFullEndpointPairs later) := by
    apply listQSum_le_of_injective
      (cutoffTwoNovelEndpointPairs later)
      (cutoffTwoCanonicalFullEndpointPairs later)
      pathLoad pathLoad (fun pair => pair)
    · exact cutoffTwoNovelEndpointPairs_nodup hcutoff
    · intro pair hpair
      exact (mem_cartesian_iff
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later) pair).mpr
          (cutoffTwoNovelEndpointPair_mem_full hpair)
    · intro left _hleft right _hright heq
      exact heq
    · intro pair _hpair
      exact Q'.le_refl' (pathLoad pair)
    · intro pair hpair
      have hfull := (mem_cartesian_iff
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
      exact cutoffTwoSimpleWeightedPathEdgeLoad_nonnegative
        later pair.1 pair.2 source target hfull.1 hfull.2
  have hnovel : cutoffTwoNovelSimpleEdgeLoad later source target ≈
      listQSum pathLoad (cutoffTwoNovelEndpointPairs later) := by
    unfold cutoffTwoNovelSimpleEdgeLoad
      cutoffTwoNovelSimpleWeightedEdgeOccurrences pathLoad
    exact weightedDirectedEdgeLoad_flatMap_eqv
      (cutoffTwoNovelEndpointPairs later)
      (fun pair => cutoffTwoSimpleWeightedPathOccurrences
        later pair.1 pair.2) source target
  have hfull : cutoffTwoSimpleFullEdgeLoad later source target ≈
      listQSum pathLoad (cutoffTwoCanonicalFullEndpointPairs later) := by
    exact cutoffTwoSimpleFullEdgeLoad_eqv_pathLoadSum
      later source target
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnovel)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfull))

/-! ## 3. Stationary endpoint multiplicity contracts to a linear shell bound -/

theorem cutoffTwoNovelSimpleEdgeLoad_le_sectorSize
    {later : Nat} (hcutoff : 2 ≤ later)
    (source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≤
      Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length := by
  exact Q'.le_trans' _ _ _
    (cutoffTwoNovelSimpleEdgeLoad_le_fullSimpleEdgeLoad
      hcutoff source target)
    (cutoffTwoSimpleFullEdgeLoad_le_sectorSize later source target)

theorem cutoffTwoNovelSimpleEdgeLoad_le_shellLinear
    {later : Nat} (hcutoff : 2 ≤ later)
    (source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≤
      Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length) := by
  have hload := cutoffTwoNovelSimpleEdgeLoad_le_sectorSize
    hcutoff source target
  rw [cutoffTwoEdgeLoadFullStates_length_eq_65_add_new hcutoff] at hload
  exact hload

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.cutoffTwoNovelEndpointPairs_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.cutoffTwoSimpleWeightedPathEdgeLoad_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.cutoffTwoNovelSimpleEdgeLoad_le_fullSimpleEdgeLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.cutoffTwoNovelSimpleEdgeLoad_le_sectorSize
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.cutoffTwoNovelSimpleEdgeLoad_le_shellLinear
