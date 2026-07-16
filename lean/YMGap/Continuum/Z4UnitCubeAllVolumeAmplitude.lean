/-
# Exact elementary-cube amplitude at every finite volume

The cube label has already been proved physical and enumerated at every box
volume.  Here the packet product is evaluated without finite-volume
computation: all auxiliary and vacuum factors are one, all unselected
plaquette factors are one, and the six selected faces contribute the same
derived heat-kernel coefficient.
-/

import YMGap.Continuum.Z4UnitCubeAllVolumeMembership
import YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence

namespace YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeMembership
open YMGap.Continuum.Z4UnitCubeAllVolumePhysicality
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem enumerateFrom_fst_nodup {a : Type} :
    ∀ (start : Nat) (xs : List a),
      ((enumerateFrom start xs).map Prod.fst).Nodup
  | _, [] => List.nodup_nil
  | start, x :: xs => by
      simp only [enumerateFrom, List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, enumerateFrom_fst_nodup (start + 1) xs⟩
      intro hmem
      obtain ⟨indexed, hindexed, hfst⟩ := List.mem_map.mp hmem
      have hge := enumerateFrom_index_ge hindexed
      have heq : indexed.1 = start := hfst
      rw [heq] at hge
      omega

private theorem enumerate_fst_nodup {a : Type} (xs : List a) :
    ((enumerate xs).map Prod.fst).Nodup :=
  enumerateFrom_fst_nodup 0 xs

/-- Numerical identifiers of the six cube faces are duplicate-free. -/
theorem unitCubeSurfaceIds_nodup (n : Nat) :
    (unitCubeSurfaceIds n).Nodup := by
  unfold unitCubeSurfaceIds
  exact (List.filter_sublist.map Prod.fst).nodup
    (enumerate_fst_nodup (boxPlaquettes n))

/-- Every box containing the cube enumerates exactly six selected plaquette
identifiers. -/
theorem unitCubeSurfaceIds_length {n : Nat} (hn : 2 ≤ n) :
    (unitCubeSurfaceIds n).length = 6 := by
  let selectedBox := (boxPlaquettes n).filter
    (fun p => decide (p ∈ unitCubeSurface))
  have hselectedNodup : selectedBox.Nodup :=
    List.filter_sublist.nodup (boxPlaquettes_nodup n)
  have hsurfaceLe : unitCubeSurface.length ≤ selectedBox.length := by
    apply nodup_subset_length_le unitCubeSurface selectedBox
      unitCubeSurface_nodup
    intro p hp
    exact List.mem_filter.mpr
      ⟨unitCubeSurface_mem_box hn hp, by simpa⟩
  have hselectedLe : selectedBox.length ≤ unitCubeSurface.length := by
    apply nodup_subset_length_le selectedBox unitCubeSurface hselectedNodup
    intro p hp
    have hsurface := (List.mem_filter.mp hp).2
    simpa only [decide_eq_true_eq] using hsurface
  have hselectedLength : selectedBox.length = 6 := by
    rw [← unitCubeSurface_length]
    exact Nat.le_antisymm hselectedLe hsurfaceLe
  unfold unitCubeSurfaceIds
  rw [List.length_map]
  let entries := enumerate (boxPlaquettes n)
  have hsnd := enumerate_map_snd (boxPlaquettes n)
  have hmapped :
      ((entries.filter fun ip => decide (ip.2 ∈ unitCubeSurface)).map
          Prod.snd) = selectedBox := by
    let pred : Z4Plaq → Bool := fun p => decide (p ∈ unitCubeSurface)
    calc
      ((entries.filter fun ip => decide (ip.2 ∈ unitCubeSurface)).map
          Prod.snd) = (entries.filter (pred ∘ Prod.snd)).map Prod.snd := rfl
      _ = (entries.map Prod.snd).filter pred :=
        List.filter_map.symm
      _ = selectedBox := by rw [hsnd]
  change (entries.filter fun ip => decide (ip.2 ∈ unitCubeSurface)).length = 6
  rw [← List.length_map (f := Prod.snd), hmapped]
  exact hselectedLength

private theorem unitCubeSurfaceId_lt_count {n edge : Nat}
    (he : edge ∈ unitCubeSurfaceIds n) : edge < plaquetteEdgeCount n := by
  unfold unitCubeSurfaceIds at he
  obtain ⟨indexed, hindexed, hedge⟩ := List.mem_map.mp he
  have hpair := (List.mem_filter.mp hindexed).1
  have hlt := enumerate_index_lt hpair
  unfold plaquetteEdgeCount
  simpa only [← hedge] using hlt

private theorem selectedRange_length_eq_ids (n : Nat) :
    ((List.range (plaquetteEdgeCount n)).filter
      fun edge => decide (edge ∈ unitCubeSurfaceIds n)).length =
        (unitCubeSurfaceIds n).length := by
  let selectedRange := (List.range (plaquetteEdgeCount n)).filter
    (fun edge => decide (edge ∈ unitCubeSurfaceIds n))
  have hrangeNodup : (List.range (plaquetteEdgeCount n)).Nodup := by
    induction plaquetteEdgeCount n with
    | zero => exact List.nodup_nil
    | succ k ih =>
        rw [List.range_succ]
        refine List.nodup_append.mpr
          ⟨ih, List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro x hx y hy hxy
        have hyk : y = k := List.mem_singleton.mp hy
        rw [hxy, hyk] at hx
        exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)
  have hselectedNodup : selectedRange.Nodup :=
    List.filter_sublist.nodup hrangeNodup
  apply Nat.le_antisymm
  · apply nodup_subset_length_le selectedRange (unitCubeSurfaceIds n)
      hselectedNodup
    intro edge he
    have hmem := (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hmem
  · apply nodup_subset_length_le (unitCubeSurfaceIds n) selectedRange
      (unitCubeSurfaceIds_nodup n)
    intro edge he
    exact List.mem_filter.mpr
      ⟨List.mem_range.mpr (unitCubeSurfaceId_lt_count he), by simpa⟩

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (f g : Nat → Q') : ∀ edges : List Nat,
    (∀ edge, edge ∈ edges → f edge ≈ g edge) →
      eliminateLinks f edges ≈ eliminateLinks g edges
  | [], _ => Q'.eqv_refl _
  | edge :: rest, h =>
      q_mul_congr
        (h edge List.mem_cons_self)
        (eliminateLinks_congr_on f g rest
          (fun e he => h e (List.mem_cons_of_mem edge he)))

private theorem eliminateLinks_append (f : Nat → Q') : ∀ xs ys,
    eliminateLinks f (xs ++ ys) ≈
      eliminateLinks f xs * eliminateLinks f ys
  | [], ys => Q'.eqv_symm (Q'.one_mul_eqv _)
  | x :: xs, ys => by
      simp only [List.cons_append, eliminateLinks]
      exact Q'.eqv_trans _ _ _
        (q_mul_congr (Q'.eqv_refl _)
          (eliminateLinks_append f xs ys))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem eliminateLinks_one : ∀ xs : List Nat,
    eliminateLinks (fun _ => (1 : Q')) xs ≈ 1
  | [] => Q'.eqv_refl _
  | _ :: xs => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 1 _ _ (eliminateLinks_one xs))
      (Q'.one_mul_eqv _)

private theorem eliminateLinks_indicator_pow (selected : List Nat)
    (a : Q') : ∀ xs : List Nat,
    eliminateLinks
        (fun edge => if edge ∈ selected then a else 1) xs ≈
      a ^ ((xs.filter fun edge => decide
        (edge ∈ selected)).length)
  | [] => Q'.eqv_refl _
  | edge :: rest => by
      by_cases he : edge ∈ selected
      · simp only [eliminateLinks, he, if_pos, List.filter_cons,
          decide_true, List.length_cons, Q'.pow_succ]
        exact q_mul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow selected a rest)
      · simp only [eliminateLinks, he, List.filter_cons,
          decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow selected a rest))
          (Q'.one_mul_eqv _)

private theorem usedAuxiliaryEdge_ge_count {n edge : Nat}
    (he : edge ∈ usedAuxiliaryEdges n) : plaquetteEdgeCount n ≤ edge := by
  unfold usedAuxiliaryEdges at he
  simp only [List.mem_eraseDups, List.mem_filter,
    decide_eq_true_eq] at he
  exact he.2

private theorem unitCubeSurfaceLabel_on_vacuumEdge {n edge : Nat}
    (he : edge ∈ vacuumBaseEdgeIds n) :
    unitCubeSurfaceLabel n edge = 0 := by
  unfold vacuumBaseEdgeIds at he
  obtain ⟨indexed, _, hindex⟩ := List.mem_map.mp he
  obtain ⟨linkId, ell⟩ := indexed
  change linkBlockBase n linkId = edge at hindex
  rw [← hindex]
  exact unitCubeSurfaceLabel_on_vacuumBase n linkId

/-- On every used edge, the cube packet coefficient is the selected-face
heat-kernel coefficient or the exact unit. -/
theorem unitCube_edgeCoefficient_all_volumes {n edge : Nat}
    (hedge : edge ∈ usedResolutionEdges n) :
    coeffAt (gaugeHeatKernelBoxPackets n edge)
        (unitCubeSurfaceLabel n edge) =
      if edge < plaquetteEdgeCount n then
        if edge ∈ unitCubeSurfaceIds n then coeffW coupling 2 else 1
      else 1 := by
  have hold := boundedEdgeLabellings_sound 2
    (usedResolutionEdges n) (unitCubeSurfaceLabel n)
    (unitCubeSurfaceLabel_mem_bounded_all_volumes n)
  have hspin := hold.1 edge hedge
  unfold gaugeHeatKernelBoxPackets
  by_cases hphysical : edge < plaquetteEdgeCount n
  · rw [if_pos hphysical]
    by_cases hselected : edge ∈ unitCubeSurfaceIds n
    · have hlabel : unitCubeSurfaceLabel n edge = 2 := by
        simp [unitCubeSurfaceLabel, hedge, hphysical, hselected]
      rw [hlabel, coeffAt_heatKernelPacket (by omega)]
      simp [hphysical, hselected]
    · have hlabel : unitCubeSurfaceLabel n edge = 0 := by
        simp [unitCubeSurfaceLabel, hedge, hphysical, hselected]
      rw [hlabel, coeffAt_heatKernelPacket (by omega), coeffW_zero]
      simp [hphysical, hselected]
  · rw [if_neg hphysical]
    by_cases hvacuum : edge ∈ vacuumBaseEdgeIds n
    · rw [if_pos hvacuum]
      have hlabel := unitCubeSurfaceLabel_on_vacuumEdge hvacuum
      rw [hlabel, coeffAt_vacuumPacket]
      simp [hphysical]
    · rw [if_neg hvacuum, coeffAt_allOnesPacket hspin]
      simp [hphysical]

private def canonicalCubeCoefficient (n edge : Nat) : Q' :=
  if edge < plaquetteEdgeCount n then
    if edge ∈ unitCubeSurfaceIds n then coeffW coupling 2 else 1
  else 1

private theorem eliminateCanonical_range {n : Nat} (hn : 2 ≤ n) :
    eliminateLinks (canonicalCubeCoefficient n)
        (List.range (plaquetteEdgeCount n)) ≈
      (coeffW coupling 2) ^ 6 := by
  have hcongr :
      eliminateLinks (canonicalCubeCoefficient n)
          (List.range (plaquetteEdgeCount n)) ≈
        eliminateLinks
          (fun edge => if edge ∈ unitCubeSurfaceIds n
            then coeffW coupling 2 else 1)
          (List.range (plaquetteEdgeCount n)) := by
    apply eliminateLinks_congr_on
    intro edge hedge
    have hlt := List.mem_range.mp hedge
    unfold canonicalCubeCoefficient
    rw [if_pos hlt]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hcongr ?_
  have hpow := eliminateLinks_indicator_pow (unitCubeSurfaceIds n)
    (coeffW coupling 2) (List.range (plaquetteEdgeCount n))
  rw [selectedRange_length_eq_ids n, unitCubeSurfaceIds_length hn] at hpow
  exact hpow

private theorem eliminateCanonical_aux (n : Nat) :
    eliminateLinks (canonicalCubeCoefficient n) (usedAuxiliaryEdges n) ≈ 1 := by
  refine Q'.eqv_trans _
    (eliminateLinks (fun _ => (1 : Q')) (usedAuxiliaryEdges n)) _ ?_
    (eliminateLinks_one (usedAuxiliaryEdges n))
  apply eliminateLinks_congr_on
  intro edge hedge
  have hge := usedAuxiliaryEdge_ge_count hedge
  unfold canonicalCubeCoefficient
  rw [if_neg (Nat.not_lt.mpr hge)]
  exact Q'.eqv_refl _

/-- The bare packet product is independent of the surrounding finite volume:
only the six elementary cube faces contribute. -/
theorem unitCube_heatKernel_bare_amplitude_all_volumes
    {n : Nat} (hn : 2 ≤ n) :
    packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPackets n) (unitCubeSurfaceLabel n) ≈
      (coeffW coupling 2) ^ 6 := by
  unfold packetGraphBareAmplitude usedResolutionEdges
  let actual : Nat → Q' := fun edge =>
    coeffAt (gaugeHeatKernelBoxPackets n edge)
      (unitCubeSurfaceLabel n edge)
  have hactual :
      eliminateLinks actual
          (List.range (plaquetteEdgeCount n) ++ usedAuxiliaryEdges n) ≈
        eliminateLinks (canonicalCubeCoefficient n)
          (List.range (plaquetteEdgeCount n) ++ usedAuxiliaryEdges n) := by
    apply eliminateLinks_congr_on
    intro edge hedge
    apply Q'.eqv_of_eq
    exact unitCube_edgeCoefficient_all_volumes hedge
  have happ := eliminateLinks_append (canonicalCubeCoefficient n)
    (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
  exact Q'.eqv_trans _ _ _ hactual
    (Q'.eqv_trans _ _ _ happ
      (Q'.eqv_trans _
        ((coeffW coupling 2) ^ 6 * 1) _
        (q_mul_congr (eliminateCanonical_range hn)
          (eliminateCanonical_aux n))
        (Q'.mul_one_eqv _)))

private theorem cubeFaceCoefficient_pow_six :
    (coeffW coupling 2) ^ 6 ≈ unitCubeHeatKernelAmplitude := by
  decide

/-- Exact projected six-face amplitude in every finite box containing the
cube. -/
theorem unitCube_heatKernel_amplitude_exact_all_volumes
    {n : Nat} (hn : 2 ≤ n) :
    packetGraphProjectedAmplitude (usedResolutionEdges n)
        (resolutionVertices n) (gaugeHeatKernelBoxPackets n)
        (unitCubeSurfaceLabel n) ≈ unitCubeHeatKernelAmplitude := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos (unitCubeSurfaceLabel_physical_all_volumes hn)]
  exact Q'.eqv_trans _ _ _
    (unitCube_heatKernel_bare_amplitude_all_volumes hn)
    cubeFaceCoefficient_pow_six

/-- Every finite box contains a positive-weight copy of the same exact
closed-surface mode. -/
theorem unitCube_heatKernel_nonzero_mode_all_volumes
    {n : Nat} (hn : 2 ≤ n) :
    ∃ i, i < (physicalEdgeLabellings 2 (usedResolutionEdges n)
        (resolutionVertices n)).length ∧
      packetGraphModeWeight (usedResolutionEdges n) (resolutionVertices n)
        (gaugeHeatKernelBoxPackets n) i ≈
          unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem
    (unitCubeSurfaceLabel_mem_physical_all_volumes hn)
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel 2 (usedResolutionEdges n)
      (resolutionVertices n) i = unitCubeSurfaceLabel n := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact q_mul_congr
    (unitCube_heatKernel_amplitude_exact_all_volumes hn)
    (unitCube_heatKernel_amplitude_exact_all_volumes hn)

/-- Every coefficient sampled by the all-volume cube label is unchanged when
the character cutoff is enlarged. -/
theorem unitCube_edgeCoefficient_cutoff_eq_two_all_volumes
    {K n edge : Nat} (hK : 2 ≤ K)
    (hedge : edge ∈ usedResolutionEdges n) :
    coeffAt (gaugeHeatKernelBoxPacketsAtCutoff K n edge)
        (unitCubeSurfaceLabel n edge) =
      coeffAt (gaugeHeatKernelBoxPackets n edge)
        (unitCubeSurfaceLabel n edge) := by
  have hold := boundedEdgeLabellings_sound 2
    (usedResolutionEdges n) (unitCubeSurfaceLabel n)
    (unitCubeSurfaceLabel_mem_bounded_all_volumes n)
  have htwo := hold.1 edge hedge
  have hlarge : unitCubeSurfaceLabel n edge < K + 1 := by omega
  unfold gaugeHeatKernelBoxPacketsAtCutoff gaugeHeatKernelBoxPackets
  by_cases hp : edge < plaquetteEdgeCount n
  · rw [if_pos hp, if_pos hp,
      coeffAt_heatKernelPacket hlarge, coeffAt_heatKernelPacket htwo]
  · rw [if_neg hp, if_neg hp]
    by_cases hv : edge ∈ vacuumBaseEdgeIds n
    · rw [if_pos hv, if_pos hv,
        coeffAt_vacuumPacket, coeffAt_vacuumPacket]
    · rw [if_neg hv, if_neg hv,
        coeffAt_allOnesPacket hlarge, coeffAt_allOnesPacket htwo]

/-- The projected cube amplitude is modewise invariant under every cutoff
increase, at every finite volume. -/
theorem unitCube_heatKernel_amplitude_cutoff_eq_two_all_volumes
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    packetGraphProjectedAmplitude (usedResolutionEdges n)
        (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n)
        (unitCubeSurfaceLabel n) ≈
      packetGraphProjectedAmplitude (usedResolutionEdges n)
        (resolutionVertices n) (gaugeHeatKernelBoxPackets n)
        (unitCubeSurfaceLabel n) := by
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  rw [if_pos (unitCubeSurfaceLabel_physical_all_volumes hn),
    if_pos (unitCubeSurfaceLabel_physical_all_volumes hn)]
  unfold packetGraphBareAmplitude
  apply eliminateLinks_congr_on
  intro edge hedge
  rw [unitCube_edgeCoefficient_cutoff_eq_two_all_volumes hK hedge]
  exact Q'.eqv_refl _

/-- The exact derived cube amplitude is uniform jointly in finite volume and
character cutoff. -/
theorem unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    packetGraphProjectedAmplitude (usedResolutionEdges n)
        (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n)
        (unitCubeSurfaceLabel n) ≈ unitCubeHeatKernelAmplitude :=
  Q'.eqv_trans _ _ _
    (unitCube_heatKernel_amplitude_cutoff_eq_two_all_volumes hK hn)
    (unitCube_heatKernel_amplitude_exact_all_volumes hn)

/-- Every finite volume and every cutoff at least two contains the same
positive-weight gauge-closed cube mode. -/
theorem unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    ∃ i, i < (physicalEdgeLabellings K (usedResolutionEdges n)
        (resolutionVertices n)).length ∧
      packetGraphModeWeight (usedResolutionEdges n) (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n) i ≈
          unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem
    (unitCubeSurfaceLabel_mem_physical_all_volumes_at_cutoff hK hn)
  refine ⟨i, hi, ?_⟩
  have hlabel : physicalModeLabel K (usedResolutionEdges n)
      (resolutionVertices n) i = unitCubeSurfaceLabel n := by
    unfold physicalModeLabel supportLabel
    rw [List.getElem?_eq_getElem hi, Option.getD_some, hget]
  unfold packetGraphModeWeight
  rw [hlabel]
  exact q_mul_congr
    (unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff hK hn)
    (unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff hK hn)

#print axioms unitCubeSurfaceIds_nodup
#print axioms unitCubeSurfaceIds_length
#print axioms unitCube_edgeCoefficient_all_volumes
#print axioms unitCube_heatKernel_bare_amplitude_all_volumes
#print axioms unitCube_heatKernel_amplitude_exact_all_volumes
#print axioms unitCube_heatKernel_nonzero_mode_all_volumes
#print axioms unitCube_edgeCoefficient_cutoff_eq_two_all_volumes
#print axioms unitCube_heatKernel_amplitude_cutoff_eq_two_all_volumes
#print axioms unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff
#print axioms unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff

end YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude
