/-
# Geometric normalization of cutoff-one local link multiplicities

The finite-box resolver presents a link factor using the box-dependent list
of incident numerical plaquette identifiers.  At cutoff one all external
labels are zero or fundamental.  This module proves by a complete exact local
audit that the fusion-path count depends only on the number of fundamental
labels, not their positions or the number of inserted vacuum labels.

This is the local algebraic half of cross-volume compatibility: after this
normalization, changing the finite box can affect a fixed polymer activity
only through the actual geometric set of excited plaquettes incident on each
physical link.
-/

import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact fundamental invariant multiplicities -/

/-- Dimension of the invariant subspace in a tensor product of at most six
fundamental SU(2) representations.  Odd counts vanish; the even values are
the first Catalan numbers `1, 1, 2, 5`. -/
def fundamentalInvariantMultiplicity : Nat → Nat
  | 0 => 1
  | 2 => 1
  | 4 => 2
  | 6 => 5
  | _ => 0

private theorem binary_value {x : Nat} (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  omega

/-- The literal cutoff-one fusion-path formula is invariant under arbitrary
permutations and vacuum insertions: it is exactly a function of the number
of fundamental external spins. -/
theorem explicitValenceMultiplicity_six_binary_eq_count
    {degree : Nat} {external : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hbinary : ∀ position, position < degree → external position ≤ 1) :
    explicitValenceMultiplicity 6 degree external =
      fundamentalInvariantMultiplicity
        (localExternalSpinSum degree external) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 1 = fundamentalInvariantMultiplicity 0
    rfl
  · change oneValentMultiplicity 6 (external 0) =
      fundamentalInvariantMultiplicity (external 0)
    have h0 := binary_value (hbinary 0 (by omega))
    rcases h0 with h0 | h0 <;> rw [h0] <;> decide
  · change twoValentMultiplicity 6 (external 0) (external 1) =
      fundamentalInvariantMultiplicity (external 0 + external 1)
    have h0 := binary_value (hbinary 0 (by omega))
    have h1 := binary_value (hbinary 1 (by omega))
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rw [h0, h1] <;> decide
  · change boolMultiplicity
        (fusionOK (external 0) (external 1) (external 2)) =
      fundamentalInvariantMultiplicity
        (external 0 + (external 1 + external 2))
    have h0 := binary_value (hbinary 0 (by omega))
    have h1 := binary_value (hbinary 1 (by omega))
    have h2 := binary_value (hbinary 2 (by omega))
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rw [h0, h1, h2] <;> decide
  · change oneChannelMultiplicity 6 (external 0) (external 1)
        (external 2) (external 3) =
      fundamentalInvariantMultiplicity
        (external 0 + (external 1 + (external 2 + external 3)))
    have h0 := binary_value (hbinary 0 (by omega))
    have h1 := binary_value (hbinary 1 (by omega))
    have h2 := binary_value (hbinary 2 (by omega))
    have h3 := binary_value (hbinary 3 (by omega))
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      rw [h0, h1, h2, h3] <;> decide
  · change twoChannelMultiplicity 6 (external 0) (external 1)
        (external 2) (external 3) (external 4) =
      fundamentalInvariantMultiplicity
        (external 0 + (external 1 +
          (external 2 + (external 3 + external 4))))
    have h0 := binary_value (hbinary 0 (by omega))
    have h1 := binary_value (hbinary 1 (by omega))
    have h2 := binary_value (hbinary 2 (by omega))
    have h3 := binary_value (hbinary 3 (by omega))
    have h4 := binary_value (hbinary 4 (by omega))
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      rw [h0, h1, h2, h3, h4] <;> decide
  · change threeChannelMultiplicity 6 (external 0) (external 1)
        (external 2) (external 3) (external 4) (external 5) =
      fundamentalInvariantMultiplicity
        (external 0 + (external 1 + (external 2 +
          (external 3 + (external 4 + external 5)))))
    have h0 := binary_value (hbinary 0 (by omega))
    have h1 := binary_value (hbinary 1 (by omega))
    have h2 := binary_value (hbinary 2 (by omega))
    have h3 := binary_value (hbinary 3 (by omega))
    have h4 := binary_value (hbinary 4 (by omega))
    have h5 := binary_value (hbinary 5 (by omega))
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      rcases h5 with h5 | h5 <;>
      rw [h0, h1, h2, h3, h4, h5] <;> decide

/-! ## 2. The production link factor depends only on excited incidence -/

theorem explicitLinkMultiplicityFactor_cutoff_one_eq_incidenceCount
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n)
    (indexed : Nat × Z4Link) :
    explicitLinkMultiplicityFactor 1 n physical indexed =
      Q'.ofNat (fundamentalInvariantMultiplicity
        (excitedIncidentPlaqIds n physical indexed.2).length) := by
  unfold explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  have hlocal := explicitValenceMultiplicity_six_binary_eq_count
    (external := fun position => physical
      (localIdentifierRename (incidentPlaqIds n indexed.2)
        (linkBlockBase n indexed.1) position))
    (incidentPlaqIds_length_le_six n indexed.2)
    (fun position hposition => by
      have hidIncident :
          localIdentifierRename (incidentPlaqIds n indexed.2)
              (linkBlockBase n indexed.1) position ∈
            incidentPlaqIds n indexed.2 :=
        localIdentifierRename_mem_of_lt _ _ _ hposition
      obtain ⟨plaquette, hindexed, _⟩ :=
        mem_incidentPlaqIds.mp hidIncident
      have hidlt :=
        Z4LinkIdentifierFreshness.enumerate_index_lt hindexed
      have hidPhysical :
          localIdentifierRename (incidentPlaqIds n indexed.2)
              (linkBlockBase n indexed.1) position ∈
            physicalFaceEdges n := by
        unfold physicalFaceEdges plaquetteEdgeCount
        exact List.mem_range.mpr hidlt
      have hlt := (boundedEdgeLabellings_sound 1
        (physicalFaceEdges n) physical hphysical).1 _ hidPhysical
      show physical
        (localIdentifierRename (incidentPlaqIds n indexed.2)
          (linkBlockBase n indexed.1) position) ≤ 1
      omega)
  have hsum := localExternalSpinSum_eq_incidentSpinSum
    n indexed.1 physical indexed.2
  have hcount := incidentSpinSum_eq_excitedIncidence_of_cutoff_one
    hphysical indexed.2
  change explicitValenceMultiplicity 6 (incidentPlaqIds n indexed.2).length
      (fun position => physical
        (localIdentifierRename (incidentPlaqIds n indexed.2)
          (linkBlockBase n indexed.1) position)) = _
  rw [hlocal, hsum, hcount]

/-! ## 3. Numerical incidence is exactly geometric incidence -/

private theorem enumerateFrom_getD_mem {A : Type} (fallback : A) :
    ∀ (start : Nat) (xs : List A) (i : Nat), i < xs.length →
      (start + i, xs.getD i fallback) ∈ enumerateFrom start xs
  | _, [], _, hi => absurd hi (Nat.not_lt_zero _)
  | start, head :: tail, 0, _ => by
      simp [enumerateFrom]
  | start, head :: tail, i + 1, hi => by
      have ih := enumerateFrom_getD_mem fallback (start + 1) tail i (by
        simp only [List.length_cons] at hi
        omega)
      have hindex : start + (i + 1) = (start + 1) + i := by omega
      rw [hindex]
      simp only [List.getD_cons_succ, enumerateFrom, List.mem_cons]
      exact Or.inr ih

theorem boxPlaquetteAt_mem_enumerate {n i : Nat}
    (hi : i < (boxPlaquettes n).length) :
    (i, boxPlaquetteAt n i) ∈ enumerate (boxPlaquettes n) := by
  unfold enumerate boxPlaquetteAt
  simpa only [Nat.zero_add] using
    (enumerateFrom_getD_mem fallbackPlaquette 0 (boxPlaquettes n) i hi)

def geometricIncidentPlaquettes
    (support : List Z4Plaq) (ell : Z4Link) : List Z4Plaq :=
  support.filter (fun p => decide (ell ∈ edgesOf p))

def numericExcitedIncidentPlaquettes
    (n : Nat) (support : List Nat) (ell : Z4Link) : List Z4Plaq :=
  (excitedIncidentPlaqIds n (componentLabel support) ell).map
    (boxPlaquetteAt n)

theorem numericExcitedIncidentPlaquettes_sameSupport
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) (ell : Z4Link) :
    sameSupport (L := z4Chain.toLattice)
      (numericExcitedIncidentPlaquettes n support ell)
      (geometricIncidentPlaquettes (geometricPolymer n support) ell) := by
  constructor
  · intro q hq
    obtain ⟨id, hidExcited, hidq⟩ := List.mem_map.mp hq
    have hparts := List.mem_filter.mp hidExcited
    have hpositive : 1 ≤ componentLabel support id := by
      simpa only [decide_eq_true_eq] using hparts.2
    have hidSupport : id ∈ support := by
      by_cases hmem : id ∈ support
      · exact hmem
      · exfalso
        rw [componentLabel_eq_zero_of_not_mem hmem] at hpositive
        omega
    obtain ⟨p, hip, hedge⟩ := mem_incidentPlaqIds.mp hparts.1
    have hidp := boxPlaquetteAt_eq_of_enumerate hip
    have hgeom : boxPlaquetteAt n id ∈ geometricPolymer n support := by
      unfold geometricPolymer
      exact List.mem_map.mpr ⟨id, hidSupport, rfl⟩
    rw [← hidq]
    apply List.mem_filter.mpr
    exact ⟨hgeom, by
      simpa only [decide_eq_true_eq, hidp] using hedge⟩
  · intro q hq
    have hparts := List.mem_filter.mp hq
    obtain ⟨id, hidSupport, hidq⟩ := List.mem_map.mp hparts.1
    rw [← hidq]
    apply List.mem_map.mpr
    refine ⟨id, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply mem_incidentPlaqIds.mpr
      have hidPhysical : id ∈ physicalFaceEdges n :=
        mem_of_mem_sublists (physicalFaceEdges n) support hsupport id hidSupport
      have hidlt := physicalFaceId_lt hidPhysical
      exact ⟨boxPlaquetteAt n id,
        boxPlaquetteAt_mem_enumerate hidlt,
        by
          rw [hidq]
          simpa only [decide_eq_true_eq] using hparts.2⟩
    · have hone : componentLabel support id = 1 :=
        componentLabel_eq_one_iff.mpr hidSupport
      simp only [decide_eq_true_eq, hone]
      omega

theorem numericExcitedIncidentPlaquettes_nodup
    {n : Nat} {support : List Nat} (ell : Z4Link) :
    (numericExcitedIncidentPlaquettes n support ell).Nodup := by
  unfold numericExcitedIncidentPlaquettes
  apply nodup_map_of_injOn (boxPlaquetteAt n)
  · exact List.filter_sublist.nodup (incidentPlaqIds_nodup n ell)
  · intro left hleft right hright heq
    apply boxPlaquetteAt_injective_on_physical
    · have hincident := (List.mem_filter.mp hleft).1
      obtain ⟨p, hip, _⟩ := mem_incidentPlaqIds.mp hincident
      unfold physicalFaceEdges plaquetteEdgeCount
      exact List.mem_range.mpr
        (Z4LinkIdentifierFreshness.enumerate_index_lt hip)
    · have hincident := (List.mem_filter.mp hright).1
      obtain ⟨p, hip, _⟩ := mem_incidentPlaqIds.mp hincident
      unfold physicalFaceEdges plaquetteEdgeCount
      exact List.mem_range.mpr
        (Z4LinkIdentifierFreshness.enumerate_index_lt hip)
    · exact heq

theorem geometricIncidentPlaquettes_nodup
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) (ell : Z4Link) :
    (geometricIncidentPlaquettes
      (geometricPolymer n support) ell).Nodup := by
  unfold geometricIncidentPlaquettes
  exact List.filter_sublist.nodup (geometricPolymer_nodup hsupport)

private theorem length_map_local {A B : Type} (f : A → B) :
    ∀ xs : List A, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (length_map_local f xs)

theorem excitedIncidentPlaqIds_length_eq_geometric
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) (ell : Z4Link) :
    (excitedIncidentPlaqIds n (componentLabel support) ell).length =
      (geometricIncidentPlaquettes
        (geometricPolymer n support) ell).length := by
  have hlength := sameSupport_length_eq_of_nodup
    (numericExcitedIncidentPlaquettes_sameSupport hsupport ell)
    (numericExcitedIncidentPlaquettes_nodup ell)
    (geometricIncidentPlaquettes_nodup hsupport ell)
  unfold numericExcitedIncidentPlaquettes at hlength
  have hmap := length_map_local (boxPlaquetteAt n)
    (excitedIncidentPlaqIds n (componentLabel support) ell)
  exact hmap.symm.trans hlength

theorem explicitLinkMultiplicityFactor_componentLabel_eq_geometric
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (indexed : Nat × Z4Link) :
    explicitLinkMultiplicityFactor 1 n (componentLabel support) indexed =
      Q'.ofNat (fundamentalInvariantMultiplicity
        (geometricIncidentPlaquettes
          (geometricPolymer n support) indexed.2).length) := by
  have hphysical : componentLabel support ∈
      explicitPhysicalLabellings 1 n := by
    apply componentLabel_mem_physical_of_subset
    intro edge hedge
    exact mem_of_mem_sublists
      (physicalFaceEdges n) support hsupport edge hedge
  rw [explicitLinkMultiplicityFactor_cutoff_one_eq_incidenceCount
    hphysical indexed,
    excitedIncidentPlaqIds_length_eq_geometric hsupport indexed.2]

/-! ## 4. Exact cross-volume invariance of one physical-link factor -/

theorem geometricIncidentPlaquettes_sameSupport
    {left right : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (ell : Z4Link) :
    sameSupport (L := z4Chain.toLattice)
      (geometricIncidentPlaquettes left ell)
      (geometricIncidentPlaquettes right ell) := by
  constructor
  · intro q hq
    have hparts := List.mem_filter.mp hq
    exact List.mem_filter.mpr ⟨hsupport.1 q hparts.1, hparts.2⟩
  · intro q hq
    have hparts := List.mem_filter.mp hq
    exact List.mem_filter.mpr ⟨hsupport.2 q hparts.1, hparts.2⟩

theorem geometricIncidentPlaquettes_length_eq_of_sameSupport
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right))
    (ell : Z4Link) :
    (geometricIncidentPlaquettes (geometricPolymer n left) ell).length =
      (geometricIncidentPlaquettes (geometricPolymer m right) ell).length := by
  exact sameSupport_length_eq_of_nodup
    (geometricIncidentPlaquettes_sameSupport hsupport ell)
    (geometricIncidentPlaquettes_nodup hleft ell)
    (geometricIncidentPlaquettes_nodup hright ell)

/-- The cutoff-one local Haar factor is literally unchanged under a change of
finite box, numerical plaquette IDs, incident-list order, link ID, and vacuum
padding, provided the actual excited plaquette support is the same. -/
theorem explicitLinkMultiplicityFactor_cross_volume
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right))
    (leftLinkId rightLinkId : Nat) (ell : Z4Link) :
    explicitLinkMultiplicityFactor 1 n (componentLabel left)
        (leftLinkId, ell) =
      explicitLinkMultiplicityFactor 1 m (componentLabel right)
        (rightLinkId, ell) := by
  calc
    explicitLinkMultiplicityFactor 1 n (componentLabel left)
        (leftLinkId, ell) =
        Q'.ofNat (fundamentalInvariantMultiplicity
          (geometricIncidentPlaquettes
            (geometricPolymer n left) ell).length) :=
      explicitLinkMultiplicityFactor_componentLabel_eq_geometric
        hleft (leftLinkId, ell)
    _ = Q'.ofNat (fundamentalInvariantMultiplicity
          (geometricIncidentPlaquettes
            (geometricPolymer m right) ell).length) := by
      rw [geometricIncidentPlaquettes_length_eq_of_sameSupport
        hleft hright hsupport ell]
    _ = explicitLinkMultiplicityFactor 1 m (componentLabel right)
          (rightLinkId, ell) :=
      (explicitLinkMultiplicityFactor_componentLabel_eq_geometric
        hright (rightLinkId, ell)).symm

/-! ## 5. Exact cross-volume invariance of the face factor -/

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') : (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on_local
    (f g : Nat → Q') : ∀ edges : List Nat,
    (∀ edge, edge ∈ edges → (f edge).eqv (g edge)) →
      (eliminateLinks f edges).eqv (eliminateLinks g edges)
  | [], _ => Q'.eqv_refl _
  | edge :: rest, h =>
      qmul_congr
        (h edge List.mem_cons_self)
        (eliminateLinks_congr_on_local f g rest
          (fun item hitem => h item (List.mem_cons_of_mem edge hitem)))

private theorem eliminateLinks_indicator_pow_local
    (selected : List Nat) (a : Q') : ∀ xs : List Nat,
    (eliminateLinks
      (fun edge => if edge ∈ selected then a else 1) xs).eqv
        (a ^ (xs.filter (fun edge => decide (edge ∈ selected))).length)
  | [] => Q'.eqv_refl _
  | edge :: rest => by
      by_cases he : edge ∈ selected
      · simp only [eliminateLinks, he, if_pos, List.filter_cons,
          decide_true, List.length_cons, Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow_local selected a rest)
      · simp only [eliminateLinks, he, List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow_local selected a rest))
          (Q'.one_mul_eqv _)

theorem physicalFaceFilter_eq_support
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (physicalFaceEdges n).filter
      (fun edge => decide (edge ∈ support)) = support := by
  apply sublists_eq_of_mem_iff
    (physicalFaceEdges n)
    ((physicalFaceEdges n).filter
      (fun edge => decide (edge ∈ support))) support
    (physicalFaceEdges_nodup n)
    (filter_mem_sublists _ _) hsupport
  intro edge
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨mem_of_mem_sublists
      (physicalFaceEdges n) support hsupport edge h, h⟩

theorem parametricPhysicalFaceFactor_componentLabel_eqv_pow
    (w : Q') {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (parametricPhysicalFaceFactor w n (componentLabel support)).eqv
      ((coeffW w 1) ^ support.length) := by
  unfold parametricPhysicalFaceFactor
  have hcoeff :
      (eliminateLinks
        (fun edge => coeffAt
          (heatKernelPacket 1 w) (componentLabel support edge))
        (physicalFaceEdges n)).eqv
      (eliminateLinks
        (fun edge => if edge ∈ support then coeffW w 1 else 1)
        (physicalFaceEdges n)) := by
    apply eliminateLinks_congr_on_local
    intro edge _
    by_cases hmem : edge ∈ support
    · have hone := componentLabel_eq_one_iff.mpr hmem
      rw [hone, coeffAt_heatKernelPacket (by decide), if_pos hmem]
      exact Q'.eqv_refl _
    · have hzero := componentLabel_eq_zero_of_not_mem hmem
      rw [hzero, coeffAt_heatKernelPacket (by decide), coeffW_zero,
        if_neg hmem]
      exact Q'.eqv_refl _
  have hpow := eliminateLinks_indicator_pow_local
    support (coeffW w 1) (physicalFaceEdges n)
  rw [physicalFaceFilter_eq_support hsupport] at hpow
  exact Q'.eqv_trans _ _ _ hcoeff hpow

theorem geometricPolymer_length_eq_support_length
    (n : Nat) (support : List Nat) :
    (geometricPolymer n support).length = support.length := by
  unfold geometricPolymer
  exact length_map_local (boxPlaquetteAt n) support

theorem numericalSupport_length_eq_of_geometric_sameSupport
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    left.length = right.length := by
  have hgeom := sameSupport_length_eq_of_nodup hsupport
    (geometricPolymer_nodup hleft) (geometricPolymer_nodup hright)
  rw [geometricPolymer_length_eq_support_length,
    geometricPolymer_length_eq_support_length] at hgeom
  exact hgeom

/-- The heat-kernel face factor is unchanged across boxes for the same actual
geometric support. -/
theorem parametricPhysicalFaceFactor_cross_volume
    (w : Q') {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (parametricPhysicalFaceFactor w n (componentLabel left)).eqv
      (parametricPhysicalFaceFactor w m (componentLabel right)) := by
  have hlength := numericalSupport_length_eq_of_geometric_sameSupport
    hleft hright hsupport
  exact Q'.eqv_trans _ ((coeffW w 1) ^ left.length) _
    (parametricPhysicalFaceFactor_componentLabel_eqv_pow w hleft)
    (Q'.eqv_trans _ ((coeffW w 1) ^ right.length) _
      (Q'.eqv_of_eq (congrArg (fun size => (coeffW w 1) ^ size) hlength))
      (Q'.eqv_symm
        (parametricPhysicalFaceFactor_componentLabel_eqv_pow w hright)))

/-! ## 6. The touched physical-link set is geometric -/

/-- The finite geometric link support of a plaquette polymer.  Duplicate
boundary occurrences are erased because a Haar factor is attached once to
each physical link. -/
def geometricTouchedLinks (support : List Z4Plaq) : List Z4Link :=
  (support.flatMap edgesOf).eraseDups

theorem mem_geometricTouchedLinks {support : List Z4Plaq} {ell : Z4Link} :
    ell ∈ geometricTouchedLinks support ↔
      ∃ plaquette, plaquette ∈ support ∧ ell ∈ edgesOf plaquette := by
  unfold geometricTouchedLinks
  rw [List.mem_eraseDups, List.mem_flatMap]

/-- The box-local Boolean excitation filter selects exactly the links on the
actual geometric support. -/
theorem mem_touchedPhysicalLinks_iff_geometric
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) (ell : Z4Link) :
    ell ∈ touchedPhysicalLinks n (componentLabel support) ↔
      ell ∈ geometricTouchedLinks (geometricPolymer n support) := by
  constructor
  · intro htouched
    have hboundary := touchedPhysicalLink_mem_excitedBoundary htouched
    unfold excitedBoundaryLinks at hboundary
    obtain ⟨⟨id, plaquette⟩, hentry, hedge⟩ :=
      List.mem_flatMap.mp hboundary
    have hentryParts := List.mem_filter.mp hentry
    have hpositive : 1 ≤ componentLabel support id := by
      simpa only [decide_eq_true_eq] using hentryParts.2
    have hidSupport : id ∈ support := by
      by_cases hid : id ∈ support
      · exact hid
      · exfalso
        rw [componentLabel_eq_zero_of_not_mem hid] at hpositive
        omega
    have hpEq : boxPlaquetteAt n id = plaquette :=
      boxPlaquetteAt_eq_of_enumerate hentryParts.1
    apply mem_geometricTouchedLinks.mpr
    refine ⟨boxPlaquetteAt n id, ?_, ?_⟩
    · unfold geometricPolymer
      exact List.mem_map.mpr ⟨id, hidSupport, rfl⟩
    · simpa only [hpEq] using hedge
  · intro hgeometric
    obtain ⟨plaquette, hpSupport, hedge⟩ :=
      mem_geometricTouchedLinks.mp hgeometric
    obtain ⟨id, hidSupport, hidPlaq⟩ := List.mem_map.mp hpSupport
    have hidPhysical : id ∈ physicalFaceEdges n :=
      mem_of_mem_sublists
        (physicalFaceEdges n) support hsupport id hidSupport
    have hidlt := physicalFaceId_lt hidPhysical
    have hindexed :
        (id, boxPlaquetteAt n id) ∈ enumerate (boxPlaquettes n) :=
      boxPlaquetteAt_mem_enumerate hidlt
    have hpBox : boxPlaquetteAt n id ∈ boxPlaquettes n := by
      have hmap : boxPlaquetteAt n id ∈
          (enumerate (boxPlaquettes n)).map Prod.snd :=
        List.mem_map.mpr ⟨(id, boxPlaquetteAt n id), hindexed, rfl⟩
      rw [enumerate_map_snd] at hmap
      exact hmap
    have hedgeAt : ell ∈ edgesOf (boxPlaquetteAt n id) := by
      simpa only [hidPlaq] using hedge
    apply List.mem_filter.mpr
    constructor
    · unfold distinctBoxLinks
      apply List.mem_eraseDups.mpr
      exact boundary_mem_boxLinks hpBox hedgeAt
    · have hincident : id ∈ incidentPlaqIds n ell :=
        mem_incidentPlaqIds.mpr ⟨boxPlaquetteAt n id, hindexed, hedgeAt⟩
      have hone : componentLabel support id = 1 :=
        componentLabel_eq_one_iff.mpr hidSupport
      apply hasExcitedB_true_of_mem (componentLabel support) hincident
      rw [hone]
      omega

private theorem filtered_eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ p : A → Bool, (xs.filter p).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons a rest ih =>
      intro p
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun b => (!(b == a)) && p b)⟩
        intro ha
        have ha' : a ∈ rest.filter (fun b => (!(b == a)) && p b) :=
          List.mem_eraseDups.mp ha
        have hfalse := (List.mem_filter.mp ha').2
        have hself : (a == a) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih p

private theorem filter_true_local {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | a :: rest => congrArg (List.cons a) (filter_true_local rest)

private theorem eraseDups_nodup_geometric {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup_local xs (fun _ => true)
  rw [filter_true_local] at h
  exact h

theorem geometricTouchedLinks_nodup (support : List Z4Plaq) :
    (geometricTouchedLinks support).Nodup := by
  unfold geometricTouchedLinks
  exact eraseDups_nodup_geometric _

theorem touchedPhysicalLinks_perm_cross_volume
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (touchedPhysicalLinks n (componentLabel left)).Perm
      (touchedPhysicalLinks m (componentLabel right)) := by
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    (touchedPhysicalLinks n (componentLabel left))
    (touchedPhysicalLinks m (componentLabel right))
    (touchedPhysicalLinks_nodup n (componentLabel left))
    (touchedPhysicalLinks_nodup m (componentLabel right))
  intro ell
  rw [mem_touchedPhysicalLinks_iff_geometric hleft,
    mem_touchedPhysicalLinks_iff_geometric hright]
  constructor
  · intro hlink
    obtain ⟨plaquette, hp, hell⟩ := mem_geometricTouchedLinks.mp hlink
    exact mem_geometricTouchedLinks.mpr
      ⟨plaquette, hsupport.1 plaquette hp, hell⟩
  · intro hlink
    obtain ⟨plaquette, hp, hell⟩ := mem_geometricTouchedLinks.mp hlink
    exact mem_geometricTouchedLinks.mpr
      ⟨plaquette, hsupport.2 plaquette hp, hell⟩

/-! ## 7. Full link-product and activity compatibility -/

def geometricLinkMultiplicityFactor
    (support : List Z4Plaq) (ell : Z4Link) : Q' :=
  Q'.ofNat (fundamentalInvariantMultiplicity
    (geometricIncidentPlaquettes support ell).length)

def geometricLinkMultiplicityProduct
    (support : List Z4Plaq) : List Z4Link → Q'
  | [] => 1
  | ell :: rest =>
      geometricLinkMultiplicityFactor support ell *
        geometricLinkMultiplicityProduct support rest

private theorem geometricLinkMultiplicityProduct_congr_on
    (left right : List Z4Plaq) : ∀ links : List Z4Link,
    (∀ ell, ell ∈ links →
      (geometricLinkMultiplicityFactor left ell).eqv
        (geometricLinkMultiplicityFactor right ell)) →
      (geometricLinkMultiplicityProduct left links).eqv
        (geometricLinkMultiplicityProduct right links)
  | [], _ => Q'.eqv_refl _
  | ell :: rest, h =>
      qmul_congr
        (h ell List.mem_cons_self)
        (geometricLinkMultiplicityProduct_congr_on left right rest
          (fun item hitem => h item (List.mem_cons_of_mem ell hitem)))

private theorem geometricLinkMultiplicityProduct_perm
    (support : List Z4Plaq) : ∀ {left right : List Z4Link},
    left.Perm right →
      (geometricLinkMultiplicityProduct support left).eqv
        (geometricLinkMultiplicityProduct support right)
  | _, _, List.Perm.nil => Q'.eqv_refl _
  | _, _, List.Perm.cons _ h =>
      Q'.mul_eqv_congr_left _ _ _
        (geometricLinkMultiplicityProduct_perm support h)
  | _, _, List.Perm.swap a b rest => by
      change geometricLinkMultiplicityFactor support b *
          (geometricLinkMultiplicityFactor support a *
            geometricLinkMultiplicityProduct support rest) ≈
        geometricLinkMultiplicityFactor support a *
          (geometricLinkMultiplicityFactor support b *
            geometricLinkMultiplicityProduct support rest)
      refine Q'.eqv_trans _
        ((geometricLinkMultiplicityFactor support b *
            geometricLinkMultiplicityFactor support a) *
          geometricLinkMultiplicityProduct support rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((geometricLinkMultiplicityFactor support a *
            geometricLinkMultiplicityFactor support b) *
          geometricLinkMultiplicityProduct support rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (geometricLinkMultiplicityProduct_perm support hleft)
        (geometricLinkMultiplicityProduct_perm support hright)

/-- The complete localized fusion product has a box-free geometric
normal form. -/
theorem explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (explicitLinkMultiplicityProduct 1 n (componentLabel support)
      (touchedIndexedLinks n (componentLabel support))).eqv
      (geometricLinkMultiplicityProduct (geometricPolymer n support)
        (touchedPhysicalLinks n (componentLabel support))) := by
  have general : ∀ links : List (Nat × Z4Link),
      (explicitLinkMultiplicityProduct 1 n (componentLabel support) links).eqv
        (geometricLinkMultiplicityProduct (geometricPolymer n support)
          (links.map Prod.snd)) := by
    intro links
    induction links with
    | nil => exact Q'.eqv_refl _
    | cons indexed rest ih =>
        change (explicitLinkMultiplicityFactor 1 n
            (componentLabel support) indexed *
              explicitLinkMultiplicityProduct 1 n
                (componentLabel support) rest).eqv
          (geometricLinkMultiplicityFactor (geometricPolymer n support)
              indexed.2 *
            geometricLinkMultiplicityProduct (geometricPolymer n support)
              (rest.map Prod.snd))
        exact qmul_congr
          (Q'.eqv_of_eq
            (explicitLinkMultiplicityFactor_componentLabel_eq_geometric
              hsupport indexed)) ih
  have h := general (touchedIndexedLinks n (componentLabel support))
  rw [map_touchedIndexedLinks_snd] at h
  exact h

theorem geometricLinkMultiplicityProduct_cross_volume
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (geometricLinkMultiplicityProduct (geometricPolymer n left)
      (touchedPhysicalLinks n (componentLabel left))).eqv
    (geometricLinkMultiplicityProduct (geometricPolymer m right)
      (touchedPhysicalLinks m (componentLabel right))) := by
  have hfactor :
      (geometricLinkMultiplicityProduct (geometricPolymer n left)
        (touchedPhysicalLinks n (componentLabel left))).eqv
      (geometricLinkMultiplicityProduct (geometricPolymer m right)
        (touchedPhysicalLinks n (componentLabel left))) := by
    apply geometricLinkMultiplicityProduct_congr_on
    intro ell _
    apply Q'.eqv_of_eq
    unfold geometricLinkMultiplicityFactor
    rw [geometricIncidentPlaquettes_length_eq_of_sameSupport
      hleft hright hsupport ell]
  have hperm :
      (geometricLinkMultiplicityProduct (geometricPolymer m right)
        (touchedPhysicalLinks n (componentLabel left))).eqv
      (geometricLinkMultiplicityProduct (geometricPolymer m right)
        (touchedPhysicalLinks m (componentLabel right))) :=
    geometricLinkMultiplicityProduct_perm (geometricPolymer m right)
      (touchedPhysicalLinks_perm_cross_volume hleft hright hsupport)
  exact Q'.eqv_trans _ _ _ hfactor hperm

/-- The entire localized cutoff-one link integral is independent of the
ambient finite box whenever the actual geometric polymer is unchanged. -/
theorem explicitLinkMultiplicityProduct_cross_volume
    {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (explicitLinkMultiplicityProduct 1 n (componentLabel left)
      (touchedIndexedLinks n (componentLabel left))).eqv
    (explicitLinkMultiplicityProduct 1 m (componentLabel right)
      (touchedIndexedLinks m (componentLabel right))) :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric hleft)
    (Q'.eqv_trans _ _ _
      (geometricLinkMultiplicityProduct_cross_volume
        hleft hright hsupport)
      (Q'.eqv_symm
        (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
          hright)))

/-- The complete localized spin-foam weight defines a compatible geometric
polymer activity across the cofinal family of finite boxes. -/
theorem parametricLocalizedSpinFoamWeight_cross_volume
    (w : Q') {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (parametricLocalizedSpinFoamWeight w n
      (componentLabel left)).eqv
    (parametricLocalizedSpinFoamWeight w m
      (componentLabel right)) := by
  unfold parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor w n (componentLabel left) *
      explicitLinkMultiplicityProduct 1 n (componentLabel left)
        (touchedIndexedLinks n (componentLabel left))).eqv
    (parametricPhysicalFaceFactor w m (componentLabel right) *
      explicitLinkMultiplicityProduct 1 m (componentLabel right)
        (touchedIndexedLinks m (componentLabel right)))
  exact qmul_congr
    (parametricPhysicalFaceFactor_cross_volume w hleft hright hsupport)
    (explicitLinkMultiplicityProduct_cross_volume hleft hright hsupport)

theorem canonicalSurfaceActivity_cross_volume
    (w : Q') {n m : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports m)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer m right)) :
    (canonicalSurfaceActivity w n left).eqv
      (canonicalSurfaceActivity w m right) := by
  unfold canonicalSurfaceActivity
  exact parametricLocalizedSpinFoamWeight_cross_volume
    w hleft hright hsupport

end YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitValenceMultiplicity_six_binary_eq_count
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitLinkMultiplicityFactor_cutoff_one_eq_incidenceCount
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.excitedIncidentPlaqIds_length_eq_geometric
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitLinkMultiplicityFactor_componentLabel_eq_geometric
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitLinkMultiplicityFactor_cross_volume
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.parametricPhysicalFaceFactor_componentLabel_eqv_pow
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.parametricPhysicalFaceFactor_cross_volume
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.mem_touchedPhysicalLinks_iff_geometric
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.touchedPhysicalLinks_perm_cross_volume
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.explicitLinkMultiplicityProduct_cross_volume
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.parametricLocalizedSpinFoamWeight_cross_volume
#print axioms YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.canonicalSurfaceActivity_cross_volume
