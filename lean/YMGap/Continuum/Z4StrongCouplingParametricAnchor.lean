/-
# Parametric very-strong-coupling spin-foam anchor

This module starts the coupling-parameter repair identified by
`Z4SpinFoamKPCouplingFence`.  The link fusion multiplicities do not depend on
the heat-kernel coupling.  At physical cutoff one every external label is
binary, and a complete local valence audit bounds every link multiplicity by
eight.  We then combine that bound with a coupling-parametric face product.

The deliberately small rational anchor `w = 1/400` leaves enough room for the
proved degree-625 Z4 lattice-animal count even under the conservative
four-links-per-face incidence envelope.  This is a finite-cutoff strong-
coupling anchor, not a continuum result; the exact global Haar identity still
has to be generalized from the hard-coded coupling `1/2` to this parameter.
-/

import YMGap.Continuum.Z4SpinFoamKPCouplingFence

namespace YMGap.Continuum.Z4StrongCouplingParametricAnchor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Exact binary external-spin multiplicity envelope -/

private theorem binary_value {x : Nat} (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  omega

theorem explicitValenceMultiplicity_binary_le_eight
    {degree : Nat} {external : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hbinary : ∀ position, position < degree → external position ≤ 1) :
    explicitValenceMultiplicity 6 degree external ≤ 8 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 1 ≤ 8
    decide
  · exact Nat.le_trans (oneValentMultiplicity_le 6 (external 0)) (by decide)
  · exact Nat.le_trans
      (twoValentMultiplicity_le 6 (external 0) (external 1)) (by decide)
  · change boolMultiplicity
      (fusionOK (external 0) (external 1) (external 2)) ≤ 8
    unfold boolMultiplicity
    cases fusionOK (external 0) (external 1) (external 2) <;> decide
  · exact Nat.le_trans
      (oneChannelMultiplicity_le 6
        (external 0) (external 1) (external 2) (external 3)) (by decide)
  · change twoChannelMultiplicity 6 (external 0) (external 1)
      (external 2) (external 3) (external 4) ≤ 8
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
      rw [h0, h1, h2, h3, h4] <;>
      decide
  · change threeChannelMultiplicity 6 (external 0) (external 1)
      (external 2) (external 3) (external 4) (external 5) ≤ 8
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
      rw [h0, h1, h2, h3, h4, h5] <;>
      decide

def binaryLinkMultiplicityBound : Q' := Q'.ofNat 8

theorem explicitLinkMultiplicityFactor_cutoff_one_le_eight
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n)
    (indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    explicitLinkMultiplicityFactor 1 n physical indexed ≤
      binaryLinkMultiplicityBound := by
  unfold explicitLinkMultiplicityFactor binaryLinkMultiplicityBound
  apply Q'.ofNat_le_ofNat
  apply explicitValenceMultiplicity_binary_le_eight
  · exact incidentPlaqIds_length_le_six n indexed.2
  · intro position hposition
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
            (linkBlockBase n indexed.1) position ∈ physicalFaceEdges n := by
      unfold physicalFaceEdges plaquetteEdgeCount
      exact List.mem_range.mpr hidlt
    have hsound := boundedEdgeLabellings_sound 1
      (physicalFaceEdges n) physical hphysical
    have hlt := hsound.1 _ hidPhysical
    omega

theorem explicitLinkMultiplicityProduct_cutoff_one_le_pow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      explicitLinkMultiplicityProduct 1 n physical links ≤
        binaryLinkMultiplicityBound ^ links.length
  | [] => Q'.le_refl' 1
  | indexed :: rest => by
      change explicitLinkMultiplicityFactor 1 n physical indexed *
          explicitLinkMultiplicityProduct 1 n physical rest ≤
        binaryLinkMultiplicityBound ^ (rest.length + 1)
      rw [Q'.pow_succ]
      have hrest0 : (0 : Q') ≤
          explicitLinkMultiplicityProduct 1 n physical rest :=
        explicitLinkMultiplicityProduct_nonnegative 1 n physical rest
      have hbound0 : (0 : Q') ≤ binaryLinkMultiplicityBound := by
        unfold binaryLinkMultiplicityBound
        rw [Q'.zero_le_iff_num_nonneg]
        decide
      have hfirst :
          explicitLinkMultiplicityFactor 1 n physical indexed *
              explicitLinkMultiplicityProduct 1 n physical rest ≤
            binaryLinkMultiplicityBound *
              explicitLinkMultiplicityProduct 1 n physical rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (explicitLinkMultiplicityFactor_cutoff_one_le_eight
            hphysical indexed) hrest0
      have hsecond :
          binaryLinkMultiplicityBound *
              explicitLinkMultiplicityProduct 1 n physical rest ≤
            binaryLinkMultiplicityBound *
              binaryLinkMultiplicityBound ^ rest.length :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (explicitLinkMultiplicityProduct_cutoff_one_le_pow
            hphysical rest) hbound0
      exact Q'.le_trans' _ _ _ hfirst hsecond

private theorem qpow_le_succ {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : B ^ s ≤ B ^ (s + 1) := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  show B ^ s ≤ B * B ^ s
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (B ^ s))) ?_
  exact Q'.mul_le_mul_of_nonneg_right 1 B (B ^ s) hB
    (Q'.pow_nonneg B hB0 s)

private theorem qpow_add_le {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : ∀ d, B ^ s ≤ B ^ (s + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have hindex : s + (d + 1) = (s + d) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _ (qpow_add_le hB s d)
        (qpow_le_succ hB (s + d))

private theorem qpow_mono_exp {B : Q'} (hB : (1 : Q') ≤ B)
    {s t : Nat} (hst : s ≤ t) : B ^ s ≤ B ^ t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact qpow_add_le hB s d

theorem localizedLinkMultiplicityProduct_cutoff_one_le_supportPow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    explicitLinkMultiplicityProduct 1 n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) ≤
      binaryLinkMultiplicityBound ^
        ((excitedPlaquetteEntries n physical).length * 4) := by
  have hproduct :=
    explicitLinkMultiplicityProduct_cutoff_one_le_pow hphysical
      ((enumerate (distinctBoxLinks n)).filter
        (linkTouchesExcitationB n physical))
  have hcount := touchedIndexedLinks_length_le n physical
  unfold touchedIndexedLinks at hcount
  have hone : (1 : Q') ≤ binaryLinkMultiplicityBound := by
    unfold binaryLinkMultiplicityBound
    decide
  exact Q'.le_trans' _ _ _ hproduct (qpow_mono_exp hone hcount)

/-! ## 2. A coupling-parametric cutoff-one face product -/

def parametricPhysicalFaceFactor (w : Q') (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun edge => coeffAt (heatKernelPacket 1 w) (physical edge))
    (physicalFaceEdges n)

def parametricLocalizedSpinFoamWeight (w : Q') (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  parametricPhysicalFaceFactor w n physical *
    explicitLinkMultiplicityProduct 1 n physical
      ((enumerate (distinctBoxLinks n)).filter
        (linkTouchesExcitationB n physical))

def anchorCoupling : Q' := Q'.mkPos 1 400 (by decide)

def anchorFaceCoefficient : Q' := Q'.mkPos 1 32000000 (by decide)

theorem anchorFundamentalCoefficient :
    coeffW anchorCoupling 1 ≈ anchorFaceCoefficient := by
  decide

private theorem parametricCoefficient_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket 1 w) spin := by
  by_cases hspin : spin < 2
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : 1 < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket 1 w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local (value : Nat → Q')
    (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem eliminateLinks_le_filteredPow
    (value : Nat → Q') (excited : Nat → Bool) (q : Q')
    (hq0 : (0 : Q') ≤ q)
    (hvalue0 : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → excited edge = false → value edge ≈ 1) →
      (∀ edge, edge ∈ edges → excited edge = true → value edge ≤ q) →
      eliminateLinks value edges ≤ q ^ (edges.filter excited).length
  | [], _, _ => Q'.le_refl' 1
  | edge :: rest, hvacuum, hexcited => by
      have hvacuumRest : ∀ item, item ∈ rest → excited item = false →
          value item ≈ 1 := by
        intro item hitem hzero
        exact hvacuum item (List.mem_cons_of_mem edge hitem) hzero
      have hexcitedRest : ∀ item, item ∈ rest → excited item = true →
          value item ≤ q := by
        intro item hitem hexc
        exact hexcited item (List.mem_cons_of_mem edge hitem) hexc
      have ih := eliminateLinks_le_filteredPow value excited q hq0 hvalue0
        rest hvacuumRest hexcitedRest
      cases hedge : excited edge with
      | false =>
          simp only [List.filter_cons, hedge, Bool.false_eq_true, if_false]
          have hhead := hvacuum edge List.mem_cons_self hedge
          have hdrop : eliminateLinks value (edge :: rest) ≈
              eliminateLinks value rest := by
            exact Q'.eqv_trans _ (1 * eliminateLinks value rest) _
              (qmul_congr hhead (Q'.eqv_refl _))
              (Q'.one_mul_eqv _)
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdrop) ih
      | true =>
          simp only [List.filter_cons, hedge, if_true, List.length_cons]
          rw [Q'.pow_succ]
          have hrest0 : (0 : Q') ≤ eliminateLinks value rest :=
            eliminateLinks_nonnegative_local value hvalue0 rest
          have hfirst : value edge * eliminateLinks value rest ≤
              q * eliminateLinks value rest :=
            Q'.mul_le_mul_of_nonneg_right _ _ _
              (hexcited edge List.mem_cons_self hedge) hrest0
          have hsecond : q * eliminateLinks value rest ≤
              q * q ^ (rest.filter excited).length :=
            Q'.mul_le_mul_of_nonneg_left _ _ _ ih hq0
          exact Q'.le_trans' _ _ _ hfirst hsecond

theorem parametricPhysicalFaceFactor_anchor_le_supportPow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricPhysicalFaceFactor anchorCoupling n physical ≤
      anchorFaceCoefficient ^ (excitedPlaquetteIds n physical).length := by
  unfold parametricPhysicalFaceFactor excitedPlaquetteIds
  apply eliminateLinks_le_filteredPow
  · unfold anchorFaceCoefficient
    decide
  · intro edge
    exact parametricCoefficient_nonnegative (by decide) (physical edge)
  · intro edge hedge hzero
    have hnot : ¬ 1 ≤ physical edge := by
      simpa only [decide_eq_false_iff_not] using hzero
    have hspin : physical edge = 0 := by omega
    rw [hspin, coeffAt_heatKernelPacket (by decide), coeffW_zero]
    exact Q'.eqv_refl 1
  · intro edge hedge hexcited
    have hsound := boundedEdgeLabellings_sound 1
      (physicalFaceEdges n) physical hphysical
    have hlt := hsound.1 edge hedge
    have hpos : 1 ≤ physical edge := by
      simpa only [decide_eq_true_eq] using hexcited
    have hspin : physical edge = 1 := by omega
    rw [hspin, coeffAt_heatKernelPacket (by decide)]
    exact Q'.le_of_eqv anchorFundamentalCoefficient

theorem parametricPhysicalFaceFactor_anchor_le_entryPow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricPhysicalFaceFactor anchorCoupling n physical ≤
      anchorFaceCoefficient ^
        (excitedPlaquetteEntries n physical).length := by
  rw [excitedPlaquetteEntries_length_eq_ids]
  exact parametricPhysicalFaceFactor_anchor_le_supportPow hphysical

/-! ## 3. The support envelope closes the genuine Z4 counting budget -/

theorem parametricLocalizedSpinFoamWeight_anchor_le_supportProduct
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricLocalizedSpinFoamWeight anchorCoupling n physical ≤
      anchorFaceCoefficient ^
          (excitedPlaquetteEntries n physical).length *
        binaryLinkMultiplicityBound ^
          ((excitedPlaquetteEntries n physical).length * 4) := by
  unfold parametricLocalizedSpinFoamWeight
  have hface := parametricPhysicalFaceFactor_anchor_le_entryPow hphysical
  have hlink :=
    localizedLinkMultiplicityProduct_cutoff_one_le_supportPow hphysical
  have hface0 : (0 : Q') ≤
      parametricPhysicalFaceFactor anchorCoupling n physical := by
    unfold parametricPhysicalFaceFactor
    exact eliminateLinks_nonnegative_local _
      (fun edge => parametricCoefficient_nonnegative (by decide)
        (physical edge)) _
  have hlink0 : (0 : Q') ≤
      explicitLinkMultiplicityProduct 1 n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) :=
    explicitLinkMultiplicityProduct_nonnegative 1 n physical _
  have hfacePow0 : (0 : Q') ≤
      anchorFaceCoefficient ^
        (excitedPlaquetteEntries n physical).length :=
    Q'.pow_nonneg anchorFaceCoefficient (by decide) _
  have hfirst :
      parametricPhysicalFaceFactor anchorCoupling n physical *
          explicitLinkMultiplicityProduct 1 n physical
            ((enumerate (distinctBoxLinks n)).filter
              (linkTouchesExcitationB n physical)) ≤
        anchorFaceCoefficient ^
            (excitedPlaquetteEntries n physical).length *
          explicitLinkMultiplicityProduct 1 n physical
            ((enumerate (distinctBoxLinks n)).filter
              (linkTouchesExcitationB n physical)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hface hlink0
  have hsecond :
      anchorFaceCoefficient ^
            (excitedPlaquetteEntries n physical).length *
          explicitLinkMultiplicityProduct 1 n physical
            ((enumerate (distinctBoxLinks n)).filter
              (linkTouchesExcitationB n physical)) ≤
        anchorFaceCoefficient ^
            (excitedPlaquetteEntries n physical).length *
          binaryLinkMultiplicityBound ^
            ((excitedPlaquetteEntries n physical).length * 4) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlink hfacePow0
  exact Q'.le_trans' _ _ _ hfirst hsecond

def anchorPerFaceEnvelope : Q' :=
  anchorFaceCoefficient * binaryLinkMultiplicityBound ^ 4

theorem anchorPerFaceEnvelope_eqv :
    anchorPerFaceEnvelope ≈ Q'.mkPos 16 125000 (by decide) := by
  decide

private theorem mul_four_regroup (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem pow_mul_base_eqv (a b : Q') : ∀ s : Nat,
    (a * b) ^ s ≈ a ^ s * b ^ s
  | 0 => by
      simp only [Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | s + 1 => by
      simp only [Q'.pow_succ]
      refine Q'.eqv_trans _
        ((a * b) * (a ^ s * b ^ s)) _
        (Q'.mul_eqv_congr_left (a * b) _ _
          (pow_mul_base_eqv a b s)) ?_
      exact mul_four_regroup a b (a ^ s) (b ^ s)

private theorem pow_nat_mul_eqv (b : Q') (k : Nat) : ∀ s : Nat,
    b ^ (s * k) ≈ (b ^ k) ^ s
  | 0 => by
      simp only [Nat.zero_mul, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | s + 1 => by
      have hindex : (s + 1) * k = s * k + k := by
        simp [Nat.add_mul]
      rw [hindex, Q'.pow_succ]
      refine Q'.eqv_trans _ (b ^ (s * k) * b ^ k) _
        (Q'.pow_add_eqv b (s * k) k) ?_
      refine Q'.eqv_trans _ ((b ^ k) ^ s * b ^ k) _
        (qmul_congr (pow_nat_mul_eqv b k s) (Q'.eqv_refl _)) ?_
      exact Q'.mul_comm_eqv _ _

theorem supportProduct_eqv_anchorPerFaceEnvelopePow (s : Nat) :
    anchorFaceCoefficient ^ s *
        binaryLinkMultiplicityBound ^ (s * 4) ≈
      anchorPerFaceEnvelope ^ s := by
  unfold anchorPerFaceEnvelope
  refine Q'.eqv_trans _
    (anchorFaceCoefficient ^ s *
      (binaryLinkMultiplicityBound ^ 4) ^ s) _
    (qmul_congr (Q'.eqv_refl _)
      (pow_nat_mul_eqv binaryLinkMultiplicityBound 4 s)) ?_
  exact Q'.eqv_symm
    (pow_mul_base_eqv anchorFaceCoefficient
      (binaryLinkMultiplicityBound ^ 4) s)

theorem parametricLocalizedSpinFoamWeight_anchor_le_envelopePow
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricLocalizedSpinFoamWeight anchorCoupling n physical ≤
      anchorPerFaceEnvelope ^
        (excitedPlaquetteEntries n physical).length := by
  have hproduct :=
    parametricLocalizedSpinFoamWeight_anchor_le_supportProduct hphysical
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv
      (supportProduct_eqv_anchorPerFaceEnvelopePow
        (excitedPlaquetteEntries n physical).length))

def anchorEffectiveRatio : Q' :=
  animalK z4Chain * anchorPerFaceEnvelope * eSurrogate

theorem anchorEffectiveRatio_eqv_six_twentyfive :
    anchorEffectiveRatio ≈ Q'.mkPos 6 25 (by decide) := by
  decide

theorem anchorEffectiveRatio_le_half :
    anchorEffectiveRatio ≤ Q'.mkPos 1 2 (by decide) := by
  decide

theorem anchorEffectiveRatio_lt_one :
    anchorEffectiveRatio < (1 : Q') := by
  decide

end YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.explicitValenceMultiplicity_binary_le_eight
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.explicitLinkMultiplicityFactor_cutoff_one_le_eight
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.localizedLinkMultiplicityProduct_cutoff_one_le_supportPow
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorFundamentalCoefficient
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.parametricPhysicalFaceFactor_anchor_le_entryPow
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.parametricLocalizedSpinFoamWeight_anchor_le_supportProduct
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorPerFaceEnvelope_eqv
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.parametricLocalizedSpinFoamWeight_anchor_le_envelopePow
#print axioms YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorEffectiveRatio_le_half
