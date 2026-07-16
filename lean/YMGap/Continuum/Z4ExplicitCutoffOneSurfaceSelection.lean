/-
# Exact closed-surface selection at the first physical cutoff

For an SU(2) fusion path, the parity of the sum of all external labels is
even.  At physical cutoff one every face label is either zero or one, so this
parity is exactly the parity of the number of excited plaquettes incident on
the link.  Consequently a labelling with odd excited incidence at any link
has identically zero spin-foam weight.  In particular, the surviving cutoff-
one supports are mod-two closed plaquette surfaces rather than arbitrary
plaquette animals.
-/

import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.Z4ExplicitSupportMajorantFence
import YMGap.Continuum.Z4LinkIdentifierFreshness

namespace YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Parity selection for the seven explicit local formulas -/

def localExternalSpinSum (degree : Nat) (external : EdgeLabelling) : Nat :=
  natListSum ((List.range degree).map external)

private theorem range_one : List.range 1 = [0] := rfl
private theorem range_two : List.range 2 = [0, 1] := rfl
private theorem range_three : List.range 3 = [0, 1, 2] := rfl
private theorem range_four : List.range 4 = [0, 1, 2, 3] := rfl
private theorem range_five : List.range 5 = [0, 1, 2, 3, 4] := rfl
private theorem range_six : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

private theorem filter_len_zero_local {A : Type} (p : A → Bool) :
    ∀ xs : List A, (∀ x, x ∈ xs → p x = false) →
      (xs.filter p).length = 0
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.filter_cons, h x List.mem_cons_self]
      exact filter_len_zero_local p xs
        (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem explicitValenceMultiplicity_eq_zero_of_odd_sum
    {cutoff degree : Nat} {external : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hodd : localExternalSpinSum degree external % 2 = 1) :
    explicitValenceMultiplicity cutoff degree external = 0 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [localExternalSpinSum, natListSum] at hodd
  · change oneValentMultiplicity cutoff (external 0) = 0
    unfold oneValentMultiplicity
    apply filter_len_zero_local
    intro vacuum _
    cases hguard :
        (BondMovingStep.fusionOK (external 0) vacuum vacuum &&
          decide (vacuum = 0)) with
    | false => rfl
    | true =>
        have hparts := (Bool.and_eq_true _ _).mp hguard
        have hvacuum : vacuum = 0 := by
          simpa only [decide_eq_true_eq] using hparts.2
        have hparity :=
          ((fusionOK_eq_true_iff (external 0) vacuum vacuum).1 hparts.1).2.2
        simp [localExternalSpinSum, natListSum] at hodd
        omega
  · change twoValentMultiplicity cutoff (external 0) (external 1) = 0
    unfold twoValentMultiplicity
    apply filter_len_zero_local
    intro vacuum _
    cases hguard :
        (BondMovingStep.fusionOK (external 0) (external 1) vacuum &&
          decide (vacuum = 0)) with
    | false => rfl
    | true =>
        have hparts := (Bool.and_eq_true _ _).mp hguard
        have hvacuum : vacuum = 0 := by
          simpa only [decide_eq_true_eq] using hparts.2
        have hparity :=
          ((fusionOK_eq_true_iff (external 0) (external 1) vacuum).1
            hparts.1).2.2
        simp [localExternalSpinSum, range_two, natListSum] at hodd
        omega
  · change boolMultiplicity
      (BondMovingStep.fusionOK (external 0) (external 1) (external 2)) = 0
    unfold boolMultiplicity
    cases hfusion :
        BondMovingStep.fusionOK (external 0) (external 1) (external 2) with
    | false => rfl
    | true =>
        have hparity :=
          ((fusionOK_eq_true_iff (external 0) (external 1) (external 2)).1
            hfusion).2.2
        simp [localExternalSpinSum, range_three, natListSum] at hodd
        omega
  · change oneChannelMultiplicity cutoff (external 0) (external 1)
      (external 2) (external 3) = 0
    unfold oneChannelMultiplicity
    apply filter_len_zero_local
    intro x _
    cases hguard :
        (BondMovingStep.fusionOK (external 0) (external 1) x &&
          BondMovingStep.fusionOK x (external 2) (external 3)) with
    | false => rfl
    | true =>
        have hparts := (Bool.and_eq_true _ _).mp hguard
        have hfirst :=
          ((fusionOK_eq_true_iff (external 0) (external 1) x).1
            hparts.1).2.2
        have hsecond :=
          ((fusionOK_eq_true_iff x (external 2) (external 3)).1
            hparts.2).2.2
        simp [localExternalSpinSum, range_four, natListSum] at hodd
        omega
  · change twoChannelMultiplicity cutoff (external 0) (external 1)
      (external 2) (external 3) (external 4) = 0
    unfold twoChannelMultiplicity
    apply filter_len_zero_local
    intro xy _
    cases hguard :
        (BondMovingStep.fusionOK (external 0) (external 1) xy.1 &&
          (BondMovingStep.fusionOK xy.1 (external 2) xy.2 &&
            BondMovingStep.fusionOK xy.2 (external 3) (external 4))) with
    | false => rfl
    | true =>
        have hparts := (Bool.and_eq_true _ _).mp hguard
        have htail := (Bool.and_eq_true _ _).mp hparts.2
        have hfirst :=
          ((fusionOK_eq_true_iff (external 0) (external 1) xy.1).1
            hparts.1).2.2
        have hsecond :=
          ((fusionOK_eq_true_iff xy.1 (external 2) xy.2).1
            htail.1).2.2
        have hthird :=
          ((fusionOK_eq_true_iff xy.2 (external 3) (external 4)).1
            htail.2).2.2
        simp [localExternalSpinSum, range_five, natListSum] at hodd
        omega
  · change threeChannelMultiplicity cutoff (external 0) (external 1)
      (external 2) (external 3) (external 4) (external 5) = 0
    unfold threeChannelMultiplicity
    apply filter_len_zero_local
    intro xyz _
    cases hguard :
        (BondMovingStep.fusionOK (external 0) (external 1) xyz.1 &&
          (BondMovingStep.fusionOK xyz.1 (external 2) xyz.2.1 &&
            (BondMovingStep.fusionOK xyz.2.1 (external 3) xyz.2.2 &&
              BondMovingStep.fusionOK xyz.2.2 (external 4) (external 5)))) with
    | false => rfl
    | true =>
        have hparts := (Bool.and_eq_true _ _).mp hguard
        have htail := (Bool.and_eq_true _ _).mp hparts.2
        have hlast := (Bool.and_eq_true _ _).mp htail.2
        have hfirst :=
          ((fusionOK_eq_true_iff (external 0) (external 1) xyz.1).1
            hparts.1).2.2
        have hsecond :=
          ((fusionOK_eq_true_iff xyz.1 (external 2) xyz.2.1).1
            htail.1).2.2
        have hthird :=
          ((fusionOK_eq_true_iff xyz.2.1 (external 3) xyz.2.2).1
            hlast.1).2.2
        have hfourth :=
          ((fusionOK_eq_true_iff xyz.2.2 (external 4) (external 5)).1
            hlast.2).2.2
        simp [localExternalSpinSum, range_six, natListSum] at hodd
        omega

/-! ## 2. At cutoff one, spin parity is excitation-count parity -/

def incidentSpinSum (n : Nat) (physical : EdgeLabelling)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Nat :=
  natListSum ((incidentPlaqIds n ell).map physical)

def excitedIncidentPlaqIds (n : Nat) (physical : EdgeLabelling)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : List Nat :=
  (incidentPlaqIds n ell).filter
    (fun plaquetteId => decide (1 ≤ physical plaquetteId))

theorem localExternalSpinSum_eq_incidentSpinSum
    (n i : Nat) (physical : EdgeLabelling)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    localExternalSpinSum (incidentPlaqIds n ell).length
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) position)) =
      incidentSpinSum n physical ell := by
  unfold localExternalSpinSum incidentSpinSum
  have hrename := map_localIdentifierRename_range
    (incidentPlaqIds n ell) (linkBlockBase n i)
  have hmapped := congrArg (List.map physical) hrename
  rw [List.map_map] at hmapped
  simpa only [Function.comp_apply] using congrArg natListSum hmapped

private theorem natListSum_map_eq_filter_length_of_binary
    (physical : EdgeLabelling) : ∀ ids : List Nat,
    (∀ plaquetteId, plaquetteId ∈ ids → physical plaquetteId ≤ 1) →
    natListSum (ids.map physical) =
      (ids.filter (fun plaquetteId =>
        decide (1 ≤ physical plaquetteId))).length
  | [], _ => rfl
  | plaquetteId :: rest, hbound => by
      have hrest := natListSum_map_eq_filter_length_of_binary physical rest
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem plaquetteId hitem))
      have hhead := hbound plaquetteId List.mem_cons_self
      by_cases hexcited : 1 ≤ physical plaquetteId
      · have hone : physical plaquetteId = 1 := by omega
        simp [natListSum, hone, hrest, Nat.add_comm]
      · have hzero : physical plaquetteId = 0 := by omega
        simp [natListSum, hzero, hrest]

theorem incidentSpinSum_eq_excitedIncidence_of_cutoff_one
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    incidentSpinSum n physical ell =
      (excitedIncidentPlaqIds n physical ell).length := by
  unfold incidentSpinSum excitedIncidentPlaqIds
  apply natListSum_map_eq_filter_length_of_binary
  intro plaquetteId hid
  have hsound := boundedEdgeLabellings_sound 1 (physicalFaceEdges n)
    physical hphysical
  have hidGlobal := (mem_incidentPlaqIds.mp hid)
  obtain ⟨plaquette, hindexed, _⟩ := hidGlobal
  have hidlt :=
    Z4LinkIdentifierFreshness.enumerate_index_lt hindexed
  have hidPhysical : plaquetteId ∈ physicalFaceEdges n := by
    unfold physicalFaceEdges plaquetteEdgeCount
    exact List.mem_range.mpr hidlt
  have := hsound.1 plaquetteId hidPhysical
  omega

/-! ## 3. Odd incidence annihilates the global spin-foam weight -/

/-- At every physical cutoff, odd total incident SU(2) label parity kills the
local Haar multiplicity. -/
theorem explicitLinkMultiplicityFactor_eq_zero_of_odd_incidentSpinSum
    {K n i : Nat} {physical : EdgeLabelling}
    {ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hodd : incidentSpinSum n physical ell % 2 = 1) :
    explicitLinkMultiplicityFactor K n physical (i, ell) = 0 := by
  have hlocalSum := localExternalSpinSum_eq_incidentSpinSum n i physical ell
  have hlocalOdd :
      localExternalSpinSum (incidentPlaqIds n ell).length
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) position)) % 2 = 1 := by
    rw [hlocalSum]
    exact hodd
  have hzero := explicitValenceMultiplicity_eq_zero_of_odd_sum
    (cutoff := linkAuxiliaryCutoff K)
    (incidentPlaqIds_length_le_six n ell) hlocalOdd
  unfold explicitLinkMultiplicityFactor
  rw [hzero]
  rfl

theorem explicitLinkMultiplicityFactor_eq_zero_of_odd_incidence
    {n i : Nat} {physical : EdgeLabelling}
    {ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n)
    (hodd : (excitedIncidentPlaqIds n physical ell).length % 2 = 1) :
    explicitLinkMultiplicityFactor 1 n physical (i, ell) = 0 := by
  have hsum := incidentSpinSum_eq_excitedIncidence_of_cutoff_one
    hphysical ell
  apply explicitLinkMultiplicityFactor_eq_zero_of_odd_incidentSpinSum
  rw [hsum]
  exact hodd

private theorem explicitLinkMultiplicityProduct_eqv_zero_of_factor
    {K n : Nat} {physical : EdgeLabelling}
    {indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hfactor : explicitLinkMultiplicityFactor K n physical indexed = 0) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      indexed ∈ links →
      explicitLinkMultiplicityProduct K n physical links ≈ 0
  | [], hmem => by cases hmem
  | head :: rest, hmem => by
      rw [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · subst head
        change explicitLinkMultiplicityFactor K n physical indexed *
            explicitLinkMultiplicityProduct K n physical rest ≈ 0
        rw [hfactor]
        exact Q'.zero_mul_eqv _
      · change explicitLinkMultiplicityFactor K n physical head *
            explicitLinkMultiplicityProduct K n physical rest ≈ 0
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (explicitLinkMultiplicityProduct_eqv_zero_of_factor hfactor
              rest hrest))
          (Q'.mul_zero_eqv _)

/-- At arbitrary cutoff, a single odd-spin-sum link annihilates the complete
finite-volume spin-foam configuration. -/
theorem explicitSpinFoamWeight_eqv_zero_of_odd_incidentSpinSum
    {K n i : Nat} {physical : EdgeLabelling}
    {ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (hodd : incidentSpinSum n physical ell % 2 = 1) :
    explicitSpinFoamWeight K n physical ≈ 0 := by
  have hfactor :=
    explicitLinkMultiplicityFactor_eq_zero_of_odd_incidentSpinSum
      (K := K) (i := i) hodd
  have hproduct := explicitLinkMultiplicityProduct_eqv_zero_of_factor
    hfactor (enumerate (distinctBoxLinks n)) hindexed
  unfold explicitSpinFoamWeight
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hproduct)
    (Q'.mul_zero_eqv _)

/-- A cutoff-one labelling with odd excited incidence at any physical link has
exactly zero global spin-foam weight. -/
theorem explicitSpinFoamWeight_eqv_zero_of_odd_incidence
    {n i : Nat} {physical : EdgeLabelling}
    {ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n)
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (hodd : (excitedIncidentPlaqIds n physical ell).length % 2 = 1) :
    explicitSpinFoamWeight 1 n physical ≈ 0 := by
  have hfactor := explicitLinkMultiplicityFactor_eq_zero_of_odd_incidence
    (i := i) hphysical hodd
  have hproduct := explicitLinkMultiplicityProduct_eqv_zero_of_factor
    hfactor (enumerate (distinctBoxLinks n)) hindexed
  unfold explicitSpinFoamWeight
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hproduct)
    (Q'.mul_zero_eqv _)

end YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.explicitValenceMultiplicity_eq_zero_of_odd_sum
#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.incidentSpinSum_eq_excitedIncidence_of_cutoff_one
#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.explicitLinkMultiplicityFactor_eq_zero_of_odd_incidentSpinSum
#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.explicitSpinFoamWeight_eqv_zero_of_odd_incidentSpinSum
#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.explicitLinkMultiplicityFactor_eq_zero_of_odd_incidence
#print axioms YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection.explicitSpinFoamWeight_eqv_zero_of_odd_incidence
