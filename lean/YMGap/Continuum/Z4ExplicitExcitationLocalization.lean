/-
# Exact localization of link multiplicities to excited plaquettes

After the vacuum term is separated, a naive product still ranges over every
physical link in the box.  This file proves that a link whose incident
plaquette spins are all zero contributes exactly one.  Therefore the literal
link product may be filtered, without approximation, to links touching the
excitation support of the physical labelling.

The result removes volume-only factors before any estimate is applied.  A
subsequent polymer argument must still control the number and weights of the
remaining connected supports.
-/

import YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

namespace YMGap.Continuum.Z4ExplicitExcitationLocalization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FuseChainIdentifierTransport

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. A local factor only reads its geometric prefix -/

theorem explicitValenceMultiplicity_eq_one_of_zero_prefix
    {cutoff degree : Nat} {external : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hzero : ∀ position, position < degree → external position = 0) :
    explicitValenceMultiplicity cutoff degree external = 1 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · change oneValentMultiplicity cutoff (external 0) = 1
    rw [hzero 0 (by omega)]
    exact oneValentMultiplicity_allZero cutoff
  · change twoValentMultiplicity cutoff (external 0) (external 1) = 1
    rw [hzero 0 (by omega), hzero 1 (by omega)]
    exact twoValentMultiplicity_allZero cutoff
  · change boolMultiplicity
      (BondMovingStep.fusionOK (external 0) (external 1) (external 2)) = 1
    rw [hzero 0 (by omega), hzero 1 (by omega), hzero 2 (by omega)]
    rfl
  · change oneChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3) = 1
    rw [hzero 0 (by omega), hzero 1 (by omega), hzero 2 (by omega),
      hzero 3 (by omega)]
    exact oneChannelMultiplicity_allZero cutoff
  · change twoChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3) (external 4) = 1
    rw [hzero 0 (by omega), hzero 1 (by omega), hzero 2 (by omega),
      hzero 3 (by omega), hzero 4 (by omega)]
    exact twoChannelMultiplicity_allZero cutoff
  · change threeChannelMultiplicity cutoff
      (external 0) (external 1) (external 2) (external 3) (external 4)
        (external 5) = 1
    rw [hzero 0 (by omega), hzero 1 (by omega), hzero 2 (by omega),
      hzero 3 (by omega), hzero 4 (by omega), hzero 5 (by omega)]
    exact threeChannelMultiplicity_allZero cutoff

theorem localIdentifierRename_mem_of_lt
    (labels : List Nat) (base position : Nat)
    (hposition : position < labels.length) :
    localIdentifierRename labels base position ∈ labels := by
  have hpositionRange : position ∈ List.range labels.length :=
    List.mem_range.mpr hposition
  have hmapped : localIdentifierRename labels base position ∈
      (List.range labels.length).map (localIdentifierRename labels base) :=
    List.mem_map.mpr ⟨position, hpositionRange, rfl⟩
  rw [map_localIdentifierRename_range] at hmapped
  exact hmapped

/-! ## 2. Untouched physical links contribute the multiplicative unit -/

def linkTouchesExcitationB (n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Bool :=
  hasExcitedB physical (incidentPlaqIds n indexed.2)

def explicitLinkMultiplicityFactor (K n : Nat)
    (physical : EdgeLabelling)
    (indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Q' :=
  Q'.ofNat
    (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
      (incidentPlaqIds n indexed.2).length
      (fun position => physical
        (localIdentifierRename (incidentPlaqIds n indexed.2)
          (linkBlockBase n indexed.1) position)))

theorem explicitLinkMultiplicityFactor_eq_one_of_untouched
    {K n : Nat} {physical : EdgeLabelling}
    {indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    (huntouched : linkTouchesExcitationB n physical indexed = false) :
    explicitLinkMultiplicityFactor K n physical indexed = 1 := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on physical
      (incidentPlaqIds n indexed.2)).1 huntouched
  have hlocal : explicitValenceMultiplicity (linkAuxiliaryCutoff K)
      (incidentPlaqIds n indexed.2).length
      (fun position => physical
        (localIdentifierRename (incidentPlaqIds n indexed.2)
          (linkBlockBase n indexed.1) position)) = 1 := by
    apply explicitValenceMultiplicity_eq_one_of_zero_prefix
    · exact incidentPlaqIds_length_le_six n indexed.2
    · intro position hposition
      exact hzeroOn _
        (localIdentifierRename_mem_of_lt _ _ _ hposition)
  unfold explicitLinkMultiplicityFactor
  rw [hlocal]
  rfl

theorem explicitLinkMultiplicityProduct_eq_touched
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      explicitLinkMultiplicityProduct K n physical links ≈
        explicitLinkMultiplicityProduct K n physical
          (links.filter (linkTouchesExcitationB n physical))
  | [] => Q'.eqv_refl 1
  | indexed :: rest => by
      cases htouched : linkTouchesExcitationB n physical indexed with
      | false =>
          simp only [List.filter_cons, htouched, Bool.false_eq_true, if_false]
          change explicitLinkMultiplicityFactor K n physical indexed *
              explicitLinkMultiplicityProduct K n physical rest ≈
            explicitLinkMultiplicityProduct K n physical
              (rest.filter (linkTouchesExcitationB n physical))
          rw [explicitLinkMultiplicityFactor_eq_one_of_untouched htouched]
          exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
            (explicitLinkMultiplicityProduct_eq_touched K n physical rest)
      | true =>
          simp only [List.filter_cons, htouched, if_true]
          change explicitLinkMultiplicityFactor K n physical indexed *
              explicitLinkMultiplicityProduct K n physical rest ≈
            explicitLinkMultiplicityFactor K n physical indexed *
              explicitLinkMultiplicityProduct K n physical
                (rest.filter (linkTouchesExcitationB n physical))
          exact qmul_congr (Q'.eqv_refl _)
            (explicitLinkMultiplicityProduct_eq_touched K n physical rest)

/-! ## 3. The whole excited partition has an exactly localized product -/

def localizedSpinFoamWeight (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  explicitPhysicalFaceFactor K n physical *
    explicitLinkMultiplicityProduct K n physical
      ((enumerate (distinctBoxLinks n)).filter
        (linkTouchesExcitationB n physical))

theorem explicitSpinFoamWeight_eq_localized
    (K n : Nat) (physical : EdgeLabelling) :
    explicitSpinFoamWeight K n physical ≈
      localizedSpinFoamWeight K n physical := by
  unfold explicitSpinFoamWeight localizedSpinFoamWeight
  exact qmul_congr (Q'.eqv_refl _)
    (explicitLinkMultiplicityProduct_eq_touched K n physical _)

private theorem listQSum_congr_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h =>
      Q'.add_eqv_congr' (h x List.mem_cons_self)
        (listQSum_congr_local xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem explicitExcitedSpinFoamSum_eq_localized (K n : Nat) :
    explicitExcitedSpinFoamSum K n ≈
      listQSum (localizedSpinFoamWeight K n)
        (explicitExcitedPhysicalLabellings K n) := by
  unfold explicitExcitedSpinFoamSum
  apply listQSum_congr_local
  intro physical _
  exact explicitSpinFoamWeight_eq_localized K n physical

theorem fusionCompleteBoxVertexCartesianSum_eq_one_add_localizedExcited
    (K n : Nat) :
    Z4ConditionalLinkAuxiliaryElimination.fusionCompleteBoxVertexCartesianSum
        K n ≈
      1 + listQSum (localizedSpinFoamWeight K n)
        (explicitExcitedPhysicalLabellings K n) := by
  exact Q'.eqv_trans _ (1 + explicitExcitedSpinFoamSum K n) _
    (fusionCompleteBoxVertexCartesianSum_eq_one_add_excited K n)
    (Q'.add_eqv_congr' (Q'.eqv_refl 1)
      (explicitExcitedSpinFoamSum_eq_localized K n))

end YMGap.Continuum.Z4ExplicitExcitationLocalization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitExcitationLocalization.explicitValenceMultiplicity_eq_one_of_zero_prefix
#print axioms YMGap.Continuum.Z4ExplicitExcitationLocalization.explicitLinkMultiplicityFactor_eq_one_of_untouched
#print axioms YMGap.Continuum.Z4ExplicitExcitationLocalization.explicitLinkMultiplicityProduct_eq_touched
#print axioms YMGap.Continuum.Z4ExplicitExcitationLocalization.explicitExcitedSpinFoamSum_eq_localized
#print axioms YMGap.Continuum.Z4ExplicitExcitationLocalization.fusionCompleteBoxVertexCartesianSum_eq_one_add_localizedExcited
