/-
# Exact factorization of link-separated cutoff-one components

At cutoff one a physical face labelling is binary.  This module proves the
pointwise algebra behind the corrected polymer gas: if two binary supports
are face-disjoint and no physical lattice link is touched by both supports,
then their union is again a physical labelling and its exact parameterized
spin-foam weight is the product of the two component weights.

This is stronger than an activity bound.  It is an exact statement about the
same packet graph constructed in `Z4ParametricCutoffOneSpinFoamIdentity`.
The remaining combinatorial step is to enumerate every binary support by its
maximal link-connected components and prove uniqueness of that decomposition.
-/

import YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity

namespace YMGap.Continuum.Z4LinkSeparatedComponentFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def binaryUnionLabel (left right : EdgeLabelling) : EdgeLabelling :=
  fun edge => left edge + right edge

def FaceDisjoint (n : Nat) (left right : EdgeLabelling) : Prop :=
  ∀ edge, edge ∈ physicalFaceEdges n →
    left edge = 0 ∨ right edge = 0

def LinkSeparated (n : Nat) (left right : EdgeLabelling) : Prop :=
  ∀ indexed, indexed ∈ enumerate (distinctBoxLinks n) →
    ¬ (linkTouchesExcitationB n left indexed = true ∧
      linkTouchesExcitationB n right indexed = true)

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

private theorem binary_cases {x : Nat} (hx : x < 2) : x = 0 ∨ x = 1 := by
  omega

/-! ## 1. Face products factor on disjoint binary supports -/

theorem binaryFaceCoefficient_union_eqv_mul
    (w : Q') {left right : Nat}
    (hleft : left < 2) (hright : right < 2)
    (hdisjoint : left = 0 ∨ right = 0) :
    coeffAt (heatKernelPacket 1 w) (left + right) ≈
      coeffAt (heatKernelPacket 1 w) left *
        coeffAt (heatKernelPacket 1 w) right := by
  rcases hdisjoint with hleft0 | hright0
  · subst left
    rcases binary_cases hright with hright0 | hright1
    · subst right
      rw [coeffAt_heatKernelPacket (by decide), coeffW_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
    · subst right
      simp only [Nat.zero_add]
      rw [coeffAt_heatKernelPacket (K := 1) (w := w)
        (spin := 0) (by decide), coeffW_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · subst right
    rcases binary_cases hleft with hleft0 | hleft1
    · subst left
      rw [coeffAt_heatKernelPacket (by decide), coeffW_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
    · subst left
      simp only [Nat.add_zero]
      rw [coeffAt_heatKernelPacket (K := 1) (w := w)
        (spin := 0) (by decide), coeffW_zero]
      exact Q'.eqv_symm (Q'.mul_one_eqv _)

private theorem eliminateBinaryUnion_factor
    (w : Q') (left right : EdgeLabelling) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → left edge < 2) →
      (∀ edge, edge ∈ edges → right edge < 2) →
      (∀ edge, edge ∈ edges → left edge = 0 ∨ right edge = 0) →
      eliminateLinks
          (fun edge => coeffAt (heatKernelPacket 1 w)
            (binaryUnionLabel left right edge)) edges ≈
        eliminateLinks
            (fun edge => coeffAt (heatKernelPacket 1 w) (left edge))
            edges *
          eliminateLinks
            (fun edge => coeffAt (heatKernelPacket 1 w) (right edge))
            edges
  | [], _, _, _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | edge :: rest, hleft, hright, hdisjoint => by
      have hhead := binaryFaceCoefficient_union_eqv_mul w
        (hleft edge List.mem_cons_self)
        (hright edge List.mem_cons_self)
        (hdisjoint edge List.mem_cons_self)
      have hrest := eliminateBinaryUnion_factor w left right rest
        (fun item hitem => hleft item (List.mem_cons_of_mem edge hitem))
        (fun item hitem => hright item (List.mem_cons_of_mem edge hitem))
        (fun item hitem => hdisjoint item
          (List.mem_cons_of_mem edge hitem))
      exact Q'.eqv_trans _
        ((coeffAt (heatKernelPacket 1 w) (left edge) *
            coeffAt (heatKernelPacket 1 w) (right edge)) *
          (eliminateLinks
              (fun item => coeffAt (heatKernelPacket 1 w) (left item))
              rest *
            eliminateLinks
              (fun item => coeffAt (heatKernelPacket 1 w) (right item))
              rest)) _
        (qmul_congr hhead hrest)
        (mul_four_regroup _ _ _ _)

theorem parametricPhysicalFaceFactor_union_factor
    {w : Q'} {n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ explicitPhysicalLabellings 1 n)
    (hright : right ∈ explicitPhysicalLabellings 1 n)
    (hdisjoint : FaceDisjoint n left right) :
    parametricPhysicalFaceFactor w n (binaryUnionLabel left right) ≈
      parametricPhysicalFaceFactor w n left *
        parametricPhysicalFaceFactor w n right := by
  have hleftSound := boundedEdgeLabellings_sound 1
    (physicalFaceEdges n) left hleft
  have hrightSound := boundedEdgeLabellings_sound 1
    (physicalFaceEdges n) right hright
  unfold parametricPhysicalFaceFactor
  exact eliminateBinaryUnion_factor w left right (physicalFaceEdges n)
    hleftSound.1 hrightSound.1 hdisjoint

/-! ## 2. Link multiplicities factor when no link is touched twice -/

private theorem explicitValenceMultiplicity_congr_prefix
    {cutoff degree : Nat} {left right : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hagree : ∀ position, position < degree →
      left position = right position) :
    explicitValenceMultiplicity cutoff degree left =
      explicitValenceMultiplicity cutoff degree right := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · change oneValentMultiplicity cutoff (left 0) =
      oneValentMultiplicity cutoff (right 0)
    rw [hagree 0 (by omega)]
  · change twoValentMultiplicity cutoff (left 0) (left 1) =
      twoValentMultiplicity cutoff (right 0) (right 1)
    rw [hagree 0 (by omega), hagree 1 (by omega)]
  · change boolMultiplicity (fusionOK (left 0) (left 1) (left 2)) =
      boolMultiplicity (fusionOK (right 0) (right 1) (right 2))
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega)]
  · change oneChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) =
      oneChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega)]
  · change twoChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) (left 4) =
      twoChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3) (right 4)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega), hagree 4 (by omega)]
  · change threeChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) (left 4) (left 5) =
      threeChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3) (right 4) (right 5)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega), hagree 4 (by omega),
      hagree 5 (by omega)]

private theorem explicitLinkMultiplicityFactor_union_eq_right_of_left_untouched
    {n : Nat} {left right : EdgeLabelling}
    {indexed : Nat × Z4Link}
    (huntouched : linkTouchesExcitationB n left indexed = false) :
    explicitLinkMultiplicityFactor 1 n (binaryUnionLabel left right)
        indexed =
      explicitLinkMultiplicityFactor 1 n right indexed := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on left
      (incidentPlaqIds n indexed.2)).1 huntouched
  unfold explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  apply explicitValenceMultiplicity_congr_prefix
  · exact incidentPlaqIds_length_le_six n indexed.2
  · intro position hposition
    have hid := localIdentifierRename_mem_of_lt
      (incidentPlaqIds n indexed.2) (linkBlockBase n indexed.1)
      position hposition
    unfold binaryUnionLabel
    rw [hzeroOn _ hid, Nat.zero_add]

private theorem explicitLinkMultiplicityFactor_union_eq_left_of_right_untouched
    {n : Nat} {left right : EdgeLabelling}
    {indexed : Nat × Z4Link}
    (huntouched : linkTouchesExcitationB n right indexed = false) :
    explicitLinkMultiplicityFactor 1 n (binaryUnionLabel left right)
        indexed =
      explicitLinkMultiplicityFactor 1 n left indexed := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on right
      (incidentPlaqIds n indexed.2)).1 huntouched
  unfold explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  apply explicitValenceMultiplicity_congr_prefix
  · exact incidentPlaqIds_length_le_six n indexed.2
  · intro position hposition
    have hid := localIdentifierRename_mem_of_lt
      (incidentPlaqIds n indexed.2) (linkBlockBase n indexed.1)
      position hposition
    unfold binaryUnionLabel
    rw [hzeroOn _ hid, Nat.add_zero]

theorem explicitLinkMultiplicityFactor_union_factor
    {n : Nat} {left right : EdgeLabelling}
    (indexed : Nat × Z4Link)
    (hseparated : ¬
      (linkTouchesExcitationB n left indexed = true ∧
        linkTouchesExcitationB n right indexed = true)) :
    explicitLinkMultiplicityFactor 1 n (binaryUnionLabel left right)
        indexed ≈
      explicitLinkMultiplicityFactor 1 n left indexed *
        explicitLinkMultiplicityFactor 1 n right indexed := by
  cases hleft : linkTouchesExcitationB n left indexed with
  | false =>
      rw [explicitLinkMultiplicityFactor_union_eq_right_of_left_untouched
        hleft,
        explicitLinkMultiplicityFactor_eq_one_of_untouched hleft]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | true =>
      have hright : linkTouchesExcitationB n right indexed = false := by
        cases hr : linkTouchesExcitationB n right indexed with
        | false => rfl
        | true => exact False.elim (hseparated ⟨hleft, hr⟩)
      rw [explicitLinkMultiplicityFactor_union_eq_left_of_right_untouched
        hright,
        explicitLinkMultiplicityFactor_eq_one_of_untouched hright]
      exact Q'.eqv_symm (Q'.mul_one_eqv _)

theorem explicitLinkMultiplicityProduct_union_factor
    (n : Nat) (left right : EdgeLabelling) :
    ∀ links : List (Nat × Z4Link),
      (∀ indexed, indexed ∈ links → ¬
        (linkTouchesExcitationB n left indexed = true ∧
          linkTouchesExcitationB n right indexed = true)) →
      explicitLinkMultiplicityProduct 1 n (binaryUnionLabel left right)
          links ≈
        explicitLinkMultiplicityProduct 1 n left links *
          explicitLinkMultiplicityProduct 1 n right links
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | indexed :: rest, hseparated => by
      have hhead := explicitLinkMultiplicityFactor_union_factor indexed
        (hseparated indexed List.mem_cons_self)
      have hrest := explicitLinkMultiplicityProduct_union_factor
        n left right rest
        (fun item hitem => hseparated item
          (List.mem_cons_of_mem indexed hitem))
      exact Q'.eqv_trans _
        ((explicitLinkMultiplicityFactor 1 n left indexed *
            explicitLinkMultiplicityFactor 1 n right indexed) *
          (explicitLinkMultiplicityProduct 1 n left rest *
            explicitLinkMultiplicityProduct 1 n right rest)) _
        (qmul_congr hhead hrest)
        (mul_four_regroup _ _ _ _)

/-! ## 3. Exact component factorization in the physical sum -/

def parametricFullSpinFoamWeight (w : Q') (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  parametricPhysicalFaceFactor w n physical *
    explicitLinkMultiplicityProduct 1 n physical
      (enumerate (distinctBoxLinks n))

theorem binaryUnionLabel_mem_physical
    {n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ explicitPhysicalLabellings 1 n)
    (hright : right ∈ explicitPhysicalLabellings 1 n)
    (hdisjoint : FaceDisjoint n left right) :
    binaryUnionLabel left right ∈ explicitPhysicalLabellings 1 n := by
  unfold explicitPhysicalLabellings
  have hleftSound := boundedEdgeLabellings_sound 1
    (physicalFaceEdges n) left hleft
  have hrightSound := boundedEdgeLabellings_sound 1
    (physicalFaceEdges n) right hright
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    unfold binaryUnionLabel
    rcases hdisjoint edge hedge with hleft0 | hright0
    · rw [hleft0, Nat.zero_add]
      exact hrightSound.1 edge hedge
    · rw [hright0, Nat.add_zero]
      exact hleftSound.1 edge hedge
  · intro edge hedge
    unfold binaryUnionLabel
    rw [hleftSound.2 edge hedge, hrightSound.2 edge hedge]

theorem parametricFullSpinFoamWeight_union_factor
    {w : Q'} {n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ explicitPhysicalLabellings 1 n)
    (hright : right ∈ explicitPhysicalLabellings 1 n)
    (hface : FaceDisjoint n left right)
    (hlink : LinkSeparated n left right) :
    parametricFullSpinFoamWeight w n (binaryUnionLabel left right) ≈
      parametricFullSpinFoamWeight w n left *
        parametricFullSpinFoamWeight w n right := by
  unfold parametricFullSpinFoamWeight
  have hfaces := parametricPhysicalFaceFactor_union_factor (w := w)
    hleft hright hface
  have hlinks := explicitLinkMultiplicityProduct_union_factor
    n left right (enumerate (distinctBoxLinks n)) hlink
  exact Q'.eqv_trans _
    ((parametricPhysicalFaceFactor w n left *
        parametricPhysicalFaceFactor w n right) *
      (explicitLinkMultiplicityProduct 1 n left
          (enumerate (distinctBoxLinks n)) *
        explicitLinkMultiplicityProduct 1 n right
          (enumerate (distinctBoxLinks n)))) _
    (qmul_congr hfaces hlinks)
    (mul_four_regroup _ _ _ _)

theorem parametricLocalizedSpinFoamWeight_union_factor
    {w : Q'} {n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ explicitPhysicalLabellings 1 n)
    (hright : right ∈ explicitPhysicalLabellings 1 n)
    (hface : FaceDisjoint n left right)
    (hlink : LinkSeparated n left right) :
    parametricLocalizedSpinFoamWeight w n (binaryUnionLabel left right) ≈
      parametricLocalizedSpinFoamWeight w n left *
        parametricLocalizedSpinFoamWeight w n right := by
  have hunionLocal := parametricSpinFoamWeight_eq_localized
    w n (binaryUnionLabel left right)
  have hleftLocal := parametricSpinFoamWeight_eq_localized w n left
  have hrightLocal := parametricSpinFoamWeight_eq_localized w n right
  refine Q'.eqv_trans _
    (parametricFullSpinFoamWeight w n (binaryUnionLabel left right)) _
    (Q'.eqv_symm hunionLocal) ?_
  refine Q'.eqv_trans _
    (parametricFullSpinFoamWeight w n left *
      parametricFullSpinFoamWeight w n right) _
    (parametricFullSpinFoamWeight_union_factor
      hleft hright hface hlink) ?_
  exact qmul_congr hleftLocal hrightLocal

end YMGap.Continuum.Z4LinkSeparatedComponentFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LinkSeparatedComponentFactorization.binaryFaceCoefficient_union_eqv_mul
#print axioms YMGap.Continuum.Z4LinkSeparatedComponentFactorization.parametricPhysicalFaceFactor_union_factor
#print axioms YMGap.Continuum.Z4LinkSeparatedComponentFactorization.explicitLinkMultiplicityProduct_union_factor
#print axioms YMGap.Continuum.Z4LinkSeparatedComponentFactorization.binaryUnionLabel_mem_physical
#print axioms YMGap.Continuum.Z4LinkSeparatedComponentFactorization.parametricLocalizedSpinFoamWeight_union_factor
