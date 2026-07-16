/-
# Exact factorization of link-separated components at arbitrary spin cutoff

The cutoff-one component factorization is not intrinsically binary.  If two
physical labellings have disjoint nonzero face support, then the heat-kernel
face coefficient of their pointwise sum is the product of their coefficients:
one of the two factors is the vacuum coefficient `1`.  If, in addition, no
physical lattice link is touched by both supports, the exact fusion
multiplicity factors for the same reason.

This module carries that observation through the literal arbitrary-cutoff
spin-foam term.  It is the algebraic prerequisite for replacing the binary
connected-surface gas by a gas whose polymers retain their complete spin
decoration.
-/

import YMGap.Continuum.Z4LinkSeparatedComponentFactorization
import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

namespace YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization

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
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

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

/-! ## 1. Arbitrary-cutoff face factors -/

theorem parametricKFaceCoefficient_union_eqv_mul
    (w : Q') (K : Nat) {left right : Nat}
    (hleft : left < K + 1) (hright : right < K + 1)
    (hdisjoint : left = 0 ∨ right = 0) :
    coeffAt (heatKernelPacket K w) (left + right) ≈
      coeffAt (heatKernelPacket K w) left *
        coeffAt (heatKernelPacket K w) right := by
  rcases hdisjoint with hleft0 | hright0
  · subst left
    simp only [Nat.zero_add]
    rw [coeffAt_heatKernelPacket hright,
      coeffAt_heatKernelPacket (show 0 < K + 1 by omega), coeffW_zero]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · subst right
    simp only [Nat.add_zero]
    rw [coeffAt_heatKernelPacket hleft,
      coeffAt_heatKernelPacket (show 0 < K + 1 by omega), coeffW_zero]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)

private theorem eliminateKUnion_factor
    (w : Q') (K : Nat) (left right : EdgeLabelling) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → left edge < K + 1) →
      (∀ edge, edge ∈ edges → right edge < K + 1) →
      (∀ edge, edge ∈ edges → left edge = 0 ∨ right edge = 0) →
      eliminateLinks
          (fun edge => coeffAt (heatKernelPacket K w)
            (binaryUnionLabel left right edge)) edges ≈
        eliminateLinks
            (fun edge => coeffAt (heatKernelPacket K w) (left edge))
            edges *
          eliminateLinks
            (fun edge => coeffAt (heatKernelPacket K w) (right edge))
            edges
  | [], _, _, _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | edge :: rest, hleft, hright, hdisjoint => by
      have hhead := parametricKFaceCoefficient_union_eqv_mul w K
        (hleft edge List.mem_cons_self)
        (hright edge List.mem_cons_self)
        (hdisjoint edge List.mem_cons_self)
      have hrest := eliminateKUnion_factor w K left right rest
        (fun item hitem => hleft item (List.mem_cons_of_mem edge hitem))
        (fun item hitem => hright item (List.mem_cons_of_mem edge hitem))
        (fun item hitem => hdisjoint item
          (List.mem_cons_of_mem edge hitem))
      exact Q'.eqv_trans _
        ((coeffAt (heatKernelPacket K w) (left edge) *
            coeffAt (heatKernelPacket K w) (right edge)) *
          (eliminateLinks
              (fun item => coeffAt (heatKernelPacket K w) (left item))
              rest *
            eliminateLinks
              (fun item => coeffAt (heatKernelPacket K w) (right item))
              rest)) _
        (qmul_congr hhead hrest)
        (mul_four_regroup _ _ _ _)

theorem parametricKPhysicalFaceFactor_union_factor
    {w : Q'} {K n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hdisjoint : FaceDisjoint n left right) :
    parametricKPhysicalFaceFactor w K n
        (binaryUnionLabel left right) ≈
      parametricKPhysicalFaceFactor w K n left *
        parametricKPhysicalFaceFactor w K n right := by
  have hleftSound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) left hleft
  have hrightSound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) right hright
  have hdisjoint' : ∀ edge,
      edge ∈ List.range (plaquetteEdgeCount n) →
        left edge = 0 ∨ right edge = 0 := by
    simpa [FaceDisjoint, physicalFaceEdges] using hdisjoint
  unfold parametricKPhysicalFaceFactor
  exact eliminateKUnion_factor w K left right
    (List.range (plaquetteEdgeCount n))
    hleftSound.1 hrightSound.1 hdisjoint'

/-! ## 2. Arbitrary-cutoff link multiplicities -/

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
    {K n : Nat} {left right : EdgeLabelling}
    {indexed : Nat × Z4Link}
    (huntouched : linkTouchesExcitationB n left indexed = false) :
    explicitLinkMultiplicityFactor K n (binaryUnionLabel left right)
        indexed =
      explicitLinkMultiplicityFactor K n right indexed := by
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
    {K n : Nat} {left right : EdgeLabelling}
    {indexed : Nat × Z4Link}
    (huntouched : linkTouchesExcitationB n right indexed = false) :
    explicitLinkMultiplicityFactor K n (binaryUnionLabel left right)
        indexed =
      explicitLinkMultiplicityFactor K n left indexed := by
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
    {K n : Nat} {left right : EdgeLabelling}
    (indexed : Nat × Z4Link)
    (hseparated : ¬
      (linkTouchesExcitationB n left indexed = true ∧
        linkTouchesExcitationB n right indexed = true)) :
    explicitLinkMultiplicityFactor K n (binaryUnionLabel left right)
        indexed ≈
      explicitLinkMultiplicityFactor K n left indexed *
        explicitLinkMultiplicityFactor K n right indexed := by
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
    (K n : Nat) (left right : EdgeLabelling) :
    ∀ links : List (Nat × Z4Link),
      (∀ indexed, indexed ∈ links → ¬
        (linkTouchesExcitationB n left indexed = true ∧
          linkTouchesExcitationB n right indexed = true)) →
      explicitLinkMultiplicityProduct K n (binaryUnionLabel left right)
          links ≈
        explicitLinkMultiplicityProduct K n left links *
          explicitLinkMultiplicityProduct K n right links
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | indexed :: rest, hseparated => by
      have hhead := explicitLinkMultiplicityFactor_union_factor
        (K := K) indexed
        (hseparated indexed List.mem_cons_self)
      have hrest := explicitLinkMultiplicityProduct_union_factor
        K n left right rest
        (fun item hitem => hseparated item
          (List.mem_cons_of_mem indexed hitem))
      exact Q'.eqv_trans _
        ((explicitLinkMultiplicityFactor K n left indexed *
            explicitLinkMultiplicityFactor K n right indexed) *
          (explicitLinkMultiplicityProduct K n left rest *
            explicitLinkMultiplicityProduct K n right rest)) _
        (qmul_congr hhead hrest)
        (mul_four_regroup _ _ _ _)

/-! ## 3. Exact arbitrary-cutoff term factorization -/

theorem unionLabel_mem_bounded
    {K n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hdisjoint : FaceDisjoint n left right) :
    binaryUnionLabel left right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)) := by
  have hleftSound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) left hleft
  have hrightSound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) right hright
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

private theorem eliminateLinks_eqv_one_local (value : Nat → Q') :
    ∀ edges : List Nat, (∀ edge, edge ∈ edges → value edge ≈ 1) →
      eliminateLinks value edges ≈ 1
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hvalue => by
      have hhead := hvalue edge List.mem_cons_self
      have hrest := eliminateLinks_eqv_one_local value rest
        (fun item hitem => hvalue item (List.mem_cons_of_mem edge hitem))
      exact Q'.eqv_trans _ (1 * 1) _
        (qmul_congr hhead hrest) (Q'.one_mul_eqv 1)

theorem parametricKPhysicalFaceFactor_zero_eqv_one
    (w : Q') (K n : Nat) :
    parametricKPhysicalFaceFactor w K n zeroEdgeLabelling ≈ 1 := by
  unfold parametricKPhysicalFaceFactor
  apply eliminateLinks_eqv_one_local
  intro edge _
  change coeffAt (heatKernelPacket K w) 0 ≈ 1
  rw [coeffAt_heatKernelPacket (show 0 < K + 1 by omega), coeffW_zero]
  exact Q'.eqv_refl 1

theorem parametricKPhysicalTerm_zero_eqv_one
    (w : Q') (K n : Nat) :
    parametricKPhysicalTerm w K n zeroEdgeLabelling ≈ 1 := by
  unfold parametricKPhysicalTerm
  exact Q'.eqv_trans _ (1 * 1) _
    (qmul_congr
      (parametricKPhysicalFaceFactor_zero_eqv_one w K n)
      (explicitLinkMultiplicityProduct_zero_eqv_one K n _))
    (Q'.one_mul_eqv 1)

theorem parametricKPhysicalTerm_union_factor
    {w : Q'} {K n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hface : FaceDisjoint n left right)
    (hlink : LinkSeparated n left right) :
    parametricKPhysicalTerm w K n (binaryUnionLabel left right) ≈
      parametricKPhysicalTerm w K n left *
        parametricKPhysicalTerm w K n right := by
  unfold parametricKPhysicalTerm
  have hfaces := parametricKPhysicalFaceFactor_union_factor
    (w := w) hleft hright hface
  have hlinks := explicitLinkMultiplicityProduct_union_factor
    K n left right (enumerate (distinctBoxLinks n)) hlink
  exact Q'.eqv_trans _
    ((parametricKPhysicalFaceFactor w K n left *
        parametricKPhysicalFaceFactor w K n right) *
      (explicitLinkMultiplicityProduct K n left
          (enumerate (distinctBoxLinks n)) *
        explicitLinkMultiplicityProduct K n right
          (enumerate (distinctBoxLinks n)))) _
    (qmul_congr hfaces hlinks)
    (mul_four_regroup _ _ _ _)

end YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.parametricKFaceCoefficient_union_eqv_mul
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.parametricKPhysicalFaceFactor_union_factor
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.explicitLinkMultiplicityProduct_union_factor
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.unionLabel_mem_bounded
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.parametricKPhysicalTerm_zero_eqv_one
#print axioms YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization.parametricKPhysicalTerm_union_factor
