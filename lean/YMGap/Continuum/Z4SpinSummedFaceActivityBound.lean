/-
# Cutoff-uniform summation of spin-decorated face activities

The exact incidence allocation charges the cubic link-fusion multiplicity by
`(spin + 1)^12` on every physical face.  Together with the heat-kernel
dimension factor, the resulting one-face weight is the existing Casimir tail
term of polynomial degree thirteen.

At the derived strong-coupling anchor `w = 1/400`, its exact consecutive-spin
ratio gives a cutoff-uniform sum below `1/7500`.  This is only slightly larger
than the cutoff-one envelope `16/125000`, and still gives the exact animal/KP
ratio `1/4`.
-/

import YMGap.Continuum.Z4SpinDependentIncidenceProductBound
import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
import YMGap.Continuum.Z4StrongCouplingParametricAnchor
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup
import YMGap.Continuum.Z4CanonicalPinnedPolymerBound

namespace YMGap.Continuum.Z4SpinSummedFaceActivityBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The degree-thirteen decorated face sequence -/

def anchorDecoratedFaceActivity (spin : Nat) : Q' :=
  tailTerm anchorCoupling 13 spin

def anchorDecoratedPlaqActivity (cutoff : Nat) : Q' :=
  finSum (fun offset => anchorDecoratedFaceActivity (1 + offset)) cutoff

def anchorDecoratedRatio : Q' :=
  Q'.ofNat (2 ^ 13) * qpow anchorCoupling 5

def anchorDecoratedFaceEnvelope : Q' :=
  Q'.mkPos 1 7500 (by decide)

theorem anchorDecoratedRatio_nonnegative :
    (0 : Q') ≤ anchorDecoratedRatio := by
  unfold anchorDecoratedRatio
  exact Q'.mul_nonneg _ _ (zero_le_ofNat _)
    (qpow_nonneg anchorCoupling (by decide) 5)

theorem anchorDecoratedFaceEnvelope_nonnegative :
    (0 : Q') ≤ anchorDecoratedFaceEnvelope := by decide

theorem anchorDecoratedFaceActivity_succ_ratio (offset : Nat) :
    anchorDecoratedFaceActivity (1 + (offset + 1)) ≤
      anchorDecoratedRatio * anchorDecoratedFaceActivity (1 + offset) := by
  have hindex : (1 + (offset + 1) : Nat) = (1 + offset) + 1 := by
    omega
  rw [hindex]
  simpa [anchorDecoratedFaceActivity, anchorDecoratedRatio] using
    tailTerm_ratio_gen
    (w := anchorCoupling) (by decide) (by decide)
    13 1 (1 + offset) (by omega)

theorem anchorDecoratedRecurrence :
    anchorDecoratedFaceActivity 1 +
      anchorDecoratedRatio * anchorDecoratedFaceEnvelope ≤
      anchorDecoratedFaceEnvelope := by
  unfold anchorDecoratedFaceActivity anchorDecoratedRatio
    anchorDecoratedFaceEnvelope tailTerm anchorCoupling
  dsimp [c4, qpow]
  decide

/-- The complete sum over spins `1, ..., cutoff` is bounded independently of
the cutoff. -/
theorem anchorDecoratedPlaqActivity_le_envelope (cutoff : Nat) :
    anchorDecoratedPlaqActivity cutoff ≤
      anchorDecoratedFaceEnvelope := by
  unfold anchorDecoratedPlaqActivity
  exact CharacterTail.geom_series_le
    (fun offset => anchorDecoratedFaceActivity (1 + offset))
    (anchorDecoratedFaceActivity 1) anchorDecoratedRatio
    anchorDecoratedFaceEnvelope
    anchorDecoratedRatio_nonnegative
    anchorDecoratedFaceEnvelope_nonnegative
    (Q'.le_refl' _)
    anchorDecoratedFaceActivity_succ_ratio
    anchorDecoratedRecurrence cutoff

/-! ## 2. A facewise majorant for every arbitrary-cutoff spin foam term -/

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_three_regroup (A B C : Q') :
    (A * B) * C ≈ (A * C) * B := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B C) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left A _ _ (Q'.mul_comm_eqv B C)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv A C B)

private theorem mul_four_regroup (A B C D : Q') :
    (A * B) * (C * D) ≈ (A * C) * (B * D) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem ofNat_mul_eqv (left right : Nat) :
    (Q'.ofNat left * Q'.ofNat right).eqv
      (Q'.ofNat (left * right)) := by
  show (Q'.ofNat left * Q'.ofNat right).num *
      ((Q'.ofNat (left * right)).den : Int) =
    (Q'.ofNat (left * right)).num *
      ((Q'.ofNat left * Q'.ofNat right).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat left) * (Int.ofNat right)) * 1 =
    (Int.ofNat (left * right)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

theorem coeffW_mul_twelfth_eqv_decoratedActivity
    (w : Q') (spin : Nat) :
    coeffW w spin * Q'.ofNat ((spin + 1) ^ 12) ≈
      tailTerm w 13 spin := by
  unfold coeffW dimQ tailTerm
  refine Q'.eqv_trans _ _ _
    (mul_three_regroup (Q'.ofNat (spin + 1))
      (qpow w (c4 spin)) (Q'.ofNat ((spin + 1) ^ 12))) ?_
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _ _ _
    (ofNat_mul_eqv (spin + 1) ((spin + 1) ^ 12)) ?_
  apply Q'.eqv_of_eq
  congr 1
  rw [Nat.pow_succ]
  exact Nat.mul_comm (spin + 1) ((spin + 1) ^ 12)

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem eliminateLinks_congr_eqv_local
    (left right : Nat → Q') :
    ∀ edges : List Nat, (∀ edge, edge ∈ edges → left edge ≈ right edge) →
      eliminateLinks left edges ≈ eliminateLinks right edges
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hagree =>
      qmul_congr (hagree edge List.mem_cons_self)
        (eliminateLinks_congr_eqv_local left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem edge hitem)))

private theorem eliminateLinks_pair_natProduct_eqv
    (value : Nat → Q') (charge : Nat → Nat) :
    ∀ edges : List Nat,
      eliminateLinks value edges *
          Q'.ofNat (natListProduct (edges.map charge)) ≈
        eliminateLinks
          (fun edge => value edge * Q'.ofNat (charge edge)) edges
  | [] => by
      change ((1 : Q') * Q'.ofNat 1).eqv 1
      decide
  | edge :: rest => by
      simp only [eliminateLinks, List.map_cons, natListProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (value edge * eliminateLinks value rest)
          _ _ (Q'.eqv_symm
            (ofNat_mul_eqv (charge edge)
              (natListProduct (rest.map charge))))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_four_regroup (value edge) (eliminateLinks value rest)
          (Q'.ofNat (charge edge))
          (Q'.ofNat (natListProduct (rest.map charge)))) ?_
      exact Q'.mul_eqv_congr_left
        (value edge * Q'.ofNat (charge edge)) _ _
        (eliminateLinks_pair_natProduct_eqv value charge rest)

theorem boxFaceTwelfthSpinProduct_eq_rangeProduct
    (n : Nat) (physical : EdgeLabelling) :
    boxFaceTwelfthSpinProduct n physical =
      natListProduct ((List.range (plaquetteEdgeCount n)).map fun edge =>
        (physical edge + 1) ^ 12) := by
  unfold boxFaceTwelfthSpinProduct plaquetteEdgeCount
  change natListProduct ((enumerate (boxPlaquettes n)).map
      ((fun edge => (physical edge + 1) ^ 12) ∘ Prod.fst)) = _
  rw [← List.map_map, enumerate_map_fst_eq_range]

theorem parametricKPhysicalFaceFactor_eq_coeffWProduct
    {w : Q'} {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalFaceFactor w K n physical =
      eliminateLinks (fun edge => coeffW w (physical edge))
        (List.range (plaquetteEdgeCount n)) := by
  unfold parametricKPhysicalFaceFactor
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  rw [coeffAt_heatKernelPacket (hsound.1 edge hedge)]

def anchorDecoratedFaceProduct (n : Nat)
    (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun edge => anchorDecoratedFaceActivity (physical edge))
    (List.range (plaquetteEdgeCount n))

/-- Every literal arbitrary-cutoff spin-foam term is bounded by the product of
its degree-thirteen decorated one-face activities. -/
theorem parametricKPhysicalTerm_anchor_le_decoratedFaceProduct
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm anchorCoupling K n physical ≤
      anchorDecoratedFaceProduct n physical := by
  have hfaceEq := parametricKPhysicalFaceFactor_eq_coeffWProduct
    (w := anchorCoupling) hphysical
  have hface0 : (0 : Q') ≤
      parametricKPhysicalFaceFactor anchorCoupling K n physical := by
    rw [hfaceEq]
    exact eliminateLinks_nonnegative_local _
      (fun edge => coeffW_nonneg (by decide) (physical edge)) _
  have hlink :=
    explicitLinkMultiplicityProduct_le_faceTwelfthSpinProduct
      K n physical
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hlink hface0
  unfold parametricKPhysicalTerm
  rw [hfaceEq]
  rw [hfaceEq, boxFaceTwelfthSpinProduct_eq_rangeProduct] at hmul
  refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (eliminateLinks_pair_natProduct_eqv
      (fun edge => coeffW anchorCoupling (physical edge))
      (fun edge => (physical edge + 1) ^ 12)
      (List.range (plaquetteEdgeCount n))) ?_
  unfold anchorDecoratedFaceProduct anchorDecoratedFaceActivity
  apply eliminateLinks_congr_eqv_local
  intro edge _
  exact coeffW_mul_twelfth_eqv_decoratedActivity
    anchorCoupling (physical edge)

/-! ## 3. Exact Cartesian enumeration of positive spin decorations -/

def positiveSpinValues (cutoff : Nat) : List Nat :=
  (List.range cutoff).map (fun offset => 1 + offset)

private theorem one_le_one_add (offset : Nat) : 1 ≤ 1 + offset :=
  Nat.le_add_right 1 offset

private theorem one_add_le_of_lt {offset cutoff : Nat}
    (hlt : offset < cutoff) : 1 + offset ≤ cutoff := by
  rw [Nat.add_comm]
  exact Nat.succ_le_of_lt hlt

private theorem sub_one_lt_of_bounds {spin cutoff : Nat}
    (hlower : 1 ≤ spin) (hupper : spin ≤ cutoff) :
    spin - 1 < cutoff := by
  have hback : spin - 1 + 1 = spin := Nat.sub_add_cancel hlower
  have hsucc : spin - 1 + 1 ≤ cutoff := hback ▸ hupper
  exact Nat.lt_of_succ_le hsucc

private theorem one_add_sub_one {spin : Nat} (hlower : 1 ≤ spin) :
    1 + (spin - 1) = spin := by
  rw [Nat.add_comm, Nat.sub_add_cancel hlower]

theorem mem_positiveSpinValues_iff {cutoff spin : Nat} :
    spin ∈ positiveSpinValues cutoff ↔ 1 ≤ spin ∧ spin ≤ cutoff := by
  constructor
  · intro hspin
    obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hspin
    exact ⟨one_le_one_add offset,
      one_add_le_of_lt (List.mem_range.mp hoffset)⟩
  · intro hspin
    apply List.mem_map.mpr
    exact ⟨spin - 1,
      List.mem_range.mpr (sub_one_lt_of_bounds hspin.1 hspin.2),
      one_add_sub_one hspin.1⟩

def positiveSpinVectors (cutoff : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | size + 1 =>
      (cartesian (positiveSpinValues cutoff)
        (positiveSpinVectors cutoff size)).map
          (fun pair => pair.1 :: pair.2)

theorem mem_positiveSpinVectors_iff (cutoff size : Nat)
    (vector : List Nat) :
    vector ∈ positiveSpinVectors cutoff size ↔
      vector.length = size ∧
        ∀ spin, spin ∈ vector → 1 ≤ spin ∧ spin ≤ cutoff := by
  induction size generalizing vector with
  | zero =>
      constructor
      · intro hvector
        change vector ∈ [[]] at hvector
        rcases List.mem_cons.mp hvector with hnil | himpossible
        · subst vector
          exact ⟨rfl, fun spin hspin =>
            absurd hspin List.not_mem_nil⟩
        · exact absurd himpossible List.not_mem_nil
      · intro hvector
        have hnil : vector = [] :=
          List.length_eq_zero_iff.mp hvector.1
        subst vector
        exact List.mem_cons_self
  | succ size ih =>
      constructor
      · intro hvector
        change vector ∈
          (cartesian (positiveSpinValues cutoff)
            (positiveSpinVectors cutoff size)).map
              (fun pair => pair.1 :: pair.2) at hvector
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hvector
        have hparts :=
          (mem_cartesian_iff (positiveSpinValues cutoff)
            (positiveSpinVectors cutoff size) pair).1 hpair
        have hhead := mem_positiveSpinValues_iff.mp hparts.1
        have htail := (ih pair.2).1 hparts.2
        constructor
        · exact congrArg Nat.succ htail.1
        · intro spin hspin
          rcases List.mem_cons.mp hspin with hheadEq | hrest
          · subst spin
            exact hhead
          · exact htail.2 spin hrest
      · intro hvector
        cases vector with
        | nil =>
            exact absurd hvector.1 (fun h => Nat.noConfusion h)
        | cons head tail =>
            have htailLength : tail.length = size :=
              Nat.succ.inj hvector.1
            have hhead : 1 ≤ head ∧ head ≤ cutoff :=
              hvector.2 head List.mem_cons_self
            have htail : ∀ spin, spin ∈ tail →
                1 ≤ spin ∧ spin ≤ cutoff := by
              intro spin hspin
              exact hvector.2 spin
                (List.mem_cons_of_mem head hspin)
            change head :: tail ∈
              (cartesian (positiveSpinValues cutoff)
                (positiveSpinVectors cutoff size)).map
                  (fun pair => pair.1 :: pair.2)
            apply List.mem_map.mpr
            refine ⟨(head, tail), ?_, rfl⟩
            exact (mem_cartesian_iff (positiveSpinValues cutoff)
              (positiveSpinVectors cutoff size) (head, tail)).2
              ⟨mem_positiveSpinValues_iff.mpr hhead,
                (ih tail).2 ⟨htailLength, htail⟩⟩

def anchorSpinVectorWeight : List Nat → Q'
  | [] => 1
  | spin :: rest =>
      anchorDecoratedFaceActivity spin * anchorSpinVectorWeight rest

theorem anchorSpinVectorWeight_nonnegative : ∀ vector : List Nat,
    (0 : Q') ≤ anchorSpinVectorWeight vector
  | [] => Q'.zero_le_one
  | spin :: rest => Q'.mul_nonneg _ _
      (tailTerm_nonneg (by decide) 13 spin)
      (anchorSpinVectorWeight_nonnegative rest)

private theorem listQSum_range_eqv_finSum (value : Nat → Q') :
    ∀ cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

theorem positiveSpinValues_weight_sum (cutoff : Nat) :
    listQSum anchorDecoratedFaceActivity (positiveSpinValues cutoff) ≈
      anchorDecoratedPlaqActivity cutoff := by
  unfold positiveSpinValues anchorDecoratedPlaqActivity
  rw [listQSum_map]
  exact listQSum_range_eqv_finSum _ cutoff

theorem positiveSpinVectors_weight_sum (cutoff : Nat) :
    ∀ size : Nat,
      listQSum anchorSpinVectorWeight
          (positiveSpinVectors cutoff size) ≈
        anchorDecoratedPlaqActivity cutoff ^ size
  | 0 => by
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | size + 1 => by
      unfold positiveSpinVectors
      rw [listQSum_map]
      refine Q'.eqv_trans _ _ _
        (listQSum_cartesian_product anchorDecoratedFaceActivity
          anchorSpinVectorWeight (positiveSpinValues cutoff)
          (positiveSpinVectors cutoff size)) ?_
      rw [Q'.pow_succ]
      exact qmul_congr
        (positiveSpinValues_weight_sum cutoff)
        (positiveSpinVectors_weight_sum cutoff size)

/-! ## 4. Injection of exact-support labellings into spin vectors -/

def physicalLabellingsWithSupport (cutoff n : Nat)
    (support : List Nat) : List EdgeLabelling :=
  (boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))).filter
    (fun physical =>
      decide (excitedPlaquetteIds n physical = support))

theorem mem_physicalLabellingsWithSupport_iff
    {cutoff n : Nat} {support : List Nat} {physical : EdgeLabelling} :
    physical ∈ physicalLabellingsWithSupport cutoff n support ↔
      physical ∈ boundedEdgeLabellings cutoff
          (List.range (plaquetteEdgeCount n)) ∧
        excitedPlaquetteIds n physical = support := by
  unfold physicalLabellingsWithSupport
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem physicalLabellingsWithSupport_nodup
    (cutoff n : Nat) (support : List Nat) :
    (physicalLabellingsWithSupport cutoff n support).Nodup := by
  unfold physicalLabellingsWithSupport
  apply List.filter_sublist.nodup
  apply boundedEdgeLabellings_nodup
  simpa [physicalFaceEdges] using physicalFaceEdges_nodup n

theorem supportValueVector_mem_positiveSpinVectors
    {cutoff n : Nat} {support : List Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff n support) :
    support.map physical ∈ positiveSpinVectors cutoff support.length := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
  have hsound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) physical hparts.1
  apply (mem_positiveSpinVectors_iff cutoff support.length
    (support.map physical)).2
  constructor
  · simp only [List.length_map]
  · intro spin hspin
    obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hspin
    have hexcited : edge ∈ excitedPlaquetteIds n physical := by
      rw [hparts.2]
      exact hedge
    have hselected := List.mem_filter.mp hexcited
    have hpositive : 1 ≤ physical edge := by
      simpa only [decide_eq_true_eq] using hselected.2
    have hupper := hsound.1 edge (by
      simpa [physicalFaceEdges] using hselected.1)
    exact ⟨hpositive, Nat.le_of_lt_succ hupper⟩

private theorem map_values_eq_of_mem {A B : Type}
    (left right : A → B) : ∀ {xs : List A},
    xs.map left = xs.map right → ∀ {x}, x ∈ xs → left x = right x
  | [], _, _, hmem => absurd hmem List.not_mem_nil
  | head :: rest, heq, x, hmem => by
      injection heq with hhead htail
      rcases List.mem_cons.mp hmem with hx | hrest
      · subst x
        exact hhead
      · exact map_values_eq_of_mem left right htail hrest

theorem supportValueVector_injective_on
    {cutoff n : Nat} {support : List Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ physicalLabellingsWithSupport cutoff n support)
    (hright : right ∈ physicalLabellingsWithSupport cutoff n support)
    (hvector : support.map left = support.map right) :
    left = right := by
  have hleftParts := mem_physicalLabellingsWithSupport_iff.mp hleft
  have hrightParts := mem_physicalLabellingsWithSupport_iff.mp hright
  have hleftSound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) left hleftParts.1
  have hrightSound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) right hrightParts.1
  funext edge
  by_cases hedgeRange : edge ∈ List.range (plaquetteEdgeCount n)
  · by_cases hedgeSupport : edge ∈ support
    · exact map_values_eq_of_mem left right hvector hedgeSupport
    · have hleftZero : left edge = 0 := by
        have hnotPositive : ¬ 1 ≤ left edge := by
          intro hpositive
          have hexcited : edge ∈ excitedPlaquetteIds n left := by
            apply List.mem_filter.mpr
            exact ⟨by simpa [physicalFaceEdges] using hedgeRange,
              by simpa only [decide_eq_true_eq]⟩
          rw [hleftParts.2] at hexcited
          exact hedgeSupport hexcited
        omega
      have hrightZero : right edge = 0 := by
        have hnotPositive : ¬ 1 ≤ right edge := by
          intro hpositive
          have hexcited : edge ∈ excitedPlaquetteIds n right := by
            apply List.mem_filter.mpr
            exact ⟨by simpa [physicalFaceEdges] using hedgeRange,
              by simpa only [decide_eq_true_eq]⟩
          rw [hrightParts.2] at hexcited
          exact hedgeSupport hexcited
        omega
      exact hleftZero.trans hrightZero.symm
  · exact (hleftSound.2 edge hedgeRange).trans
      (hrightSound.2 edge hedgeRange).symm

theorem anchorDecoratedFaceActivity_zero_eqv_one :
    anchorDecoratedFaceActivity 0 ≈ 1 := by
  unfold anchorDecoratedFaceActivity tailTerm anchorCoupling
  dsimp [c4, qpow]
  decide

private theorem eliminateLinks_eqv_filter_of_one
    (value : Nat → Q') (test : Nat → Bool) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → test edge = false → value edge ≈ 1) →
      eliminateLinks value edges ≈
        eliminateLinks value (edges.filter test)
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hone => by
      have hrest := eliminateLinks_eqv_filter_of_one value test rest
        (fun item hitem =>
          hone item (List.mem_cons_of_mem edge hitem))
      cases htest : test edge with
      | false =>
          simp only [eliminateLinks, List.filter_cons, htest,
            Bool.false_eq_true, ↓reduceIte]
          exact Q'.eqv_trans _ _ _
            (qmul_congr (hone edge List.mem_cons_self htest) hrest)
            (Q'.one_mul_eqv _)
      | true =>
          simp only [eliminateLinks, List.filter_cons, htest, ↓reduceIte]
          exact qmul_congr (Q'.eqv_refl _) hrest

private theorem eliminateLinks_support_eq_vectorWeight
    (physical : EdgeLabelling) : ∀ support : List Nat,
    eliminateLinks
        (fun edge => anchorDecoratedFaceActivity (physical edge)) support =
      anchorSpinVectorWeight (support.map physical)
  | [] => rfl
  | edge :: rest => by
      simp only [eliminateLinks, List.map_cons, anchorSpinVectorWeight]
      rw [eliminateLinks_support_eq_vectorWeight physical rest]

theorem anchorDecoratedFaceProduct_eqv_supportVectorWeight
    {n : Nat} {physical : EdgeLabelling} {support : List Nat}
    (hsupport : excitedPlaquetteIds n physical = support) :
    anchorDecoratedFaceProduct n physical ≈
      anchorSpinVectorWeight (support.map physical) := by
  let test : Nat → Bool := fun edge => decide (1 ≤ physical edge)
  have hfilter :
      eliminateLinks
          (fun edge => anchorDecoratedFaceActivity (physical edge))
          (List.range (plaquetteEdgeCount n)) ≈
        eliminateLinks
          (fun edge => anchorDecoratedFaceActivity (physical edge))
          ((List.range (plaquetteEdgeCount n)).filter test) := by
    apply eliminateLinks_eqv_filter_of_one
    intro edge _ hzero
    have hnot : ¬ 1 ≤ physical edge := by
      dsimp [test] at hzero
      exact of_decide_eq_false hzero
    have heq : physical edge = 0 := by omega
    rw [heq]
    exact anchorDecoratedFaceActivity_zero_eqv_one
  unfold anchorDecoratedFaceProduct
  refine Q'.eqv_trans _ _ _ hfilter ?_
  have hselected :
      (List.range (plaquetteEdgeCount n)).filter test = support := by
    change excitedPlaquetteIds n physical = support
    exact hsupport
  rw [hselected]
  exact Q'.eqv_of_eq
    (eliminateLinks_support_eq_vectorWeight physical support)

/-! ## 5. Cutoff-uniform activity of every fixed support -/

def parametricKSupportActivity (cutoff n : Nat)
    (support : List Nat) : Q' :=
  listQSum (parametricKPhysicalTerm anchorCoupling cutoff n)
    (physicalLabellingsWithSupport cutoff n support)

theorem anchorDecoratedPlaqActivity_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ anchorDecoratedPlaqActivity cutoff := by
  unfold anchorDecoratedPlaqActivity
  induction cutoff with
  | zero => exact Q'.le_refl' 0
  | succ cutoff ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih
        (tailTerm_nonneg (by decide) 13 (1 + cutoff))

private theorem qpow_le_qpow_of_le {left right : Q'}
    (hleft0 : (0 : Q') ≤ left) (hle : left ≤ right) :
    ∀ exponent : Nat, left ^ exponent ≤ right ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      have hleftPow0 : (0 : Q') ≤ left ^ exponent :=
        Q'.pow_nonneg left hleft0 exponent
      have hright0 : (0 : Q') ≤ right :=
        Q'.le_trans' _ _ _ hleft0 hle
      have hfirst : left * left ^ exponent ≤
          right * left ^ exponent :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hle hleftPow0
      have hsecond : right * left ^ exponent ≤
          right * right ^ exponent :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (qpow_le_qpow_of_le hleft0 hle exponent) hright0
      exact Q'.le_trans' _ _ _ hfirst hsecond

/-- After summing every spin decoration `1, ..., cutoff` on a fixed face
support, the total literal spin-foam activity is bounded by
`(1/7500)^|support|`, uniformly in the representation cutoff and box volume. -/
theorem parametricKSupportActivity_le_envelopePow
    (cutoff n : Nat) (support : List Nat) :
    parametricKSupportActivity cutoff n support ≤
      anchorDecoratedFaceEnvelope ^ support.length := by
  let source := physicalLabellingsWithSupport cutoff n support
  let target := positiveSpinVectors cutoff support.length
  let encode : EdgeLabelling → List Nat := fun physical =>
    support.map physical
  have hinjection :
      listQSum (parametricKPhysicalTerm anchorCoupling cutoff n) source ≤
        listQSum anchorSpinVectorWeight target := by
    apply listQSum_le_of_injective source target
      (parametricKPhysicalTerm anchorCoupling cutoff n)
      anchorSpinVectorWeight encode
    · exact physicalLabellingsWithSupport_nodup cutoff n support
    · intro physical hphysical
      exact supportValueVector_mem_positiveSpinVectors hphysical
    · intro left hleft right hright heq
      exact supportValueVector_injective_on hleft hright heq
    · intro physical hphysical
      have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
      have hterm :=
        parametricKPhysicalTerm_anchor_le_decoratedFaceProduct hparts.1
      exact Q'.le_trans' _ _ _ hterm
        (Q'.le_of_eqv
          (anchorDecoratedFaceProduct_eqv_supportVectorWeight hparts.2))
    · intro vector _
      exact anchorSpinVectorWeight_nonnegative vector
  have htarget : listQSum anchorSpinVectorWeight target ≤
      anchorDecoratedPlaqActivity cutoff ^ support.length :=
    Q'.le_of_eqv (positiveSpinVectors_weight_sum cutoff support.length)
  have hpower : anchorDecoratedPlaqActivity cutoff ^ support.length ≤
      anchorDecoratedFaceEnvelope ^ support.length :=
    qpow_le_qpow_of_le
      (anchorDecoratedPlaqActivity_nonnegative cutoff)
      (anchorDecoratedPlaqActivity_le_envelope cutoff)
      support.length
  unfold parametricKSupportActivity
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_trans' _ _ _ htarget hpower)

/-! ## 6. A uniform pinned KP bound for all representation cutoffs -/

def anchorDecoratedEffectiveRatio : Q' :=
  animalK z4Chain * anchorDecoratedFaceEnvelope * eSurrogate

theorem anchorDecoratedEffectiveRatio_eqv_quarter :
    anchorDecoratedEffectiveRatio ≈ Q'.mkPos 1 4 (by decide) := by
  unfold anchorDecoratedEffectiveRatio anchorDecoratedFaceEnvelope
    animalK z4Chain eSurrogate
  decide

theorem anchorDecoratedEffectiveRatio_nonnegative :
    (0 : Q') ≤ anchorDecoratedEffectiveRatio := by
  unfold anchorDecoratedEffectiveRatio
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (animalK_nonneg z4Chain)
      anchorDecoratedFaceEnvelope_nonnegative)
    eSurrogate_nonneg

theorem anchorDecoratedEffectiveRatio_le_half :
    anchorDecoratedEffectiveRatio ≤ Q'.mkPos 1 2 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv anchorDecoratedEffectiveRatio_eqv_quarter)
    (by decide)

def parametricKPinnedSizeActivitySum
    (cutoff n rootId size : Nat) : Q' :=
  listQSum (parametricKSupportActivity cutoff n)
    (canonicalPinnedSizePolymers n rootId size)

theorem parametricKSupportActivity_nonnegative
    (cutoff n : Nat) (support : List Nat) :
    (0 : Q') ≤ parametricKSupportActivity cutoff n support := by
  unfold parametricKSupportActivity
  exact listQSum_nonnegative _
    (parametricKPhysicalTerm_nonnegative (by decide) cutoff n)
    (physicalLabellingsWithSupport cutoff n support)

theorem parametricKPinnedSizeActivitySum_nonnegative
    (cutoff n rootId size : Nat) :
    (0 : Q') ≤
      parametricKPinnedSizeActivitySum cutoff n rootId size := by
  unfold parametricKPinnedSizeActivitySum
  exact listQSum_nonnegative _
    (parametricKSupportActivity_nonnegative cutoff n)
    (canonicalPinnedSizePolymers n rootId size)

theorem parametricKPinnedSizeActivitySum_le_lengthEnvelope
    (cutoff n rootId size : Nat) :
    parametricKPinnedSizeActivitySum cutoff n rootId size ≤
      Q'.ofNat (canonicalPinnedSizePolymers n rootId size).length *
        anchorDecoratedFaceEnvelope ^ size := by
  unfold parametricKPinnedSizeActivitySum
  apply listQSum_le_length_mul
    (parametricKSupportActivity cutoff n)
    (Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size)
  intro support hsupport
  have hfacts := mem_canonicalPinnedSizePolymers_iff.mp hsupport
  have hactivity :=
    parametricKSupportActivity_le_envelopePow cutoff n support
  rw [hfacts.2.2] at hactivity
  exact hactivity

theorem parametricKPinnedSizeActivitySum_le_animalEnvelope
    (cutoff n rootId size : Nat) :
    parametricKPinnedSizeActivitySum cutoff n rootId size ≤
      (z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
        anchorDecoratedFaceEnvelope ^ size := by
  exact Q'.le_trans' _ _ _
    (parametricKPinnedSizeActivitySum_le_lengthEnvelope
      cutoff n rootId size)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalPinnedSize_count_le_animalCount n rootId size)
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size))

def parametricKPinnedSizeWeightedActivity
    (cutoff n rootId size : Nat) : Q' :=
  parametricKPinnedSizeActivitySum cutoff n rootId size *
    eSurrogate ^ size

theorem parametricKPinnedSizeWeightedActivity_le_geom
    (cutoff n rootId size : Nat) :
    parametricKPinnedSizeWeightedActivity cutoff n rootId size ≤
      anchorDecoratedEffectiveRatio ^ size := by
  unfold parametricKPinnedSizeWeightedActivity
    anchorDecoratedEffectiveRatio
  have henvelope0 : (0 : Q') ≤
      anchorDecoratedFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size
  have he0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hactivity := Q'.mul_le_mul_of_nonneg_right _ _ _
    (parametricKPinnedSizeActivitySum_le_animalEnvelope
      cutoff n rootId size) he0
  have hcount :
      (z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
            anchorDecoratedFaceEnvelope ^ size ≤
        animalK z4Chain ^ size *
          anchorDecoratedFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      ((z4ClusterCountBound
        (boxPlaquetteAt n rootId)).count_le size) henvelope0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcount he0
  have hpow :
      ((animalK z4Chain * anchorDecoratedFaceEnvelope *
          eSurrogate) ^ size).eqv
        (animalK z4Chain ^ size *
          anchorDecoratedFaceEnvelope ^ size * eSurrogate ^ size) :=
    pow_mul3_eqv (animalK z4Chain)
      anchorDecoratedFaceEnvelope eSurrogate size
  exact Q'.le_trans' _ _ _ hactivity
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpow))

def parametricKPinnedTruncatedKPSum
    (cutoff n rootId depth : Nat) : Q' :=
  finSum (fun size =>
    parametricKPinnedSizeWeightedActivity cutoff n rootId size) depth

/-- Uniform in the representation cutoff, box size, pinned face, and size
truncation. -/
theorem parametricKPinnedTruncatedKPSum_le_two
    (cutoff n rootId depth : Nat) :
    parametricKPinnedTruncatedKPSum cutoff n rootId depth ≤ Q'.ofNat 2 := by
  unfold parametricKPinnedTruncatedKPSum
  exact Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise _ _
      (parametricKPinnedSizeWeightedActivity_le_geom
        cutoff n rootId) depth)
    (geom_partial_le_two
      anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half depth)

def parametricKPinnedShiftedKPSum
    (cutoff n rootId sizeFloor depth : Nat) : Q' :=
  finSum (fun offset =>
    parametricKPinnedSizeWeightedActivity cutoff n rootId
      (sizeFloor + offset)) depth

/-- The arbitrary-cutoff pinned sum has a geometric size tail, uniformly in
the representation cutoff, finite box, and pinned physical face. -/
theorem parametricKPinnedShiftedKPSum_le_tail
    (cutoff n rootId sizeFloor depth : Nat) :
    parametricKPinnedShiftedKPSum cutoff n rootId sizeFloor depth ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  unfold parametricKPinnedShiftedKPSum
  have hsum1 :
      finSum (fun offset =>
          parametricKPinnedSizeWeightedActivity cutoff n rootId
            (sizeFloor + offset)) depth ≤
        finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ (sizeFloor + offset)) depth :=
    CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        parametricKPinnedSizeWeightedActivity_le_geom
          cutoff n rootId (sizeFloor + offset)) depth
  have hsum2 :
      (finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ (sizeFloor + offset)) depth).eqv
        (finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ sizeFloor *
            anchorDecoratedEffectiveRatio ^ offset) depth) :=
    RationalTail.finSum_eqv_congr _ _
      (fun offset =>
        Q'.pow_add_eqv anchorDecoratedEffectiveRatio sizeFloor offset) depth
  have hsum3 :
      (finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ sizeFloor *
            anchorDecoratedEffectiveRatio ^ offset) depth).eqv
        (anchorDecoratedEffectiveRatio ^ sizeFloor *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorDecoratedEffectiveRatio ^ offset)
      (anchorDecoratedEffectiveRatio ^ sizeFloor) depth)
  have hgeo :
      finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ offset) depth ≤
        Q'.ofNat 2 :=
    geom_partial_le_two anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half depth
  have hscaled :
      anchorDecoratedEffectiveRatio ^ sizeFloor *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth ≤
        anchorDecoratedEffectiveRatio ^ sizeFloor * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative sizeFloor)
  have hcomm :
      (anchorDecoratedEffectiveRatio ^ sizeFloor * Q'.ofNat 2).eqv
        (Q'.ofNat 2 *
          anchorDecoratedEffectiveRatio ^ sizeFloor) :=
    Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ hsum1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum2)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum3)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcomm))))

/-! ## 7. Compatibility with the previously proved cutoff-one scale -/

theorem anchorDecoratedFaceActivity_one_eqv_oldEnvelope :
    anchorDecoratedFaceActivity 1 ≈ anchorPerFaceEnvelope := by
  unfold anchorDecoratedFaceActivity anchorPerFaceEnvelope
    anchorFaceCoefficient binaryLinkMultiplicityBound tailTerm anchorCoupling
  dsimp [c4, qpow]
  decide

end YMGap.Continuum.Z4SpinSummedFaceActivityBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.anchorDecoratedFaceActivity_succ_ratio
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.anchorDecoratedRecurrence
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.anchorDecoratedPlaqActivity_le_envelope
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.parametricKPhysicalTerm_anchor_le_decoratedFaceProduct
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.positiveSpinVectors_weight_sum
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.supportValueVector_injective_on
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.parametricKSupportActivity_le_envelopePow
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.parametricKPinnedSizeWeightedActivity_le_geom
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.parametricKPinnedTruncatedKPSum_le_two
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.parametricKPinnedShiftedKPSum_le_tail
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityBound.anchorDecoratedEffectiveRatio_le_half
