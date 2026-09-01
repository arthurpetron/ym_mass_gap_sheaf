/-
# A decorated-face majorant for every extent-one BF4 slab term

Every corrected extent-one slab link has valence at most six.  The generic
spin-sum fusion bound charges its multiplicity by the cube of the product of
its incident `(spin + 1)` factors.  A checked incidence permutation then
allocates exactly four link occurrences to each of the 72 physical faces, so
the complete link product is bounded by one twelfth power per face.

Multiplying this charge by the heat-kernel face factor gives a product of the
degree-thirteen decorated activities.  This module is a cutoff-independent
termwise majorant; it does not sum a row, prove a replica obstruction,
construct a continuum limit, or establish the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4ResidualListMultiplicityBound
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Allocate the complete link product to physical faces -/

def extentOneSlabIncidenceIds : List Nat :=
  (boundaryCompleteSlabLinks 1).flatMap (slabIncidentPlaqIds 1)

/-- Every physical extent-one face occurs at exactly four corrected slab
links. -/
theorem extentOneSlabIncidenceIds_perm_fourfoldPhysical :
    extentOneSlabIncidenceIds.Perm
      (fourfoldIds (slabPhysicalFaceEdges 1)) := by
  exact natListPerm_of_check _ _ (by decide)

def extentOneSlabFaceTwelfthSpinProduct
    (physical : EdgeLabelling) : Nat :=
  natListProduct
    (fun id => (physical id + 1) ^ 12)
    (slabPhysicalFaceEdges 1)

private theorem natListProduct_append_local {A : Type}
    (value : A → Nat) : ∀ left right : List A,
    natListProduct value (left ++ right) =
      natListProduct value left * natListProduct value right
  | [], _right => by simp [natListProduct]
  | head :: tail, right => by
      simp only [List.cons_append, natListProduct]
      rw [natListProduct_append_local value tail right]
      exact (Nat.mul_assoc _ _ _).symm

private theorem natListProduct_flatMap_local {A B : Type}
    (value : B → Nat) (block : A → List B) : ∀ items : List A,
    natListProduct value (items.flatMap block) =
      natListProduct (fun item => natListProduct value (block item)) items
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, natListProduct]
      rw [natListProduct_append_local value (block head)
        (tail.flatMap block),
        natListProduct_flatMap_local value block tail]

private theorem natListProduct_replicate_local {A : Type}
    (value : A → Nat) (item : A) : ∀ count : Nat,
    natListProduct value (List.replicate count item) = value item ^ count
  | 0 => rfl
  | count + 1 => by
      simp only [List.replicate_succ, natListProduct, Nat.pow_succ]
      rw [natListProduct_replicate_local value item count]
      exact Nat.mul_comm (value item) (value item ^ count)

private theorem natListProduct_mono_on_local {A : Type}
    (left right : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      natListProduct left items ≤ natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on_local left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

private theorem sum_add_one_le_product_add_one_local : ∀ spins : List Nat,
    natListSum spins + 1 ≤
      natListProduct (fun spin => spin + 1) spins
  | [] => Nat.le_refl 1
  | head :: tail => by
      simp only [natListSum, natListProduct]
      have ih := sum_add_one_le_product_add_one_local tail
      have hproduct : 1 ≤
          natListProduct (fun spin => spin + 1) tail :=
        Nat.le_trans (by omega) ih
      have hscale : head ≤
          head * natListProduct (fun spin => spin + 1) tail := by
        calc
          head = 1 * head := (Nat.one_mul head).symm
          _ ≤ natListProduct (fun spin => spin + 1) tail * head :=
            Nat.mul_le_mul_right head hproduct
          _ = head * natListProduct (fun spin => spin + 1) tail :=
            Nat.mul_comm _ _
      have hadd := Nat.add_le_add hscale ih
      calc
        head + natListSum tail + 1 =
            head + (natListSum tail + 1) := by omega
        _ ≤ head * natListProduct (fun spin => spin + 1) tail +
            natListProduct (fun spin => spin + 1) tail := hadd
        _ = (head + 1) *
            natListProduct (fun spin => spin + 1) tail := by
          rw [Nat.add_mul, Nat.one_mul]

private theorem spinSumCube_le_listProductCube_local (spins : List Nat) :
    spinSumCube (natListSum spins) ≤
      spinProductCube
        (natListProduct (fun spin => spin + 1) spins) := by
  unfold spinSumCube spinProductCube
  have h := sum_add_one_le_product_add_one_local spins
  exact Nat.mul_le_mul h (Nat.mul_le_mul h h)

private theorem natListProduct_spinProductCube_local {A : Type}
    (weight : A → Nat) : ∀ items : List A,
    natListProduct (fun item => spinProductCube (weight item)) items =
      spinProductCube (natListProduct weight items)
  | [] => rfl
  | head :: tail => by
      simp only [natListProduct]
      rw [natListProduct_spinProductCube_local weight tail]
      unfold spinProductCube
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem spinProductCube_pow_four_local (value : Nat) :
    spinProductCube (value ^ 4) = value ^ 12 := by
  unfold spinProductCube
  rw [show 12 = 4 + (4 + 4) by omega, Nat.pow_add, Nat.pow_add]

/-- The complete corrected extent-one link multiplicity is bounded by a
twelfth-power spin factor on every physical face. -/
theorem slabExplicitLinkMultiplicityProduct_le_faceTwelfth
    (cutoff : Nat) (physical : EdgeLabelling) :
    slabExplicitLinkMultiplicityProduct cutoff 1 physical ≤
      extentOneSlabFaceTwelfthSpinProduct physical := by
  let faceWeight : Nat → Nat := fun id => physical id + 1
  let linkProduct : YMGap.Continuum.ClusterCount4DProgress.Z4Link → Nat :=
    fun link => natListProduct faceWeight (slabIncidentPlaqIds 1 link)
  have hlink : ∀ link, link ∈ boundaryCompleteSlabLinks 1 →
      slabExplicitLinkMultiplicity cutoff 1 physical link ≤
        spinProductCube (linkProduct link) := by
    intro link _hlink
    let spins := (slabIncidentPlaqIds 1 link).map physical
    have hvalence :
        slabExplicitLinkMultiplicity cutoff 1 physical link ≤
          spinSumCube (natListSum spins) := by
      unfold slabExplicitLinkMultiplicity
      exact explicitValenceMultiplicity_list_le_spinSumCube
        (linkAuxiliaryCutoff cutoff) spins
        (by
          unfold spins
          simpa only [List.length_map] using
            slabIncidentPlaqIds_length_le_six 1 link)
    have hproduct := spinSumCube_le_listProductCube_local spins
    unfold spins at hproduct
    rw [natListProduct_map] at hproduct
    exact Nat.le_trans hvalence hproduct
  have hproduct := natListProduct_mono_on_local
    (slabExplicitLinkMultiplicity cutoff 1 physical)
    (fun link => spinProductCube (linkProduct link))
    (boundaryCompleteSlabLinks 1) hlink
  have hcubes := natListProduct_spinProductCube_local linkProduct
    (boundaryCompleteSlabLinks 1)
  rw [hcubes] at hproduct
  have hflatten :
      natListProduct linkProduct (boundaryCompleteSlabLinks 1) =
        natListProduct faceWeight extentOneSlabIncidenceIds := by
    unfold linkProduct extentOneSlabIncidenceIds
    exact (natListProduct_flatMap_local faceWeight
      (slabIncidentPlaqIds 1) (boundaryCompleteSlabLinks 1)).symm
  rw [hflatten] at hproduct
  have hperm :
      natListProduct faceWeight extentOneSlabIncidenceIds =
        natListProduct faceWeight
          (fourfoldIds (slabPhysicalFaceEdges 1)) :=
    natListProduct_perm faceWeight
      extentOneSlabIncidenceIds_perm_fourfoldPhysical
  rw [hperm] at hproduct
  have hfourfold :
      natListProduct faceWeight
          (fourfoldIds (slabPhysicalFaceEdges 1)) =
        natListProduct (fun id => faceWeight id ^ 4)
          (slabPhysicalFaceEdges 1) := by
    unfold fourfoldIds
    rw [natListProduct_flatMap_local]
    apply natListProduct_congr
    intro id _hid
    exact natListProduct_replicate_local faceWeight id 4
  rw [hfourfold] at hproduct
  have htwelfth :
      spinProductCube
          (natListProduct (fun id => faceWeight id ^ 4)
            (slabPhysicalFaceEdges 1)) =
        extentOneSlabFaceTwelfthSpinProduct physical := by
    rw [← natListProduct_spinProductCube_local
      (fun id => faceWeight id ^ 4) (slabPhysicalFaceEdges 1)]
    unfold extentOneSlabFaceTwelfthSpinProduct faceWeight
    apply natListProduct_congr
    intro id _hid
    exact spinProductCube_pow_four_local (physical id + 1)
  rw [htwelfth] at hproduct
  simpa only [slabExplicitLinkMultiplicityProduct] using hproduct

/-! ## 2. Convert the twelfth-power charge to decorated activity -/

def extentOneSlabAnchorDecoratedFaceProduct
    (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun id => anchorDecoratedFaceActivity (physical id))
    (slabPhysicalFaceEdges 1)

private theorem qOfNat_mono_local {left right : Nat} (hle : left ≤ right) :
    Q'.ofNat left ≤ Q'.ofNat right := by
  show Int.ofNat left * (1 : Int) ≤ Int.ofNat right * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr hle

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') ≤ value id) :
    ∀ ids : List Nat, (0 : Q') ≤ eliminateLinks value ids
  | [] => Q'.zero_le_one
  | id :: rest =>
      Q'.mul_nonneg _ _ (hvalue id)
        (eliminateLinks_nonnegative_local value hvalue rest)

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_four_regroup_local (A B C D : Q') :
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

private theorem ofNat_mul_eqv_local (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈ Q'.ofNat (left * right) := by
  show (Int.ofNat left * Int.ofNat right) * 1 =
    Int.ofNat (left * right) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

private theorem eliminateLinks_pair_natProduct_eqv_local
    (value : Nat → Q') (charge : Nat → Nat) : ∀ ids : List Nat,
    eliminateLinks value ids * Q'.ofNat (natListProduct charge ids) ≈
      eliminateLinks
        (fun id => value id * Q'.ofNat (charge id)) ids
  | [] => by
      change ((1 : Q') * Q'.ofNat 1).eqv 1
      decide
  | id :: rest => by
      simp only [eliminateLinks, natListProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (value id * eliminateLinks value rest)
          _ _ (Q'.eqv_symm
            (ofNat_mul_eqv_local (charge id)
              (natListProduct charge rest)))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_four_regroup_local (value id) (eliminateLinks value rest)
          (Q'.ofNat (charge id))
          (Q'.ofNat (natListProduct charge rest))) ?_
      exact Q'.mul_eqv_congr_left
        (value id * Q'.ofNat (charge id)) _ _
        (eliminateLinks_pair_natProduct_eqv_local value charge rest)

private theorem eliminateLinks_congr_eqv_local
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hagree =>
      qmul_congr_local
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_eqv_local left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

theorem slabParametricKPhysicalFaceFactor_eq_coeffWProduct
    {w : Q'} {cutoff : Nat} {physical : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded cutoff 1 physical) :
    slabParametricKPhysicalFaceFactor w cutoff 1 physical =
      eliminateLinks (fun id => coeffW w (physical id))
        (slabPhysicalFaceEdges 1) := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_congr_eq
  intro id hid
  rw [coeffAt_heatKernelPacket
    (Nat.lt_succ_of_le (hphysical id hid))]

/-- Every bounded extent-one physical summand is at most its full product of
degree-thirteen decorated face activities. -/
theorem slabParametricKPhysicalTerm_anchor_le_decoratedFaceProduct
    {cutoff : Nat} {physical : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded cutoff 1 physical) :
    slabParametricKPhysicalTerm anchorCoupling cutoff 1 physical ≤
      extentOneSlabAnchorDecoratedFaceProduct physical := by
  have hfaceEq := slabParametricKPhysicalFaceFactor_eq_coeffWProduct
    (w := anchorCoupling) hphysical
  have hface0 : (0 : Q') ≤
      slabParametricKPhysicalFaceFactor
        anchorCoupling cutoff 1 physical := by
    rw [hfaceEq]
    exact eliminateLinks_nonnegative_local _
      (fun id => coeffW_nonneg (by decide) (physical id)) _
  have hlink :=
    slabExplicitLinkMultiplicityProduct_le_faceTwelfth cutoff physical
  have hqLink := qOfNat_mono_local hlink
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hqLink hface0
  rw [hfaceEq] at hmul
  unfold extentOneSlabFaceTwelfthSpinProduct at hmul
  unfold slabParametricKPhysicalTerm
  rw [hfaceEq]
  refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (eliminateLinks_pair_natProduct_eqv_local
      (fun id => coeffW anchorCoupling (physical id))
      (fun id => (physical id + 1) ^ 12)
      (slabPhysicalFaceEdges 1)) ?_
  unfold extentOneSlabAnchorDecoratedFaceProduct
  apply eliminateLinks_congr_eqv_local
  intro id _hid
  exact coeffW_mul_twelfth_eqv_decoratedActivity
    anchorCoupling (physical id)

end YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound

#print axioms
  YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound.extentOneSlabIncidenceIds_perm_fourfoldPhysical
#print axioms
  YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound.slabExplicitLinkMultiplicityProduct_le_faceTwelfth
#print axioms
  YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound.slabParametricKPhysicalFaceFactor_eq_coeffWProduct
#print axioms
  YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound.slabParametricKPhysicalTerm_anchor_le_decoratedFaceProduct
