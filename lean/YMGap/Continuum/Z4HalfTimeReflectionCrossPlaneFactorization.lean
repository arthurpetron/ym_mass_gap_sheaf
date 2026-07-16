/-
# Exact lower/interface/upper factorization on the corrected reflection slab

This file refines the geometric three-way partition into the literal factors
of one finite spin-foam summand.  It proves, before any sum over states, that
the full face product and actual-link multiplicity product split into lower,
fixed-interface, and upper pieces.  It also records the incident-ID locality
needed to show that the three pieces read only their corresponding face
coordinates.

The fixed-interface piece is nonnegative at nonnegative heat-kernel coupling.
This is still a summand identity, not yet the global Gram reindex of the full
Cartesian labelling sum.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Membership in the stable side partition -/

theorem mem_partitionBySide_lower {A : Type} [DecidableEq A]
    (side : A -> CrossPlaneSide) (item : A) : forall xs : List A,
    item ∈ (partitionBySide side xs).1 ↔
      item ∈ xs ∧ side item = .lower
  | [] => by simp [partitionBySide]
  | head :: tail => by
      by_cases heq : item = head
      · subst item
        cases hhead : side head <;>
          simp [partitionBySide, hhead,
            mem_partitionBySide_lower side head tail]
      · cases hhead : side head <;>
          simp [partitionBySide, hhead, heq,
            mem_partitionBySide_lower side item tail]

theorem mem_partitionBySide_fixed {A : Type} [DecidableEq A]
    (side : A -> CrossPlaneSide) (item : A) : forall xs : List A,
    item ∈ (partitionBySide side xs).2.1 ↔
      item ∈ xs ∧ side item = .fixed
  | [] => by simp [partitionBySide]
  | head :: tail => by
      by_cases heq : item = head
      · subst item
        cases hhead : side head <;>
          simp [partitionBySide, hhead,
            mem_partitionBySide_fixed side head tail]
      · cases hhead : side head <;>
          simp [partitionBySide, hhead, heq,
            mem_partitionBySide_fixed side item tail]

theorem mem_partitionBySide_upper {A : Type} [DecidableEq A]
    (side : A -> CrossPlaneSide) (item : A) : forall xs : List A,
    item ∈ (partitionBySide side xs).2.2 ↔
      item ∈ xs ∧ side item = .upper
  | [] => by simp [partitionBySide]
  | head :: tail => by
      by_cases heq : item = head
      · subst item
        cases hhead : side head <;>
          simp [partitionBySide, hhead,
            mem_partitionBySide_upper side head tail]
      · cases hhead : side head <;>
          simp [partitionBySide, hhead, heq,
            mem_partitionBySide_upper side item tail]

def centralLowerFaceIds (half : Nat) : List Nat :=
  (centralSlabFaceIdParts half).1

def centralFixedFaceIds (half : Nat) : List Nat :=
  (centralSlabFaceIdParts half).2.1

def centralUpperFaceIds (half : Nat) : List Nat :=
  (centralSlabFaceIdParts half).2.2

def centralLowerLinks (half : Nat) : List Z4Link :=
  (centralSlabLinkParts half).1

def centralFixedLinks (half : Nat) : List Z4Link :=
  (centralSlabLinkParts half).2.1

def centralUpperLinks (half : Nat) : List Z4Link :=
  (centralSlabLinkParts half).2.2

theorem mem_centralLowerFaceIds {half id : Nat} :
    id ∈ centralLowerFaceIds half ↔
      id ∈ slabPhysicalFaceEdges (centralExtent half) ∧
      plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_centralFixedFaceIds {half id : Nat} :
    id ∈ centralFixedFaceIds half ↔
      id ∈ slabPhysicalFaceEdges (centralExtent half) ∧
      plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

theorem mem_centralUpperFaceIds {half id : Nat} :
    id ∈ centralUpperFaceIds half ↔
      id ∈ slabPhysicalFaceEdges (centralExtent half) ∧
      plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) = .upper := by
  exact mem_partitionBySide_upper _ _ _

theorem mem_centralLowerLinks {half : Nat} {link : Z4Link} :
    link ∈ centralLowerLinks half ↔
      link ∈ boundaryCompleteSlabLinks (centralExtent half) ∧
      linkHalfSide half link = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_centralFixedLinks {half : Nat} {link : Z4Link} :
    link ∈ centralFixedLinks half ↔
      link ∈ boundaryCompleteSlabLinks (centralExtent half) ∧
      linkHalfSide half link = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

theorem mem_centralUpperLinks {half : Nat} {link : Z4Link} :
    link ∈ centralUpperLinks half ↔
      link ∈ boundaryCompleteSlabLinks (centralExtent half) ∧
      linkHalfSide half link = .upper := by
  exact mem_partitionBySide_upper _ _ _

/-! ## 2. Exact product splitting -/

def slabFaceFactorOn
    (w : Q') (K : Nat) (physical : EdgeLabelling)
    (ids : List Nat) : Q' :=
  eliminateLinks
    (fun id => coeffAt (heatKernelPacket K w) (physical id)) ids

def slabLinkMultiplicityProductOn
    (K extent : Nat) (physical : EdgeLabelling)
    (links : List Z4Link) : Nat :=
  natListProduct (slabExplicitLinkMultiplicity K extent physical) links

def centralLowerFactor
    (w : Q') (K half : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (centralLowerFaceIds half) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (centralExtent half)
      physical (centralLowerLinks half))

def centralFixedWeight
    (w : Q') (K half : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (centralFixedFaceIds half) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (centralExtent half)
      physical (centralFixedLinks half))

def centralUpperFactor
    (w : Q') (K half : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (centralUpperFaceIds half) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (centralExtent half)
      physical (centralUpperLinks half))

private theorem eliminateLinks_append
    (value : Nat -> Q') : forall (left right : List Nat),
    eliminateLinks value (left ++ right) ≈
      eliminateLinks value left * eliminateLinks value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, eliminateLinks]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_append value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem natListProduct_append {A : Type}
    (value : A -> Nat) : forall (left right : List A),
    natListProduct value (left ++ right) =
      natListProduct value left * natListProduct value right
  | [], right => by simp [natListProduct]
  | _ :: tail, right => by
      simp only [List.cons_append, natListProduct]
      rw [natListProduct_append value tail right, Nat.mul_assoc]

private theorem rearrange_six
    (a b c d e f : Q') :
    (a * (b * c)) * (d * (e * f)) ≈
      (a * d) * ((b * e) * (c * f)) := by
  show ((a * (b * c)) * (d * (e * f))).num *
      ((((a * d) * ((b * e) * (c * f))).den) : Int) =
    ((a * d) * ((b * e) * (c * f))).num *
      ((((a * (b * c)) * (d * (e * f))).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (Q'.ofNat (a * b)).num *
      (((Q'.ofNat a * Q'.ofNat b).den) : Int) =
    (Q'.ofNat a * Q'.ofNat b).num *
      (((Q'.ofNat (a * b)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  push_cast
  omega

theorem slabParametricKPhysicalTerm_crossPlane_factorization
    (w : Q') (K half : Nat) (physical : EdgeLabelling) :
    slabParametricKPhysicalTerm w K (centralExtent half) physical ≈
      centralLowerFactor w K half physical *
        (centralFixedWeight w K half physical *
          centralUpperFactor w K half physical) := by
  let faceValue : Nat -> Q' := fun id =>
    coeffAt (heatKernelPacket K w) (physical id)
  let linkValue : Z4Link -> Nat :=
    slabExplicitLinkMultiplicity K (centralExtent half) physical
  have hface :
      slabParametricKPhysicalFaceFactor w K (centralExtent half) physical ≈
        slabFaceFactorOn w K physical (centralLowerFaceIds half) *
          (slabFaceFactorOn w K physical (centralFixedFaceIds half) *
            slabFaceFactorOn w K physical (centralUpperFaceIds half)) := by
    unfold slabParametricKPhysicalFaceFactor slabFaceFactorOn
    calc
      eliminateLinks faceValue
          (slabPhysicalFaceEdges (centralExtent half)) ≈
        eliminateLinks faceValue
          (centralLowerFaceIds half ++ centralFixedFaceIds half ++
            centralUpperFaceIds half) :=
        eliminateLinks_perm faceValue
          (centralSlabFaceIdParts_perm half).symm
      _ ≈ eliminateLinks faceValue (centralLowerFaceIds half) *
          eliminateLinks faceValue
            (centralFixedFaceIds half ++ centralUpperFaceIds half) := by
        simpa only [List.append_assoc] using
          (eliminateLinks_append faceValue (centralLowerFaceIds half)
            (centralFixedFaceIds half ++ centralUpperFaceIds half))
      _ ≈ eliminateLinks faceValue (centralLowerFaceIds half) *
          (eliminateLinks faceValue (centralFixedFaceIds half) *
            eliminateLinks faceValue (centralUpperFaceIds half)) :=
        Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_append faceValue (centralFixedFaceIds half)
            (centralUpperFaceIds half))
  have hlink :
      slabExplicitLinkMultiplicityProduct K (centralExtent half) physical =
        slabLinkMultiplicityProductOn K (centralExtent half) physical
            (centralLowerLinks half) *
          (slabLinkMultiplicityProductOn K (centralExtent half) physical
              (centralFixedLinks half) *
            slabLinkMultiplicityProductOn K (centralExtent half) physical
              (centralUpperLinks half)) := by
    unfold slabExplicitLinkMultiplicityProduct
      slabLinkMultiplicityProductOn
    calc
      natListProduct linkValue
          (boundaryCompleteSlabLinks (centralExtent half)) =
        natListProduct linkValue
          (centralLowerLinks half ++ centralFixedLinks half ++
            centralUpperLinks half) :=
        natListProduct_perm linkValue
          (centralSlabLinkParts_perm half).symm
      _ = natListProduct linkValue (centralLowerLinks half) *
          natListProduct linkValue
            (centralFixedLinks half ++ centralUpperLinks half) := by
        simpa only [List.append_assoc] using
          (natListProduct_append linkValue (centralLowerLinks half)
            (centralFixedLinks half ++ centralUpperLinks half))
      _ = natListProduct linkValue (centralLowerLinks half) *
          (natListProduct linkValue (centralFixedLinks half) *
            natListProduct linkValue (centralUpperLinks half)) := by
        rw [natListProduct_append linkValue (centralFixedLinks half)
          (centralUpperLinks half)]
  unfold slabParametricKPhysicalTerm centralLowerFactor
    centralFixedWeight centralUpperFactor
  rw [hlink]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hface) ?_
  let lowerLinks := slabLinkMultiplicityProductOn K (centralExtent half)
    physical (centralLowerLinks half)
  let fixedLinks := slabLinkMultiplicityProductOn K (centralExtent half)
    physical (centralFixedLinks half)
  let upperLinks := slabLinkMultiplicityProductOn K (centralExtent half)
    physical (centralUpperLinks half)
  have hlinkCast :
      Q'.ofNat (lowerLinks * (fixedLinks * upperLinks)) ≈
        Q'.ofNat lowerLinks *
          (Q'.ofNat fixedLinks * Q'.ofNat upperLinks) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv lowerLinks (fixedLinks * upperLinks))
      (Q'.mul_eqv_congr_left _ _ _
        (ofNat_mul_eqv fixedLinks upperLinks))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hlinkCast) ?_
  exact rearrange_six _ _ _ _ _ _

/-! ## 3. Incident-coordinate locality -/

private theorem slabPlaquetteAt_eq_of_indexed
    {extent id : Nat} {plaquette : Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

theorem incident_of_lower_link_ne_upper
    {half id : Nat} {link : Z4Link}
    (hlink : link ∈ centralLowerLinks half)
    (hid : id ∈ slabIncidentPlaqIds (centralExtent half) link) :
    plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) ≠ .upper := by
  obtain ⟨plaquette, hindexed, hincidence⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  rw [slabPlaquetteAt_eq_of_indexed hindexed]
  exact lower_link_incident_face_ne_upper
    (mem_centralLowerLinks.mp hlink).2 hincidence

theorem incident_of_fixed_link_fixed
    {half id : Nat} {link : Z4Link}
    (hlink : link ∈ centralFixedLinks half)
    (hid : id ∈ slabIncidentPlaqIds (centralExtent half) link) :
    plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) = .fixed := by
  obtain ⟨plaquette, hindexed, hincidence⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  rw [slabPlaquetteAt_eq_of_indexed hindexed]
  exact fixed_link_incident_face_fixed
    (mem_centralFixedLinks.mp hlink).2 hincidence

theorem incident_of_upper_link_ne_lower
    {half id : Nat} {link : Z4Link}
    (hlink : link ∈ centralUpperLinks half)
    (hid : id ∈ slabIncidentPlaqIds (centralExtent half) link) :
    plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id) ≠ .lower := by
  obtain ⟨plaquette, hindexed, hincidence⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  rw [slabPlaquetteAt_eq_of_indexed hindexed]
  exact upper_link_incident_face_ne_lower
    (mem_centralUpperLinks.mp hlink).2 hincidence

/-! ## 4. Nonnegativity of the fixed interface weight -/

private theorem slabFaceFactorOn_nonnegative
    {w : Q'} {K : Nat} {physical : EdgeLabelling}
    (hw : (0 : Q') <= w) : forall ids : List Nat,
    (∀ id, id ∈ ids -> physical id < K + 1) ->
    (0 : Q') <= slabFaceFactorOn w K physical ids
  | [], _ => by change (0 : Q') <= 1; decide
  | head :: tail, hbounded => by
      unfold slabFaceFactorOn eliminateLinks
      rw [coeffAt_heatKernelPacket
        (hbounded head List.mem_cons_self)]
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg hw _)
        (slabFaceFactorOn_nonnegative hw tail
          (fun id hid => hbounded id
            (List.mem_cons_of_mem head hid)))

theorem centralFixedWeight_nonnegative
    {w : Q'} {K half : Nat} {physical : EdgeLabelling}
    (hw : (0 : Q') <= w)
    (hbounded : SlabFaceLabellingBounded K
      (centralExtent half) physical) :
    (0 : Q') <= centralFixedWeight w K half physical := by
  unfold centralFixedWeight
  apply Q'.mul_nonneg
  · apply slabFaceFactorOn_nonnegative hw
    intro id hid
    exact Nat.lt_succ_of_le
      (hbounded id (mem_centralFixedFaceIds.mp hid).1)
  · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _

end YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.mem_partitionBySide_lower
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.mem_partitionBySide_fixed
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.mem_partitionBySide_upper
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.slabParametricKPhysicalTerm_crossPlane_factorization
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.incident_of_lower_link_ne_upper
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.incident_of_fixed_link_fixed
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.incident_of_upper_link_ne_lower
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.centralFixedWeight_nonnegative
