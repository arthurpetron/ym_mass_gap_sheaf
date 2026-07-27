/-
# Conditional fixed-face integration and the U(1) twisted reflection Gram

The orientation-correct dual U(1) reflection acts by charge conjugation on
time-oriented face labels.  On a fixed cross-plane face this conjugates the
interface charge itself, so the raw dual kernel is not an ordinary Gram on
arbitrary functions of signed charges.

This module performs the genuine conditional integration over the complete
fixed-face carrier.  It splits every physical summand into lower, fixed, and
upper factors and proves that the upper factor is the lower amplitude of the
charge-conjugated right state.  Thus

`physicalTerm(assemble(left,boundary,right))
  = boundaryWeight(boundary) *
      amplitude(left,boundary) * amplitude(C right,boundary)`.

The symmetric signed-charge half carrier is explicitly permuted by
`C : q ↦ -q`.  Reindexing that carrier converts the twisted kernel into the
ordinary `FiniteWeightedGramSOS` quadratic for every charge-conjugation-even
coefficient.  This proves exact finite reflection positivity for the even
dual observable algebra, which includes all magnitude/exponent profiles.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1ReflectionCovariance
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4U1TwistedReflectionGram

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4U1ReflectionCovariance
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

def u1FaceFactorOn
    (D : U1SlabData) (state : ChargeLabelling)
    (ids : List Nat) : Q' :=
  listQProduct
    (fun id => abelCoeff D.coupling (chargeMagnitude (state id))) ids

def u1HaarFactorOn
    (D : U1SlabData) (state : ChargeLabelling)
    (links : List Z4Link) : Q' :=
  listQProduct (u1HaarLinkFactor D.extent state) links

def u1LowerFactor (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  u1FaceFactorOn D state (centralLowerFaceIds D.half) *
    u1HaarFactorOn D state (centralLowerLinks D.half)

def u1FixedWeight (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  u1FaceFactorOn D state (centralFixedFaceIds D.half) *
    u1HaarFactorOn D state (centralFixedLinks D.half)

def u1UpperFactor (D : U1SlabData) (state : ChargeLabelling) : Q' :=
  u1FaceFactorOn D state (centralUpperFaceIds D.half) *
    u1HaarFactorOn D state (centralUpperLinks D.half)

private theorem listQProduct_append_eqv {A : Type}
    (value : A → Q') : ∀ left right : List A,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_eqv value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

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

theorem physicalTerm_crossPlane_factorization
    (D : U1SlabData) (state : ChargeLabelling) :
    D.physicalTerm state ≈
      u1LowerFactor D state *
        (u1FixedWeight D state * u1UpperFactor D state) := by
  have hface :
      D.faceFactor state ≈
        u1FaceFactorOn D state (centralLowerFaceIds D.half) *
          (u1FaceFactorOn D state (centralFixedFaceIds D.half) *
            u1FaceFactorOn D state (centralUpperFaceIds D.half)) := by
    unfold U1SlabData.faceFactor U1SlabData.faceEdges
      U1SlabData.carrierData
      YMGap.Continuum.CompactDualSlabPhysicalData.SlabPhysicalData.faceEdges
      u1FaceFactorOn
    let value : Nat → Q' := fun id =>
      abelCoeff D.coupling (chargeMagnitude (state id))
    calc
      listQProduct value
          (slabPhysicalFaceEdges (centralExtent D.half)) ≈
        listQProduct value
          (centralLowerFaceIds D.half ++
            centralFixedFaceIds D.half ++
            centralUpperFaceIds D.half) :=
        listQProduct_perm value
          (centralSlabFaceIdParts_perm D.half).symm
      _ ≈ listQProduct value (centralLowerFaceIds D.half) *
          listQProduct value
            (centralFixedFaceIds D.half ++
              centralUpperFaceIds D.half) := by
        simpa only [List.append_assoc] using
          listQProduct_append_eqv value (centralLowerFaceIds D.half)
            (centralFixedFaceIds D.half ++
              centralUpperFaceIds D.half)
      _ ≈ listQProduct value (centralLowerFaceIds D.half) *
          (listQProduct value (centralFixedFaceIds D.half) *
            listQProduct value (centralUpperFaceIds D.half)) :=
        Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_eqv value
            (centralFixedFaceIds D.half)
            (centralUpperFaceIds D.half))
  have hhaar :
      D.haarFactor state ≈
        u1HaarFactorOn D state (centralLowerLinks D.half) *
          (u1HaarFactorOn D state (centralFixedLinks D.half) *
            u1HaarFactorOn D state (centralUpperLinks D.half)) := by
    unfold U1SlabData.haarFactor u1HaarFactorOn
    let value : Z4Link → Q' := u1HaarLinkFactor D.extent state
    calc
      listQProduct value
          (boundaryCompleteSlabLinks (centralExtent D.half)) ≈
        listQProduct value
          (centralLowerLinks D.half ++ centralFixedLinks D.half ++
            centralUpperLinks D.half) :=
        listQProduct_perm value
          (centralSlabLinkParts_perm D.half).symm
      _ ≈ listQProduct value (centralLowerLinks D.half) *
          listQProduct value
            (centralFixedLinks D.half ++
              centralUpperLinks D.half) := by
        simpa only [List.append_assoc] using
          listQProduct_append_eqv value (centralLowerLinks D.half)
            (centralFixedLinks D.half ++ centralUpperLinks D.half)
      _ ≈ listQProduct value (centralLowerLinks D.half) *
          (listQProduct value (centralFixedLinks D.half) *
            listQProduct value (centralUpperLinks D.half)) :=
        Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_eqv value (centralFixedLinks D.half)
            (centralUpperLinks D.half))
  unfold U1SlabData.physicalTerm u1LowerFactor u1FixedWeight
    u1UpperFactor
  refine Q'.eqv_trans _
    ((u1FaceFactorOn D state (centralLowerFaceIds D.half) *
      (u1FaceFactorOn D state (centralFixedFaceIds D.half) *
        u1FaceFactorOn D state (centralUpperFaceIds D.half))) *
      (u1HaarFactorOn D state (centralLowerLinks D.half) *
        (u1HaarFactorOn D state (centralFixedLinks D.half) *
          u1HaarFactorOn D state (centralUpperLinks D.half)))) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hface)
      (Q'.mul_eqv_congr_left _ _ _ hhaar)
  · exact rearrange_six _ _ _ _ _ _

private theorem listQProduct_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQProduct value items
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (listQProduct_nonnegative value hvalue tail)

theorem u1FixedWeight_nonnegative
    (D : U1SlabData) (state : ChargeLabelling) :
    (0 : Q') ≤ u1FixedWeight D state := by
  unfold u1FixedWeight u1FaceFactorOn u1HaarFactorOn
  apply Q'.mul_nonneg
  · apply listQProduct_nonnegative
    intro id
    exact abelCoeff_nonneg D.coupling_nonnegative _
  · apply listQProduct_nonnegative
    intro link
    unfold u1HaarLinkFactor
    split
    · exact Q'.zero_le_one
    · exact Q'.le_refl' 0

def conjugateChargeLabelling
    (state : ChargeLabelling) : ChargeLabelling :=
  fun id => negateChargeLabel (state id)

@[simp] theorem conjugateChargeLabelling_zero :
    conjugateChargeLabelling zeroEdgeLabelling = zeroEdgeLabelling := by
  funext id
  rfl

theorem conjugateChargeLabelling_involutive
    (state : ChargeLabelling) :
    conjugateChargeLabelling (conjugateChargeLabelling state) = state := by
  funext id
  exact negateChargeLabel_involutive _

private theorem listIntSum_neg {A : Type} (value : A → Int) :
    ∀ items : List A,
      listIntSum (fun item => -value item) items =
        -listIntSum value items
  | [] => rfl
  | head :: tail => by
      simp only [listIntSum]
      rw [listIntSum_neg value tail, Int.neg_add]

private theorem listIntSum_congr {A : Type}
    (left right : A → Int) :
    ∀ items : List A, (∀ item, left item = right item) →
      listIntSum left items = listIntSum right items
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listIntSum]
      rw [hagree head, listIntSum_congr left right tail hagree]

theorem u1LinkCharge_conjugate
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) :
    u1LinkCharge extent (conjugateChargeLabelling state) link =
      -u1LinkCharge extent state link := by
  unfold u1LinkCharge conjugateChargeLabelling
  let value : Nat → Int := fun id =>
    orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
      decodeCharge (state id)
  have hpoint : ∀ id,
      orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
          decodeCharge (negateChargeLabel (state id)) =
        -value id := by
    intro id
    rw [decodeCharge_negateChargeLabel, Int.mul_neg]
  calc
    listIntSum
        (fun id =>
          orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
            decodeCharge (negateChargeLabel (state id)))
        (slabIncidentPlaqIds extent link) =
      listIntSum (fun id => -value id)
        (slabIncidentPlaqIds extent link) := by
      apply listIntSum_congr
      exact hpoint
    _ = -listIntSum value (slabIncidentPlaqIds extent link) :=
      listIntSum_neg value _

theorem u1HaarLinkFactor_conjugate
    (extent : Nat) (state : ChargeLabelling) (link : Z4Link) :
    u1HaarLinkFactor extent (conjugateChargeLabelling state) link =
      u1HaarLinkFactor extent state link := by
  unfold u1HaarLinkFactor
  rw [u1LinkCharge_conjugate]
  simp

theorem u1FaceFactorOn_conjugate
    (D : U1SlabData) (state : ChargeLabelling) (ids : List Nat) :
    u1FaceFactorOn D (conjugateChargeLabelling state) ids =
      u1FaceFactorOn D state ids := by
  unfold u1FaceFactorOn conjugateChargeLabelling
  apply listQProduct_congr
  intro id _
  rw [chargeMagnitude_negateChargeLabel]

theorem u1HaarFactorOn_conjugate
    (D : U1SlabData) (state : ChargeLabelling) (links : List Z4Link) :
    u1HaarFactorOn D (conjugateChargeLabelling state) links =
      u1HaarFactorOn D state links := by
  unfold u1HaarFactorOn
  apply listQProduct_congr
  intro link _
  exact u1HaarLinkFactor_conjugate D.extent state link

theorem u1LowerFactor_conjugate
    (D : U1SlabData) (state : ChargeLabelling) :
    u1LowerFactor D (conjugateChargeLabelling state) =
      u1LowerFactor D state := by
  unfold u1LowerFactor
  rw [u1FaceFactorOn_conjugate, u1HaarFactorOn_conjugate]

private theorem u1FaceFactorOn_upper_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    u1FaceFactorOn D state (centralUpperFaceIds D.half) ≈
      u1FaceFactorOn D (reflectU1SlabLabelling D.extent state)
        (centralLowerFaceIds D.half) := by
  let sourceValue : Nat → Q' := fun id =>
    abelCoeff D.coupling (chargeMagnitude (state id))
  let reflectedValue : Nat → Q' := fun id =>
    abelCoeff D.coupling
      (chargeMagnitude (reflectU1SlabLabelling D.extent state id))
  calc
    u1FaceFactorOn D state (centralUpperFaceIds D.half) ≈
      listQProduct reflectedValue
        ((centralUpperFaceIds D.half).map
          (slabFaceReflectId D.extent)) := by
      unfold u1FaceFactorOn
      rw [listQProduct_map]
      apply listQProduct_congr_eqv
      intro id hid
      have hidPhysical := (mem_centralUpperFaceIds.mp hid).1
      have hidPhysicalD :
          id ∈ slabPhysicalFaceEdges D.extent := by
        simpa [U1SlabData.extent] using hidPhysical
      unfold reflectedValue
      rw [reflectU1SlabLabelling_on_physical
          (slabFaceReflectId_physical hidPhysicalD),
        slabFaceReflectId_involutive hidPhysicalD,
        chargeMagnitude_reflectChargeLabel]
      exact Q'.eqv_refl _
    _ ≈ listQProduct reflectedValue
        (centralLowerFaceIds D.half) :=
      listQProduct_perm reflectedValue
        (centralUpperFaceIds_reflection_perm D.half)

private theorem u1HaarFactorOn_upper_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    u1HaarFactorOn D state (centralUpperLinks D.half) ≈
      u1HaarFactorOn D (reflectU1SlabLabelling D.extent state)
        (centralLowerLinks D.half) := by
  let reflectedValue : Z4Link → Q' := fun link =>
    u1HaarLinkFactor D.extent
      (reflectU1SlabLabelling D.extent state) link
  calc
    u1HaarFactorOn D state (centralUpperLinks D.half) =
      listQProduct
        (fun link => reflectedValue (timeReflectLink D.extent link))
        (centralUpperLinks D.half) := by
      unfold u1HaarFactorOn
      apply listQProduct_congr
      intro link hlink
      exact (u1HaarLinkFactor_reflection
        (mem_centralUpperLinks.mp hlink).1).symm
    _ = listQProduct reflectedValue
        ((centralUpperLinks D.half).map
          (timeReflectLink D.extent)) :=
      (listQProduct_map reflectedValue (timeReflectLink D.extent) _).symm
    _ ≈ listQProduct reflectedValue
        (centralLowerLinks D.half) :=
      listQProduct_perm reflectedValue
        (centralUpperLinks_reflection_perm D.half)

theorem u1UpperFactor_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    u1UpperFactor D state ≈
      u1LowerFactor D (reflectU1SlabLabelling D.extent state) := by
  unfold u1UpperFactor u1LowerFactor
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (u1FaceFactorOn_upper_reflection D state))
    (Q'.mul_eqv_congr_left _ _ _
      (u1HaarFactorOn_upper_reflection D state))

private theorem listIntSum_congr_on {A : Type}
    (left right : A → Int) :
    ∀ items : List A,
      (∀ item, item ∈ items → left item = right item) →
      listIntSum left items = listIntSum right items
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listIntSum]
      rw [hagree head List.mem_cons_self,
        listIntSum_congr_on left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

private theorem u1LinkCharge_eq_of_eq_on_incident
    (extent : Nat) (left right : ChargeLabelling) (link : Z4Link)
    (hagree : ∀ id, id ∈ slabIncidentPlaqIds extent link →
      left id = right id) :
    u1LinkCharge extent left link = u1LinkCharge extent right link := by
  unfold u1LinkCharge
  apply listIntSum_congr_on
  intro id hid
  rw [hagree id hid]

private theorem u1HaarLinkFactor_eq_of_eq_on_incident
    (extent : Nat) (left right : ChargeLabelling) (link : Z4Link)
    (hagree : ∀ id, id ∈ slabIncidentPlaqIds extent link →
      left id = right id) :
    u1HaarLinkFactor extent left link =
      u1HaarLinkFactor extent right link := by
  unfold u1HaarLinkFactor
  rw [u1LinkCharge_eq_of_eq_on_incident extent left right link hagree]

private theorem u1FaceFactorOn_congr
    (D : U1SlabData) (left right : ChargeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id = right id) →
      u1FaceFactorOn D left ids = u1FaceFactorOn D right ids
  | ids, hagree => by
      unfold u1FaceFactorOn
      apply listQProduct_congr
      intro id hid
      rw [hagree id hid]

private theorem u1HaarFactorOn_congr
    (D : U1SlabData) (left right : ChargeLabelling) :
    ∀ links : List Z4Link,
      (∀ link, link ∈ links →
        ∀ id, id ∈ slabIncidentPlaqIds D.extent link →
          left id = right id) →
      u1HaarFactorOn D left links = u1HaarFactorOn D right links
  | links, hagree => by
      unfold u1HaarFactorOn
      apply listQProduct_congr
      intro link hlink
      exact u1HaarLinkFactor_eq_of_eq_on_incident
        D.extent left right link (hagree link hlink)

theorem u1LowerFactor_eq_of_eq_on_not_upper
    (D : U1SlabData) (left right : ChargeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges D.extent →
      plaquetteHalfSide D.half (slabPlaquetteAt D.extent id) ≠ .upper →
      left id = right id) :
    u1LowerFactor D left = u1LowerFactor D right := by
  have hface :
      u1FaceFactorOn D left (centralLowerFaceIds D.half) =
        u1FaceFactorOn D right (centralLowerFaceIds D.half) := by
    apply u1FaceFactorOn_congr
    intro id hid
    have hparts := mem_centralLowerFaceIds.mp hid
    apply hagree id
    · simpa [U1SlabData.extent] using hparts.1
    · simpa [U1SlabData.extent, hparts.2]
  have hhaar :
      u1HaarFactorOn D left (centralLowerLinks D.half) =
        u1HaarFactorOn D right (centralLowerLinks D.half) := by
    apply u1HaarFactorOn_congr
    intro link hlink id hid
    apply hagree id
    · simpa [U1SlabData.extent] using slabIncidentPlaqId_physical hid
    · simpa [U1SlabData.extent] using
        incident_of_lower_link_ne_upper hlink hid
  unfold u1LowerFactor
  rw [hface, hhaar]

theorem u1FixedWeight_eq_of_eq_on_fixed
    (D : U1SlabData) (left right : ChargeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges D.extent →
      plaquetteHalfSide D.half (slabPlaquetteAt D.extent id) = .fixed →
      left id = right id) :
    u1FixedWeight D left = u1FixedWeight D right := by
  have hface :
      u1FaceFactorOn D left (centralFixedFaceIds D.half) =
        u1FaceFactorOn D right (centralFixedFaceIds D.half) := by
    apply u1FaceFactorOn_congr
    intro id hid
    have hparts := mem_centralFixedFaceIds.mp hid
    exact hagree id
      (by simpa [U1SlabData.extent] using hparts.1)
      (by simpa [U1SlabData.extent] using hparts.2)
  have hhaar :
      u1HaarFactorOn D left (centralFixedLinks D.half) =
        u1HaarFactorOn D right (centralFixedLinks D.half) := by
    apply u1HaarFactorOn_congr
    intro link hlink id hid
    exact hagree id
      (by simpa [U1SlabData.extent] using
        slabIncidentPlaqId_physical hid)
      (by simpa [U1SlabData.extent] using
        incident_of_fixed_link_fixed hlink hid)
  unfold u1FixedWeight
  rw [hface, hhaar]

def assembleU1ReflectedSlabLabelling
    (half : Nat) (left boundary right : ChargeLabelling) :
    ChargeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges (centralExtent half) then
      match plaquetteHalfSide half
          (slabPlaquetteAt (centralExtent half) id) with
      | .lower => left id
      | .fixed => boundary id
      | .upper =>
          reflectChargeLabel
            (slabPlaquetteAt (centralExtent half) id).2
            (right (slabFaceReflectId (centralExtent half) id))
    else 0

theorem assembleU1ReflectedSlabLabelling_lower
    {half id : Nat} {left boundary right : ChargeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .lower) :
    assembleU1ReflectedSlabLabelling half left boundary right id =
      left id := by
  simp [assembleU1ReflectedSlabLabelling, hid, hside]

theorem assembleU1ReflectedSlabLabelling_fixed
    {half id : Nat} {left boundary right : ChargeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .fixed) :
    assembleU1ReflectedSlabLabelling half left boundary right id =
      boundary id := by
  simp [assembleU1ReflectedSlabLabelling, hid, hside]

theorem assembleU1ReflectedSlabLabelling_upper
    {half id : Nat} {left boundary right : ChargeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .upper) :
    assembleU1ReflectedSlabLabelling half left boundary right id =
      reflectChargeLabel
        (slabPlaquetteAt (centralExtent half) id).2
        (right (slabFaceReflectId (centralExtent half) id)) := by
  simp [assembleU1ReflectedSlabLabelling, hid, hside]

theorem u1LowerFactor_assemble_independent_right
    (D : U1SlabData) (left boundary right : ChargeLabelling) :
    u1LowerFactor D
        (assembleU1ReflectedSlabLabelling D.half left boundary right) =
      u1LowerFactor D
        (assembleU1ReflectedSlabLabelling D.half left boundary
          zeroEdgeLabelling) := by
  apply u1LowerFactor_eq_of_eq_on_not_upper
  intro id hid hnotUpper
  have hid' : id ∈ slabPhysicalFaceEdges (centralExtent D.half) := by
    simpa [U1SlabData.extent] using hid
  cases hside : plaquetteHalfSide D.half
      (slabPlaquetteAt (centralExtent D.half) id)
  · rw [assembleU1ReflectedSlabLabelling_lower hid' hside,
      assembleU1ReflectedSlabLabelling_lower hid' hside]
  · rw [assembleU1ReflectedSlabLabelling_fixed hid' hside,
      assembleU1ReflectedSlabLabelling_fixed hid' hside]
  · exact False.elim (hnotUpper (by
      simpa [U1SlabData.extent] using hside))

theorem u1FixedWeight_assemble_only_boundary
    (D : U1SlabData) (left boundary right : ChargeLabelling) :
    u1FixedWeight D
        (assembleU1ReflectedSlabLabelling D.half left boundary right) =
      u1FixedWeight D
        (assembleU1ReflectedSlabLabelling D.half zeroEdgeLabelling
          boundary zeroEdgeLabelling) := by
  apply u1FixedWeight_eq_of_eq_on_fixed
  intro id hid hfixed
  have hid' : id ∈ slabPhysicalFaceEdges (centralExtent D.half) := by
    simpa [U1SlabData.extent] using hid
  have hfixed' : plaquetteHalfSide D.half
      (slabPlaquetteAt (centralExtent D.half) id) = .fixed := by
    simpa [U1SlabData.extent] using hfixed
  rw [assembleU1ReflectedSlabLabelling_fixed hid' hfixed',
    assembleU1ReflectedSlabLabelling_fixed hid' hfixed']

private theorem reflectChargeLabel_eq_negate_of_fixed
    {half : Nat} {plaquette : Z4Plaq} {label : Nat}
    (hfixed : plaquetteHalfSide half plaquette = .fixed) :
    reflectChargeLabel plaquette.2 label = negateChargeLabel label := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := plaquette
  cases plane
  · simp only [plaquetteHalfSide, spatialHalfSide] at hfixed
    split at hfixed <;> cases hfixed
  · simp only [plaquetteHalfSide, spatialHalfSide] at hfixed
    split at hfixed <;> cases hfixed
  · rfl
  · simp only [plaquetteHalfSide, spatialHalfSide] at hfixed
    split at hfixed <;> cases hfixed
  · rfl
  · rfl

private theorem conjugate_reflect_assemble_eq_on_not_upper
    (D : U1SlabData)
    (left boundary right : ChargeLabelling)
    {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges D.extent)
    (hnotUpper : plaquetteHalfSide D.half
      (slabPlaquetteAt D.extent id) ≠ .upper) :
    conjugateChargeLabelling
        (reflectU1SlabLabelling D.extent
          (assembleU1ReflectedSlabLabelling
            D.half left boundary right)) id =
      assembleU1ReflectedSlabLabelling D.half
        (conjugateChargeLabelling right) boundary
        zeroEdgeLabelling id := by
  have hid' : id ∈ slabPhysicalFaceEdges (centralExtent D.half) := by
    simpa [U1SlabData.extent] using hid
  have hnotUpper' : plaquetteHalfSide D.half
      (slabPlaquetteAt (centralExtent D.half) id) ≠ .upper := by
    simpa [U1SlabData.extent] using hnotUpper
  unfold conjugateChargeLabelling
  rw [reflectU1SlabLabelling_on_physical hid]
  change negateChargeLabel
      (reflectChargeLabel
        (slabPlaquetteAt (centralExtent D.half) id).2
        (assembleU1ReflectedSlabLabelling D.half left boundary right
          (slabFaceReflectId (centralExtent D.half) id))) =
    assembleU1ReflectedSlabLabelling D.half
      (fun item => negateChargeLabel (right item)) boundary
      zeroEdgeLabelling id
  cases hside : plaquetteHalfSide D.half
      (slabPlaquetteAt (centralExtent D.half) id)
  · have hreflectedPhysical := slabFaceReflectId_physical hid'
    have hreflectedSide := slabFaceReflectId_side hid'
    rw [hside] at hreflectedSide
    have hupper : plaquetteHalfSide D.half
        (slabPlaquetteAt (centralExtent D.half)
          (slabFaceReflectId (centralExtent D.half) id)) = .upper := by
      simpa [flipSide] using hreflectedSide
    rw [assembleU1ReflectedSlabLabelling_upper
        hreflectedPhysical hupper,
      slabPlaquetteAt_slabFaceReflectId hid',
      timeReflectPlaquette_plane,
      slabFaceReflectId_involutive hid',
      reflectChargeLabel_involutive,
      assembleU1ReflectedSlabLabelling_lower hid' hside]
  · have hreflectedPhysical := slabFaceReflectId_physical hid'
    have hfixedId :=
      slabFaceReflectId_eq_self_of_fixed_side hid' hside
    have hreflectedSide := slabFaceReflectId_side hid'
    rw [hside] at hreflectedSide
    have hfixedReflected : plaquetteHalfSide D.half
        (slabPlaquetteAt (centralExtent D.half)
          (slabFaceReflectId (centralExtent D.half) id)) = .fixed := by
      simpa [flipSide] using hreflectedSide
    rw [assembleU1ReflectedSlabLabelling_fixed
        hreflectedPhysical hfixedReflected,
      hfixedId,
      reflectChargeLabel_eq_negate_of_fixed hside,
      negateChargeLabel_involutive,
      assembleU1ReflectedSlabLabelling_fixed hid' hside]
  · exact False.elim (hnotUpper' hside)

theorem u1UpperFactor_assembled_eq_conjugate_lowerAmplitude
    (D : U1SlabData)
    (left boundary right : ChargeLabelling) :
    u1UpperFactor D
        (assembleU1ReflectedSlabLabelling D.half left boundary right) ≈
      u1LowerFactor D
        (assembleU1ReflectedSlabLabelling D.half
          (conjugateChargeLabelling right) boundary
          zeroEdgeLabelling) := by
  let assembled :=
    assembleU1ReflectedSlabLabelling D.half left boundary right
  refine Q'.eqv_trans _
    (u1LowerFactor D (reflectU1SlabLabelling D.extent assembled)) _
    (u1UpperFactor_reflection D assembled) ?_
  refine Q'.eqv_trans _
    (u1LowerFactor D
      (conjugateChargeLabelling
        (reflectU1SlabLabelling D.extent assembled))) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.eqv_of_eq
      (u1LowerFactor_conjugate D
        (reflectU1SlabLabelling D.extent assembled)))
  · exact Q'.eqv_of_eq
      (u1LowerFactor_eq_of_eq_on_not_upper D _ _
        (fun id hid hnotUpper =>
          conjugate_reflect_assemble_eq_on_not_upper
            D left boundary right hid hnotUpper))

def u1HalfStates (D : U1SlabData) : List ChargeLabelling :=
  boundedEdgeLabellings (2 * D.chargeCutoff)
    (centralLowerFaceIds D.half)

def u1BoundaryChannels (D : U1SlabData) : List ChargeLabelling :=
  boundedEdgeLabellings (2 * D.chargeCutoff)
    (centralFixedFaceIds D.half)

def u1HalfAmplitude
    (D : U1SlabData) (state boundary : ChargeLabelling) : Q' :=
  u1LowerFactor D
    (assembleU1ReflectedSlabLabelling D.half
      state boundary zeroEdgeLabelling)

def u1BoundaryWeight
    (D : U1SlabData) (boundary : ChargeLabelling) : Q' :=
  u1FixedWeight D
    (assembleU1ReflectedSlabLabelling D.half
      zeroEdgeLabelling boundary zeroEdgeLabelling)

def u1PhysicalReflectedKernel
    (D : U1SlabData) (left right : ChargeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      D.physicalTerm
        (assembleU1ReflectedSlabLabelling D.half left boundary right))
    (u1BoundaryChannels D)

private theorem rotate_three (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  show (a * (b * c)).num * (((b * (a * c)).den) : Int) =
    (b * (a * c)).num * (((a * (b * c)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

theorem u1PhysicalTerm_eq_twisted_gram_integrand
    (D : U1SlabData)
    (left boundary right : ChargeLabelling) :
    D.physicalTerm
        (assembleU1ReflectedSlabLabelling D.half left boundary right) ≈
      u1BoundaryWeight D boundary *
        (u1HalfAmplitude D left boundary *
          u1HalfAmplitude D (conjugateChargeLabelling right) boundary) := by
  let assembled :=
    assembleU1ReflectedSlabLabelling D.half left boundary right
  refine Q'.eqv_trans _
    (u1LowerFactor D assembled *
      (u1FixedWeight D assembled * u1UpperFactor D assembled)) _
    (physicalTerm_crossPlane_factorization D assembled) ?_
  rw [u1LowerFactor_assemble_independent_right D left boundary right,
    u1FixedWeight_assemble_only_boundary D left boundary right]
  refine Q'.eqv_trans _
    (u1HalfAmplitude D left boundary *
      (u1BoundaryWeight D boundary *
        u1HalfAmplitude D (conjugateChargeLabelling right) boundary)) _
    ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (u1UpperFactor_assembled_eq_conjugate_lowerAmplitude
          D left boundary right))
  · exact rotate_three _ _ _

theorem u1PhysicalReflectedKernel_eq_twistedGram
    (D : U1SlabData) (left right : ChargeLabelling) :
    u1PhysicalReflectedKernel D left right ≈
      weightedGram (u1BoundaryChannels D)
        (u1BoundaryWeight D) (u1HalfAmplitude D)
        left (conjugateChargeLabelling right) := by
  unfold u1PhysicalReflectedKernel weightedGram
  apply listQSum_congr_on
  intro boundary _
  exact u1PhysicalTerm_eq_twisted_gram_integrand
    D left boundary right

theorem u1BoundaryWeight_nonnegative_on
    (D : U1SlabData) :
    ∀ boundary, boundary ∈ u1BoundaryChannels D →
      (0 : Q') ≤ u1BoundaryWeight D boundary := by
  intro boundary _
  unfold u1BoundaryWeight
  exact u1FixedWeight_nonnegative D _

private theorem negateChargeLabel_lt_cutoff
    {cutoff label : Nat} (hlabel : label < 2 * cutoff + 1) :
    negateChargeLabel label < 2 * cutoff + 1 := by
  simpa [reflectChargeLabel] using
    (reflectChargeLabel_lt_cutoff (plane := Z4Plane.p03) hlabel)

theorem conjugateChargeLabelling_mem_half
    (D : U1SlabData) {state : ChargeLabelling}
    (hstate : state ∈ u1HalfStates D) :
    conjugateChargeLabelling state ∈ u1HalfStates D := by
  unfold u1HalfStates at hstate ⊢
  have hsound := boundedEdgeLabellings_sound
    (2 * D.chargeCutoff) (centralLowerFaceIds D.half) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    unfold conjugateChargeLabelling
    exact negateChargeLabel_lt_cutoff (hsound.1 id hid)
  · intro id hid
    unfold conjugateChargeLabelling
    rw [hsound.2 id hid]
    rfl

private theorem permOfNodupMemIff {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := permOfNodupMemIff tail (before ++ after)
        hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem conjugateHalfStates_perm (D : U1SlabData) :
    ((u1HalfStates D).map conjugateChargeLabelling).Perm
      (u1HalfStates D) := by
  have hnodup : (u1HalfStates D).Nodup := by
    unfold u1HalfStates
    exact centralHalfStates_nodup (2 * D.chargeCutoff) D.half
  apply permOfNodupMemIff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      conjugateChargeLabelling (u1HalfStates D) hnodup
    intro left _ right _ heq
    rw [← conjugateChargeLabelling_involutive left,
      ← conjugateChargeLabelling_involutive right]
    exact congrArg conjugateChargeLabelling heq
  · exact hnodup
  · intro state
    constructor
    · intro hstate
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hstate
      rw [← hsourceEq]
      exact conjugateChargeLabelling_mem_half D hsource
    · intro hstate
      have hconj := conjugateChargeLabelling_mem_half D hstate
      exact List.mem_map.mpr
        ⟨conjugateChargeLabelling state, hconj,
          conjugateChargeLabelling_involutive state⟩

def ChargeConjugationEvenOn
    (D : U1SlabData) (coefficient : ChargeLabelling → Q') : Prop :=
  ∀ state, state ∈ u1HalfStates D →
    coefficient (conjugateChargeLabelling state) = coefficient state

def u1PhysicalReflectionQuadratic
    (D : U1SlabData) (coefficient : ChargeLabelling → Q') : Q' :=
  listQSum
    (fun left =>
      listQSum
        (fun right =>
          (coefficient left * coefficient right) *
            u1PhysicalReflectedKernel D left right)
        (u1HalfStates D))
    (u1HalfStates D)

theorem u1PhysicalReflectionQuadratic_eq_weightedGram
    (D : U1SlabData) (coefficient : ChargeLabelling → Q')
    (heven : ChargeConjugationEvenOn D coefficient) :
    u1PhysicalReflectionQuadratic D coefficient ≈
      weightedGramQuadratic
        (u1HalfStates D) (u1BoundaryChannels D)
        (u1BoundaryWeight D) (u1HalfAmplitude D)
        coefficient := by
  unfold u1PhysicalReflectionQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hleft
  let sourceValue : ChargeLabelling → Q' := fun right =>
    (coefficient left * coefficient right) *
      u1PhysicalReflectedKernel D left right
  let targetValue : ChargeLabelling → Q' := fun right =>
    (coefficient left * coefficient right) *
      weightedGram (u1BoundaryChannels D)
        (u1BoundaryWeight D) (u1HalfAmplitude D) left right
  calc
    listQSum sourceValue (u1HalfStates D) ≈
      listQSum sourceValue
        ((u1HalfStates D).map conjugateChargeLabelling) :=
      YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm
        sourceValue (conjugateHalfStates_perm D).symm
    _ = listQSum
        (fun right => sourceValue (conjugateChargeLabelling right))
        (u1HalfStates D) :=
      YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm.listQSum_map
        sourceValue conjugateChargeLabelling _
    _ ≈ listQSum targetValue (u1HalfStates D) := by
      apply listQSum_congr_on
      intro right hright
      unfold sourceValue targetValue
      rw [heven right hright]
      have hkernel :=
        u1PhysicalReflectedKernel_eq_twistedGram
          D left (conjugateChargeLabelling right)
      rw [conjugateChargeLabelling_involutive] at hkernel
      exact Q'.mul_eqv_congr_left _ _ _
        hkernel

theorem u1PhysicalReflectionQuadratic_nonnegative
    (D : U1SlabData) (coefficient : ChargeLabelling → Q')
    (heven : ChargeConjugationEvenOn D coefficient) :
    (0 : Q') ≤ u1PhysicalReflectionQuadratic D coefficient := by
  have hgram : (0 : Q') ≤
      weightedGramQuadratic
        (u1HalfStates D) (u1BoundaryChannels D)
        (u1BoundaryWeight D) (u1HalfAmplitude D)
        coefficient :=
    weightedGramQuadratic_nonnegative _ _ _ _ _
      (u1BoundaryWeight_nonnegative_on D)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (u1PhysicalReflectionQuadratic_eq_weightedGram
        D coefficient heven))

end YMGap.Continuum.BF4U1TwistedReflectionGram

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.physicalTerm_crossPlane_factorization
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.u1UpperFactor_reflection
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.u1PhysicalTerm_eq_twisted_gram_integrand
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.u1PhysicalReflectedKernel_eq_twistedGram
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.conjugateHalfStates_perm
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.u1PhysicalReflectionQuadratic_eq_weightedGram
#print axioms YMGap.Continuum.BF4U1TwistedReflectionGram.u1PhysicalReflectionQuadratic_nonnegative
