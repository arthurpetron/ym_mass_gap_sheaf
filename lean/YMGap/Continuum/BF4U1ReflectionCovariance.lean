/-
# Orientation-correct U(1) reflection on the corrected BF4 slab

The U(1) dual carrier uses signed Fourier charges, so Euclidean time
reflection cannot reuse the self-dual SU(2) label reflection verbatim.
Time-oriented plaquettes reverse orientation and their charges must be
negated; spatial plaquette charges are unchanged.  Likewise a reflected
positive time link carries the opposite geometric orientation.

This module proves the exact local incidence identity

`ε(θp, θl) σp = σl ε(p,l)`

and lifts it to the complete corrected slab.  The reflected divergence is
the original divergence multiplied by the link sign, hence every U(1) Haar
delta is invariant.  The signed reflection is a bounded-carrier involution,
permutes the literal finite Cartesian labelling list, and preserves the
complete physical summand.

This is the orientation/covariance layer.  Reflection positivity of the
resulting charge-conjugation-twisted Gram is proved separately.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1SameCarrierPushforward
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.BF4U1ReflectionCovariance

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact signed-label involution -/

/-- Encoding and then decoding an integer U(1) charge is exact. -/
theorem decodeCharge_encodeCharge (charge : Int) :
    decodeCharge (encodeCharge charge) = charge := by
  cases charge with
  | ofNat magnitude =>
      cases magnitude with
      | zero => rfl
      | succ predecessor =>
          simp only [encodeCharge, Nat.succ_ne_zero, ↓reduceIte]
          have hlabel :
              2 * (predecessor + 1) - 1 = 2 * predecessor + 1 := by
            omega
          rw [hlabel]
          simp [decodeCharge]
  | negSucc predecessor =>
      have hlabel :
          2 * (predecessor + 1) = (2 * predecessor + 1) + 1 := by
        omega
      rw [encodeCharge, hlabel]
      simp only [decodeCharge]
      have hmod : (2 * predecessor + 1) % 2 ≠ 0 := by omega
      rw [if_neg hmod]
      change -(Int.ofNat ((2 * predecessor + 1) / 2 + 1)) =
        Int.negSucc predecessor
      have hdiv : (2 * predecessor + 1) / 2 = predecessor := by omega
      rw [hdiv]
      rfl

/-- Natural-label implementation of charge conjugation `q ↦ -q`. -/
def negateChargeLabel (label : Nat) : Nat :=
  encodeCharge (-decodeCharge label)

theorem decodeCharge_negateChargeLabel (label : Nat) :
    decodeCharge (negateChargeLabel label) = -decodeCharge label := by
  exact decodeCharge_encodeCharge _

theorem negateChargeLabel_involutive (label : Nat) :
    negateChargeLabel (negateChargeLabel label) = label := by
  unfold negateChargeLabel
  rw [decodeCharge_encodeCharge, Int.neg_neg]
  cases label with
  | zero => rfl
  | succ index =>
      simp only [decodeCharge]
      by_cases heven : index % 2 = 0
      · rw [if_pos heven]
        simp [encodeCharge]
        omega
      · rw [if_neg heven]
        have hodd : index % 2 = 1 := by omega
        change encodeCharge (-(Int.ofNat (index / 2 + 1))) = index + 1
        rw [show -(Int.ofNat (index / 2 + 1)) =
            Int.negSucc (index / 2) by rfl]
        simp only [encodeCharge]
        omega

theorem chargeMagnitude_negateChargeLabel (label : Nat) :
    chargeMagnitude (negateChargeLabel label) =
      chargeMagnitude label := by
  rw [← decodeCharge_natAbs, decodeCharge_negateChargeLabel,
    Int.natAbs_neg, decodeCharge_natAbs]

/-! ## 2. Orientation signs and the local incidence identity -/

/-- A reflected two-cell reverses orientation exactly when it contains the
Euclidean time direction. -/
def plaquetteReflectionSign : Z4Plane → Int
  | .p01 | .p02 | .p12 => 1
  | .p03 | .p13 | .p23 => -1

/-- A reflected positive link reverses orientation exactly in direction
`x3`. -/
def linkReflectionSign : Dir4 → Int
  | .x0 | .x1 | .x2 => 1
  | .x3 => -1

/-- Reflect one charge label with the geometric orientation of its face. -/
def reflectChargeLabel (plane : Z4Plane) (label : Nat) : Nat :=
  match plane with
  | .p01 | .p02 | .p12 => label
  | .p03 | .p13 | .p23 => negateChargeLabel label

theorem decodeCharge_reflectChargeLabel
    (plane : Z4Plane) (label : Nat) :
    decodeCharge (reflectChargeLabel plane label) =
      plaquetteReflectionSign plane * decodeCharge label := by
  cases plane <;>
    simp [reflectChargeLabel, plaquetteReflectionSign,
      decodeCharge_negateChargeLabel]

theorem chargeMagnitude_reflectChargeLabel
    (plane : Z4Plane) (label : Nat) :
    chargeMagnitude (reflectChargeLabel plane label) =
      chargeMagnitude label := by
  cases plane <;>
    simp [reflectChargeLabel, chargeMagnitude_negateChargeLabel]

theorem reflectChargeLabel_involutive
    (plane : Z4Plane) (label : Nat) :
    reflectChargeLabel plane (reflectChargeLabel plane label) = label := by
  cases plane <;>
    simp [reflectChargeLabel, negateChargeLabel_involutive]

theorem timeReflectPlaquette_plane
    (extent : Nat) (plaquette : Z4Plaq) :
    (timeReflectPlaquette extent plaquette).2 = plaquette.2 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;> rfl

private theorem addE_ne
    (vertex : Z4Vertex) (direction : Dir4) :
    addE vertex direction ≠ vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction
  · intro heq
    have hcoord := congrArg Prod.fst heq
    change Nat.succ a = a at hcoord
    exact Nat.succ_ne_self a hcoord
  · intro heq
    have hcoord := congrArg (fun v => v.2.1) heq
    change Nat.succ b = b at hcoord
    exact Nat.succ_ne_self b hcoord
  · intro heq
    have hcoord := congrArg (fun v => v.2.2.1) heq
    change Nat.succ c = c at hcoord
    exact Nat.succ_ne_self c hcoord
  · intro heq
    have hcoord := congrArg (fun v => v.2.2.2) heq
    change Nat.succ d = d at hcoord
    exact Nat.succ_ne_self d hcoord

private theorem orientedBoundaryCoefficient_first (plaquette : Z4Plaq) :
    orientedBoundaryCoefficient plaquette
      (plaquette.1, (dirsOf plaquette.2).1) = 1 := by
  unfold orientedBoundaryCoefficient
  rw [if_pos rfl]

private theorem orientedBoundaryCoefficient_second (plaquette : Z4Plaq) :
    orientedBoundaryCoefficient plaquette
      (plaquette.1, (dirsOf plaquette.2).2) = -1 := by
  unfold orientedBoundaryCoefficient
  have hne :
      (plaquette.1, (dirsOf plaquette.2).2) ≠
        (plaquette.1, (dirsOf plaquette.2).1) := by
    intro heq
    exact dirsOf_ne plaquette.2 (congrArg Prod.snd heq).symm
  rw [if_neg hne, if_pos rfl]

private theorem orientedBoundaryCoefficient_third (plaquette : Z4Plaq) :
    orientedBoundaryCoefficient plaquette
      (addE plaquette.1 (dirsOf plaquette.2).2,
        (dirsOf plaquette.2).1) = -1 := by
  unfold orientedBoundaryCoefficient
  have hfirst :
      (addE plaquette.1 (dirsOf plaquette.2).2,
          (dirsOf plaquette.2).1) ≠
        (plaquette.1, (dirsOf plaquette.2).1) := by
    intro heq
    exact addE_ne plaquette.1 (dirsOf plaquette.2).2
      (congrArg Prod.fst heq)
  have hsecond :
      (addE plaquette.1 (dirsOf plaquette.2).2,
          (dirsOf plaquette.2).1) ≠
        (plaquette.1, (dirsOf plaquette.2).2) := by
    intro heq
    exact dirsOf_ne plaquette.2 (congrArg Prod.snd heq)
  rw [if_neg hfirst, if_neg hsecond, if_pos rfl]

private theorem orientedBoundaryCoefficient_fourth (plaquette : Z4Plaq) :
    orientedBoundaryCoefficient plaquette
      (addE plaquette.1 (dirsOf plaquette.2).1,
        (dirsOf plaquette.2).2) = 1 := by
  unfold orientedBoundaryCoefficient
  have hfirst :
      (addE plaquette.1 (dirsOf plaquette.2).1,
          (dirsOf plaquette.2).2) ≠
        (plaquette.1, (dirsOf plaquette.2).1) := by
    intro heq
    exact dirsOf_ne plaquette.2 (congrArg Prod.snd heq).symm
  have hsecond :
      (addE plaquette.1 (dirsOf plaquette.2).1,
          (dirsOf plaquette.2).2) ≠
        (plaquette.1, (dirsOf plaquette.2).2) := by
    intro heq
    exact addE_ne plaquette.1 (dirsOf plaquette.2).1
      (congrArg Prod.fst heq)
  have hthird :
      (addE plaquette.1 (dirsOf plaquette.2).1,
          (dirsOf plaquette.2).2) ≠
        (addE plaquette.1 (dirsOf plaquette.2).2,
          (dirsOf plaquette.2).1) := by
    intro heq
    exact dirsOf_ne plaquette.2 (congrArg Prod.snd heq).symm
  rw [if_neg hfirst, if_neg hsecond, if_neg hthird, if_pos rfl]

private inductive BoundaryEdgeSlot
  | first | second | third | fourth

private def boundaryEdgeAt
    (plaquette : Z4Plaq) : BoundaryEdgeSlot → Z4Link
  | .first => (plaquette.1, (dirsOf plaquette.2).1)
  | .second => (plaquette.1, (dirsOf plaquette.2).2)
  | .third => (addE plaquette.1 (dirsOf plaquette.2).2,
      (dirsOf plaquette.2).1)
  | .fourth => (addE plaquette.1 (dirsOf plaquette.2).1,
      (dirsOf plaquette.2).2)

private def reflectedBoundaryEdgeSlot :
    Z4Plane → BoundaryEdgeSlot → BoundaryEdgeSlot
  | .p01, slot | .p02, slot | .p12, slot => slot
  | .p03, .first | .p13, .first | .p23, .first => .third
  | .p03, .third | .p13, .third | .p23, .third => .first
  | .p03, .second | .p13, .second | .p23, .second => .second
  | .p03, .fourth | .p13, .fourth | .p23, .fourth => .fourth

private def boundarySlotCoefficient : BoundaryEdgeSlot → Int
  | .first => 1
  | .second => -1
  | .third => -1
  | .fourth => 1

private theorem orientedBoundaryCoefficient_boundaryEdgeAt
    (plaquette : Z4Plaq) (slot : BoundaryEdgeSlot) :
    orientedBoundaryCoefficient plaquette (boundaryEdgeAt plaquette slot) =
      boundarySlotCoefficient slot := by
  cases slot
  · exact orientedBoundaryCoefficient_first plaquette
  · exact orientedBoundaryCoefficient_second plaquette
  · exact orientedBoundaryCoefficient_third plaquette
  · exact orientedBoundaryCoefficient_fourth plaquette

private theorem timeReflectLink_boundaryEdgeAt
    (extent : Nat) (plaquette : Z4Plaq) (slot : BoundaryEdgeSlot)
    (hplaquette : plaquetteTimeAdmissible extent plaquette) :
    timeReflectLink extent (boundaryEdgeAt plaquette slot) =
      boundaryEdgeAt (timeReflectPlaquette extent plaquette)
        (reflectedBoundaryEdgeSlot plaquette.2 slot) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;> cases slot
  all_goals simp only [plaquetteTimeAdmissible] at hplaquette
  all_goals simp only [boundaryEdgeAt, dirsOf, addE, timeReflectLink,
    timeReflectPlaquette, reflectedBoundaryEdgeSlot]
  all_goals try rfl
  all_goals
    have hshift : extent - (d + 1) + 1 = extent - d := by omega
    rw [hshift]

private theorem boundarySlot_sign_identity
    (plaquette : Z4Plaq) (slot : BoundaryEdgeSlot) :
    boundarySlotCoefficient
          (reflectedBoundaryEdgeSlot plaquette.2 slot) *
        plaquetteReflectionSign plaquette.2 =
      linkReflectionSign (boundaryEdgeAt plaquette slot).2 *
        boundarySlotCoefficient slot := by
  obtain ⟨vertex, plane⟩ := plaquette
  cases plane <;> cases slot <;> rfl

/-- Orientation covariance of the cubical boundary coefficient. -/
theorem orientedBoundaryCoefficient_reflection
    {extent : Nat} {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquetteTimeAdmissible extent plaquette)
    (hlink : link ∈ edgesOf plaquette) :
    orientedBoundaryCoefficient
        (timeReflectPlaquette extent plaquette)
        (timeReflectLink extent link) *
        plaquetteReflectionSign plaquette.2 =
      linkReflectionSign link.2 *
        orientedBoundaryCoefficient plaquette link := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at hlink
  rcases hlink with hfirst | hsecond | hthird | hfourth
  · change link = boundaryEdgeAt plaquette .first at hfirst
    rw [hfirst, timeReflectLink_boundaryEdgeAt extent plaquette .first
      hplaquette, orientedBoundaryCoefficient_boundaryEdgeAt,
      orientedBoundaryCoefficient_boundaryEdgeAt]
    exact boundarySlot_sign_identity plaquette .first
  · change link = boundaryEdgeAt plaquette .second at hsecond
    rw [hsecond, timeReflectLink_boundaryEdgeAt extent plaquette .second
      hplaquette, orientedBoundaryCoefficient_boundaryEdgeAt,
      orientedBoundaryCoefficient_boundaryEdgeAt]
    exact boundarySlot_sign_identity plaquette .second
  · change link = boundaryEdgeAt plaquette .third at hthird
    rw [hthird, timeReflectLink_boundaryEdgeAt extent plaquette .third
      hplaquette, orientedBoundaryCoefficient_boundaryEdgeAt,
      orientedBoundaryCoefficient_boundaryEdgeAt]
    exact boundarySlot_sign_identity plaquette .third
  · change link = boundaryEdgeAt plaquette .fourth at hfourth
    rw [hfourth, timeReflectLink_boundaryEdgeAt extent plaquette .fourth
      hplaquette, orientedBoundaryCoefficient_boundaryEdgeAt,
      orientedBoundaryCoefficient_boundaryEdgeAt]
    exact boundarySlot_sign_identity plaquette .fourth

/-! ## 3. Supported signed reflection and Gauss-law covariance -/

/-- Orientation-correct reflection, explicitly zero away from the finite
physical corrected-slab carrier. -/
def reflectU1SlabLabelling
    (extent : Nat) (state : ChargeLabelling) : ChargeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges extent then
      reflectChargeLabel
        (slabPlaquetteAt extent id).2
        (state (slabFaceReflectId extent id))
    else 0

theorem reflectU1SlabLabelling_on_physical
    {extent id : Nat} {state : ChargeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    reflectU1SlabLabelling extent state id =
      reflectChargeLabel
        (slabPlaquetteAt extent id).2
        (state (slabFaceReflectId extent id)) := by
  simp [reflectU1SlabLabelling, hid]

theorem reflectU1SlabLabelling_reflected_id
    {extent id : Nat} {state : ChargeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    decodeCharge
        (reflectU1SlabLabelling extent state
          (slabFaceReflectId extent id)) =
      plaquetteReflectionSign (slabPlaquetteAt extent id).2 *
        decodeCharge (state id) := by
  have hreflected := slabFaceReflectId_physical hid
  rw [reflectU1SlabLabelling_on_physical hreflected,
    slabFaceReflectId_involutive hid,
    decodeCharge_reflectChargeLabel]
  rw [slabPlaquetteAt_slabFaceReflectId hid,
    timeReflectPlaquette_plane]

private theorem listIntSum_perm {A : Type} (value : A → Int) :
    ∀ {left right : List A}, left.Perm right →
      listIntSum value left = listIntSum value right
  | _, _, List.Perm.nil => rfl
  | _, _, List.Perm.cons _ h => by
      simp only [listIntSum]
      rw [listIntSum_perm value h]
  | _, _, List.Perm.swap a b rest => by
      simp only [listIntSum]
      omega
  | _, _, List.Perm.trans hleft hright =>
      (listIntSum_perm value hleft).trans
        (listIntSum_perm value hright)

private theorem listIntSum_map {A B : Type}
    (value : B → Int) (f : A → B) :
    ∀ xs : List A,
      listIntSum value (xs.map f) =
        listIntSum (fun item => value (f item)) xs
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, listIntSum]
      rw [listIntSum_map value f tail]

private theorem listIntSum_mul_left {A : Type}
    (constant : Int) (value : A → Int) :
    ∀ xs : List A,
      listIntSum (fun item => constant * value item) xs =
        constant * listIntSum value xs
  | [] => by simp [listIntSum]
  | head :: tail => by
      simp only [listIntSum]
      rw [listIntSum_mul_left constant value tail, Int.mul_add]

private theorem listIntSum_congr_on {A : Type}
    (left right : A → Int) :
    ∀ xs : List A, (∀ item, item ∈ xs → left item = right item) →
      listIntSum left xs = listIntSum right xs
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listIntSum]
      rw [hagree head List.mem_cons_self,
        listIntSum_congr_on left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

private theorem reflectedIncidentTerm
    {extent : Nat} {state : ChargeLabelling}
    {link : Z4Link} {id : Nat}
    (hid : id ∈ slabIncidentPlaqIds extent link) :
    orientedBoundaryCoefficient
        (slabPlaquetteAt extent (slabFaceReflectId extent id))
        (timeReflectLink extent link) *
        decodeCharge
          (reflectU1SlabLabelling extent state
            (slabFaceReflectId extent id)) =
      linkReflectionSign link.2 *
        (orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
          decodeCharge (state id)) := by
  have hidPhysical := slabIncidentPlaqId_physical hid
  have hplaquetteMem := slabPlaquetteAt_mem hidPhysical
  have hadmissible :=
    ((mem_boundaryCompleteSlabPlaquettes extent _).mp hplaquetteMem).2
  have hincidence :
      link ∈ edgesOf (slabPlaquetteAt extent id) := by
    obtain ⟨plaquette, hindexed, hedge⟩ :=
      mem_slabIncidentPlaqIds.mp hid
    have hlookup : slabPlaquetteAt extent id = plaquette := by
      unfold slabPlaquetteAt
      exact enumerate_getD_of_mem fallbackPlaquette hindexed
    simpa only [hlookup] using hedge
  rw [slabPlaquetteAt_slabFaceReflectId hidPhysical,
    reflectU1SlabLabelling_reflected_id hidPhysical]
  rw [← Int.mul_assoc,
    orientedBoundaryCoefficient_reflection hadmissible hincidence,
    Int.mul_assoc]

/-- The complete reflected link divergence differs only by the orientation
sign of the reflected positive link. -/
theorem u1LinkCharge_reflection
    {extent : Nat} {state : ChargeLabelling} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    u1LinkCharge extent
        (reflectU1SlabLabelling extent state)
        (timeReflectLink extent link) =
      linkReflectionSign link.2 * u1LinkCharge extent state link := by
  unfold u1LinkCharge
  let targetValue : Nat → Int := fun id =>
    orientedBoundaryCoefficient (slabPlaquetteAt extent id)
        (timeReflectLink extent link) *
      decodeCharge (reflectU1SlabLabelling extent state id)
  let sourceValue : Nat → Int := fun id =>
    orientedBoundaryCoefficient (slabPlaquetteAt extent id) link *
      decodeCharge (state id)
  have hperm := slabIncidentPlaqIds_reflection_perm hlink
  calc
    listIntSum targetValue
        (slabIncidentPlaqIds extent (timeReflectLink extent link)) =
      listIntSum targetValue
        ((slabIncidentPlaqIds extent link).map
          (slabFaceReflectId extent)) :=
        (listIntSum_perm targetValue hperm).symm
    _ = listIntSum
        (fun id => targetValue (slabFaceReflectId extent id))
        (slabIncidentPlaqIds extent link) :=
      listIntSum_map targetValue (slabFaceReflectId extent) _
    _ = listIntSum
        (fun id => linkReflectionSign link.2 * sourceValue id)
        (slabIncidentPlaqIds extent link) := by
      apply listIntSum_congr_on
      intro id hid
      exact reflectedIncidentTerm hid
    _ = linkReflectionSign link.2 *
        listIntSum sourceValue (slabIncidentPlaqIds extent link) :=
      listIntSum_mul_left _ _ _

theorem u1HaarLinkFactor_reflection
    {extent : Nat} {state : ChargeLabelling} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    u1HaarLinkFactor extent
        (reflectU1SlabLabelling extent state)
        (timeReflectLink extent link) =
      u1HaarLinkFactor extent state link := by
  unfold u1HaarLinkFactor
  rw [u1LinkCharge_reflection hlink]
  cases link.2 <;> simp [linkReflectionSign]

/-! ## 4. Bounded-carrier involution and literal list permutation -/

theorem reflectChargeLabel_lt_cutoff
    {cutoff label : Nat} (plane : Z4Plane)
    (hlabel : label < 2 * cutoff + 1) :
    reflectChargeLabel plane label < 2 * cutoff + 1 := by
  cases plane <;> simp only [reflectChargeLabel]
  all_goals try exact hlabel
  all_goals
    apply Nat.lt_succ_of_le
    apply Nat.le_trans
      (encodeCharge_le_twice_natAbs (-decodeCharge label))
    rw [Int.natAbs_neg, decodeCharge_natAbs]
    exact Nat.mul_le_mul_left 2
      (chargeMagnitude_le_of_label_lt hlabel)

theorem reflectU1SlabLabelling_mem_bounded
    {cutoff extent : Nat} {state : ChargeLabelling}
    (hstate : state ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges extent)) :
    reflectU1SlabLabelling extent state ∈
      boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges extent) := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (slabPhysicalFaceEdges extent) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    rw [reflectU1SlabLabelling_on_physical hid]
    apply reflectChargeLabel_lt_cutoff
    exact hsound.1 _ (slabFaceReflectId_physical hid)
  · intro id hid
    simp [reflectU1SlabLabelling, hid]

theorem reflectU1SlabLabelling_involutive
    {cutoff extent : Nat} {state : ChargeLabelling}
    (hstate : state ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges extent)) :
    reflectU1SlabLabelling extent
        (reflectU1SlabLabelling extent state) = state := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (slabPhysicalFaceEdges extent) state hstate
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges extent
  · have hreflected := slabFaceReflectId_physical hid
    rw [reflectU1SlabLabelling_on_physical hid,
      reflectU1SlabLabelling_on_physical hreflected,
      slabFaceReflectId_involutive hid]
    rw [slabPlaquetteAt_slabFaceReflectId hid,
      timeReflectPlaquette_plane, reflectChargeLabel_involutive]
  · rw [hsound.2 id hid]
    simp [reflectU1SlabLabelling, hid]

theorem reflectU1SlabLabelling_injective_on_bounded
    {cutoff extent : Nat} {left right : ChargeLabelling}
    (hleft : left ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges extent))
    (hright : right ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges extent))
    (heq : reflectU1SlabLabelling extent left =
      reflectU1SlabLabelling extent right) :
    left = right := by
  rw [← reflectU1SlabLabelling_involutive hleft,
    ← reflectU1SlabLabelling_involutive hright]
  exact congrArg (reflectU1SlabLabelling extent) heq

private theorem rangeNodupLocal (n : Nat) :
    (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

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

/-- The orientation-correct reflection is a literal permutation of the
symmetric signed-charge Cartesian carrier. -/
theorem boundedU1SlabLabellings_reflection_perm
    (cutoff extent : Nat) :
    ((boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges extent)).map
      (reflectU1SlabLabelling extent)).Perm
      (boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges extent)) := by
  let labels := boundedEdgeLabellings (2 * cutoff)
    (slabPhysicalFaceEdges extent)
  have hedgeNodup : (slabPhysicalFaceEdges extent).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hlabelsNodup : labels.Nodup :=
    boundedEdgeLabellings_nodup (2 * cutoff)
      (slabPhysicalFaceEdges extent) hedgeNodup
  apply permOfNodupMemIff
  · apply nodup_map_of_injOn
      (reflectU1SlabLabelling extent) labels hlabelsNodup
    intro left hleft right hright heq
    exact reflectU1SlabLabelling_injective_on_bounded
      hleft hright heq
  · exact hlabelsNodup
  · intro state
    constructor
    · intro hstate
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hstate
      rw [← hsourceEq]
      exact reflectU1SlabLabelling_mem_bounded hsource
    · intro hstate
      have hreflected := reflectU1SlabLabelling_mem_bounded hstate
      exact List.mem_map.mpr
        ⟨reflectU1SlabLabelling extent state, hreflected,
          reflectU1SlabLabelling_involutive hstate⟩

/-! ## 5. Full physical weight invariance -/

theorem U1SlabData.faceFactor_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    D.faceFactor (reflectU1SlabLabelling D.extent state) ≈
      D.faceFactor state := by
  unfold U1SlabData.faceFactor U1SlabData.faceEdges
    U1SlabData.carrierData SlabPhysicalData.faceEdges
  let value : Nat → Q' := fun id =>
    abelCoeff D.coupling (chargeMagnitude (state id))
  have hpoint : ∀ id,
      id ∈ slabPhysicalFaceEdges D.extent →
      abelCoeff D.coupling
          (chargeMagnitude (reflectU1SlabLabelling D.extent state id)) =
        value (slabFaceReflectId D.extent id) := by
    intro id hid
    rw [reflectU1SlabLabelling_on_physical hid,
      chargeMagnitude_reflectChargeLabel]
  calc
    listQProduct
        (fun id =>
          abelCoeff D.coupling
            (chargeMagnitude
              (reflectU1SlabLabelling D.extent state id)))
        (slabPhysicalFaceEdges D.extent) =
      listQProduct
        (fun id => value (slabFaceReflectId D.extent id))
        (slabPhysicalFaceEdges D.extent) :=
      listQProduct_congr _ _ _ hpoint
    _ = listQProduct value
        ((slabPhysicalFaceEdges D.extent).map
          (slabFaceReflectId D.extent)) :=
      (listQProduct_map value (slabFaceReflectId D.extent) _).symm
    _ ≈ listQProduct value (slabPhysicalFaceEdges D.extent) :=
      listQProduct_perm value (slabFaceReflectId_range_perm D.extent)

theorem U1SlabData.haarFactor_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    D.haarFactor (reflectU1SlabLabelling D.extent state) ≈
      D.haarFactor state := by
  unfold U1SlabData.haarFactor
  let reflectedValue : Z4Link → Q' := fun link =>
    u1HaarLinkFactor D.extent
      (reflectU1SlabLabelling D.extent state) link
  let sourceValue : Z4Link → Q' := fun link =>
    u1HaarLinkFactor D.extent state link
  calc
    listQProduct reflectedValue
        (boundaryCompleteSlabLinks D.extent) ≈
      listQProduct reflectedValue
        ((boundaryCompleteSlabLinks D.extent).map
          (timeReflectLink D.extent)) :=
      listQProduct_perm reflectedValue
        (timeReflect_boundaryCompleteSlabLinks_perm D.extent).symm
    _ = listQProduct
        (fun link => reflectedValue (timeReflectLink D.extent link))
        (boundaryCompleteSlabLinks D.extent) :=
      listQProduct_map reflectedValue (timeReflectLink D.extent) _
    _ = listQProduct sourceValue
        (boundaryCompleteSlabLinks D.extent) := by
      apply listQProduct_congr
      intro link hlink
      exact u1HaarLinkFactor_reflection hlink

theorem U1SlabData.physicalTerm_reflection
    (D : U1SlabData) (state : ChargeLabelling) :
    D.physicalTerm (reflectU1SlabLabelling D.extent state) ≈
      D.physicalTerm state := by
  unfold U1SlabData.physicalTerm
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (faceFactor_reflection D state))
    (Q'.mul_eqv_congr_left _ _ _ (haarFactor_reflection D state))

end YMGap.Continuum.BF4U1ReflectionCovariance

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.decodeCharge_encodeCharge
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.negateChargeLabel_involutive
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.orientedBoundaryCoefficient_reflection
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.u1LinkCharge_reflection
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.u1HaarLinkFactor_reflection
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.reflectU1SlabLabelling_involutive
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.boundedU1SlabLabellings_reflection_perm
#print axioms YMGap.Continuum.BF4U1ReflectionCovariance.U1SlabData.physicalTerm_reflection
