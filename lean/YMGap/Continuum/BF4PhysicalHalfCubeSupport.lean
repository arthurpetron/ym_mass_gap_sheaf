/-
# All-cutoff half-slab support and boundary parity constraints

Eighteen lower faces have a production link incident only on that face,
with no fixed-interface coordinate. Nonzero half amplitude therefore forces
every lower label outside the central cube to zero, at arbitrary cutoff.
Five further production links read the pair parities of a spanning tree on
the six cube faces against their fixed-interface labels. Two nonzero half
amplitudes sharing a boundary have the same five pair parities.

All statements concern the original physical half amplitude. The tables are
checked geometry, not enumerations of bounded spin assignments. There is no
spectral, traffic, thermodynamic, or continuum claim.
-/

import YMGap.Continuum.BF4CentralLowerCubePositiveRow
import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalHalfCubeSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def lowerLinkAt (index : Nat) : Z4Link :=
  (centralLowerLinks 0).getD index ((0, 0, 0, 0), .x0)

def exteriorPinIndex (face : Nat) : Nat :=
  match face with
  | 10 => 12 | 12 => 14 | 18 => 17 | 21 => 21 | 27 => 22 | 28 => 24
  | 30 => 26 | 36 => 30 | 37 => 32 | 45 => 34 | 46 => 35 | 48 => 37
  | 54 => 38 | 55 => 40 | 57 => 41 | 63 => 42 | 64 => 44 | 66 => 46
  | _ => 0

/-- These are full production incidence lists, not vacuum-restricted scopes. -/
theorem exteriorPin_geometry (face : Nat)
    (hlower : face ∈ centralLowerFaceIds 0)
    (hoff : face ∉ centralLowerCubeFaceIds) :
    lowerLinkAt (exteriorPinIndex face) ∈ centralLowerLinks 0 ∧
      slabIncidentPlaqIds 1 (lowerLinkAt (exteriorPinIndex face)) = [face] := by
  have hfaces : centralLowerFaceIds 0 =
      [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
       36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66] := by decide
  rw [hfaces] at hlower
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlower
  rcases hlower with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (hoff (by decide)) | decide +kernel

private theorem natProduct_zero {A : Type} (f : A → Nat) :
    ∀ (xs : List A) {a : A}, a ∈ xs → f a = 0 → natListProduct f xs = 0
  | [], _, h, _ => False.elim (List.not_mem_nil h)
  | x :: xs, a, h, hz => by
      rcases List.mem_cons.mp h with heq | ht
      · subst a; simp [natListProduct, hz]
      · simp only [natListProduct, natProduct_zero f xs ht hz, Nat.mul_zero]

/-- Nonzero half amplitude forces every production lower-link factor positive. -/
theorem halfAmplitude_link_pos (w : Q') (K : Nat)
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0)
    (hne : ¬ centralHalfAmplitude w K 0 state boundary ≈ 0) :
    0 < slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) link := by
  by_cases hp : 0 < slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) link
  · exact hp
  · have hz : slabExplicitLinkMultiplicity K 1
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) link = 0 := by omega
    have hprod := natProduct_zero
      (slabExplicitLinkMultiplicity K 1
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling))
      (centralLowerLinks 0) hlink hz
    apply False.elim (hne ?_)
    unfold centralHalfAmplitude centralLowerFactor
    change slabFaceFactorOn w K
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)
        (centralLowerFaceIds 0) * Q'.ofNat
      (natListProduct (slabExplicitLinkMultiplicity K 1
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling))
        (centralLowerLinks 0)) ≈ 0
    rw [hprod]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv) (Q'.mul_zero_eqv _)

theorem assembled_lower (state boundary : EdgeLabelling) {face : Nat}
    (hface : face ∈ centralLowerFaceIds 0) :
    assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling face = state face := by
  have hs := mem_centralLowerFaceIds.mp hface
  exact assembleReflectedSlabLabelling_lower hs.1 hs.2

theorem assembled_fixed (state boundary : EdgeLabelling) {face : Nat}
    (hface : face ∈ centralFixedFaceIds 0) :
    assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling face = boundary face := by
  have hs := mem_centralFixedFaceIds.mp hface
  exact assembleReflectedSlabLabelling_fixed hs.1 hs.2

/-- Every nonzero half amplitude is supported on the six cube coordinates,
at arbitrary coupling, boundary, and representation cutoff. -/
theorem halfAmplitude_zero_off_cube (w : Q') (K : Nat)
    (state boundary : EdgeLabelling) (hstate : state ∈ centralHalfStates K 0)
    (hne : ¬ centralHalfAmplitude w K 0 state boundary ≈ 0)
    (face : Nat) (hoff : face ∉ centralLowerCubeFaceIds) : state face = 0 := by
  by_cases hlower : face ∈ centralLowerFaceIds 0
  · have hg := exteriorPin_geometry face hlower hoff
    have hp := halfAmplitude_link_pos w K state boundary _ hg.1 hne
    unfold slabExplicitLinkMultiplicity at hp
    rw [hg.2] at hp
    simp only [List.map_singleton, assembled_lower state boundary hlower] at hp
    change 0 < oneValentMultiplicity (linkAuxiliaryCutoff K) (state face) at hp
    rw [oneValentMultiplicity_eq_bool_zero] at hp
    by_cases hz : state face = 0
    · exact hz
    · simp [boolMultiplicity, hz] at hp
  · exact (boundedEdgeLabellings_sound K (centralLowerFaceIds 0) state hstate).2 face hlower

structure CubeParityEdge where
  linkIndex : Nat
  left : Nat
  right : Nat
  boundary : Nat
  deriving DecidableEq

def cubeParityEdges : List CubeParityEdge :=
  [⟨0, 0, 1, 2⟩, ⟨1, 0, 3, 4⟩, ⟨5, 1, 9, 11⟩,
   ⟨8, 3, 19, 23⟩, ⟨3, 0, 39, 40⟩]

theorem cubeParityEdge_geometry (edge : CubeParityEdge)
    (he : edge ∈ cubeParityEdges) :
    lowerLinkAt edge.linkIndex ∈ centralLowerLinks 0 ∧
      edge.left ∈ centralLowerCubeFaceIds ∧ edge.right ∈ centralLowerCubeFaceIds := by
  simp only [cubeParityEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def lowerLinkSpinSum (state boundary : EdgeLabelling) (link : Z4Link) : Nat :=
  let spins := (slabIncidentPlaqIds 1 link).map
    (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)
  localExternalSpinSum spins.length (externalSpinsOfList spins)

theorem lowerLinkSpinSum_even (w : Q') (K : Nat)
    (state boundary : EdgeLabelling) (link : Z4Link)
    (hlink : link ∈ centralLowerLinks 0)
    (hne : ¬ centralHalfAmplitude w K 0 state boundary ≈ 0) :
    lowerLinkSpinSum state boundary link % 2 = 0 := by
  have hp := halfAmplitude_link_pos w K state boundary link hlink hne
  by_cases heven : lowerLinkSpinSum state boundary link % 2 = 0
  · exact heven
  · have hodd : lowerLinkSpinSum state boundary link % 2 = 1 := by omega
    have hzero := explicitValenceMultiplicity_eq_zero_of_odd_sum
      (cutoff := linkAuxiliaryCutoff K)
      (degree := ((slabIncidentPlaqIds 1 link).map
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)).length)
      (external := externalSpinsOfList ((slabIncidentPlaqIds 1 link).map
        (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)))
      (by simpa only [List.length_map] using slabIncidentPlaqIds_length_le_six 1 link)
      hodd
    unfold slabExplicitLinkMultiplicity at hp
    rw [hzero] at hp
    omega

/-- Exact spanning-tree parity equations after the eighteen unary pins. -/
theorem cubeParityEdge_spinSum (edge : CubeParityEdge)
    (he : edge ∈ cubeParityEdges) (state boundary : EdgeLabelling)
    (hoff : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    lowerLinkSpinSum state boundary (lowerLinkAt edge.linkIndex) =
      state edge.left + state edge.right + boundary edge.boundary := by
  have h10 := hoff 10 (by decide)
  have h21 := hoff 21 (by decide)
  have h36 := hoff 36 (by decide)
  have hg0 : slabIncidentPlaqIds 1 (lowerLinkAt 0) = [0, 1, 2] := by decide +kernel
  have hg1 : slabIncidentPlaqIds 1 (lowerLinkAt 1) = [0, 3, 4] := by decide +kernel
  have hg5 : slabIncidentPlaqIds 1 (lowerLinkAt 5) = [1, 9, 10, 11] := by decide +kernel
  have hg8 : slabIncidentPlaqIds 1 (lowerLinkAt 8) = [3, 19, 21, 23] := by decide +kernel
  have hg3 : slabIncidentPlaqIds 1 (lowerLinkAt 3) = [0, 36, 39, 40] := by decide +kernel
  simp only [cubeParityEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · unfold lowerLinkSpinSum
    rw [hg0]
    change _ + (_ + (_ + 0)) = state 0 + state 1 + boundary 2
    dsimp only [List.map, List.length, externalSpinsOfList, List.getD]
    rw [assembled_lower state boundary (face := 0) (by decide),
      assembled_lower state boundary (face := 1) (by decide),
      assembled_fixed state boundary (face := 2) (by decide)]
    simp [Nat.add_assoc]
  · unfold lowerLinkSpinSum
    rw [hg1]
    change _ + (_ + (_ + 0)) = state 0 + state 3 + boundary 4
    dsimp only [List.map, List.length, externalSpinsOfList, List.getD]
    rw [assembled_lower state boundary (face := 0) (by decide),
      assembled_lower state boundary (face := 3) (by decide),
      assembled_fixed state boundary (face := 4) (by decide)]
    simp [Nat.add_assoc]
  · unfold lowerLinkSpinSum
    rw [hg5]
    change _ + (_ + (_ + (_ + 0))) = state 1 + state 9 + boundary 11
    dsimp only [List.map, List.length, externalSpinsOfList, List.getD]
    rw [assembled_lower state boundary (face := 1) (by decide),
      assembled_lower state boundary (face := 9) (by decide),
      assembled_lower state boundary (face := 10) (by decide),
      assembled_fixed state boundary (face := 11) (by decide), h10]
    simp [Nat.add_assoc]
  · unfold lowerLinkSpinSum
    rw [hg8]
    change _ + (_ + (_ + (_ + 0))) = state 3 + state 19 + boundary 23
    dsimp only [List.map, List.length, externalSpinsOfList, List.getD]
    rw [assembled_lower state boundary (face := 3) (by decide),
      assembled_lower state boundary (face := 19) (by decide),
      assembled_lower state boundary (face := 21) (by decide),
      assembled_fixed state boundary (face := 23) (by decide), h21]
    simp [Nat.add_assoc]
  · unfold lowerLinkSpinSum
    rw [hg3]
    change _ + (_ + (_ + (_ + 0))) = state 0 + state 39 + boundary 40
    dsimp only [List.map, List.length, externalSpinsOfList, List.getD]
    rw [assembled_lower state boundary (face := 0) (by decide),
      assembled_lower state boundary (face := 36) (by decide),
      assembled_lower state boundary (face := 39) (by decide),
      assembled_fixed state boundary (face := 40) (by decide), h36]
    simp [Nat.add_assoc]

def cubeEdgeParity (edge : CubeParityEdge) (state : EdgeLabelling) : Nat :=
  (state edge.left + state edge.right) % 2

/-- A shared nonzero OS boundary preserves all five relative cube parities. -/
theorem sharedBoundary_cubeEdgeParity_eq (w : Q') (K : Nat)
    (left right boundary : EdgeLabelling)
    (hleft : left ∈ centralHalfStates K 0) (hright : right ∈ centralHalfStates K 0)
    (hleftNe : ¬ centralHalfAmplitude w K 0 left boundary ≈ 0)
    (hrightNe : ¬ centralHalfAmplitude w K 0 right boundary ≈ 0)
    (edge : CubeParityEdge) (he : edge ∈ cubeParityEdges) :
    cubeEdgeParity edge left = cubeEdgeParity edge right := by
  have hg := cubeParityEdge_geometry edge he
  have hl := lowerLinkSpinSum_even w K left boundary _ hg.1 hleftNe
  have hr := lowerLinkSpinSum_even w K right boundary _ hg.1 hrightNe
  rw [cubeParityEdge_spinSum edge he left boundary
    (halfAmplitude_zero_off_cube w K left boundary hleft hleftNe)] at hl
  rw [cubeParityEdge_spinSum edge he right boundary
    (halfAmplitude_zero_off_cube w K right boundary hright hrightNe)] at hr
  unfold cubeEdgeParity
  omega

end YMGap.Continuum.BF4PhysicalHalfCubeSupport

#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.exteriorPin_geometry
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.halfAmplitude_link_pos
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.halfAmplitude_zero_off_cube
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.cubeParityEdge_geometry
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.lowerLinkSpinSum_even
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.cubeParityEdge_spinSum
#print axioms YMGap.Continuum.BF4PhysicalHalfCubeSupport.sharedBoundary_cubeEdgeParity_eq
