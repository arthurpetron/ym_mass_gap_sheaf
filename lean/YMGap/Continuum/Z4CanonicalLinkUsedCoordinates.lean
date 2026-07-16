/-
# Exact removal of unused coordinates from the canonical link resolver

For geometric link degrees zero through six, this module records the exact
coordinates that occur in `fuseLabels`.  The complement inside the canonical
eight-coordinate reserved block is explicit.  Every complementary coordinate
carries the normalized vacuum packet, so the constructive vacuum-cylinder
theorem deletes the entire complement without a multiplicity factor.
-/

import YMGap.Continuum.Z4VertexCartesianVacuumRemoval

namespace YMGap.Continuum.Z4CanonicalLinkUsedCoordinates

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4VertexCartesianVacuumRemoval

local infix:50 " ≈ " => Q'.eqv

/-- Coordinates actually read by the canonical `fuseLabels` vertices. -/
def canonicalUsedCoordinates : Nat → List Nat
  | 0 => []
  | 1 => [0, 1]
  | 2 => [0, 1, 2]
  | 3 => [0, 1, 2]
  | 4 => [0, 1, 2, 3, 5]
  | 5 => [0, 1, 2, 3, 4, 6, 7]
  | 6 => [0, 1, 2, 3, 4, 5, 7, 8, 9]
  | degree => canonicalLocalCoordinates degree

/-- The complementary reserved coordinates, in a convenient removal order. -/
def canonicalUnusedCoordinates : Nat → List Nat
  | 0 => List.range 8
  | 1 => (List.range 7).map (fun j => 2 + j)
  | 2 => (List.range 7).map (fun j => 3 + j)
  | 3 => (List.range 8).map (fun j => 3 + j)
  | 4 => 4 :: (List.range 6).map (fun j => 6 + j)
  | 5 => 5 :: (List.range 5).map (fun j => 8 + j)
  | 6 => 6 :: (List.range 4).map (fun j => 10 + j)
  | _ => []

private theorem perm_four_blocks {A B C D : List Nat} :
    (A ++ B ++ C ++ D).Perm (B ++ D ++ A ++ C) := by
  have hswap : (A ++ B ++ C ++ D).Perm (B ++ A ++ C ++ D) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc A B (C ++ D))
  have hmove : (A ++ C ++ D).Perm (D ++ A ++ C) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := A ++ C) (l₂ := D))
  have htail : (B ++ A ++ C ++ D).Perm (B ++ D ++ A ++ C) := by
    simpa only [List.append_assoc] using hmove.append_left B
  exact hswap.trans htail

/-- The explicit used/unused split is a permutation of the complete
canonical coordinate presentation. -/
theorem canonicalCoordinates_perm_unused_used {degree : Nat}
    (hdegree : degree ≤ linkIncidenceBound) :
    (canonicalLocalCoordinates degree).Perm
      (canonicalUnusedCoordinates degree ++
        canonicalUsedCoordinates degree) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change [0, 1, 2, 3, 4, 5, 6, 7].Perm
      [0, 1, 2, 3, 4, 5, 6, 7]
    exact List.Perm.refl _
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8].Perm
      [2, 3, 4, 5, 6, 7, 8, 0, 1]
    simpa using perm_four_blocks
      (A := [0, 1]) (B := []) (C := [])
      (D := [2, 3, 4, 5, 6, 7, 8])
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].Perm
      [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]
    simpa using perm_four_blocks
      (A := [0, 1, 2]) (B := []) (C := [])
      (D := [3, 4, 5, 6, 7, 8, 9])
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10].Perm
      [3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2]
    simpa using perm_four_blocks
      (A := [0, 1, 2]) (B := []) (C := [])
      (D := [3, 4, 5, 6, 7, 8, 9, 10])
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11].Perm
      [4, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 5]
    simpa using perm_four_blocks
      (A := [0, 1, 2, 3]) (B := [4]) (C := [5])
      (D := [6, 7, 8, 9, 10, 11])
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].Perm
      [5, 8, 9, 10, 11, 12, 0, 1, 2, 3, 4, 6, 7]
    simpa using perm_four_blocks
      (A := [0, 1, 2, 3, 4]) (B := [5]) (C := [6, 7])
      (D := [8, 9, 10, 11, 12])
  · change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13].Perm
      [6, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 7, 8, 9]
    simpa using perm_four_blocks
      (A := [0, 1, 2, 3, 4, 5]) (B := [6]) (C := [7, 8, 9])
      (D := [10, 11, 12, 13])

theorem canonicalUnusedUsed_nodup {degree : Nat}
    (hdegree : degree ≤ linkIncidenceBound) :
    (canonicalUnusedCoordinates degree ++
      canonicalUsedCoordinates degree).Nodup := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem unused_coordinate_shape {degree edge : Nat}
    (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUnusedCoordinates degree) :
    ¬ edge < degree ∧
      (edge - degree = 0 ∨
        (edge - degree ≠ 0 ∧ ¬ edge - degree + 3 ≤ degree)) := by
  cases degree with
  | zero =>
      constructor
      · omega
      · by_cases hzero : edge = 0
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, by omega⟩
  | succ d1 =>
      cases d1 with
      | zero =>
          rw [canonicalUnusedCoordinates] at hedge
          obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hedge
          have hjlt := List.mem_range.mp hj
          rw [← hedgeEq]
          exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
      | succ d2 =>
          cases d2 with
          | zero =>
              rw [canonicalUnusedCoordinates] at hedge
              obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hedge
              have hjlt := List.mem_range.mp hj
              rw [← hedgeEq]
              exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
          | succ d3 =>
              cases d3 with
              | zero =>
                  rw [canonicalUnusedCoordinates] at hedge
                  obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hedge
                  have hjlt := List.mem_range.mp hj
                  rw [← hedgeEq]
                  by_cases hzero : j = 0
                  · exact ⟨by omega, Or.inl (by omega)⟩
                  · exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
              | succ d4 =>
                  cases d4 with
                  | zero =>
                      rw [canonicalUnusedCoordinates] at hedge
                      rcases List.mem_cons.mp hedge with hedgeEq | hedgeTail
                      · rw [hedgeEq]
                        exact ⟨by omega, Or.inl (by omega)⟩
                      · obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hedgeTail
                        have hjlt := List.mem_range.mp hj
                        rw [← hedgeEq]
                        exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
                  | succ d5 =>
                      cases d5 with
                      | zero =>
                          rw [canonicalUnusedCoordinates] at hedge
                          rcases List.mem_cons.mp hedge with hedgeEq | hedgeTail
                          · rw [hedgeEq]
                            exact ⟨by omega, Or.inl (by omega)⟩
                          · obtain ⟨j, hj, hedgeEq⟩ := List.mem_map.mp hedgeTail
                            have hjlt := List.mem_range.mp hj
                            rw [← hedgeEq]
                            exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
                      | succ d6 =>
                          cases d6 with
                          | zero =>
                              rw [canonicalUnusedCoordinates] at hedge
                              rcases List.mem_cons.mp hedge with hedgeEq | hedgeTail
                              · rw [hedgeEq]
                                exact ⟨by omega, Or.inl (by omega)⟩
                              · obtain ⟨j, hj, hedgeEq⟩ :=
                                    List.mem_map.mp hedgeTail
                                have hjlt := List.mem_range.mp hj
                                rw [← hedgeEq]
                                exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
                          | succ beyond =>
                              unfold linkIncidenceBound at hdegree
                              omega

/-- Every complementary coordinate carries the exact normalized vacuum
packet; in particular, none of the unused positions is silently assigned an
all-ones carrier. -/
theorem canonicalUnusedCoordinate_is_vacuum {K degree edge : Nat}
    (P : CharacterPacket K) (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUnusedCoordinates degree) :
    canonicalLinkGraphPacket P degree edge =
      vacuumPacket (linkAuxiliaryCutoff K) := by
  obtain ⟨hphysical, hzero | ⟨hnonzero, hcarrier⟩⟩ :=
    unused_coordinate_shape hdegree hedge
  · unfold canonicalLinkGraphPacket
    rw [if_neg hphysical]
    simp only
    rw [if_pos hzero]
  · unfold canonicalLinkGraphPacket
    rw [if_neg hphysical]
    simp only
    rw [if_neg hnonzero, if_neg hcarrier]

def canonicalUsedVertexCartesianSum {K : Nat} (P : CharacterPacket K)
    (degree : Nat) : Q' :=
  vertexCartesianSum (canonicalUsedCoordinates degree)
    (fuseLabels degree (degree + 1) (List.range degree))
    (canonicalLinkGraphPacket P degree)

/-- **No reserved-coordinate multiplicity.**  The complete transported
canonical sum is exactly the Cartesian sum over only those identifiers that
the resolver reads. -/
theorem canonicalLinkVertexCartesianSum_eq_used {K degree : Nat}
    (P : CharacterPacket K) (hdegree : degree ≤ linkIncidenceBound) :
    canonicalLinkVertexCartesianSum P degree ≈
      canonicalUsedVertexCartesianSum P degree := by
  unfold canonicalLinkVertexCartesianSum canonicalUsedVertexCartesianSum
    vertexCartesianSum
  exact vertexCartesianSum_remove_vacuum_list
    (canonicalUnusedCoordinates degree)
    (canonicalLocalCoordinates degree)
    (canonicalUsedCoordinates degree)
    (fuseLabels degree (degree + 1) (List.range degree))
    (canonicalLinkGraphPacket P degree)
    (canonicalCoordinates_perm_unused_used hdegree)
    (canonicalUnusedUsed_nodup hdegree)
    (fun edge hedge =>
      canonicalUnusedCoordinate_is_vacuum P hdegree hedge)

end YMGap.Continuum.Z4CanonicalLinkUsedCoordinates

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalLinkUsedCoordinates.canonicalCoordinates_perm_unused_used
#print axioms YMGap.Continuum.Z4CanonicalLinkUsedCoordinates.canonicalUnusedUsed_nodup
#print axioms YMGap.Continuum.Z4CanonicalLinkUsedCoordinates.unused_coordinate_shape
#print axioms YMGap.Continuum.Z4CanonicalLinkUsedCoordinates.canonicalUnusedCoordinate_is_vacuum
#print axioms YMGap.Continuum.Z4CanonicalLinkUsedCoordinates.canonicalLinkVertexCartesianSum_eq_used
