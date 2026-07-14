import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

/-!
# Volume-independent geometry of the elementary cube surface

The heat-kernel box witness uses the six plaquettes bounding the unit cube in
the first three coordinate directions.  This file separates that local
surface from the size-two enumeration.  All six faces occur in every box of
size at least two.  Expanding their 24 boundary occurrences and pairing equal
link indicators proves constructively that every lattice link has even
multiplicity in the closed surface.

The next volume-compatibility step is bookkeeping: relate this geometric
occurrence counter to `enumerate`, `incidentPlaqIds`, and the prefix-parity
labels in each trivalent fusion chain.  No thermodynamic-limit claim is made.
-/

namespace YMGap.Continuum.Z4UnitCubeSurfaceGeometry

set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

theorem unitCubeSurface_length : unitCubeSurface.length = 6 := by
  rfl

theorem unitCubeSurface_nodup : unitCubeSurface.Nodup := by
  simp [unitCubeSurface]

/-- All six cube faces occur in every box stage `n ≥ 2`. -/
theorem unitCubeSurface_mem_box {n : Nat} (hn : 2 ≤ n)
    {p : Z4Plaq} (hp : p ∈ unitCubeSurface) :
    p ∈ boxPlaquettes n := by
  apply (mem_boxPlaquettes p n).2
  simp only [unitCubeSurface, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp
  all_goals exact ⟨by omega, by omega, by omega, by omega⟩

/-- A structural link-occurrence counter, used instead of a classical
permutation or multiset quotient. -/
def occurrenceCount (ell : Z4Link) : List Z4Link → Nat
  | [] => 0
  | edge :: rest =>
      (if edge = ell then 1 else 0) + occurrenceCount ell rest

theorem occurrenceCount_append (ell : Z4Link) : ∀ xs ys,
    occurrenceCount ell (xs ++ ys) =
      occurrenceCount ell xs + occurrenceCount ell ys
  | [], _ => by simp [occurrenceCount]
  | edge :: rest, ys => by
      simp only [List.cons_append, occurrenceCount]
      rw [occurrenceCount_append ell rest ys]
      omega

/-- Multiplicity of a lattice link in the complete cube boundary list. -/
def unitCubeBoundaryMultiplicity (ell : Z4Link) : Nat :=
  occurrenceCount ell (unitCubeSurface.flatMap edgesOf)

/-- The closed-surface law: all 24 explicit boundary occurrences pair, so
every lattice link occurs an even number of times. -/
theorem unitCubeBoundaryMultiplicity_even (ell : Z4Link) :
    unitCubeBoundaryMultiplicity ell % 2 = 0 := by
  simp [unitCubeBoundaryMultiplicity, unitCubeSurface, edgesOf, dirsOf,
    addE, occurrenceCount]
  omega

#print axioms unitCubeSurface_length
#print axioms unitCubeSurface_nodup
#print axioms unitCubeSurface_mem_box
#print axioms occurrenceCount_append
#print axioms unitCubeBoundaryMultiplicity_even

end YMGap.Continuum.Z4UnitCubeSurfaceGeometry
