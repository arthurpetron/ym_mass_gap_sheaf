import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

namespace ScratchZ4UnitCubeGeometry

set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

theorem unitCubeSurface_length : unitCubeSurface.length = 6 := by decide

theorem unitCubeSurface_nodup : unitCubeSurface.Nodup := by decide

theorem unitCubeSurface_mem_box {n : Nat} (hn : 2 ≤ n)
    {p : Z4Plaq} (hp : p ∈ unitCubeSurface) :
    p ∈ boxPlaquettes n := by
  apply (mem_boxPlaquettes p n).2
  simp only [unitCubeSurface, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Prod.fst, Prod.snd]
  all_goals exact ⟨by omega, by omega, by omega, by omega⟩

def unitCubeIncidentFaces (ell : Z4Link) : List Z4Plaq :=
  unitCubeSurface.filter fun p => decide (ell ∈ edgesOf p)

def occurrenceCount (ell : Z4Link) : List Z4Link → Nat
  | [] => 0
  | edge :: rest => (if edge = ell then 1 else 0) + occurrenceCount ell rest

def unitCubeBoundaryMultiplicity (ell : Z4Link) : Nat :=
  occurrenceCount ell (unitCubeSurface.flatMap edgesOf)

theorem occurrenceCount_append (ell : Z4Link) : ∀ xs ys,
    occurrenceCount ell (xs ++ ys) =
      occurrenceCount ell xs + occurrenceCount ell ys
  | [], _ => by simp [occurrenceCount]
  | edge :: rest, ys => by
      simp only [List.cons_append, occurrenceCount]
      rw [occurrenceCount_append ell rest ys]
      omega

theorem unitCubeBoundaryMultiplicity_even (ell : Z4Link) :
    unitCubeBoundaryMultiplicity ell % 2 = 0 := by
  simp [unitCubeBoundaryMultiplicity, unitCubeSurface, edgesOf, dirsOf,
    addE, occurrenceCount]
  omega

theorem edgesOf_nodup (p : Z4Plaq) : (edgesOf p).Nodup := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have ha : a ≠ a + 1 := by omega
  have ha' : a + 1 ≠ a := by omega
  have hb : b ≠ b + 1 := by omega
  have hb' : b + 1 ≠ b := by omega
  have hc : c ≠ c + 1 := by omega
  have hc' : c + 1 ≠ c := by omega
  have hd : d ≠ d + 1 := by omega
  have hd' : d + 1 ≠ d := by omega
  have h01 : Dir4.x0 ≠ Dir4.x1 := by decide
  have h10 : Dir4.x1 ≠ Dir4.x0 := by decide
  have h02 : Dir4.x0 ≠ Dir4.x2 := by decide
  have h20 : Dir4.x2 ≠ Dir4.x0 := by decide
  have h03 : Dir4.x0 ≠ Dir4.x3 := by decide
  have h30 : Dir4.x3 ≠ Dir4.x0 := by decide
  have h12 : Dir4.x1 ≠ Dir4.x2 := by decide
  have h21 : Dir4.x2 ≠ Dir4.x1 := by decide
  have h13 : Dir4.x1 ≠ Dir4.x3 := by decide
  have h31 : Dir4.x3 ≠ Dir4.x1 := by decide
  have h23 : Dir4.x2 ≠ Dir4.x3 := by decide
  have h32 : Dir4.x3 ≠ Dir4.x2 := by decide
  cases plane <;>
    simp only [edgesOf, dirsOf, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, Prod.mk.injEq, addE,
      ha, ha', hb, hb', hc, hc', hd, hd',
      h01, h10, h02, h20, h03, h30, h12, h21, h13, h31, h23, h32,
      true_and, and_true, false_and, and_false, not_false_eq_true,
      List.nodup_nil]

theorem occurrenceCount_eq_zero_of_not_mem (ell : Z4Link) :
    ∀ xs : List Z4Link, ell ∉ xs → occurrenceCount ell xs = 0
  | [], _ => rfl
  | edge :: rest, hnot => by
      have hedge : edge ≠ ell := by
        intro h
        apply hnot
        subst edge
        exact List.mem_cons_self
      have hrest : ell ∉ rest := by
        intro h
        exact hnot (List.mem_cons_of_mem edge h)
      simp only [occurrenceCount, if_neg hedge,
        Nat.zero_add, occurrenceCount_eq_zero_of_not_mem ell rest hrest]

theorem occurrenceCount_eq_one_of_mem_nodup (ell : Z4Link) :
    ∀ xs : List Z4Link, xs.Nodup → ell ∈ xs →
      occurrenceCount ell xs = 1
  | [], _, hmem => by cases hmem
  | edge :: rest, hnodup, hmem => by
      have hfresh := (List.nodup_cons.mp hnodup).1
      have hrestNodup := (List.nodup_cons.mp hnodup).2
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · subst edge
        simp only [occurrenceCount, if_pos rfl]
        rw [occurrenceCount_eq_zero_of_not_mem ell rest hfresh]
        rfl
      · have hne : edge ≠ ell := by
          intro h
          subst edge
          exact hfresh hrest
        simp only [occurrenceCount, if_neg hne, Nat.zero_add]
        exact occurrenceCount_eq_one_of_mem_nodup ell rest hrestNodup hrest

theorem occurrenceCount_edgesOf (ell : Z4Link) (p : Z4Plaq) :
    occurrenceCount ell (edgesOf p) =
      if ell ∈ edgesOf p then 1 else 0 := by
  by_cases hmem : ell ∈ edgesOf p
  · rw [if_pos hmem]
    exact occurrenceCount_eq_one_of_mem_nodup ell (edgesOf p)
      (edgesOf_nodup p) hmem
  · rw [if_neg hmem]
    exact occurrenceCount_eq_zero_of_not_mem ell (edgesOf p) hmem

def faceIncidenceCount (ell : Z4Link) : List Z4Plaq → Nat
  | [] => 0
  | p :: rest =>
      (if ell ∈ edgesOf p then 1 else 0) + faceIncidenceCount ell rest

theorem occurrenceCount_flatMap_edgesOf (ell : Z4Link) :
    ∀ faces : List Z4Plaq,
    occurrenceCount ell (faces.flatMap edgesOf) =
      faceIncidenceCount ell faces
  | [] => rfl
  | p :: rest => by
      rw [List.flatMap_cons, occurrenceCount_append,
        occurrenceCount_edgesOf, occurrenceCount_flatMap_edgesOf]
      rfl

theorem unitCubeFaceIncidenceCount_even (ell : Z4Link) :
    faceIncidenceCount ell unitCubeSurface % 2 = 0 := by
  rw [← occurrenceCount_flatMap_edgesOf]
  exact unitCubeBoundaryMultiplicity_even ell

#print axioms unitCubeSurface_length
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.mem_boxPlaquettes
#print axioms unitCubeSurface_nodup
#print axioms unitCubeSurface_mem_box
#print axioms unitCubeBoundaryMultiplicity_even
#print axioms edgesOf_nodup
#print axioms occurrenceCount_edgesOf
#print axioms occurrenceCount_flatMap_edgesOf
#print axioms unitCubeFaceIncidenceCount_even

end ScratchZ4UnitCubeGeometry
