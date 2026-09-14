/-
# Four plaquettes with even boundary incidence pair exactly

Distinct plaquettes share at most one edge. A face's four boundary edges
cannot all be covered by only three distinct other faces. Even incidence
therefore forces a repeated face, and cancellation forces the other pair.
The result preserves list occurrences and gives all three ordered pairings.
It uses no gauge, weight, spin or spatial-plane assumption.
-/

import YMGap.Continuum.Z4PlaquetteBoundaryRigidity

namespace YMGap.Continuum.Z4FourFaceClosedPairing

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity

theorem three_filter_cover (p q r : Z4Link → Bool) : ∀ xs : List Z4Link,
    (∀ x, x ∈ xs → p x=true ∨ q x=true ∨ r x=true) →
    xs.length ≤ (xs.filter p).length+(xs.filter q).length+(xs.filter r).length
  | [], _ => Nat.le_refl _
  | x::xs, hs => by
    have hh := hs x List.mem_cons_self
    have ih := three_filter_cover p q r xs (fun y hy => hs y (List.mem_cons_of_mem x hy))
    cases hp : p x <;> cases hq : q x <;> cases hr : r x
    all_goals simp only [hp,hq,hr,Bool.false_eq_true,or_false,false_or] at hh
    all_goals simp only [List.filter_cons,hp,hq,hr,Bool.false_eq_true,↓reduceIte,List.length_cons]
    all_goals omega

theorem first_face_repeated (a b c d : Z4Plaq)
    (hp : ∀ link, faceIncidenceCount link [a,b,c,d]%2=0) : a=b ∨ a=c ∨ a=d := by
  letI : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))
  by_cases hab : a=b
  · exact Or.inl hab
  by_cases hac : a=c
  · exact Or.inr (Or.inl hac)
  by_cases had : a=d
  · exact Or.inr (Or.inr had)
  have hc := three_filter_cover (fun link => decide (link ∈ edgesOf b))
    (fun link => decide (link ∈ edgesOf c)) (fun link => decide (link ∈ edgesOf d))
    (edgesOf a) (by
      intro link hl
      have hh := hp link
      simp only [faceIncidenceCount,if_pos hl,Nat.add_zero] at hh
      by_cases hb : link ∈ edgesOf b
      · exact Or.inl (decide_eq_true hb)
      by_cases hc : link ∈ edgesOf c
      · exact Or.inr (Or.inl (decide_eq_true hc))
      by_cases hd : link ∈ edgesOf d
      · exact Or.inr (Or.inr (decide_eq_true hd))
      simp only [if_neg hb,if_neg hc,if_neg hd] at hh
      contradiction)
  have hb := distinct_boundary_overlap_le_one a b hab
  have hcc := distinct_boundary_overlap_le_one a c hac
  have hd := distinct_boundary_overlap_le_one a d had
  change 4 ≤ _ at hc
  omega

theorem closed_four_pairing (a b c d : Z4Plaq)
    (hp : ∀ link, faceIncidenceCount link [a,b,c,d]%2=0) :
    (a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  rcases first_face_repeated a b c d hp with hab | hac | had
  · refine Or.inl ⟨hab,boundary_subset_eq c d ?_⟩
    intro link hl
    have hh := hp link
    rw [hab] at hh
    by_cases hd : link ∈ edgesOf d
    · exact hd
    · simp only [faceIncidenceCount,if_pos hl,if_neg hd,Nat.add_zero] at hh
      omega
  · refine Or.inr (Or.inl ⟨hac,boundary_subset_eq b d ?_⟩)
    intro link hl
    have hh := hp link
    rw [hac] at hh
    by_cases hd : link ∈ edgesOf d
    · exact hd
    · simp only [faceIncidenceCount,if_pos hl,if_neg hd,Nat.add_zero] at hh
      omega
  · refine Or.inr (Or.inr ⟨had,boundary_subset_eq b c ?_⟩)
    intro link hl
    have hh := hp link
    rw [had] at hh
    by_cases hc : link ∈ edgesOf c
    · exact hc
    · simp only [faceIncidenceCount,if_pos hl,if_neg hc,Nat.add_zero] at hh
      omega

end YMGap.Continuum.Z4FourFaceClosedPairing

#print axioms YMGap.Continuum.Z4FourFaceClosedPairing.three_filter_cover
#print axioms YMGap.Continuum.Z4FourFaceClosedPairing.first_face_repeated
#print axioms YMGap.Continuum.Z4FourFaceClosedPairing.closed_four_pairing
