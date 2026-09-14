/-
# A nonempty even-incidence Z4 link set has at least four links

Color vertices by coordinate-sum parity and orient every link from its
even endpoint to its odd endpoint. The orientation is injective; in
particular two geometric links cannot become parallel bipartite edges.
The general four-edge obstruction then applies to actual lattice links.
No connectedness or extracted cycle is needed.
-/

import YMGap.Continuum.EvenBipartiteEdgeMinimum
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.Z4EvenLinkMinimum

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.EvenBipartiteEdgeMinimum
open YMGap.Continuum.CayleyPruferInjection

def height (v : Z4Vertex) : Nat := v.1 + v.2.1 + v.2.2.1 + v.2.2.2

theorem height_addE (v : Z4Vertex) (d : Dir4) : height (addE v d) = height v + 1 := by
  rcases v with ⟨a,b,c,t⟩
  cases d <;> simp [height, addE] <;> omega

theorem base_ne_tip (e : Z4Link) : e.1 ≠ addE e.1 e.2 := by
  intro h
  have hh := congrArg height h
  rw [height_addE] at hh
  omega

def colored (e : Z4Link) : Z4Vertex × Z4Vertex :=
  if height e.1 % 2 = 0 then (e.1,addE e.1 e.2) else (addE e.1 e.2,e.1)

theorem colored_parities (e : Z4Link) :
    height (colored e).1 % 2 = 0 ∧ height (colored e).2 % 2 = 1 := by
  by_cases h : height e.1 % 2 = 0
  · simp only [colored, if_pos h, height_addE]
    exact ⟨h,by omega⟩
  · simp only [colored, if_neg h, height_addE]
    constructor <;> omega

private theorem addE_dir_injective (v : Z4Vertex) (d e : Dir4) (h : addE v d = addE v e) : d = e := by
  rcases v with ⟨a,b,c,t⟩
  cases d <;> cases e
  all_goals first | rfl | (exfalso; simp only [addE, Prod.mk.injEq] at h; omega)

theorem colored_injective {e f : Z4Link} (h : colored e = colored f) : e = f := by
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  by_cases he : height e.1 % 2 = 0 <;> by_cases hf : height f.1 % 2 = 0
  all_goals simp only [colored, he, hf, ↓reduceIte] at hl hr
  · exact Prod.ext hl (addE_dir_injective e.1 e.2 f.2 (by simpa only [← hl] using hr))
  · exfalso
    have ha := congrArg height hl
    have hb := congrArg height hr
    simp only [height_addE] at ha hb
    omega
  · exfalso
    have ha := congrArg height hl
    have hb := congrArg height hr
    simp only [height_addE] at ha hb
    omega
  · exact Prod.ext hr (addE_dir_injective e.1 e.2 f.2 (by simpa only [← hr] using hl))

def vertexDegree (v : Z4Vertex) : List Z4Link → Nat
  | [] => 0
  | e::es => (if e.1 = v then 1 else 0) + (if addE e.1 e.2 = v then 1 else 0) + vertexDegree v es

theorem degree_sum (v : Z4Vertex) : ∀ es : List Z4Link,
    leftDegree v (es.map colored) + rightDegree v (es.map colored) = vertexDegree v es
  | [] => rfl
  | e::es => by
    simp only [List.map_cons, leftDegree, rightDegree, vertexDegree]
    have ih := degree_sum v es
    by_cases h : height e.1 % 2 = 0
    · rw [show colored e = (e.1,addE e.1 e.2) from if_pos h]
      dsimp only
      omega
    · rw [show colored e = (addE e.1 e.2,e.1) from if_neg h]
      dsimp only
      omega

private theorem left_odd_zero (v : Z4Vertex) (hv : height v % 2 = 1) : ∀ es : List Z4Link,
    leftDegree v (es.map colored) = 0
  | [] => rfl
  | e::es => by
    have hn : (colored e).1 ≠ v := by
      intro h
      have hp := (colored_parities e).1
      rw [h, hv] at hp
      cases hp
    simp only [List.map_cons, leftDegree, if_neg hn, Nat.zero_add, left_odd_zero v hv es]

private theorem right_even_zero (v : Z4Vertex) (hv : height v % 2 = 0) : ∀ es : List Z4Link,
    rightDegree v (es.map colored) = 0
  | [] => rfl
  | e::es => by
    have hn : (colored e).2 ≠ v := by
      intro h
      have hp := (colored_parities e).2
      rw [h, hv] at hp
      cases hp
    simp only [List.map_cons, rightDegree, if_neg hn, Nat.zero_add, right_even_zero v hv es]

theorem minimum_four (es : List Z4Link) (hn : es.Nodup) (hne : es ≠ [])
    (he : ∀ v, vertexDegree v es % 2 = 0) : 4 ≤ es.length := by
  have hl (v : Z4Vertex) : leftDegree v (es.map colored) % 2 = 0 := by
    by_cases hv : height v % 2 = 0
    · have hs := degree_sum v es
      rw [right_even_zero v hv es, Nat.add_zero] at hs
      rw [hs]; exact he v
    · rw [left_odd_zero v (by omega) es]
  have hr (v : Z4Vertex) : rightDegree v (es.map colored) % 2 = 0 := by
    by_cases hv : height v % 2 = 0
    · rw [right_even_zero v hv es]
    · have hs := degree_sum v es
      rw [left_odd_zero v (by omega) es, Nat.zero_add] at hs
      rw [hs]; exact he v
  have hd := nodup_map_of_injOn colored es hn (fun _ _ _ _ => colored_injective)
  have hne' : es.map colored ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_map, List.length_nil] at hh
    cases es with
    | nil => exact hne rfl
    | cons _ _ => simp only [List.length_cons] at hh; omega
  simpa only [List.length_map] using EvenBipartiteEdgeMinimum.minimum_four (es.map colored) hd hne' hl hr

end YMGap.Continuum.Z4EvenLinkMinimum

#print axioms YMGap.Continuum.Z4EvenLinkMinimum.height_addE
#print axioms YMGap.Continuum.Z4EvenLinkMinimum.base_ne_tip
#print axioms YMGap.Continuum.Z4EvenLinkMinimum.colored_parities
#print axioms YMGap.Continuum.Z4EvenLinkMinimum.colored_injective
#print axioms YMGap.Continuum.Z4EvenLinkMinimum.degree_sum
#print axioms YMGap.Continuum.Z4EvenLinkMinimum.minimum_four
