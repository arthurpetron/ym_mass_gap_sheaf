/-
# Four faces per nonempty temporal cut without degree-one links

The original temporal-link incidence equals the cut graph degree. The
lattice bipartition and absence of duplicate edges therefore turn the
no-singleton condition into a four-face minimum. Evenness is not used.
Cut nonemptiness remains an explicit hypothesis, including for replicas.
-/

import YMGap.Continuum.LeaflessBipartiteEdgeMinimum
import YMGap.Continuum.Z4TemporalCutParityMinimum

namespace YMGap.Continuum.Z4LeaflessTemporalCutMinimum

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.EvenBipartiteEdgeMinimum
open YMGap.Continuum.Z4EvenLinkMinimum
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity

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

theorem link_minimum_four (es : List Z4Link) (hn : es.Nodup) (hne : es ≠ [])
    (he : ∀ v, vertexDegree v es ≠ 1) : 4 ≤ es.length := by
  have hl (v : Z4Vertex) : leftDegree v (es.map colored) ≠ 1 := by
    by_cases hv : height v % 2 = 0
    · have hs := degree_sum v es
      rw [right_even_zero v hv es, Nat.add_zero] at hs
      rw [hs]; exact he v
    · rw [left_odd_zero v (by omega) es]; exact Nat.zero_ne_one
  have hr (v : Z4Vertex) : rightDegree v (es.map colored) ≠ 1 := by
    by_cases hv : height v % 2 = 0
    · rw [right_even_zero v hv es]; exact Nat.zero_ne_one
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
  simpa only [List.length_map] using LeaflessBipartiteEdgeMinimum.minimum_four (es.map colored) hd hne' hl hr

theorem degree_outside (v : Z4Vertex) (time : Nat) (hv : v.2.2.2 ≠ time) :
    ∀ faces : List Z4Plaq, vertexDegree v (cut time faces) = 0
  | [] => rfl
  | f::fs => by
    cases h : crosses time f with
    | false => simpa only [cut, List.filter_cons, h] using degree_outside v time hv fs
    | true =>
      have ht := (of_decide_eq_true h).2
      have hp := (of_decide_eq_true h).1
      have hbase : (cutEdge f).1 ≠ v := by
        intro he
        exact hv ((congrArg (fun x : Z4Vertex => x.2.2.2) he).symm.trans ht)
      have htip : addE (cutEdge f).1 (cutEdge f).2 ≠ v := by
        intro he
        have htime := congrArg (fun x : Z4Vertex => x.2.2.2) he
        rcases f with ⟨⟨a,b,c,t⟩,p⟩
        cases p <;> simp only [cutEdge, dirsOf, addE] at hp htime
        all_goals first | contradiction | exact hv (htime.symm.trans ht)
      simp only [cut, List.filter_cons, h, ↓reduceIte, List.map_cons, vertexDegree,
        if_neg hbase, if_neg htip, Nat.zero_add]
      exact degree_outside v time hv fs

theorem cut_minimum_four (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup)
    (he : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) faces ≠ 1)
    (hne : cut time faces ≠ []) : 4 ≤ (cut time faces).length := by
  apply link_minimum_four _ (cut_nodup time faces hn) hne
  intro v
  by_cases ht : v.2.2.2 = time
  · rw [← ht, degree_pin]; exact he v
  · rw [degree_outside v time ht faces]; exact Nat.zero_ne_one

/-- Coverage can alternate replicas: neither replica is assumed to cross every cut. -/
theorem pair_cut_minimum_four (time : Nat) (left right : List Z4Plaq)
    (hl : left.Nodup) (hr : right.Nodup)
    (el : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) left ≠ 1)
    (er : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) right ≠ 1)
    (hne : cut time left ≠ [] ∨ cut time right ≠ []) :
    4 ≤ (cut time left).length + (cut time right).length := by
  cases hne with
  | inl h => have hb := cut_minimum_four time left hl el h; omega
  | inr h => have hb := cut_minimum_four time right hr er h; omega

theorem pair_three_cut_minimum_twelve (time : Nat) (left right : List Z4Plaq)
    (hl : left.Nodup) (hr : right.Nodup)
    (el : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) left ≠ 1)
    (er : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) right ≠ 1)
    (h0 : cut time left ≠ [] ∨ cut time right ≠ [])
    (h1 : cut (time+1) left ≠ [] ∨ cut (time+1) right ≠ [])
    (h2 : cut (time+2) left ≠ [] ∨ cut (time+2) right ≠ []) :
    12 ≤ left.length + right.length := by
  have b0 := pair_cut_minimum_four time left right hl hr el er h0
  have b1 := pair_cut_minimum_four (time+1) left right hl hr el er h1
  have b2 := pair_cut_minimum_four (time+2) left right hl hr el er h2
  have sl := three_cut_size_le time left
  have sr := three_cut_size_le time right
  omega

end YMGap.Continuum.Z4LeaflessTemporalCutMinimum

#print axioms YMGap.Continuum.Z4LeaflessTemporalCutMinimum.link_minimum_four
#print axioms YMGap.Continuum.Z4LeaflessTemporalCutMinimum.degree_outside
#print axioms YMGap.Continuum.Z4LeaflessTemporalCutMinimum.cut_minimum_four
#print axioms YMGap.Continuum.Z4LeaflessTemporalCutMinimum.pair_cut_minimum_four
#print axioms YMGap.Continuum.Z4LeaflessTemporalCutMinimum.pair_three_cut_minimum_twelve
