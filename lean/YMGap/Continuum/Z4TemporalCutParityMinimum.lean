/-
# Four faces per nonempty even temporal cut

A temporal plaquette crossing time t supplies its lower spatial edge.
At each vertex on that cut the graph degree is EXACTLY the incidence
count at the corresponding original temporal link. Hence even temporal
link incidence gives an even spatial graph. Distinct faces give distinct
edges, so a nonempty cut has at least four plaquettes.

Three nonempty consecutive cuts therefore require at least twelve faces.
Nonemptiness is explicit; it is not asserted for every connected replica
selection. Nor is a Haar sign or response lower bound inferred from area.
-/

import YMGap.Continuum.Z4EvenLinkMinimum
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.Z4TemporalCutParityMinimum

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4EvenLinkMinimum

def crosses (time : Nat) (face : Z4Plaq) : Bool :=
  decide ((dirsOf face.2).2 = Dir4.x3 ∧ face.1.2.2.2 = time)

def cutEdge (face : Z4Plaq) : Z4Link := (face.1,(dirsOf face.2).1)

def cut (time : Nat) (faces : List Z4Plaq) : List Z4Link :=
  (faces.filter (crosses time)).map cutEdge

theorem cutEdge_injective {time : Nat} {f g : Z4Plaq}
    (hf : crosses time f = true) (hg : crosses time g = true) (h : cutEdge f = cutEdge g) : f = g := by
  have hfp := (of_decide_eq_true hf).1
  have hgp := (of_decide_eq_true hg).1
  have hb := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  rcases f with ⟨v,p⟩
  rcases g with ⟨w,q⟩
  cases p <;> cases q <;> simp_all [cutEdge, dirsOf]

theorem cut_nodup (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup) : (cut time faces).Nodup :=
  nodup_map_of_injOn cutEdge _ (hn.filter _) (fun _ hf _ hg =>
    cutEdge_injective (List.mem_filter.mp hf).2 (List.mem_filter.mp hg).2)

private theorem face_degree_pin (v : Z4Vertex) (face : Z4Plaq) :
    (if crosses v.2.2.2 face then
      (if (cutEdge face).1 = v then 1 else 0) +
      (if addE (cutEdge face).1 (cutEdge face).2 = v then 1 else 0) else 0) =
      (if (v,Dir4.x3) ∈ edgesOf face then 1 else 0) := by
  rcases v with ⟨a,b,c,t⟩
  rcases face with ⟨⟨x,y,z,s⟩,p⟩
  have ha : a + 1 ≠ a := by omega
  have hb : b + 1 ≠ b := by omega
  have hc : c + 1 ≠ c := by omega
  cases p <;> simp [crosses, cutEdge, dirsOf, edgesOf, addE, -Nat.add_eq_left, -Nat.left_eq_add]
  all_goals by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hz : z = c <;> by_cases hs : s = t
  all_goals simp_all [eq_comm, -Nat.add_eq_left, -Nat.left_eq_add]

/-- The graph degree is the original vertical-link incidence, not a proxy. -/
theorem degree_pin (v : Z4Vertex) : ∀ faces : List Z4Plaq,
    vertexDegree v (cut v.2.2.2 faces) = faceIncidenceCount (v,Dir4.x3) faces
  | [] => rfl
  | f::fs => by
    have ih := degree_pin v fs
    have hp := face_degree_pin v f
    cases h : crosses v.2.2.2 f with
    | false =>
      simp only [cut, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte] at *
      simp only [faceIncidenceCount, ← hp, Nat.zero_add]
      exact ih
    | true =>
      simp only [cut, List.filter_cons, h, ↓reduceIte, List.map_cons, vertexDegree] at *
      rw [faceIncidenceCount, ← hp, ih]

private theorem degree_outside (v : Z4Vertex) (time : Nat) (hv : v.2.2.2 ≠ time) :
    ∀ faces : List Z4Plaq, vertexDegree v (cut time faces) = 0
  | [] => rfl
  | f::fs => by
    cases h : crosses time f with
    | false => simpa only [cut, List.filter_cons, h] using degree_outside v time hv fs
    | true =>
      have ht := (of_decide_eq_true h).2
      have hp := (of_decide_eq_true h).1
      have hbase : (cutEdge f).1 ≠ v := by intro he; exact hv ((congrArg (fun x : Z4Vertex => x.2.2.2) he).symm.trans ht)
      have htip : addE (cutEdge f).1 (cutEdge f).2 ≠ v := by
        intro he
        have htime := congrArg (fun x : Z4Vertex => x.2.2.2) he
        rcases f with ⟨⟨a,b,c,t⟩,p⟩
        cases p <;> simp only [cutEdge, dirsOf, addE] at hp htime
        all_goals first | contradiction | exact hv (htime.symm.trans ht)
      simp only [cut, List.filter_cons, h, ↓reduceIte, List.map_cons, vertexDegree, if_neg hbase, if_neg htip, Nat.zero_add]
      exact degree_outside v time hv fs

theorem cut_minimum_four (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup)
    (he : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) faces % 2 = 0)
    (hne : cut time faces ≠ []) : 4 ≤ (cut time faces).length := by
  apply Z4EvenLinkMinimum.minimum_four _ (cut_nodup time faces hn) hne
  intro v
  by_cases ht : v.2.2.2 = time
  · rw [← ht, degree_pin]; exact he v
  · rw [degree_outside v time ht faces]

theorem three_cut_size_le (time : Nat) : ∀ faces : List Z4Plaq,
    (cut time faces).length + (cut (time+1) faces).length + (cut (time+2) faces).length ≤ faces.length
  | [] => Nat.le_refl 0
  | f::fs => by
    have ih := three_cut_size_le time fs
    have hdis : ¬(crosses time f = true ∧ crosses (time+1) f = true) ∧
        ¬(crosses time f = true ∧ crosses (time+2) f = true) ∧
        ¬(crosses (time+1) f = true ∧ crosses (time+2) f = true) := by
      constructor
      · intro h; have h0 := (of_decide_eq_true h.1).2; have h1 := (of_decide_eq_true h.2).2; omega
      · constructor
        · intro h; have h0 := (of_decide_eq_true h.1).2; have h2 := (of_decide_eq_true h.2).2; omega
        · intro h; have h1 := (of_decide_eq_true h.1).2; have h2 := (of_decide_eq_true h.2).2; omega
    cases h0 : crosses time f <;> cases h1 : crosses (time+1) f <;> cases h2 : crosses (time+2) f
    all_goals simp_all only [cut, List.filter_cons, List.length_map, List.length_cons,
      Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte]
    all_goals omega

/-- Area bound with the nonempty-cut requirements visible, not assumed from a diagram. -/
theorem three_cut_minimum_twelve (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup)
    (he : ∀ v : Z4Vertex, faceIncidenceCount (v,Dir4.x3) faces % 2 = 0)
    (h0 : cut time faces ≠ []) (h1 : cut (time+1) faces ≠ []) (h2 : cut (time+2) faces ≠ []) :
    12 ≤ faces.length := by
  have b0 := cut_minimum_four time faces hn he h0
  have b1 := cut_minimum_four (time+1) faces hn he h1
  have b2 := cut_minimum_four (time+2) faces hn he h2
  have hs := three_cut_size_le time faces
  omega

end YMGap.Continuum.Z4TemporalCutParityMinimum

#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.cutEdge_injective
#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.cut_nodup
#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.degree_pin
#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.cut_minimum_four
#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.three_cut_size_le
#print axioms YMGap.Continuum.Z4TemporalCutParityMinimum.three_cut_minimum_twelve
