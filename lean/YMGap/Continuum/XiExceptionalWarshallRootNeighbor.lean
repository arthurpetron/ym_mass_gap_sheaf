/-
# Canonical Warshall paths use only one root neighbor

The constructive `warshallSound` algorithm prefers a path avoiding the next
listed pivot whenever one exists.  Consequently, when the distinguished root
is absent from the intermediate list, its canonical sound path cannot pass
through two vertices joined directly from that root: the second would give a
shortcut contradicting the branch that introduced the first.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary

namespace YMGap.Continuum.XiExceptionalWarshallRootNeighbor

open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction

private theorem boolRec_true {C : Type} (b : Bool)
    (f : b = false → C) (t : b = true → C) (p : b = b)
    (hb : b = true) :
    (@Bool.casesOn (fun u => b = u → C) b f t) p = t hb := by
  cases b with
  | false => cases hb
  | true => congr

private theorem boolRec_false {C : Type} (b : Bool)
    (f : b = false → C) (t : b = true → C) (p : b = b)
    (hb : b = false) :
    (@Bool.casesOn (fun u => b = u → C) b f t) p = f hb := by
  cases b with
  | false => congr
  | true => cases hb

private theorem boolRec'_true {C : Type} (b : Bool)
    (f : b = false → C) (t : b = true → C) (p : b = b)
    (hb : b = true) :
    (@Bool.rec (fun u => b = u → C) f t b) p = t hb := by
  cases b with
  | false => cases hb
  | true => congr

private theorem eqRec_eqProof {α C : Type} {a b c : α}
    (f : a = b → C) (h : b = c) (p : a = c) :
    @Eq.rec α b (fun z _ => a = z → C) f c h p =
      f (p.trans h.symm) := by
  cases h
  rfl

theorem warshallSound_direct {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (k : α) (ks : List α) (x y : α)
    (h : warshall edge (k :: ks) x y = true)
    (hdirect : warshall edge ks x y = true) :
    warshallSound edge (k :: ks) x y h =
      warshallSound edge ks x y hdirect := by
  rw [warshallSound.eq_2]
  rw [boolRec_true _ _ _ _ hdirect]
  simp only [eqRec_eqProof]

theorem warshallSound_nil_ne {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (x y : α)
    (h : warshall edge [] x y = true) (hne : x ≠ y) :
    ∃ he : edge x y = true,
      warshallSound edge [] x y h = DWalk.edge he := by
  rw [warshallSound.eq_1]
  have hb : decide (x = y) = false := decide_eq_false hne
  rw [boolRec_false _ _ _ _ hb]
  simp only [eqRec_eqProof]
  let he : edge x y = true := by simpa [warshall, hb] using h
  refine ⟨he, ?_⟩
  congr
  trivial

theorem warshallSound_nil_eq {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (x : α)
    (h : warshall edge [] x x = true) :
    warshallSound edge [] x x h = DWalk.refl x := by
  rw [warshallSound.eq_1]
  have hb : decide (x = x) = true := decide_eq_true rfl
  rw [boolRec_true _ _ _ _ hb]
  simp only [eqRec_eqProof]

theorem warshallSound_via {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (k : α) (ks : List α) (x y : α)
    (h : warshall edge (k :: ks) x y = true)
    (hdirect : warshall edge ks x y = false)
    (hxk : warshall edge ks x k = true)
    (hky : warshall edge ks k y = true) :
    warshallSound edge (k :: ks) x y h =
      DWalk.trans (warshallSound edge ks x k hxk)
        (warshallSound edge ks k y hky) := by
  rw [warshallSound.eq_2]
  rw [boolRec_false _ _ _ _ hdirect]
  simp only [eqRec_eqProof]
  rw [boolRec'_true _ _ _ _ hxk]
  rw [boolRec'_true _ _ _ _ hky]

def canonicalWarshallWalk {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (U : List α) (x y : α)
    (h : warshall edge U x y = true) : CWalk edge x y :=
  CWalk.ofDWalk (warshallSound edge U x y h)

theorem canonicalWarshallWalk_direct {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (k : α) (ks : List α) (x y : α)
    (h : warshall edge (k :: ks) x y = true)
    (hdirect : warshall edge ks x y = true) :
    canonicalWarshallWalk edge (k :: ks) x y h =
      canonicalWarshallWalk edge ks x y hdirect := by
  unfold canonicalWarshallWalk
  rw [warshallSound_direct edge k ks x y h hdirect]

theorem canonicalWarshallWalk_via {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (k : α) (ks : List α) (x y : α)
    (h : warshall edge (k :: ks) x y = true)
    (hdirect : warshall edge ks x y = false)
    (hxk : warshall edge ks x k = true)
    (hky : warshall edge ks k y = true) :
    canonicalWarshallWalk edge (k :: ks) x y h =
      (canonicalWarshallWalk edge ks x k hxk).append
        (canonicalWarshallWalk edge ks k y hky) := by
  unfold canonicalWarshallWalk
  rw [warshallSound_via edge k ks x y h hdirect hxk hky]
  rfl

theorem CWalk.mem_append_elim {α : Type} {edge : α → α → Bool} :
    ∀ {x y z : α} (p : CWalk edge x y) (q : CWalk edge y z) (v : α),
      v ∈ (p.append q).vertices → v ∈ p.vertices ∨ v ∈ q.vertices
  | _, _, _, .single _, q, v, hv => Or.inr hv
  | _, _, _, .cons _ rest, q, v, hv => by
      rcases List.mem_cons.mp hv with hv | hv
      · exact Or.inl (List.mem_cons.mpr (Or.inl hv))
      · rcases CWalk.mem_append_elim rest q v hv with hp | hq
        · exact Or.inl (List.mem_cons_of_mem _ hp)
        · exact Or.inr hq

theorem CWalk.end_mem_vertices {α : Type} {edge : α → α → Bool} :
    ∀ {x y : α} (p : CWalk edge x y), y ∈ p.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest => List.mem_cons_of_mem _ (end_mem_vertices rest)

theorem canonicalWarshallWalk_vertices_subset
    {α : Type} [DecidableEq α] (edge : α → α → Bool) :
    ∀ (U : List α) (x y : α) (h : warshall edge U x y = true)
      (v : α), v ∈ (canonicalWarshallWalk edge U x y h).vertices →
        v = x ∨ v = y ∨ v ∈ U
  | [], x, y, h, v, hv => by
      by_cases hxy : x = y
      · subst y
        unfold canonicalWarshallWalk at hv
        rw [warshallSound_nil_eq edge x h] at hv
        simpa only [CWalk.ofDWalk, CWalk.vertices,
          List.mem_singleton] using Or.inl hv
      · obtain ⟨he, hs⟩ := warshallSound_nil_ne edge x y h hxy
        unfold canonicalWarshallWalk at hv
        rw [hs] at hv
        simp [CWalk.ofDWalk, CWalk.vertices] at hv
        rcases hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (Or.inl hv)
  | k :: ks, x, y, h, v, hv => by
      cases hdirect : warshall edge ks x y with
      | true =>
          rw [canonicalWarshallWalk_direct edge k ks x y h hdirect] at hv
          rcases canonicalWarshallWalk_vertices_subset
              edge ks x y hdirect v hv with hv | hv | hv
          · exact Or.inl hv
          · exact Or.inr (Or.inl hv)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem k hv))
      | false =>
          cases hxk : warshall edge ks x k with
          | false => simp [warshall, hdirect, hxk] at h
          | true =>
              cases hky : warshall edge ks k y with
              | false => simp [warshall, hdirect, hxk, hky] at h
              | true =>
                  rw [canonicalWarshallWalk_via
                    edge k ks x y h hdirect hxk hky] at hv
                  rcases CWalk.mem_append_elim _ _ v hv with hp | hq
                  · rcases canonicalWarshallWalk_vertices_subset
                        edge ks x k hxk v hp with hv | hv | hv
                    · exact Or.inl hv
                    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl hv)))
                    · exact Or.inr (Or.inr (List.mem_cons_of_mem k hv))
                  · rcases canonicalWarshallWalk_vertices_subset
                        edge ks k y hky v hq with hv | hv | hv
                    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl hv)))
                    · exact Or.inr (Or.inl hv)
                    · exact Or.inr (Or.inr (List.mem_cons_of_mem k hv))

theorem canonicalWarshallWalk_vertex_to_end
    {α : Type} [DecidableEq α] (edge : α → α → Bool) :
    ∀ (U : List α) (x y : α) (h : warshall edge U x y = true)
      (v : α), v ∈ (canonicalWarshallWalk edge U x y h).vertices →
        warshall edge U v y = true
  | [], x, y, h, v, hv => by
      by_cases hxy : x = y
      · subst y
        unfold canonicalWarshallWalk at hv
        rw [warshallSound_nil_eq edge x h] at hv
        simp only [CWalk.ofDWalk, CWalk.vertices,
          List.mem_singleton] at hv
        subst v
        exact warshall_refl edge [] x
      · obtain ⟨he, hs⟩ := warshallSound_nil_ne edge x y h hxy
        unfold canonicalWarshallWalk at hv
        rw [hs] at hv
        simp [CWalk.ofDWalk, CWalk.vertices] at hv
        rcases hv with hv | hv
        · subst v
          exact h
        · subst v
          exact warshall_refl edge [] y
  | k :: ks, x, y, h, v, hv => by
      cases hdirect : warshall edge ks x y with
      | true =>
          rw [canonicalWarshallWalk_direct edge k ks x y h hdirect] at hv
          have ih := canonicalWarshallWalk_vertex_to_end
            edge ks x y hdirect v hv
          unfold warshall
          exact (Bool.or_eq_true _ _).mpr (Or.inl ih)
      | false =>
          cases hxk : warshall edge ks x k with
          | false => simp [warshall, hdirect, hxk] at h
          | true =>
              cases hky : warshall edge ks k y with
              | false => simp [warshall, hdirect, hxk, hky] at h
              | true =>
                  rw [canonicalWarshallWalk_via
                    edge k ks x y h hdirect hxk hky] at hv
                  rcases CWalk.mem_append_elim _ _ v hv with hp | hq
                  · have hvk := canonicalWarshallWalk_vertex_to_end
                      edge ks x k hxk v hp
                    unfold warshall
                    exact (Bool.or_eq_true _ _).mpr (Or.inr
                      ((Bool.and_eq_true _ _).mpr ⟨hvk, hky⟩))
                  · have hvy := canonicalWarshallWalk_vertex_to_end
                      edge ks k y hky v hq
                    unfold warshall
                    exact (Bool.or_eq_true _ _).mpr (Or.inl hvy)

theorem canonicalWarshallWalk_root_neighbor_unique
    {α : Type} [DecidableEq α]
    (edge : α → α → Bool) (root : α) (hloop : edge root root = false) :
    ∀ (U : List α), root ∉ U → ∀ (y : α), root ≠ y →
      ∀ (h : warshall edge U root y = true) (a b : α),
        a ∈ (canonicalWarshallWalk edge U root y h).vertices →
        b ∈ (canonicalWarshallWalk edge U root y h).vertices →
        edge root a = true → edge root b = true → a = b
  | [], _, y, hry, h, a, b, ha, hb, hea, heb => by
      obtain ⟨he, hs⟩ := warshallSound_nil_ne edge root y h hry
      unfold canonicalWarshallWalk at ha hb
      rw [hs] at ha hb
      simp [CWalk.ofDWalk, CWalk.vertices] at ha hb
      rcases ha with rfl | rfl
      · rw [hloop] at hea
        cases hea
      · rcases hb with rfl | rfl
        · rw [hloop] at heb
          cases heb
        · rfl
  | k :: ks, hroot, y, hry, h, a, b, ha, hb, hea, heb => by
      have hrk : root ≠ k := by
        intro e
        subst k
        exact hroot List.mem_cons_self
      have hrks : root ∉ ks := by
        intro hm
        exact hroot (List.mem_cons_of_mem k hm)
      cases hdirect : warshall edge ks root y with
      | true =>
          rw [canonicalWarshallWalk_direct
            edge k ks root y h hdirect] at ha hb
          exact canonicalWarshallWalk_root_neighbor_unique
            edge root hloop ks hrks y hry hdirect a b ha hb hea heb
      | false =>
          cases hxk : warshall edge ks root k with
          | false => simp [warshall, hdirect, hxk] at h
          | true =>
              cases hky : warshall edge ks k y with
              | false => simp [warshall, hdirect, hxk, hky] at h
              | true =>
                  let p := canonicalWarshallWalk edge ks root k hxk
                  let q := canonicalWarshallWalk edge ks k y hky
                  have hsplit :
                      canonicalWarshallWalk edge (k :: ks) root y h =
                        p.append q :=
                    canonicalWarshallWalk_via
                      edge k ks root y h hdirect hxk hky
                  rw [hsplit] at ha hb
                  have q_neighbor_eq_k : ∀ v, v ∈ q.vertices →
                      edge root v = true → v = k := by
                    intro v hv hev
                    rcases canonicalWarshallWalk_vertices_subset
                        edge ks k y hky v hv with hv | hv | hmem
                    · exact hv
                    · subst v
                      have hd : warshall edge ks root y = true :=
                        warshall_edge edge hev ks
                      rw [hdirect] at hd
                      cases hd
                    · have hvy : warshall edge ks v y = true :=
                        canonicalWarshallWalk_vertex_to_end
                          edge ks k y hky v hv
                      have hrv : warshall edge ks root v = true :=
                        warshall_edge edge hev ks
                      have hd := warshall_trans_of_mem edge ks root v y
                        hmem hrv hvy
                      rw [hdirect] at hd
                      cases hd
                  rcases CWalk.mem_append_elim p q a ha with hap | haq <;>
                    rcases CWalk.mem_append_elim p q b hb with hbp | hbq
                  · exact canonicalWarshallWalk_root_neighbor_unique
                      edge root hloop ks hrks k hrk hxk
                      a b hap hbp hea heb
                  · have eb : b = k := q_neighbor_eq_k b hbq heb
                    have hkmem : k ∈ p.vertices := CWalk.end_mem_vertices p
                    have hek : edge root k = true := eb ▸ heb
                    have ea := canonicalWarshallWalk_root_neighbor_unique
                      edge root hloop ks hrks k hrk hxk
                      a k hap hkmem hea hek
                    exact ea.trans eb.symm
                  · have ea : a = k := q_neighbor_eq_k a haq hea
                    have hkmem : k ∈ p.vertices := CWalk.end_mem_vertices p
                    have hek : edge root k = true := ea ▸ hea
                    have eb := canonicalWarshallWalk_root_neighbor_unique
                      edge root hloop ks hrks k hrk hxk
                      k b hkmem hbp hek heb
                    exact ea.trans eb
                  · exact (q_neighbor_eq_k a haq hea).trans
                      (q_neighbor_eq_k b hbq heb).symm

#print axioms warshallSound_direct
#print axioms warshallSound_nil_ne
#print axioms warshallSound_nil_eq
#print axioms warshallSound_via
#print axioms canonicalWarshallWalk_root_neighbor_unique

end YMGap.Continuum.XiExceptionalWarshallRootNeighbor
