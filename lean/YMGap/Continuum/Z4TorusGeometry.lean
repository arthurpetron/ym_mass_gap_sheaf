/-
# Periodic four-dimensional torus geometry (C1 Milestone 1)

Companion to `audits/SCOPE-C1-SQUARE-BOX-DOUBLING-2026-10-06.md` §5 (Milestone 1).
ADDITIVE.  `Z4FiniteBoxExhaustion` builds corner-anchored FREE-boundary boxes;
this file builds the genuinely periodic torus `(ℤ/N)⁴` on the same vertex list.

All statements are for GENERAL `N` (no case enumeration, no large `decide`):

* `wrapSucc`/`wrapPred`, `tAdd`/`tSub`: periodic `±1` in one coordinate, with
  exact inverses `tSub_tAdd`, `tAdd_tSub` on in-range vertices (`0 < N`) and
  `tSub_ne` (`2 ≤ N`).
* `torusPlaquettes N` (`= boxPlaquettes N`): length `6N⁴`, no duplicates.
* `torusLinks N`: length `4N⁴`, no duplicates, membership = in-range base.
* `torusEdgesOf`: the four wrap-around boundary links of a plaquette.
* `torus_link_incidence_eq_six`: for `2 ≤ N` (hence for the requested
  `N ≥ 3`) every torus link lies on exactly 6 torus plaquettes (exact count,
  via the explicit incidence list `incidentPlaqs` of length 6).
* Translation action `tShift`: preserves range, identity and composition
  laws, commutes with `tAdd`, maps plaquette boundaries to boundaries.
* Embedding: for `L + 1 ≤ N`, every free-box plaquette of `boxPlaquettes L`
  is a torus plaquette with `torusEdgesOf N p = edgesOf p`.

Proved finite combinatorics; choice-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.Z4FiniteBoxExhaustion
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.Z4TorusGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)

/-! ## 1. Periodic coordinate steps -/

def wrapSucc (N x : Nat) : Nat := (x + 1) % N
def wrapPred (N x : Nat) : Nat := (x + (N - 1)) % N

theorem wrapSucc_lt {N : Nat} (hN : 0 < N) (x : Nat) : wrapSucc N x < N :=
  Nat.mod_lt _ hN
theorem wrapPred_lt {N : Nat} (hN : 0 < N) (x : Nat) : wrapPred N x < N :=
  Nat.mod_lt _ hN

theorem wrapPred_wrapSucc {N x : Nat} (hx : x < N) : wrapPred N (wrapSucc N x) = x := by
  unfold wrapSucc wrapPred
  rcases Nat.lt_or_ge (x + 1) N with h | h
  · rw [Nat.mod_eq_of_lt h, show x + 1 + (N - 1) = x + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show x + 1 = N by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (show N - 1 < N by omega)]
    omega

theorem wrapSucc_wrapPred {N x : Nat} (hx : x < N) : wrapSucc N (wrapPred N x) = x := by
  unfold wrapSucc wrapPred
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show N - 1 < N by omega), show N - 1 + 1 = N by omega, Nat.mod_self]
  · rw [show x + (N - 1) = (x - 1) + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show x - 1 < N by omega), show x - 1 + 1 = x by omega, Nat.mod_eq_of_lt hx]

theorem wrapPred_ne {N x : Nat} (hN : 2 ≤ N) (hx : x < N) : wrapPred N x ≠ x := by
  intro h
  have h2 := wrapSucc_wrapPred hx
  rw [h] at h2
  unfold wrapSucc at h2
  rcases Nat.lt_or_ge (x + 1) N with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2; omega
  · rw [show x + 1 = N by omega, Nat.mod_self] at h2; omega

theorem wrapSucc_of_lt {N x : Nat} (h : x + 1 < N) : wrapSucc N x = x + 1 :=
  Nat.mod_eq_of_lt h

/-! ## 2. Periodic vertex steps -/

/-- In-range (torus) vertex. -/
def InBox (N : Nat) (v : Z4Vertex) : Prop :=
  v.1 < N ∧ v.2.1 < N ∧ v.2.2.1 < N ∧ v.2.2.2 < N

def tAdd (N : Nat) : Z4Vertex → Dir4 → Z4Vertex
  | (a, b, c, d), .x0 => (wrapSucc N a, b, c, d)
  | (a, b, c, d), .x1 => (a, wrapSucc N b, c, d)
  | (a, b, c, d), .x2 => (a, b, wrapSucc N c, d)
  | (a, b, c, d), .x3 => (a, b, c, wrapSucc N d)

def tSub (N : Nat) : Z4Vertex → Dir4 → Z4Vertex
  | (a, b, c, d), .x0 => (wrapPred N a, b, c, d)
  | (a, b, c, d), .x1 => (a, wrapPred N b, c, d)
  | (a, b, c, d), .x2 => (a, b, wrapPred N c, d)
  | (a, b, c, d), .x3 => (a, b, c, wrapPred N d)

theorem tSub_tAdd {N : Nat} {v : Z4Vertex} (hv : InBox N v) (d : Dir4) :
    tSub N (tAdd N v d) d = v := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · show (wrapPred N (wrapSucc N a), b, c, e) = _; rw [wrapPred_wrapSucc h1]
  · show (a, wrapPred N (wrapSucc N b), c, e) = _; rw [wrapPred_wrapSucc h2]
  · show (a, b, wrapPred N (wrapSucc N c), e) = _; rw [wrapPred_wrapSucc h3]
  · show (a, b, c, wrapPred N (wrapSucc N e)) = _; rw [wrapPred_wrapSucc h4]

theorem tAdd_tSub {N : Nat} {v : Z4Vertex} (hv : InBox N v) (d : Dir4) :
    tAdd N (tSub N v d) d = v := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · show (wrapSucc N (wrapPred N a), b, c, e) = _; rw [wrapSucc_wrapPred h1]
  · show (a, wrapSucc N (wrapPred N b), c, e) = _; rw [wrapSucc_wrapPred h2]
  · show (a, b, wrapSucc N (wrapPred N c), e) = _; rw [wrapSucc_wrapPred h3]
  · show (a, b, c, wrapSucc N (wrapPred N e)) = _; rw [wrapSucc_wrapPred h4]

theorem tAdd_inBox {N : Nat} (hN : 0 < N) {v : Z4Vertex} (hv : InBox N v) (d : Dir4) :
    InBox N (tAdd N v d) := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · exact ⟨wrapSucc_lt hN a, h2, h3, h4⟩
  · exact ⟨h1, wrapSucc_lt hN b, h3, h4⟩
  · exact ⟨h1, h2, wrapSucc_lt hN c, h4⟩
  · exact ⟨h1, h2, h3, wrapSucc_lt hN e⟩

theorem tSub_inBox {N : Nat} (hN : 0 < N) {v : Z4Vertex} (hv : InBox N v) (d : Dir4) :
    InBox N (tSub N v d) := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · exact ⟨wrapPred_lt hN a, h2, h3, h4⟩
  · exact ⟨h1, wrapPred_lt hN b, h3, h4⟩
  · exact ⟨h1, h2, wrapPred_lt hN c, h4⟩
  · exact ⟨h1, h2, h3, wrapPred_lt hN e⟩

theorem tSub_ne {N : Nat} (hN : 2 ≤ N) {v : Z4Vertex} (hv : InBox N v) (d : Dir4) :
    tSub N v d ≠ v := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  intro h
  cases d
  · exact wrapPred_ne hN h1 (congrArg (fun w : Z4Vertex => w.1) h)
  · exact wrapPred_ne hN h2 (congrArg (fun w : Z4Vertex => w.2.1) h)
  · exact wrapPred_ne hN h3 (congrArg (fun w : Z4Vertex => w.2.2.1) h)
  · exact wrapPred_ne hN h4 (congrArg (fun w : Z4Vertex => w.2.2.2) h)

/-! ## 3. Generic list lemmas -/

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hp := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_inj f hf hp.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      exact hp.1 ((hf _ _ heq) ▸ hy)

/-- Blocks tagged by a key are disjoint, so a tagged `flatMap` is duplicate-free. -/
theorem nodup_flatMap_tagged {α β : Type} (key : α → β) (f : β → List α)
    (hf : ∀ b, (f b).Nodup) (htag : ∀ b x, x ∈ f b → key x = b) :
    ∀ {l : List β}, l.Nodup → (l.flatMap f).Nodup
  | [], _ => List.nodup_nil
  | b :: t, h => by
      have hp := List.nodup_cons.mp h
      rw [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨hf b, nodup_flatMap_tagged key f hf htag hp.2, ?_⟩
      intro x hx y hy hxy
      obtain ⟨b', hb', hyb⟩ := List.mem_flatMap.mp hy
      have e1 := htag b x hx
      have e2 := htag b' y hyb
      rw [hxy, e2] at e1
      exact hp.1 (e1 ▸ hb')

theorem length_flatMap_const {α β : Type} (f : α → List β) (c : Nat)
    (hf : ∀ a, (f a).length = c) : ∀ l : List α, (l.flatMap f).length = l.length * c
  | [] => by simp
  | a :: t => by
      rw [List.flatMap_cons, List.length_append, hf a, length_flatMap_const f c hf t,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-! ## 4. Torus vertices, links and plaquettes -/

theorem range_nodup' : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | k + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨range_nodup' k, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

theorem mem_boxVertices_iff (N : Nat) (v : Z4Vertex) : v ∈ boxVertices N ↔ InBox N v := by
  obtain ⟨a, b, c, d⟩ := v
  exact mem_boxVertices a b c d N

theorem boxVertices_nodup' (N : Nat) : (boxVertices N).Nodup := by
  have hr : (List.range N).Nodup := range_nodup' N
  have pair : ∀ {γ : Type} (ys : List γ), ys.Nodup →
      ((List.range N).flatMap fun x => ys.map fun y => (x, y)).Nodup := by
    intro γ ys hys
    exact nodup_flatMap_tagged (fun p : Nat × γ => p.1) _
      (fun x => nodup_map_inj _ (fun _ _ h => by injection h) hys)
      (fun x p hp => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp; rfl) hr
  have h1 := pair (List.range N) hr
  have h2 := pair _ (by simpa only [List.map_flatMap, List.map_map,
    Function.comp_apply] using h1)
  have h3 := pair _ (by simpa only [List.map_flatMap, List.map_map,
    Function.comp_apply] using h2)
  unfold boxVertices
  simpa only [List.map_flatMap, List.map_map, Function.comp_apply] using h3

theorem z4Planes_nodup' : z4Planes.Nodup := by decide

theorem mem_z4Planes (P : Z4Plane) : P ∈ z4Planes := by cases P <;> decide

/-- Torus plaquettes: one per in-range base vertex and plane. -/
def torusPlaquettes (N : Nat) : List Z4Plaq := boxPlaquettes N

theorem torusPlaquettes_length (N : Nat) :
    (torusPlaquettes N).length = 6 * (N * N * N * N) := by
  rw [torusPlaquettes, boxPlaquettes_length, Nat.mul_comm]

theorem torusPlaquettes_nodup (N : Nat) : (torusPlaquettes N).Nodup := by
  unfold torusPlaquettes boxPlaquettes
  exact nodup_flatMap_tagged (fun p : Z4Plaq => p.1) _
    (fun v => nodup_map_inj _ (fun _ _ h => by injection h) z4Planes_nodup')
    (fun v p hp => by obtain ⟨P, _, rfl⟩ := List.mem_map.mp hp; rfl)
    (boxVertices_nodup' N)

theorem mem_torusPlaquettes (N : Nat) (v : Z4Vertex) (P : Z4Plane) :
    (v, P) ∈ torusPlaquettes N ↔ InBox N v := by
  obtain ⟨a, b, c, d⟩ := v
  exact mem_boxPlaquettes ((a, b, c, d), P) N

def dirs4 : List Dir4 := [.x0, .x1, .x2, .x3]

theorem mem_dirs4 (d : Dir4) : d ∈ dirs4 := by cases d <;> decide

/-- Torus links: one per in-range base vertex and direction. -/
def torusLinks (N : Nat) : List Z4Link :=
  (boxVertices N).flatMap fun v => dirs4.map fun d => (v, d)

theorem torusLinks_length (N : Nat) :
    (torusLinks N).length = 4 * (N * N * N * N) := by
  unfold torusLinks
  rw [length_flatMap_const _ 4 (fun _ => rfl), boxVertices_length, Nat.mul_comm]

theorem torusLinks_nodup (N : Nat) : (torusLinks N).Nodup := by
  unfold torusLinks
  exact nodup_flatMap_tagged (fun l : Z4Link => l.1) _
    (fun v => nodup_map_inj _ (fun _ _ h => by injection h) (by decide))
    (fun v l hl => by obtain ⟨d, _, rfl⟩ := List.mem_map.mp hl; rfl)
    (boxVertices_nodup' N)

theorem mem_torusLinks (N : Nat) (v : Z4Vertex) (d : Dir4) :
    (v, d) ∈ torusLinks N ↔ InBox N v := by
  unfold torusLinks
  constructor
  · intro h
    obtain ⟨w, hw, hl⟩ := List.mem_flatMap.mp h
    obtain ⟨d', _, he⟩ := List.mem_map.mp hl
    have : w = v := congrArg Prod.fst he
    exact (mem_boxVertices_iff N v).mp (this ▸ hw)
  · intro h
    exact List.mem_flatMap.mpr ⟨v, (mem_boxVertices_iff N v).mpr h,
      List.mem_map.mpr ⟨d, mem_dirs4 d, rfl⟩⟩

/-! ## 5. Wrap-around plaquette boundary and exact incidence -/

/-- The four periodic boundary links of a plaquette (order as `edgesOf`). -/
def torusEdgesOf (N : Nat) (p : Z4Plaq) : List Z4Link :=
  [ (p.1, (dirsOf p.2).1),
    (p.1, (dirsOf p.2).2),
    (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1),
    (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2) ]

def containsDir (P : Z4Plane) (μ : Dir4) : Bool :=
  decide ((dirsOf P).1 = μ) || decide ((dirsOf P).2 = μ)

def otherDir (P : Z4Plane) (μ : Dir4) : Dir4 :=
  if (dirsOf P).1 = μ then (dirsOf P).2 else (dirsOf P).1

theorem contains_fst (P : Z4Plane) : containsDir P (dirsOf P).1 = true := by cases P <;> rfl
theorem contains_snd (P : Z4Plane) : containsDir P (dirsOf P).2 = true := by cases P <;> rfl
theorem other_fst (P : Z4Plane) : otherDir P (dirsOf P).1 = (dirsOf P).2 := by cases P <;> rfl
theorem other_snd (P : Z4Plane) : otherDir P (dirsOf P).2 = (dirsOf P).1 := by cases P <;> rfl

theorem containsDir_cases {P : Z4Plane} {μ : Dir4} (h : containsDir P μ = true) :
    μ = (dirsOf P).1 ∨ μ = (dirsOf P).2 := by
  cases P <;> cases μ <;> first | exact Or.inl rfl | exact Or.inr rfl |
    exact absurd h (by decide)

/-- The explicit list of the plaquettes containing link `(v, μ)`: for each of
the three planes through `μ`, the plaquette based at `v` and the one based at
`v − ê_other` (periodically). -/
def incidentPlaqs (N : Nat) (ℓ : Z4Link) : List Z4Plaq :=
  z4Planes.flatMap fun P =>
    if containsDir P ℓ.2 then [(ℓ.1, P), (tSub N ℓ.1 (otherDir P ℓ.2), P)] else []

theorem incidentPlaqs_length (N : Nat) (ℓ : Z4Link) : (incidentPlaqs N ℓ).length = 6 := by
  obtain ⟨v, μ⟩ := ℓ
  cases μ <;> rfl

theorem incidentPlaqs_nodup {N : Nat} (hN : 2 ≤ N) {v : Z4Vertex} (hv : InBox N v)
    (μ : Dir4) : (incidentPlaqs N (v, μ)).Nodup := by
  unfold incidentPlaqs
  refine nodup_flatMap_tagged (fun p : Z4Plaq => p.2) _ ?_ ?_ z4Planes_nodup'
  · intro P
    cases containsDir P μ
    · exact List.nodup_nil
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
      intro hm
      have he : (v, P) = (tSub N v (otherDir P μ), P) := List.mem_singleton.mp hm
      exact tSub_ne hN hv (otherDir P μ) (congrArg Prod.fst he).symm
  · intro P x hx
    cases hc : containsDir P μ <;> rw [hc] at hx
    · cases hx
    · rcases List.mem_cons.mp hx with h | h
      · rw [h]
      · rw [List.mem_singleton.mp h]

theorem mem_incident_of {N : Nat} {v : Z4Vertex} {μ : Dir4} {P : Z4Plane} {x : Z4Plaq}
    (hc : containsDir P μ = true)
    (hx : x = (v, P) ∨ x = (tSub N v (otherDir P μ), P)) :
    x ∈ incidentPlaqs N (v, μ) := by
  refine List.mem_flatMap.mpr ⟨P, mem_z4Planes P, ?_⟩
  show x ∈ (if containsDir P μ = true then _ else _)
  rw [if_pos hc]
  rcases hx with h | h
  · rw [h]; exact List.mem_cons_self
  · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem filter_sub_incident {N : Nat} {v : Z4Vertex} {μ : Dir4} (x : Z4Plaq)
    (hx : x ∈ (torusPlaquettes N).filter (fun p => decide ((v, μ) ∈ torusEdgesOf N p))) :
    x ∈ incidentPlaqs N (v, μ) := by
  obtain ⟨w, P⟩ := x
  rw [List.mem_filter] at hx
  have hw : InBox N w := (mem_torusPlaquettes N w P).mp hx.1
  have he : (v, μ) ∈ torusEdgesOf N (w, P) := of_decide_eq_true hx.2
  simp only [torusEdgesOf, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mem_incident_of (contains_fst P) (Or.inl rfl)
  · exact mem_incident_of (contains_snd P) (Or.inl rfl)
  · refine mem_incident_of (contains_fst P) (Or.inr ?_)
    rw [other_fst, tSub_tAdd hw]
  · refine mem_incident_of (contains_snd P) (Or.inr ?_)
    rw [other_snd, tSub_tAdd hw]

theorem incident_sub_filter {N : Nat} (hN : 0 < N) {v : Z4Vertex} (hv : InBox N v)
    {μ : Dir4} (x : Z4Plaq) (hx : x ∈ incidentPlaqs N (v, μ)) :
    x ∈ (torusPlaquettes N).filter (fun p => decide ((v, μ) ∈ torusEdgesOf N p)) := by
  obtain ⟨P, _, hxP⟩ := List.mem_flatMap.mp hx
  cases hc : containsDir P μ
  · have hxP' : x ∈ (if containsDir P μ = true then
        [(v, P), (tSub N v (otherDir P μ), P)] else []) := hxP
    rw [hc] at hxP'; cases hxP'
  · have hxP' : x ∈ (if containsDir P μ = true then
        [(v, P), (tSub N v (otherDir P μ), P)] else []) := hxP
    rw [hc] at hxP'
    rw [List.mem_filter]
    rcases List.mem_cons.mp hxP' with h | h
    · subst h
      refine ⟨(mem_torusPlaquettes N v P).mpr hv, decide_eq_true ?_⟩
      rcases containsDir_cases hc with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton.mp h]
      refine ⟨(mem_torusPlaquettes N _ P).mpr (tSub_inBox hN hv _), decide_eq_true ?_⟩
      rcases containsDir_cases hc with rfl | rfl
      · rw [other_fst]
        show (v, (dirsOf P).1) ∈ [_, _, (tAdd N (tSub N v (dirsOf P).2) (dirsOf P).2,
          (dirsOf P).1), _]
        rw [tAdd_tSub hv]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [other_snd]
        show (v, (dirsOf P).2) ∈ [_, _, _, (tAdd N (tSub N v (dirsOf P).1) (dirsOf P).1,
          (dirsOf P).2)]
        rw [tAdd_tSub hv]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Exact incidence.** On the periodic torus with `2 ≤ N` (in particular for
`N ≥ 3`), every link lies on the boundary of exactly 6 torus plaquettes. -/
theorem torus_link_incidence_eq_six {N : Nat} (hN : 2 ≤ N) {ℓ : Z4Link}
    (hℓ : ℓ ∈ torusLinks N) :
    ((torusPlaquettes N).filter (fun p => decide (ℓ ∈ torusEdgesOf N p))).length = 6 := by
  obtain ⟨v, μ⟩ := ℓ
  have hv : InBox N v := (mem_torusLinks N v μ).mp hℓ
  have hle := nodup_subset_length_le
    ((torusPlaquettes N).filter (fun p => decide ((v, μ) ∈ torusEdgesOf N p)))
    (incidentPlaqs N (v, μ))
    ((torusPlaquettes_nodup N).sublist List.filter_sublist)
    (fun x hx => filter_sub_incident x hx)
  have hge := nodup_subset_length_le (incidentPlaqs N (v, μ))
    ((torusPlaquettes N).filter (fun p => decide ((v, μ) ∈ torusEdgesOf N p)))
    (incidentPlaqs_nodup hN hv μ)
    (fun x hx => incident_sub_filter (Nat.lt_of_lt_of_le (by decide) hN) hv x hx)
  rw [incidentPlaqs_length] at hle hge
  exact Nat.le_antisymm hle hge

/-! ## 6. Translation action -/

/-- Periodic translation by `t`. -/
def tShift (N : Nat) (t v : Z4Vertex) : Z4Vertex :=
  ((v.1 + t.1) % N, (v.2.1 + t.2.1) % N, (v.2.2.1 + t.2.2.1) % N,
    (v.2.2.2 + t.2.2.2) % N)

def vAdd (s t : Z4Vertex) : Z4Vertex :=
  (s.1 + t.1, s.2.1 + t.2.1, s.2.2.1 + t.2.2.1, s.2.2.2 + t.2.2.2)

theorem tShift_inBox {N : Nat} (hN : 0 < N) (t v : Z4Vertex) : InBox N (tShift N t v) :=
  ⟨Nat.mod_lt _ hN, Nat.mod_lt _ hN, Nat.mod_lt _ hN, Nat.mod_lt _ hN⟩

theorem tShift_zero {N : Nat} {v : Z4Vertex} (hv : InBox N v) :
    tShift N (0, 0, 0, 0) v = v := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  show ((a + 0) % N, (b + 0) % N, (c + 0) % N, (d + 0) % N) = (a, b, c, d)
  rw [Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]

theorem tShift_comp (N : Nat) (s t v : Z4Vertex) :
    tShift N s (tShift N t v) = tShift N (vAdd t s) v := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [tShift, vAdd, Nat.mod_add_mod, Nat.add_assoc]

theorem wrap_shift (N x t : Nat) : ((x + t) % N + 1) % N = ((x + 1) % N + t) % N := by
  rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]

theorem tAdd_tShift (N : Nat) (t v : Z4Vertex) (d : Dir4) :
    tAdd N (tShift N t v) d = tShift N t (tAdd N v d) := by
  obtain ⟨a, b, c, e⟩ := v
  cases d <;> simp only [tAdd, tShift, wrapSucc, wrap_shift]

def shiftLink (N : Nat) (t : Z4Vertex) (ℓ : Z4Link) : Z4Link := (tShift N t ℓ.1, ℓ.2)

/-- Translation maps plaquette boundaries to plaquette boundaries. -/
theorem torusEdgesOf_shift (N : Nat) (t w : Z4Vertex) (P : Z4Plane) :
    torusEdgesOf N (tShift N t w, P) = (torusEdgesOf N (w, P)).map (shiftLink N t) := by
  simp only [torusEdgesOf, List.map_cons, List.map_nil, shiftLink, tAdd_tShift]

theorem shift_mem_torusPlaquettes {N : Nat} (hN : 0 < N) (t w : Z4Vertex) (P : Z4Plane) :
    (tShift N t w, P) ∈ torusPlaquettes N :=
  (mem_torusPlaquettes N _ P).mpr (tShift_inBox hN t w)

theorem shift_mem_torusLinks {N : Nat} (hN : 0 < N) (t : Z4Vertex) (ℓ : Z4Link) :
    shiftLink N t ℓ ∈ torusLinks N :=
  (mem_torusLinks N _ ℓ.2).mpr (tShift_inBox hN t ℓ.1)

/-! ## 7. Embedding of the free boxes -/

theorem box_mem_torus {L N : Nat} (hLN : L ≤ N) {p : Z4Plaq} (hp : p ∈ boxPlaquettes L) :
    p ∈ torusPlaquettes N :=
  boxPlaquettes_mono hLN hp

theorem tAdd_eq_addE {N : Nat} {v : Z4Vertex} (hv : v.1 + 1 < N ∧ v.2.1 + 1 < N ∧
    v.2.2.1 + 1 < N ∧ v.2.2.2 + 1 < N) (d : Dir4) : tAdd N v d = addE v d := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · show (wrapSucc N a, b, c, e) = (a + 1, b, c, e); rw [wrapSucc_of_lt h1]
  · show (a, wrapSucc N b, c, e) = (a, b + 1, c, e); rw [wrapSucc_of_lt h2]
  · show (a, b, wrapSucc N c, e) = (a, b, c + 1, e); rw [wrapSucc_of_lt h3]
  · show (a, b, c, wrapSucc N e) = (a, b, c, e + 1); rw [wrapSucc_of_lt h4]

/-- **Embedding.** If `L + 1 ≤ N`, a free-box plaquette of `boxPlaquettes L`
is a torus plaquette with the SAME four boundary links (no wrap occurs). -/
theorem box_torusEdges_eq {L N : Nat} (hLN : L + 1 ≤ N) {p : Z4Plaq}
    (hp : p ∈ boxPlaquettes L) : torusEdgesOf N p = edgesOf p := by
  have h := (mem_boxPlaquettes p L).mp hp
  have hv : p.1.1 + 1 < N ∧ p.1.2.1 + 1 < N ∧ p.1.2.2.1 + 1 < N ∧ p.1.2.2.2 + 1 < N :=
    ⟨Nat.lt_of_lt_of_le (Nat.add_lt_add_right h.1 1) hLN,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_right h.2.1 1) hLN,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_right h.2.2.1 1) hLN,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_right h.2.2.2 1) hLN⟩
  simp only [torusEdgesOf, edgesOf, tAdd_eq_addE hv]

end YMGap.Continuum.Z4TorusGeometry
