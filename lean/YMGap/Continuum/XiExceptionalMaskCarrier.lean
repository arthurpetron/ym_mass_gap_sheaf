/-
# Exceptional occurrence paths as actual polymer-carrier terms

This successor specializes the frozen generic path and carrier machinery of
`XiExceptionalPathExtraction` to Boolean occurrence masks over an ambient
polymer list `Γ`.  A bounded occurrence index is evaluated by `polyAt`.
Every disagreement edge then maps to an actual hard-core incompatibility
edge, and maskwise `q`-admissibility maps to the per-polymer predicate along
the whole recovered path.

The capstone places the exact mapped path activity, dressed by any admissible
background family compatible with the path, in `connectingChainMajorant`.
The remaining global step is the finite recovered-cut injection which chooses
and accounts for the two background families; no such summation is assumed in
this file.
-/

import YMGap.Continuum.XiExceptionalPathExtraction

namespace YMGap.Continuum.XiExceptionalMaskCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Ambient occurrence evaluation -/

/-- Total evaluation of an ambient occurrence index.  All load-bearing uses
carry `i < Γ.length`, so the empty fallback is never selected. -/
def polyAt (Γ : List (Polymer L)) (i : Nat) : Polymer L :=
  (Γ[i]?).getD []

theorem polyAt_eq_getElem (Γ : List (Polymer L)) {i : Nat}
    (hi : i < Γ.length) : polyAt Γ i = Γ[i] := by
  unfold polyAt
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem polyAt_mem (Γ : List (Polymer L)) {i : Nat}
    (hi : i < Γ.length) : polyAt Γ i ∈ Γ := by
  rw [polyAt_eq_getElem Γ hi]
  exact List.getElem_mem hi

/-- Occurrence-level hard-core incompatibility induced by `Γ`. -/
def incAt (Γ : List (Polymer L)) (i j : Nat) : Bool :=
  !(compatibleB (polyAt Γ i) (polyAt Γ j))

def predAt (Γ : List (Polymer L)) (p : Polymer L → Bool) (i : Nat) : Bool :=
  p (polyAt Γ i)

/-! ## 2. Mapping cons-form walks -/

def mapCWalk {α β : Type} {edgeA : α → α → Bool}
    {edgeB : β → β → Bool} (f : α → β)
    (hedge : ∀ x y, edgeA x y = true → edgeB (f x) (f y) = true) :
    {x y : α} → CWalk edgeA x y → CWalk edgeB (f x) (f y)
  | _, _, .single x => .single (f x)
  | _, _, .cons h rest => .cons (hedge _ _ h) (mapCWalk f hedge rest)

theorem vertices_mapCWalk {α β : Type} {edgeA : α → α → Bool}
    {edgeB : β → β → Bool} (f : α → β)
    (hedge : ∀ x y, edgeA x y = true → edgeB (f x) (f y) = true) :
    ∀ {x y : α} (p : CWalk edgeA x y),
      (mapCWalk f hedge p).vertices = p.vertices.map f
  | _, _, .single _ => rfl
  | _, _, .cons _ rest => by
      simp only [mapCWalk, CWalk.vertices, List.map_cons]
      rw [vertices_mapCWalk f hedge rest]

/-! ## 3. Disagreement edges give polymer incompatibilities -/

theorem disagreementBits_source_occupied
    (li ri lj rj conflict : Bool)
    (h : disagreementBits li ri lj rj conflict = true) :
    li || ri = true := by
  cases li <;> cases ri <;> cases lj <;> cases rj <;> cases conflict <;>
    simp_all [disagreementBits, leftOnly, rightOnly]

theorem disagreementEdge_source_occupied
    (N : Nat) (inc : Nat → Nat → Bool) (left right : Nat → Bool)
    {i j : Nat} (h : disagreementEdge N inc left right i j = true) :
    left i || right i = true := by
  have hd := ((Bool.and_eq_true _ _).mp h).2
  exact disagreementBits_source_occupied _ _ _ _ _ hd

theorem disagreementEdge_incAt
    (Γ : List (Polymer L)) (left right : Nat → Bool)
    {i j : Nat}
    (h : disagreementEdge Γ.length (incAt Γ) left right i j = true) :
    (!(compatibleB (polyAt Γ i) (polyAt Γ j))) = true := by
  have hbits := ((Bool.and_eq_true _ _).mp h).2
  have hconflict := ((Bool.and_eq_true _ _).mp hbits).2
  unfold symConflict at hconflict
  rcases (Bool.or_eq_true _ _).mp hconflict with hij | hji
  · exact hij
  · unfold incAt at hji
    rw [compatibleB_symm (polyAt Γ j) (polyAt Γ i)] at hji
    exact hji

theorem forwardSeed_parts
    (N : Nat) (left right bad : Nat → Bool) {i : Nat}
    (h : forwardSeed N left right bad i = true) :
    i < N ∧ left i = true ∧ right i = false ∧ bad i = true := by
  have houter := (Bool.and_eq_true _ _).mp h
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  have hleftOnly := (Bool.and_eq_true _ _).mp hinner.1
  have hright : right i = false := eq_false_of_not_true hleftOnly.2
  exact ⟨of_decide_eq_true houter.1, hleftOnly.1, hright, hinner.2⟩

/-- Every vertex of a disagreement walk ending at a forward seed is occupied
on at least one side. -/
theorem walk_vertices_occupied_of_seed
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool) :
    ∀ {i seed : Nat}
      (p : CWalk (disagreementEdge N inc left right) i seed),
      forwardSeed N left right bad seed = true →
      ∀ k, k ∈ p.vertices → left k || right k = true
  | _, _, .single _, hseed, k, hk => by
      rw [List.mem_singleton.mp hk]
      have hp := forwardSeed_parts N left right bad hseed
      simp [hp.2.1]
  | _, _, .cons h rest, hseed, k, hk => by
      rcases List.mem_cons.mp hk with hhead | htail
      · rw [hhead]
        exact disagreementEdge_source_occupied N inc left right h
      · exact walk_vertices_occupied_of_seed N inc left right bad rest
          hseed k htail

/-- Every vertex of a disagreement walk ending at an in-range seed is itself
in range. -/
theorem walk_vertices_lt_of_seed
    (N : Nat) (inc : Nat → Nat → Bool) (left right : Nat → Bool) :
    ∀ {i seed : Nat}
      (p : CWalk (disagreementEdge N inc left right) i seed),
      seed < N → ∀ k, k ∈ p.vertices → k < N
  | _, _, .single _, hseed, k, hk => by
      rw [List.mem_singleton.mp hk]
      exact hseed
  | _, _, .cons h rest, hseed, k, hk => by
      rcases List.mem_cons.mp hk with hhead | htail
      · rw [hhead]
        exact (disagreementEdge_bounds N inc left right h).1
      · exact walk_vertices_lt_of_seed N inc left right rest hseed k htail

/-! ## 4. Constructive exceptional polymer-path package -/

/-- The recovered occurrence path together with its mapped polymer walk and
the exact admissibility data needed by the connecting-chain carrier. -/
structure ExceptionalPolymerPath
    (Γ : List (Polymer L)) (qP b2 : Polymer L → Bool)
    (left right : Nat → Bool) (marked : Nat) : Type where
  seed : Nat
  seed_true :
    forwardSeed Γ.length left right (predAt Γ b2) seed = true
  indexWalk :
    CWalk (disagreementEdge Γ.length (incAt Γ) left right) marked seed
  index_nodup : indexWalk.vertices.Nodup
  polymerWalk :
    CWalk (fun X Y : Polymer L => !(compatibleB X Y))
      (polyAt Γ marked) (polyAt Γ seed)
  polymer_vertices :
    polymerWalk.vertices = indexWalk.vertices.map (polyAt Γ)
  length_le : polymerWalk.vertices.length ≤ Γ.length
  ambient_mem : ∀ X, X ∈ polymerWalk.vertices → X ∈ Γ
  q_true : ∀ X, X ∈ polymerWalk.vertices → qP X = true

/-- Map an exceptional recovered occurrence component into an actual bounded
polymer incompatibility walk. -/
def exceptionalPolymerPathOfReach
    (Γ : List (Polymer L)) (qP b2 : Polymer L → Bool)
    (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAt Γ) left right
      (predAt Γ b2) marked = true) :
    ExceptionalPolymerPath Γ qP b2 left right marked := by
  let ep := reverseOccurrencePathOfReach Γ.length (incAt Γ) left right
    (predAt Γ b2) marked hreach
  let pw : CWalk (fun X Y : Polymer L => !(compatibleB X Y))
      (polyAt Γ marked) (polyAt Γ ep.seed) :=
    mapCWalk (edgeB := fun X Y : Polymer L => !(compatibleB X Y)) (polyAt Γ)
    (fun _ _ h => disagreementEdge_incAt Γ left right h)
    ep.walk
  have hseedN : ep.seed < Γ.length :=
    (forwardSeed_parts Γ.length left right (predAt Γ b2) ep.seed_true).1
  have hindexLt : ∀ i, i ∈ ep.walk.vertices → i < Γ.length :=
    walk_vertices_lt_of_seed Γ.length (incAt Γ) left right ep.walk hseedN
  have hoccupied : ∀ i, i ∈ ep.walk.vertices →
      left i || right i = true :=
    walk_vertices_occupied_of_seed Γ.length (incAt Γ) left right
      (predAt Γ b2) ep.walk ep.seed_true
  have hpverts : pw.vertices = ep.walk.vertices.map (polyAt Γ) :=
    vertices_mapCWalk (polyAt Γ)
      (fun _ _ h => disagreementEdge_incAt Γ left right h) ep.walk
  have hlen : pw.vertices.length ≤ Γ.length := by
    rw [hpverts, List.length_map]
    exact ep.length_le
  have hmem : ∀ X, X ∈ pw.vertices → X ∈ Γ := by
    intro X hX
    rw [hpverts] at hX
    obtain ⟨i, hi, hiX⟩ := List.mem_map.mp hX
    rw [← hiX]
    exact polyAt_mem Γ (hindexLt i hi)
  have hq : ∀ X, X ∈ pw.vertices → qP X = true := by
    intro X hX
    rw [hpverts] at hX
    obtain ⟨i, hi, hiX⟩ := List.mem_map.mp hX
    rw [← hiX]
    cases hli : left i with
    | true => exact hleftQ i (hindexLt i hi) hli
    | false =>
        have hoc := hoccupied i hi
        rw [hli] at hoc
        exact hrightQ i (hindexLt i hi) (of_decide_eq_true hoc)
  exact
    { seed := ep.seed
      seed_true := ep.seed_true
      indexWalk := ep.walk
      index_nodup := ep.nodup
      polymerWalk := pw
      polymer_vertices := hpverts
      length_le := hlen
      ambient_mem := hmem
      q_true := hq }

/-- **Exceptional path term inclusion.**  Once a compatible background
subfamily has been selected and certified compatible with every recovered
path vertex, the exact mapped path/background activity is bounded by the
existing head-rooted connecting-chain majorant. -/
theorem exceptional_path_term_le_connectingChainMajorant {w : Q'}
    (hw : (0 : Q') ≤ w)
    (Γ B : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (left right : Nat → Bool) (marked : Nat)
    (hleftQ : ∀ i, i < Γ.length → left i = true →
      qP (polyAt Γ i) = true)
    (hrightQ : ∀ i, i < Γ.length → right i = true →
      qP (polyAt Γ i) = true)
    (hreach : forwardComponent Γ.length (incAt Γ) left right
      (predAt Γ b2) marked = true)
    (hmarked : b1 (polyAt Γ marked) = true)
    (hBsub : B ∈ sublists Γ) (hBcompat : familyCompatibleB B = true)
    (hBq : B.all qP = true)
    (hBpath : ∀ X,
      X ∈ (exceptionalPolymerPathOfReach Γ qP b2 left right marked
        hleftQ hrightQ hreach).polymerWalk.vertices →
      ∀ T, T ∈ B → compatibleB X T = true) :
    let ep := exceptionalPolymerPathOfReach Γ qP b2 left right marked
      hleftQ hrightQ hreach
    ep.polymerWalk.activityWeight w label * familyActivity w B label ≤
      connectingChainMajorant w qP b1 b2 Γ label := by
  dsimp only
  let ep := exceptionalPolymerPathOfReach Γ qP b2 left right marked
    hleftQ hrightQ hreach
  have hb2seed : b2 (polyAt Γ ep.seed) = true := by
    exact (forwardSeed_parts Γ.length left right (predAt Γ b2)
      ep.seed_true).2.2.2
  exact walk_term_le_connectingChainMajorant hw qP b1 b2 Γ B label
    ep.polymerWalk ep.length_le ep.ambient_mem ep.q_true hmarked hb2seed
    hBsub hBcompat hBq hBpath

#print axioms polyAt_eq_getElem
#print axioms polyAt_mem
#print axioms vertices_mapCWalk
#print axioms disagreementBits_source_occupied
#print axioms disagreementEdge_source_occupied
#print axioms disagreementEdge_incAt
#print axioms forwardSeed_parts
#print axioms walk_vertices_occupied_of_seed
#print axioms walk_vertices_lt_of_seed
#print axioms exceptionalPolymerPathOfReach
#print axioms exceptional_path_term_le_connectingChainMajorant

end YMGap.Continuum.XiExceptionalMaskCarrier
