/-
# Bounded path extraction for the exceptional Xi switching branch

The exceptional occurrence component in `XiReverseComponentRecovery` is
presented by a Boolean Warshall closure.  Its soundness witness is a
`DWalk`, whose transitive syntax need not respect the finite carrier fuel
bound.  This file replaces that syntax by a cons-form walk, reverses it, and
constructively erases loops.  The resulting occurrence path is `Nodup`; as
all its vertices lie in `range N`, it contains at most `N` vertices.

The construction is data-valued throughout.  In particular, no shortest-path
choice or excluded-middle search over propositions is used: loop erasure only
tests decidable membership in the already computed tail path.
-/

import YMGap.Continuum.XiReverseComponentRecovery

namespace YMGap.Continuum.XiExceptionalPathExtraction

open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound

/-! ## 1. Cons-form walks and constructive loop erasure -/

/-- A directed walk whose transitive structure is normalized to one leading
edge followed by a tail walk. -/
inductive CWalk {α : Type} (edge : α → α → Bool) : α → α → Type
  | single (x : α) : CWalk edge x x
  | cons {x y z : α} : edge x y = true → CWalk edge y z → CWalk edge x z

namespace CWalk

variable {α : Type} {edge : α → α → Bool}

/-- The vertex list of a cons-form walk. -/
def vertices : {x y : α} → CWalk edge x y → List α
  | x, _, .single _ => [x]
  | x, _, .cons _ rest => x :: vertices rest

/-- The starting vertex, retained as an explicit computable projection. -/
def start : {x y : α} → CWalk edge x y → α
  | x, _, _ => x

@[simp] theorem start_eq {x y : α} (p : CWalk edge x y) : p.start = x := by
  cases p <;> rfl

/-- Concatenation of cons-form walks. -/
def append {x y z : α} : CWalk edge x y → CWalk edge y z → CWalk edge x z
  | .single _, q => q
  | .cons h rest, q => .cons h (append rest q)

/-- Normalize a transitive `DWalk` certificate to cons form. -/
def ofDWalk {x y : α} : DWalk edge x y → CWalk edge x y
  | .refl _ => .single _
  | .edge h => .cons h (.single _)
  | .trans p q => append (ofDWalk p) (ofDWalk q)

/-- Reverse a walk when the Boolean edge relation is symmetric. -/
def reverse (hsymm : ∀ a b, edge a b = true → edge b a = true) :
    {x y : α} → CWalk edge x y → CWalk edge y x
  | _, _, .single x => .single x
  | _, _, .cons h rest =>
      append (reverse hsymm rest) (.cons (hsymm _ _ h) (.single _))

/-- Drop the prefix ending immediately before the first occurrence of `a`.
The membership proof makes the result total and keeps the original endpoint. -/
def dropTo [DecidableEq α] : {x y : α} → (p : CWalk edge x y) →
    (a : α) → a ∈ vertices p → CWalk edge a y
  | _, _, .single x, a, ha => by
      have hax : a = x := List.mem_singleton.mp ha
      subst a
      exact .single x
  | x, _, .cons h rest, a, ha => by
      by_cases hax : a = x
      · subst a
        exact .cons h rest
      · have har : a ∈ vertices rest := by
          exact (List.mem_cons.mp ha).resolve_left hax
        exact dropTo rest a har

/-- Dropping to a member of a `Nodup` walk preserves `Nodup`. -/
theorem dropTo_nodup [DecidableEq α] :
    ∀ {x y : α} (p : CWalk edge x y)
      (a : α) (ha : a ∈ vertices p) (hnd : (vertices p).Nodup),
      (vertices (dropTo p a ha)).Nodup
  | _, _, .single x, a, ha, _ => by
      have hax : a = x := List.mem_singleton.mp ha
      subst a
      simp [dropTo, vertices]
  | x, _, .cons h rest, a, ha, hnd => by
      by_cases hax : a = x
      · subst a
        simpa [dropTo, vertices] using hnd
      · have har : a ∈ vertices rest :=
          (List.mem_cons.mp ha).resolve_left hax
        have htail : (vertices rest).Nodup := (List.nodup_cons.mp hnd).2
        simpa [dropTo, hax] using dropTo_nodup rest a har htail

/-- A cons-form walk together with the proof that no vertex is repeated. -/
structure Simple (edge : α → α → Bool) (x y : α) : Type where
  walk : CWalk edge x y
  nodup : walk.vertices.Nodup

/-- Chronological loop erasure.  The recursively simplified tail either
contains the current vertex, in which case its prefix is dropped, or it does
not, in which case the current edge can be prepended without a repetition. -/
def eraseLoops [DecidableEq α] : {x y : α} → CWalk edge x y → Simple edge x y
  | _, _, .single x =>
      { walk := .single x
        nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩ }
  | x, _, .cons h rest =>
      let tail := eraseLoops rest
      if hx : x ∈ tail.walk.vertices then
        { walk := tail.walk.dropTo x hx
          nodup := dropTo_nodup tail.walk x hx tail.nodup }
      else
        { walk := .cons h tail.walk
          nodup := List.nodup_cons.mpr ⟨hx, tail.nodup⟩ }

/-- Every vertex property propagated by edge targets holds along a walk. -/
theorem all_vertices_of_start
    (P : α → Prop) (hedge : ∀ a b, edge a b = true → P a → P b) :
    ∀ {x y : α} (p : CWalk edge x y), P x →
      ∀ a, a ∈ p.vertices → P a
  | _, _, .single x, hx, a, ha => by
      rw [List.mem_singleton.mp ha]
      exact hx
  | _, _, .cons h rest, hx, a, ha => by
      rcases List.mem_cons.mp ha with hax | har
      · rw [hax]
        exact hx
      · exact all_vertices_of_start P hedge rest (hedge _ _ h hx) a har

/-- The endpoint of a walk satisfies every vertex property propagated from
its start. -/
theorem end_of_start
    (P : α → Prop) (hedge : ∀ a b, edge a b = true → P a → P b) :
    ∀ {x y : α} (p : CWalk edge x y), P x → P y
  | _, _, .single _, hx => hx
  | _, _, .cons h rest, hx =>
      end_of_start P hedge rest (hedge _ _ h hx)

end CWalk

/-! ## 2. A constructive finite-pigeonhole bound -/

namespace FiniteListBound

variable {α : Type} [DecidableEq α]

/-- Remove the first occurrence of `a`. -/
def removeFirst (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: removeFirst a xs

theorem removeFirst_length (a : α) :
    ∀ (xs : List α), a ∈ xs → (removeFirst a xs).length + 1 = xs.length
  | [], ha => absurd ha List.not_mem_nil
  | x :: xs, ha => by
      by_cases hxa : x = a
      · simp [removeFirst, hxa]
      · simp only [removeFirst, hxa, ↓reduceIte, List.length_cons]
        have htail : a ∈ xs :=
          (List.mem_cons.mp ha).resolve_left (fun h => hxa h.symm)
        have ih := removeFirst_length a xs htail
        omega

theorem mem_removeFirst (a : α) :
    ∀ (xs : List α) (b : α), b ∈ xs → b ≠ a → b ∈ removeFirst a xs
  | [], b, hb, _ => absurd hb List.not_mem_nil
  | x :: xs, b, hb, hba => by
      by_cases hxa : x = a
      · rw [removeFirst, if_pos hxa]
        rcases List.mem_cons.mp hb with hbx | hbx
        · exact absurd (hbx.trans hxa) hba
        · exact hbx
      · rw [removeFirst, if_neg hxa]
        rcases List.mem_cons.mp hb with hbx | hbx
        · rw [hbx]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_removeFirst a xs b hbx hba)

/-- A duplicate-free list embedded in a finite ambient list is no longer than
that ambient list. -/
theorem nodup_subset_length_le :
    ∀ (xs U : List α), xs.Nodup →
      (∀ a, a ∈ xs → a ∈ U) → xs.length ≤ U.length
  | [], U, _, _ => Nat.zero_le _
  | a :: xs, U, hnd, hsub => by
      have haU : a ∈ U := hsub a List.mem_cons_self
      have hnd' := List.nodup_cons.mp hnd
      have hsub' : ∀ b, b ∈ xs → b ∈ removeFirst a U := by
        intro b hb
        have hba : b ≠ a := fun h => hnd'.1 (h ▸ hb)
        exact mem_removeFirst a U b
          (hsub b (List.mem_cons_of_mem _ hb)) hba
      have ih := nodup_subset_length_le xs (removeFirst a U) hnd'.2 hsub'
      have hlen := removeFirst_length a U haU
      show xs.length + 1 ≤ U.length
      omega

end FiniteListBound

/-! ## 3. Stripping the artificial root -/

/-- A walk between occurrence vertices contains only occurrence edges after
the artificial root has been stripped. -/
def leftWalkToIndex (seed : Nat → Bool) (edge : Nat → Nat → Bool) :
    {i j : Nat} →
      CWalk (occurrenceReachEdge seed edge)
        (SwitchVertex.left i) (SwitchVertex.left j) → CWalk edge i j
  | i, _, .single _ => .single i
  | _, _, @CWalk.cons _ _ _ .root _ h _ => by
      simp [occurrenceReachEdge] at h
  | _, _, @CWalk.cons _ _ _ (.left _) _ h rest =>
      .cons h (leftWalkToIndex seed edge rest)
  | _, _, @CWalk.cons _ _ _ (.right _) _ h _ => by
      simp [occurrenceReachEdge] at h

/-- Root-stripped occurrence-walk data. -/
structure RootedIndexWalk (seed : Nat → Bool) (edge : Nat → Nat → Bool)
    (finish : Nat) : Type where
  start : Nat
  seed_true : seed start = true
  walk : CWalk edge start finish

/-- Strip the unique artificial-root edge.  The result exposes, as data, the
seed index and the ordinary occurrence walk from that seed to the endpoint. -/
def stripOccurrenceRoot (seed : Nat → Bool) (edge : Nat → Nat → Bool)
    {j : Nat}
    (p : CWalk (occurrenceReachEdge seed edge)
      SwitchVertex.root (SwitchVertex.left j)) :
    RootedIndexWalk seed edge j := by
  cases p with
  | @cons x y z h rest =>
      cases y with
      | root => simp [occurrenceReachEdge] at h
      | left i => exact ⟨i, h, leftWalkToIndex seed edge rest⟩
      | right i => simp [occurrenceReachEdge] at h

/-! ## 4. The bounded reverse occurrence path -/

/-- Data extracted from an exceptional reached occurrence.  The path starts
at the reached occurrence, runs backwards to an actual forward seed, is
simple, and fits inside the `N`-vertex occurrence universe. -/
structure ReverseOccurrencePath
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) (marked : Nat) : Type where
  seed : Nat
  seed_true : forwardSeed N left right bad seed = true
  walk : CWalk (disagreementEdge N inc left right) marked seed
  nodup : walk.vertices.Nodup
  length_le : walk.vertices.length ≤ N

theorem disagreementEdge_bounds
    (N : Nat) (inc : Nat → Nat → Bool) (left right : Nat → Bool)
    {i j : Nat} (h : disagreementEdge N inc left right i j = true) :
    i < N ∧ j < N := by
  have hb := (Bool.and_eq_true _ _).mp h
  have hij := (Bool.and_eq_true _ _).mp hb.1
  exact ⟨of_decide_eq_true hij.1, of_decide_eq_true hij.2⟩

/-- Warshall reachability in the forward occurrence component yields a
concrete reversed simple path of at most `N` occurrence vertices, ending at a
genuine bad left-only seed. -/
def reverseOccurrencePathOfReach
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) (marked : Nat)
    (hreach : forwardComponent N inc left right bad marked = true) :
    ReverseOccurrencePath N inc left right bad marked := by
  let rootWalk : CWalk
      (occurrenceReachEdge (forwardSeed N left right bad)
        (disagreementEdge N inc left right))
      SwitchVertex.root (SwitchVertex.left marked) :=
    CWalk.ofDWalk (warshallSound
      (occurrenceReachEdge (forwardSeed N left right bad)
        (disagreementEdge N inc left right))
      (occurrenceUniverse N) SwitchVertex.root (SwitchVertex.left marked)
      hreach)
  let stripped := stripOccurrenceRoot
    (forwardSeed N left right bad)
    (disagreementEdge N inc left right) rootWalk
  let forward : CWalk (disagreementEdge N inc left right)
      stripped.start marked := stripped.walk
  have hseedN : stripped.start < N := by
    have hs := stripped.seed_true
    exact of_decide_eq_true
      ((Bool.and_eq_true _ _).mp hs).1
  have hmarkedN : marked < N :=
    CWalk.end_of_start (fun i => i < N)
      (fun _ _ h _ => (disagreementEdge_bounds N inc left right h).2)
      forward hseedN
  let backward : CWalk (disagreementEdge N inc left right)
      marked stripped.start :=
    CWalk.reverse (fun i j h => by
      rw [disagreementEdge_symm N inc left right j i]
      exact h) forward
  let simple := CWalk.eraseLoops backward
  have hall : ∀ i, i ∈ simple.walk.vertices → i ∈ List.range N := by
    intro i hi
    apply List.mem_range.mpr
    exact CWalk.all_vertices_of_start (fun k => k < N)
      (fun _ _ h _ => (disagreementEdge_bounds N inc left right h).2)
      simple.walk hmarkedN i hi
  have hlen : simple.walk.vertices.length ≤ N := by
    have h := FiniteListBound.nodup_subset_length_le
      simple.walk.vertices (List.range N) simple.nodup hall
    simpa using h
  exact
    { seed := stripped.start
      seed_true := stripped.seed_true
      walk := simple.walk
      nodup := simple.nodup
      length_le := hlen }

/-! ## 5. Termwise inclusion in the connecting-chain carrier -/

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-- The product of activities along a cons-form polymer walk. -/
def CWalk.activityWeight (w : Q') (label : L.Plaquette → Rep) :
    {X Y : Polymer L} →
      CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y → Q'
  | _, _, .single X => activity w X label
  | X, _, .cons _ rest => activity w X label * rest.activityWeight w label

/-- The statically known starting vertex is the head of the vertex list. -/
theorem CWalk.start_mem_vertices :
    ∀ {α : Type} {edge : α → α → Bool} {x y : α}
      (p : CWalk edge x y), x ∈ p.vertices
  | _, _, _, _, .single _ => List.mem_cons_self
  | _, _, _, _, .cons _ _ => List.mem_cons_self

theorem CWalk.activityWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (p : CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y),
      (0 : Q') ≤ p.activityWeight w label
  | _, _, .single X => activity_nonneg hw X label
  | X, _, .cons _ rest => by
      unfold CWalk.activityWeight
      exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
        (CWalk.activityWeight_nonnegative hw label rest)

omit [DecidableEq L.Plaquette] in
/-- A selected nonnegative summand is bounded by the full explicit list sum. -/
theorem polymerWeightedSum_term_le
    (F : Polymer L → Q') (hF : ∀ X, (0 : Q') ≤ F X) :
    ∀ (Γ : List (Polymer L)) {X : Polymer L}, X ∈ Γ →
      F X ≤ polymerWeightedSum F Γ
  | [], X, hX => absurd hX List.not_mem_nil
  | A :: Γ, X, hX => by
      rcases List.mem_cons.mp hX with hXA | hXΓ
      · subst X
        exact Q'.add_le_self_of_nonneg _ _
          (polymerWeightedSum_nonnegative F hF Γ)
      · refine Q'.le_trans' _ _ _
          (polymerWeightedSum_term_le F hF Γ hXΓ) ?_
        refine Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _ (hF A)) ?_
        exact Q'.le_of_eqv
          (Q'.add_comm_eqv (polymerWeightedSum F Γ) (F A))

/-- A compatible restricted subfamily contributes its exact activity as a
summand of `XiR`. -/
theorem familyActivity_le_XiR_of_mem {w : Q'} (hw : (0 : Q') ≤ w)
    (qP : Polymer L → Bool) (Γ B : List (Polymer L))
    (label : L.Plaquette → Rep)
    (hBsub : B ∈ sublists Γ) (hBq : B.all qP = true)
    (hBcompat : familyCompatibleB B = true) :
    familyActivity w B label ≤ XiR w qP Γ label := by
  unfold XiR
  have hmem : B ∈ (sublists Γ).filter
      (fun S => S.all qP && familyCompatibleB S) := by
    apply List.mem_filter.mpr
    exact ⟨hBsub, (Bool.and_eq_true _ _).mpr ⟨hBq, hBcompat⟩⟩
  have hterm : ∀ (Fams : List (List (Polymer L)))
      {C : List (Polymer L)}, C ∈ Fams →
      familyActivity w C label ≤ polySum w label Fams := by
    intro Fams
    induction Fams with
    | nil => intro C hC; exact absurd hC List.not_mem_nil
    | cons A Fams ih =>
      intro C hC
      rw [polySum_cons]
      rcases List.mem_cons.mp hC with hCA | hrest
      · subst C
        exact Q'.add_le_self_of_nonneg _ _ (polySum_nonneg hw label Fams)
      · refine Q'.le_trans' _ _ _ (ih hrest) ?_
        refine Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _
            (familyActivity_nonneg hw A label)) ?_
        exact Q'.le_of_eqv
          (Q'.add_comm_eqv (polySum w label Fams)
            (familyActivity w A label))
  exact hterm _ hmem

/-- The terminal stratum is present at every fuel depth. -/
theorem chainWalkTerminal_le_chainWalkFrom {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (bg : Polymer L → Bool)
    (X : Polymer L) :
    ∀ fuel : Nat,
      chainWalkTerminal w qP b2 bg Γ label X ≤
        chainWalkFrom w qP b2 Γ label fuel bg X
  | 0 => Q'.le_refl' _
  | fuel + 1 => by
      unfold chainWalkFrom
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (activity_nonneg hw X label)
          (polymerWeightedSum_nonnegative _ (fun Y => by
            split
            · exact chainWalkFrom_nonnegative hw qP b2 Γ label fuel
                (fun T => bg T && compatibleB X T) Y
            · exact Q'.le_refl' _) Γ))

/-- The exact activity of one incompatibility walk, dressed by a compatible
background family compatible with every walk vertex, is a term of the
fuel-bounded walk carrier. -/
theorem walk_term_le_chainWalkFrom {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ B : List (Polymer L))
    (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (p : CWalk (fun A C : Polymer L => !(compatibleB A C)) X Y)
      (fuel : Nat) (bg : Polymer L → Bool),
      p.vertices.length ≤ fuel →
      (∀ Z, Z ∈ p.vertices → Z ∈ Γ) →
      (∀ Z, Z ∈ p.vertices → qP Z = true) →
      b2 Y = true →
      B ∈ sublists Γ →
      familyCompatibleB B = true →
      B.all qP = true →
      B.all bg = true →
      (∀ Z, Z ∈ p.vertices → ∀ T, T ∈ B →
        compatibleB Z T = true) →
      p.activityWeight w label * familyActivity w B label ≤
        chainWalkFrom w qP b2 Γ label fuel bg X
  | X, _, .single _, fuel, bg, _, _, hq, hb2, hBsub, hBcompat,
      hBq, hBbg, hBpath => by
      have hqX : qP X = true := hq X List.mem_cons_self
      have hBX : B.all (fun T => (qP T && bg T) && compatibleB X T) = true := by
        apply List.all_eq_true.mpr
        intro T hTB
        have hqT := List.all_eq_true.mp hBq T hTB
        have hbgT := List.all_eq_true.mp hBbg T hTB
        have hcT := hBpath X List.mem_cons_self T hTB
        simp [hqT, hbgT, hcT]
      have hterm :
          CWalk.activityWeight w label (CWalk.single X) *
              familyActivity w B label ≤
            chainWalkTerminal w qP b2 bg Γ label X := by
        unfold CWalk.activityWeight chainWalkTerminal
        simp only [hqX, hb2, Bool.true_and, if_true]
        exact Q'.mul_le_mul_of_nonneg_left _ _ _
          (familyActivity_le_XiR_of_mem hw
            (fun T => (qP T && bg T) && compatibleB X T)
            Γ B label hBsub hBX hBcompat)
          (activity_nonneg hw X label)
      exact Q'.le_trans' _ _ _ hterm
        (chainWalkTerminal_le_chainWalkFrom hw qP b2 Γ label bg X fuel)
  | X, Y, .cons hXY rest, fuel, bg, hlen, hmem, hq, hb2,
      hBsub, hBcompat, hBq, hBbg, hBpath => by
      cases fuel with
      | zero => simp [CWalk.vertices] at hlen
      | succ fuel =>
          have hqX : qP X = true := hq X List.mem_cons_self
          have hmemNext : rest.start ∈ Γ :=
            hmem rest.start (List.mem_cons_of_mem _
              (CWalk.start_mem_vertices rest))
          have hlenRest : rest.vertices.length ≤ fuel := by
            simpa [CWalk.vertices] using hlen
          have hBbg' : B.all (fun T => bg T && compatibleB X T) = true := by
            apply List.all_eq_true.mpr
            intro T hTB
            have hbgT := List.all_eq_true.mp hBbg T hTB
            have hcT := hBpath X List.mem_cons_self T hTB
            simp [hbgT, hcT]
          have ih := walk_term_le_chainWalkFrom hw qP b2 Γ B label rest
            fuel (fun T => bg T && compatibleB X T) hlenRest
            (fun Z hZ => hmem Z (List.mem_cons_of_mem _ hZ))
            (fun Z hZ => hq Z (List.mem_cons_of_mem _ hZ)) hb2
            hBsub hBcompat hBq hBbg'
            (fun Z hZ T hTB =>
              hBpath Z (List.mem_cons_of_mem _ hZ) T hTB)
          let F : Polymer L → Q' := fun Z =>
            if qP Z && !(compatibleB X Z) then
              chainWalkFrom w qP b2 Γ label fuel
                (fun T => bg T && compatibleB X T) Z
            else 0
          have hFnonneg : ∀ Z, (0 : Q') ≤ F Z := by
            intro Z
            unfold F
            split
            · exact chainWalkFrom_nonnegative hw qP b2 Γ label fuel
                (fun T => bg T && compatibleB X T) Z
            · exact Q'.le_refl' _
          have hchoose : F rest.start =
              chainWalkFrom w qP b2 Γ label fuel
                (fun T => bg T && compatibleB X T) rest.start := by
            have hqNext : qP rest.start = true :=
              hq rest.start (List.mem_cons_of_mem _
                (CWalk.start_mem_vertices rest))
            have hincNext : (!(compatibleB X rest.start)) = true := by
              simpa using hXY
            have hcond : (qP rest.start &&
                !(compatibleB X rest.start)) = true :=
              (Bool.and_eq_true _ _).mpr ⟨hqNext, hincNext⟩
            unfold F
            rw [if_pos hcond]
          have hsum : rest.activityWeight w label *
              familyActivity w B label ≤ polymerWeightedSum F Γ := by
            have ih' : rest.activityWeight w label *
                familyActivity w B label ≤
                chainWalkFrom w qP b2 Γ label fuel
                  (fun T => bg T && compatibleB X T) rest.start := by
              simpa using ih
            refine Q'.le_trans' _ _ _ ih' ?_
            rw [← hchoose]
            exact polymerWeightedSum_term_le F hFnonneg Γ hmemNext
          have hscaled : activity w X label *
                (rest.activityWeight w label * familyActivity w B label) ≤
              activity w X label * polymerWeightedSum F Γ :=
            Q'.mul_le_mul_of_nonneg_left _ _ _ hsum
              (activity_nonneg hw X label)
          have hassoc :
              (activity w X label * rest.activityWeight w label) *
                  familyActivity w B label ≤
                activity w X label *
                  (rest.activityWeight w label * familyActivity w B label) :=
            Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)
          refine Q'.le_trans' _ _ _ (by
              simpa [CWalk.activityWeight] using hassoc)
            (Q'.le_trans' _ _ _ hscaled ?_)
          unfold chainWalkFrom
          change activity w X label * polymerWeightedSum F Γ ≤
            chainWalkTerminal w qP b2 bg Γ label X +
              activity w X label * polymerWeightedSum F Γ
          refine Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg _ _
              (chainWalkTerminal_nonnegative hw qP b2 bg Γ label X)) ?_
          exact Q'.le_of_eqv
            (Q'.add_comm_eqv
              (activity w X label * polymerWeightedSum F Γ)
              (chainWalkTerminal w qP b2 bg Γ label X))

/-- A bounded incompatibility path with marked start and bad endpoint,
dressed by an admissible compatible background, lies termwise in the full
connecting-chain majorant. -/
theorem walk_term_le_connectingChainMajorant {w : Q'}
    (hw : (0 : Q') ≤ w) (qP b1 b2 : Polymer L → Bool)
    (Γ B : List (Polymer L)) (label : L.Plaquette → Rep)
    {X Y : Polymer L}
    (p : CWalk (fun A C : Polymer L => !(compatibleB A C)) X Y)
    (hlen : p.vertices.length ≤ Γ.length)
    (hmem : ∀ Z, Z ∈ p.vertices → Z ∈ Γ)
    (hq : ∀ Z, Z ∈ p.vertices → qP Z = true)
    (hb1 : b1 X = true) (hb2 : b2 Y = true)
    (hBsub : B ∈ sublists Γ) (hBcompat : familyCompatibleB B = true)
    (hBq : B.all qP = true)
    (hBpath : ∀ Z, Z ∈ p.vertices → ∀ T, T ∈ B →
      compatibleB Z T = true) :
    p.activityWeight w label * familyActivity w B label ≤
      connectingChainMajorant w qP b1 b2 Γ label := by
  have hqX : qP X = true := hq X (CWalk.start_mem_vertices p)
  have hXmem : X ∈ Γ := hmem X (CWalk.start_mem_vertices p)
  have hwalk := walk_term_le_chainWalkFrom hw qP b2 Γ B label p Γ.length
    (fun _ => true) hlen hmem hq hb2 hBsub hBcompat hBq
    (by
      apply List.all_eq_true.mpr
      intro T _
      rfl)
    hBpath
  let F : Polymer L → Q' := fun Z =>
    if qP Z && b1 Z then
      chainWalkFrom w qP b2 Γ label Γ.length (fun _ => true) Z
    else 0
  have hFnonneg : ∀ Z, (0 : Q') ≤ F Z := by
    intro Z
    unfold F
    split
    · exact chainWalkFrom_nonnegative hw qP b2 Γ label Γ.length
        (fun _ => true) Z
    · exact Q'.le_refl' _
  have hchoose : F X =
      chainWalkFrom w qP b2 Γ label Γ.length (fun _ => true) X := by
    unfold F
    simp [hqX, hb1]
  unfold connectingChainMajorant
  refine Q'.le_trans' _ _ _ hwalk ?_
  rw [← hchoose]
  exact polymerWeightedSum_term_le F hFnonneg Γ hXmem

#print axioms CWalk.dropTo_nodup
#print axioms CWalk.start_eq
#print axioms CWalk.start_mem_vertices
#print axioms CWalk.all_vertices_of_start
#print axioms CWalk.end_of_start
#print axioms FiniteListBound.removeFirst_length
#print axioms FiniteListBound.mem_removeFirst
#print axioms FiniteListBound.nodup_subset_length_le
#print axioms disagreementEdge_bounds
#print axioms reverseOccurrencePathOfReach
#print axioms CWalk.activityWeight_nonnegative
#print axioms polymerWeightedSum_term_le
#print axioms familyActivity_le_XiR_of_mem
#print axioms chainWalkTerminal_le_chainWalkFrom
#print axioms walk_term_le_chainWalkFrom
#print axioms walk_term_le_connectingChainMajorant

end YMGap.Continuum.XiExceptionalPathExtraction
