/-
# Finite disagreement-component switching for restricted polymer pairs

The one-ended determinant in `XiOneEndedInfluence` is naturally indexed by
pairs `(S,T)` of compatible subfamilies.  This file constructs, without
choice, the disagreement component reached from the left polymers which are
incompatible with the external head.  Vertices are side-tagged: a polymer in
the left family and the same polymer in the right family are different
vertices.

Reachability is computed by a finite Warshall closure on the explicit vertex
list.  The closure is proved sound for an inductive directed walk and closed
under every alternating incompatibility edge.  Swapping the reached left and
right pieces is weight preserving.  If the reached right component contains
no marked polymer, the switched left family has exactly the predicates needed
by the opposite product in the one-ended determinant and both output families
remain compatible.

This is the finite pair-switching substrate.  The remaining summation lemma is
to separate pairs whose reached component contains a mark, encode their
certified alternating walk in the head-rooted carrier, and prove injectivity of
the resulting family-pair map.  No such global domination is assumed here.
-/

import YMGap.Continuum.XiOneEndedInfluence

namespace YMGap.Continuum.XiPairSwitching

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiOneEndedInfluence

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. A finite, constructive transitive closure -/

/-- A directed walk, with reflexive and transitive constructors exposed as
data.  `edge` remains Boolean so a closed witness computes. -/
inductive DWalk {α : Type} (edge : α → α → Bool) : α → α → Type
  | refl (x : α) : DWalk edge x x
  | edge {x y : α} : edge x y = true → DWalk edge x y
  | trans {x y z : α} : DWalk edge x y → DWalk edge y z → DWalk edge x z

/-- Warshall closure through the explicitly listed intermediate vertices.
The empty-list base already contains equality and a single directed edge. -/
def warshall [DecidableEq α] (edge : α → α → Bool) :
    List α → α → α → Bool
  | [], x, y => decide (x = y) || edge x y
  | k :: ks, x, y =>
      warshall edge ks x y ||
        (warshall edge ks x k && warshall edge ks k y)

theorem warshall_refl [DecidableEq α] (edge : α → α → Bool) :
    ∀ (U : List α) (x : α), warshall edge U x x = true
  | [], x => by simp [warshall]
  | _ :: ks, x => by
      unfold warshall
      rw [warshall_refl edge ks x]
      rfl

theorem warshall_edge [DecidableEq α] (edge : α → α → Bool)
    {x y : α} (hxy : edge x y = true) :
    ∀ U : List α, warshall edge U x y = true
  | [] => by simp [warshall, hxy]
  | _ :: ks => by
      unfold warshall
      rw [warshall_edge edge hxy ks]
      rfl

/-- Warshall truth carries an actual finite directed walk. -/
def warshallSound [DecidableEq α] (edge : α → α → Bool) :
    ∀ (U : List α) (x y : α),
      warshall edge U x y = true → DWalk edge x y
  | [], x, y, h => by
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y := of_decide_eq_true heq
          subst y
          exact DWalk.refl x
      | false =>
          have hedge : edge x y = true := by
            simpa [warshall, heq] using h
          exact DWalk.edge hedge
  | k :: ks, x, y, h => by
      cases hdirect : warshall edge ks x y with
      | true => exact warshallSound edge ks x y hdirect
      | false =>
          cases hxk : warshall edge ks x k with
          | false => simp [warshall, hdirect, hxk] at h
          | true =>
              cases hky : warshall edge ks k y with
              | false => simp [warshall, hdirect, hxk, hky] at h
              | true =>
                  exact DWalk.trans (warshallSound edge ks x _ hxk)
                    (warshallSound edge ks _ y hky)

/-- A Warshall closure is transitive at every intermediate vertex which was
included in its finite universe. -/
theorem warshall_trans_of_mem [DecidableEq α] (edge : α → α → Bool) :
    ∀ (U : List α) (x y z : α), y ∈ U →
      warshall edge U x y = true → warshall edge U y z = true →
      warshall edge U x z = true
  | [], _, y, _, hy, _, _ => by cases hy
  | k :: ks, x, y, z, hy, hxy, hyz => by
      unfold warshall at hxy hyz ⊢
      rcases List.mem_cons.mp hy with hky | hyks
      · subst y
        rcases (Bool.or_eq_true _ _).mp hxy with hxk | hxk'
        · have hxk0 := hxk
          rcases (Bool.or_eq_true _ _).mp hyz with hkz | hkz'
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk0, hkz⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk0,
                ((Bool.and_eq_true _ _).mp hkz').2⟩))
        · have hxk0 := ((Bool.and_eq_true _ _).mp hxk').1
          rcases (Bool.or_eq_true _ _).mp hyz with hkz | hkz'
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk0, hkz⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk0,
                ((Bool.and_eq_true _ _).mp hkz').2⟩))
      · rcases (Bool.or_eq_true _ _).mp hxy with hxy0 | hxyk
        · rcases (Bool.or_eq_true _ _).mp hyz with hyz0 | hyzk
          · exact (Bool.or_eq_true _ _).mpr (Or.inl
              (warshall_trans_of_mem edge ks x y z hyks hxy0 hyz0))
          · rcases (Bool.and_eq_true _ _).mp hyzk with ⟨hyk, hkz⟩
            have hxk := warshall_trans_of_mem edge ks x y k hyks hxy0 hyk
            exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk, hkz⟩))
        · rcases (Bool.and_eq_true _ _).mp hxyk with ⟨hxk, hky⟩
          rcases (Bool.or_eq_true _ _).mp hyz with hyz0 | hyzk
          · have hkz := warshall_trans_of_mem edge ks k y z hyks hky hyz0
            exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk, hkz⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr ⟨hxk,
                ((Bool.and_eq_true _ _).mp hyzk).2⟩))

/-! ## 2. The side-tagged disagreement graph -/

/-- Side-tagged vertices prevent a left occurrence and a right occurrence of
the same polymer value from being silently identified. -/
inductive SwitchVertex (α : Type)
  | root
  | left (x : α)
  | right (x : α)
deriving DecidableEq

def switchUniverse (S T : List (Polymer L)) :
    List (SwitchVertex (Polymer L)) :=
  .root :: (S.map SwitchVertex.left ++ T.map SwitchVertex.right)

/-- Directed alternating edges.  The root points to precisely the left
polymers which fail the external-head compatibility predicate `c`. -/
def switchEdge (S T : List (Polymer L)) (c : Polymer L → Bool) :
    SwitchVertex (Polymer L) → SwitchVertex (Polymer L) → Bool
  | .root, .left X => decide (X ∈ S) && !(c X)
  | .left X, .right Y =>
      (decide (X ∈ S) && decide (Y ∈ T)) && !(compatibleB X Y)
  | .right Y, .left X =>
      (decide (Y ∈ T) && decide (X ∈ S)) && !(compatibleB Y X)
  | _, _ => false

def switchReach (S T : List (Polymer L)) (c : Polymer L → Bool)
    (v : SwitchVertex (Polymer L)) : Bool :=
  warshall (switchEdge S T c) (switchUniverse S T) .root v

def reachedLeft (S T : List (Polymer L)) (c : Polymer L → Bool)
    (X : Polymer L) : Bool :=
  switchReach S T c (.left X)

def reachedRight (S T : List (Polymer L)) (c : Polymer L → Bool)
    (Y : Polymer L) : Bool :=
  switchReach S T c (.right Y)

omit [DecidableEq L.Plaquette] in
theorem eq_false_of_not_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a <;> simp at h ⊢

theorem left_mem_switchUniverse (S T : List (Polymer L)) {X : Polymer L}
    (hX : X ∈ S) : SwitchVertex.left X ∈ switchUniverse S T := by
  unfold switchUniverse
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨X, hX, rfl⟩

theorem right_mem_switchUniverse (S T : List (Polymer L)) {Y : Polymer L}
    (hY : Y ∈ T) : SwitchVertex.right Y ∈ switchUniverse S T := by
  unfold switchUniverse
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨Y, hY, rfl⟩

/-- Every head-incompatible left polymer is in the reached component. -/
theorem bad_left_reached (S T : List (Polymer L))
    (c : Polymer L → Bool) {X : Polymer L}
    (hX : X ∈ S) (hcX : (!(c X)) = true) :
    reachedLeft S T c X = true := by
  unfold reachedLeft switchReach
  apply warshall_edge
  have hc0 : c X = false := eq_false_of_not_true hcX
  simp [switchEdge, hX, hc0]

/-- Reachedness is closed across a left-to-right incompatibility edge. -/
theorem reachedRight_of_left_edge (S T : List (Polymer L))
    (c : Polymer L → Bool) {X Y : Polymer L}
    (hX : X ∈ S) (hY : Y ∈ T)
    (hreach : reachedLeft S T c X = true)
    (hinc : (!(compatibleB X Y)) = true) :
    reachedRight S T c Y = true := by
  unfold reachedLeft switchReach at hreach
  unfold reachedRight switchReach
  apply warshall_trans_of_mem (switchEdge S T c) (switchUniverse S T)
    .root (.left X) (.right Y) (left_mem_switchUniverse S T hX) hreach
  apply warshall_edge
  have hi0 : compatibleB X Y = false := eq_false_of_not_true hinc
  simp [switchEdge, hX, hY, hi0]

/-- Reachedness is closed across a right-to-left incompatibility edge. -/
theorem reachedLeft_of_right_edge (S T : List (Polymer L))
    (c : Polymer L → Bool) {X Y : Polymer L}
    (hX : X ∈ S) (hY : Y ∈ T)
    (hreach : reachedRight S T c Y = true)
    (hinc : (!(compatibleB Y X)) = true) :
    reachedLeft S T c X = true := by
  unfold reachedRight switchReach at hreach
  unfold reachedLeft switchReach
  apply warshall_trans_of_mem (switchEdge S T c) (switchUniverse S T)
    .root (.right Y) (.left X) (right_mem_switchUniverse S T hY) hreach
  apply warshall_edge
  have hi0 : compatibleB Y X = false := eq_false_of_not_true hinc
  simp [switchEdge, hY, hX, hi0]

/-- A reached right endpoint comes with an actual alternating directed walk
from the root, rather than only a Boolean connectivity claim. -/
def reachedRightWalk (S T : List (Polymer L))
    (c : Polymer L → Bool) (Y : Polymer L)
    (hY : reachedRight S T c Y = true) :
    DWalk (switchEdge S T c) SwitchVertex.root (SwitchVertex.right Y) :=
  warshallSound (switchEdge S T c) (switchUniverse S T)
    .root (.right Y) hY

/-! ## 3. The occurrence-mask involution

The list-valued switch below is convenient for compatibility proofs, but an
injection between `sublists Γ` must retain occurrence identities and ambient
order.  Boolean masks do exactly that. -/

/-- The canonical ambient-order subfamily selected by a Boolean occurrence
mask. -/
def maskFamilyFrom (Γ : List (Polymer L)) (mask : Nat → Bool) :
    Nat → List (Polymer L)
  | _i =>
      match Γ with
      | [] => []
      | X :: Λ =>
          if mask _i then X :: maskFamilyFrom Λ mask (_i + 1)
          else maskFamilyFrom Λ mask (_i + 1)
termination_by Γ.length

def maskFamily (Γ : List (Polymer L)) (mask : Nat → Bool) :
    List (Polymer L) := maskFamilyFrom Γ mask 0

/-- Multiplicative weight of an occurrence mask.  A missing occurrence
contributes the explicit unit factor; hence pointwise mask swapping is exact
up to the `Q'` setoid. -/
def maskWeightFrom (w : Q') (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (mask : Nat → Bool) : Nat → Q'
  | _i =>
      match Γ with
      | [] => 1
      | X :: Λ =>
          (if mask _i then activity w X label else 1) *
            maskWeightFrom w Λ label mask (_i + 1)
termination_by Γ.length

def maskWeight (w : Q') (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (mask : Nat → Bool) : Q' :=
  maskWeightFrom w Γ label mask 0

/-- Swap the two occupation bits on the selected occurrence component. -/
def swapLeftMask (cut left right : Nat → Bool) (i : Nat) : Bool :=
  if cut i then right i else left i

def swapRightMask (cut left right : Nat → Bool) (i : Nat) : Bool :=
  if cut i then left i else right i

omit [DecidableEq L.Plaquette] in
theorem swapMasks_involutive_left (cut left right : Nat → Bool) (i : Nat) :
    swapLeftMask cut (swapLeftMask cut left right)
        (swapRightMask cut left right) i = left i := by
  cases hc : cut i <;> simp [swapLeftMask, swapRightMask, hc]

omit [DecidableEq L.Plaquette] in
theorem swapMasks_involutive_right (cut left right : Nat → Bool) (i : Nat) :
    swapRightMask cut (swapLeftMask cut left right)
        (swapRightMask cut left right) i = right i := by
  cases hc : cut i <;> simp [swapLeftMask, swapRightMask, hc]

/- A fixed occurrence cut gives an injective switch on pairs of masks.  This
is the exact finite injection primitive; the remaining global step is to show
that the disagreement component is recoverable from the switched pair with
the reverse orientation. -/
theorem swapMasks_pair_injective (cut left₁ right₁ left₂ right₂ : Nat → Bool)
    (hleft : ∀ i,
      swapLeftMask cut left₁ right₁ i = swapLeftMask cut left₂ right₂ i)
    (hright : ∀ i,
      swapRightMask cut left₁ right₁ i = swapRightMask cut left₂ right₂ i) :
    (∀ i, left₁ i = left₂ i) ∧ (∀ i, right₁ i = right₂ i) := by
  constructor
  · intro i
    cases hc : cut i with
    | false => simpa [swapLeftMask, hc] using hleft i
    | true => simpa [swapRightMask, hc] using hright i
  · intro i
    cases hc : cut i with
    | false => simpa [swapRightMask, hc] using hright i
    | true => simpa [swapLeftMask, hc] using hleft i

/-- Every occurrence mask selects an actual member of the explicit
`sublists Γ` enumeration. -/
theorem maskFamilyFrom_mem_sublists (mask : Nat → Bool) :
    ∀ (Γ : List (Polymer L)) (i : Nat),
      maskFamilyFrom Γ mask i ∈ sublists Γ
  | [], i => by simp [maskFamilyFrom, sublists]
  | X :: Λ, i => by
      rw [sublists_cons]
      cases hm : mask i with
      | false =>
          apply List.mem_append_left
          simpa [maskFamilyFrom, hm] using
            maskFamilyFrom_mem_sublists mask Λ (i + 1)
      | true =>
          apply List.mem_append_right
          apply List.mem_map.mpr
          exact ⟨maskFamilyFrom Λ mask (i + 1),
            maskFamilyFrom_mem_sublists mask Λ (i + 1), by simp [maskFamilyFrom, hm]⟩

theorem maskFamily_mem_sublists (Γ : List (Polymer L)) (mask : Nat → Bool) :
    maskFamily Γ mask ∈ sublists Γ :=
  maskFamilyFrom_mem_sublists mask Γ 0

/-- Mask weights agree with the ordinary family activity of the selected
ambient-order subfamily. -/
theorem maskWeightFrom_eqv_familyActivity (w : Q')
    (label : L.Plaquette → Rep) (mask : Nat → Bool) :
    ∀ (Γ : List (Polymer L)) (i : Nat),
      maskWeightFrom w Γ label mask i ≈
        familyActivity w (maskFamilyFrom Γ mask i) label
  | [], i => by
      simp only [maskWeightFrom, maskFamilyFrom, familyActivity_nil]
      exact Q'.eqv_refl _
  | X :: Λ, i => by
      cases hm : mask i with
      | false =>
          simp only [maskWeightFrom, hm, ↓reduceIte, maskFamilyFrom]
          refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
          exact maskWeightFrom_eqv_familyActivity w label mask Λ (i + 1)
      | true =>
          simp only [maskWeightFrom, hm, ↓reduceIte, maskFamilyFrom,
            familyActivity_cons]
          exact Q'.mul_eqv_congr_left _ _ _
            (maskWeightFrom_eqv_familyActivity w label mask Λ (i + 1))

theorem maskWeight_eqv_familyActivity (w : Q')
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (mask : Nat → Bool) :
    maskWeight w Γ label mask ≈ familyActivity w (maskFamily Γ mask) label :=
  maskWeightFrom_eqv_familyActivity w label mask Γ 0

omit [DecidableEq L.Plaquette] in
private theorem pair_scale_same (a b L R S T : Q') (h : L * R ≈ S * T) :
    (a * L) * (b * R) ≈ (a * S) * (b * T) := by
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * b) _ _ h) ?_)
  · ring_qeqv
  · ring_qeqv

omit [DecidableEq L.Plaquette] in
private theorem pair_scale_swap (a b L R S T : Q') (h : L * R ≈ S * T) :
    (b * L) * (a * R) ≈ (a * S) * (b * T) := by
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * b) _ _ h) ?_)
  · ring_qeqv
  · ring_qeqv

/-- The occurrence-mask switch preserves the complete pair weight exactly.
This is the injective, order-retaining counterpart of the family-list
identity `switch_weight_preserved` below. -/
theorem maskWeight_swap_preserved_from (w : Q')
    (label : L.Plaquette → Rep) (cut left right : Nat → Bool) :
    ∀ (Γ : List (Polymer L)) (i : Nat),
      maskWeightFrom w Γ label (swapLeftMask cut left right) i *
          maskWeightFrom w Γ label (swapRightMask cut left right) i ≈
        maskWeightFrom w Γ label left i *
          maskWeightFrom w Γ label right i
  | [], i => by
      simp only [maskWeightFrom]
      exact Q'.eqv_refl _
  | X :: Λ, i => by
      simp only [maskWeightFrom]
      cases hc : cut i with
      | false =>
          simp only [swapLeftMask, swapRightMask, hc, Bool.false_eq_true,
            ↓reduceIte]
          exact pair_scale_same _ _ _ _ _ _
            (maskWeight_swap_preserved_from w label cut left right Λ (i + 1))
      | true =>
          simp only [swapLeftMask, swapRightMask, hc, ↓reduceIte]
          exact pair_scale_swap _ _ _ _ _ _
            (maskWeight_swap_preserved_from w label cut left right Λ (i + 1))

theorem maskWeight_swap_preserved (w : Q')
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (cut left right : Nat → Bool) :
    maskWeight w Γ label (swapLeftMask cut left right) *
        maskWeight w Γ label (swapRightMask cut left right) ≈
      maskWeight w Γ label left * maskWeight w Γ label right :=
  maskWeight_swap_preserved_from w label cut left right Γ 0

/-! ## 4. Exact activity preservation under component switching -/

def switchLeft (S T : List (Polymer L)) (cutS cutT : Polymer L → Bool) :
    List (Polymer L) :=
  S.filter (fun X => !(cutS X)) ++ T.filter cutT

def switchRight (S T : List (Polymer L)) (cutS cutT : Polymer L → Bool) :
    List (Polymer L) :=
  T.filter (fun X => !(cutT X)) ++ S.filter cutS

theorem familyActivity_append (w : Q') (label : L.Plaquette → Rep) :
    ∀ A B : List (Polymer L),
      familyActivity w (A ++ B) label ≈
        familyActivity w A label * familyActivity w B label
  | [], B => by
      show familyActivity w B label ≈ 1 * familyActivity w B label
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | X :: A, B => by
      show activity w X label * familyActivity w (A ++ B) label ≈
        (activity w X label * familyActivity w A label) *
          familyActivity w B label
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (familyActivity_append w label A B)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- Filtering a family into the false and true cells preserves its total
activity exactly. -/
theorem familyActivity_filter_partition (w : Q')
    (label : L.Plaquette → Rep) (cut : Polymer L → Bool) :
    ∀ S : List (Polymer L),
      familyActivity w S label ≈
        familyActivity w (S.filter (fun X => !(cut X))) label *
          familyActivity w (S.filter cut) label
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | X :: S => by
      rw [List.filter_cons, List.filter_cons]
      cases hcut : cut X with
      | false =>
          rw [if_pos (by simp [hcut]), if_neg (by simp [hcut])]
          simp only [familyActivity_cons]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (familyActivity_filter_partition w label cut S)) ?_
          exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      | true =>
          rw [if_neg (by simp [hcut]), if_pos (by simp [hcut])]
          simp only [familyActivity_cons]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (familyActivity_filter_partition w label cut S)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
          exact Q'.mul_assoc_eqv _ _ _

theorem mul_eqv_congr_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Swapping any side-tagged cut preserves the product of the two family
activities.  No reachability assumption is needed for this algebraic fact. -/
theorem switch_weight_preserved (w : Q')
    (label : L.Plaquette → Rep) (S T : List (Polymer L))
    (cutS cutT : Polymer L → Bool) :
    familyActivity w (switchLeft S T cutS cutT) label *
        familyActivity w (switchRight S T cutS cutT) label ≈
      familyActivity w S label * familyActivity w T label := by
  unfold switchLeft switchRight
  have hL := familyActivity_append w label
    (S.filter (fun X => !(cutS X))) (T.filter cutT)
  have hR := familyActivity_append w label
    (T.filter (fun X => !(cutT X))) (S.filter cutS)
  have hS := familyActivity_filter_partition w label cutS S
  have hT := familyActivity_filter_partition w label cutT T
  refine Q'.eqv_trans _ _ _ (mul_eqv_congr_both hL hR) ?_
  refine Q'.eqv_trans _ _ _ ?_ (mul_eqv_congr_both
    (Q'.eqv_symm hS) (Q'.eqv_symm hT))
  ring_qeqv

/-! ## 4. Compatibility and predicate validity of a closed switch -/

omit [DecidableEq L.Plaquette] in
theorem all_filter_of_all {p q : Polymer L → Bool} {S : List (Polymer L)}
    (h : S.all q = true) : (S.filter p).all q = true := by
  apply List.all_eq_true.mpr
  intro X hX
  exact List.all_eq_true.mp h X (List.mem_filter.mp hX).1

omit [DecidableEq L.Plaquette] in
theorem all_append_of_all {q : Polymer L → Bool} {A B : List (Polymer L)}
    (hA : A.all q = true) (hB : B.all q = true) :
    (A ++ B).all q = true := by
  apply List.all_eq_true.mpr
  intro X hX
  rcases List.mem_append.mp hX with hXA | hXB
  · exact List.all_eq_true.mp hA X hXA
  · exact List.all_eq_true.mp hB X hXB

theorem familyCompatibleB_filter {p : Polymer L → Bool}
    {S : List (Polymer L)} (hS : familyCompatibleB S = true) :
    familyCompatibleB (S.filter p) = true := by
  induction S with
  | nil => rfl
  | cons X S ih =>
      rw [familyCompatibleB_cons] at hS
      rcases (Bool.and_eq_true _ _).mp hS with ⟨hXS, hS⟩
      rw [List.filter_cons]
      cases hp : p X with
      | false =>
          simp only [hp, Bool.false_eq_true, ↓reduceIte]
          exact ih hS
      | true =>
          simp only [hp, ↓reduceIte, familyCompatibleB_cons]
          exact (Bool.and_eq_true _ _).mpr
            ⟨all_filter_of_all hXS, ih hS⟩

/-- Two compatible families with every cross pair compatible have compatible
append. -/
theorem familyCompatibleB_append {A B : List (Polymer L)}
    (hA : familyCompatibleB A = true)
    (hB : familyCompatibleB B = true)
    (hcross : ∀ X, X ∈ A → ∀ Y, Y ∈ B → compatibleB X Y = true) :
    familyCompatibleB (A ++ B) = true := by
  induction A with
  | nil => exact hB
  | cons X A ih =>
      rw [familyCompatibleB_cons] at hA
      rcases (Bool.and_eq_true _ _).mp hA with ⟨hXA, hA⟩
      rw [List.cons_append, familyCompatibleB_cons]
      apply (Bool.and_eq_true _ _).mpr
      constructor
      · apply List.all_eq_true.mpr
        intro Y hY
        rcases List.mem_append.mp hY with hYA | hYB
        · exact List.all_eq_true.mp hXA Y hYA
        · exact hcross X (List.mem_cons_self) Y hYB
      · exact ih hA (fun U hU V hV =>
          hcross U (List.mem_cons_of_mem X hU) V hV)

/-- Hard-core compatibility is symmetric even though `compatibleB` scans its
left input. -/
theorem compatibleB_symm (X Y : Polymer L) :
    compatibleB X Y = compatibleB Y X := by
  unfold compatibleB
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hXY
    apply List.all_eq_true.mpr
    intro y hy
    cases hmem : decide (y ∈ X) with
    | false => rfl
    | true =>
        have hyX : y ∈ X := of_decide_eq_true hmem
        have hnot := List.all_eq_true.mp hXY y hyX
        rw [decide_eq_true hy] at hnot
        exact absurd hnot (by decide)
  · intro hYX
    apply List.all_eq_true.mpr
    intro x hx
    cases hmem : decide (x ∈ Y) with
    | false => rfl
    | true =>
        have hxY : x ∈ Y := of_decide_eq_true hmem
        have hnot := List.all_eq_true.mp hYX x hxY
        rw [decide_eq_true hx] at hnot
        exact absurd hnot (by decide)

/-- If a Boolean cut is closed under both alternating edge directions, then
the two switched families remain internally compatible. -/
theorem switch_compatible
    (S T : List (Polymer L)) (cutS cutT : Polymer L → Bool)
    (hS : familyCompatibleB S = true)
    (hT : familyCompatibleB T = true)
    (hcloseLR : ∀ X, X ∈ S → ∀ Y, Y ∈ T →
      cutS X = true → (!(compatibleB X Y)) = true → cutT Y = true)
    (hcloseRL : ∀ X, X ∈ S → ∀ Y, Y ∈ T →
      cutT Y = true → (!(compatibleB Y X)) = true → cutS X = true) :
    familyCompatibleB (switchLeft S T cutS cutT) = true ∧
      familyCompatibleB (switchRight S T cutS cutT) = true := by
  constructor
  · unfold switchLeft
    apply familyCompatibleB_append (familyCompatibleB_filter hS)
      (familyCompatibleB_filter hT)
    intro X hX Y hY
    rcases List.mem_filter.mp hX with ⟨hXS, hnotX⟩
    rcases List.mem_filter.mp hY with ⟨hYT, hcutY⟩
    cases hcomp : compatibleB X Y with
    | true => rfl
    | false =>
        have hsymm : compatibleB Y X = false := by
          rw [← compatibleB_symm X Y, hcomp]
        have hcutX := hcloseRL X hXS Y hYT hcutY (by simp [hsymm])
        rw [hcutX] at hnotX
        exact absurd hnotX (by decide)
  · unfold switchRight
    apply familyCompatibleB_append (familyCompatibleB_filter hT)
      (familyCompatibleB_filter hS)
    intro Y hY X hX
    rcases List.mem_filter.mp hY with ⟨hYT, hnotY⟩
    rcases List.mem_filter.mp hX with ⟨hXS, hcutX⟩
    cases hcomp : compatibleB Y X with
    | true => rfl
    | false =>
        have hsymm : compatibleB X Y = false := by
          rw [compatibleB_symm X Y, hcomp]
        have hcutY := hcloseLR X hXS Y hYT hcutX (by simp [hsymm])
        rw [hcutY] at hnotY
        exact absurd hnotY (by decide)

/-- The finite reached component supplies the closure hypotheses required by
`switch_compatible`. -/
theorem reached_switch_compatible (S T : List (Polymer L))
    (c : Polymer L → Bool)
    (hS : familyCompatibleB S = true)
    (hT : familyCompatibleB T = true) :
    familyCompatibleB
        (switchLeft S T (reachedLeft S T c) (reachedRight S T c)) = true ∧
      familyCompatibleB
        (switchRight S T (reachedLeft S T c) (reachedRight S T c)) = true :=
  switch_compatible S T _ _ hS hT
    (fun X hX Y hY hreach hinc =>
      reachedRight_of_left_edge S T c hX hY hreach hinc)
    (fun X hX Y hY hreach hinc =>
      reachedLeft_of_right_edge S T c hX hY hreach hinc)

/-- In the nonexceptional branch (no reached right polymer is marked), the
switched left family satisfies `q ∧ ¬b ∧ c`, while the switched right family
satisfies `q`.  These are exactly the two factors of `oneEndedRight`. -/
theorem reached_switch_predicates
    (S T : List (Polymer L)) (q b c : Polymer L → Bool)
    (hSq : S.all q = true) (hSavoid : S.all (fun X => !(b X)) = true)
    (hTq : T.all q = true) (hTc : T.all c = true)
    (hnoMarkedReach : ∀ Y, Y ∈ T → reachedRight S T c Y = true →
      (!(b Y)) = true) :
    (switchLeft S T (reachedLeft S T c) (reachedRight S T c)).all
        (fun X => (q X && !(b X)) && c X) = true ∧
      (switchRight S T (reachedLeft S T c) (reachedRight S T c)).all q = true := by
  constructor
  · apply List.all_eq_true.mpr
    intro X hX
    rcases List.mem_append.mp hX with hXS | hXT
    · rcases List.mem_filter.mp hXS with ⟨hXS, hnotReach⟩
      have hq := List.all_eq_true.mp hSq X hXS
      have hb := List.all_eq_true.mp hSavoid X hXS
      have hc : c X = true := by
        cases hcX : c X with
        | true => rfl
        | false =>
            have hr := bad_left_reached S T c hXS (by simp [hcX])
            rw [hr] at hnotReach
            exact absurd hnotReach (by decide)
      simp [hq, hb, hc]
    · rcases List.mem_filter.mp hXT with ⟨hXT, hreach⟩
      have hq := List.all_eq_true.mp hTq X hXT
      have hb := hnoMarkedReach X hXT hreach
      have hc := List.all_eq_true.mp hTc X hXT
      have hb0 : b X = false := eq_false_of_not_true hb
      simp [hq, hb0, hc]
  · unfold switchRight
    exact all_append_of_all (all_filter_of_all hTq) (all_filter_of_all hSq)

/-! ## 5. The complete finite pair-switch package -/

/-- Every nonexceptional pair in the left one-ended product has a
weight-preserving image in the right one-ended product.  All fields are
explicit: exact activity preservation, both compatibility checks, and both
predicate checks. -/
theorem nonexceptional_pair_switch
    (w : Q') (label : L.Plaquette → Rep)
    (S T : List (Polymer L)) (q b c : Polymer L → Bool)
    (hScompat : familyCompatibleB S = true)
    (hTcompat : familyCompatibleB T = true)
    (hSq : S.all q = true) (hSavoid : S.all (fun X => !(b X)) = true)
    (hTq : T.all q = true) (hTc : T.all c = true)
    (hnoMarkedReach : ∀ Y, Y ∈ T → reachedRight S T c Y = true →
      (!(b Y)) = true) :
    let U := switchLeft S T (reachedLeft S T c) (reachedRight S T c)
    let V := switchRight S T (reachedLeft S T c) (reachedRight S T c)
    familyActivity w U label * familyActivity w V label ≈
        familyActivity w S label * familyActivity w T label ∧
      familyCompatibleB U = true ∧ familyCompatibleB V = true ∧
      U.all (fun X => (q X && !(b X)) && c X) = true ∧
      V.all q = true := by
  dsimp only
  have hw := switch_weight_preserved w label S T
    (reachedLeft S T c) (reachedRight S T c)
  have hc := reached_switch_compatible S T c hScompat hTcompat
  have hp := reached_switch_predicates S T q b c hSq hSavoid hTq hTc
    hnoMarkedReach
  exact ⟨hw, hc.1, hc.2, hp.1, hp.2⟩

/-- In the exceptional branch, a marked reached right polymer carries an
actual alternating path from a bad left seed to that mark. -/
def exceptional_pair_reach
    (S T : List (Polymer L)) (b c : Polymer L → Bool)
    (Y : Polymer L) (_hYT : Y ∈ T)
    (_hbY : b Y = true) (hreach : reachedRight S T c Y = true) :
    DWalk (switchEdge S T c) SwitchVertex.root (SwitchVertex.right Y) :=
  reachedRightWalk S T c Y hreach

/-! ## 6. Exact orientation fence -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p0 : TL.Plaquette := (0, 0)
private def X0 : Polymer TL := [p0]
private def singleLeft : List (Polymer TL) := [X0]
private def noRight : List (Polymer TL) := []
private def cFalse : Polymer TL → Bool := fun _ => false

/-- Re-running the forward-oriented reachability search after a switch is
false even for the one-vertex component: the bad left seed has moved to the
right.  Thus a proof which claims that the forward cut is literally preserved
has the wrong involution orientation. -/
theorem forward_orientation_not_preserved_on_singleton :
    reachedLeft singleLeft noRight cFalse X0 = true ∧
      reachedLeft
        (switchLeft singleLeft noRight
          (reachedLeft singleLeft noRight cFalse)
          (reachedRight singleLeft noRight cFalse))
        (switchRight singleLeft noRight
          (reachedLeft singleLeft noRight cFalse)
          (reachedRight singleLeft noRight cFalse))
        cFalse X0 = false := by
  unfold reachedLeft reachedRight switchReach switchUniverse switchEdge
    switchLeft switchRight singleLeft noRight cFalse X0 p0 warshall
  decide

/-- The reverse orientation recovers the singleton component: after the
switch, the new right family is used as the left/source family of the reverse
search. -/
theorem reverse_orientation_recovers_singleton :
    let U := switchLeft singleLeft noRight
      (reachedLeft singleLeft noRight cFalse)
      (reachedRight singleLeft noRight cFalse)
    let V := switchRight singleLeft noRight
      (reachedLeft singleLeft noRight cFalse)
      (reachedRight singleLeft noRight cFalse)
    reachedLeft V U cFalse X0 = true := by
  dsimp only
  unfold reachedLeft reachedRight switchReach switchUniverse switchEdge
    switchLeft switchRight singleLeft noRight cFalse X0 p0 warshall
  decide

#print axioms warshall_refl
#print axioms warshall_edge
#print axioms warshallSound
#print axioms warshall_trans_of_mem
#print axioms eq_false_of_not_true
#print axioms left_mem_switchUniverse
#print axioms right_mem_switchUniverse
#print axioms bad_left_reached
#print axioms reachedRight_of_left_edge
#print axioms reachedLeft_of_right_edge
#print axioms reachedRightWalk
#print axioms swapMasks_involutive_left
#print axioms swapMasks_involutive_right
#print axioms swapMasks_pair_injective
#print axioms maskFamilyFrom_mem_sublists
#print axioms maskFamily_mem_sublists
#print axioms maskWeightFrom_eqv_familyActivity
#print axioms maskWeight_eqv_familyActivity
#print axioms maskWeight_swap_preserved_from
#print axioms maskWeight_swap_preserved
#print axioms familyActivity_append
#print axioms familyActivity_filter_partition
#print axioms mul_eqv_congr_both
#print axioms switch_weight_preserved
#print axioms all_filter_of_all
#print axioms all_append_of_all
#print axioms familyCompatibleB_filter
#print axioms familyCompatibleB_append
#print axioms compatibleB_symm
#print axioms switch_compatible
#print axioms reached_switch_compatible
#print axioms reached_switch_predicates
#print axioms nonexceptional_pair_switch
#print axioms exceptional_pair_reach
#print axioms forward_orientation_not_preserved_on_singleton
#print axioms reverse_orientation_recovers_singleton

end YMGap.Continuum.XiPairSwitching
