/-
# Reverse-oriented recovery of an occurrence disagreement component

`XiPairSwitching` proved that a fixed occurrence cut acts by an exact,
weight-preserving involution on pairs of masks, and banked the fact that the
forward-oriented cut is not recovered by re-running the forward search.  This
successor proves the corrected statement.

The disagreement graph is placed on ambient occurrence indices.  A vertex is
active exactly when it is occupied on one side only; two active vertices are
joined when they are on opposite sides and their polymers conflict.  The
forward roots are head-incompatible left-only occurrences.  Switching the
entire reached component leaves this untagged graph unchanged: reached edges
have both endpoints switched, and family compatibility forbids a new conflict
edge across the boundary.  The switched pair is searched in the reverse
orientation (head-incompatible right-only roots), recovering exactly the same
Boolean cut.

This closes the generic reverse-component residual.  Encoding an exceptional
marked recovered component into the existing weighted head-rooted walk carrier
is the next, separate summation step; it is not assumed here.
-/

import YMGap.Continuum.XiPairSwitching

namespace YMGap.Continuum.XiReverseComponentRecovery

open YMGap.Continuum.XiPairSwitching

/-! ## 1. Boolean disagreement cells -/

def leftOnly (left right : Bool) : Bool := left && !right

def rightOnly (left right : Bool) : Bool := !left && right

/-- An untagged disagreement edge: exclusive occupation at both endpoints,
opposite family sides, and a polymer conflict. -/
def disagreementBits (li ri lj rj conflict : Bool) : Bool :=
  ((leftOnly li ri && rightOnly lj rj) ||
    (rightOnly li ri && leftOnly lj rj)) && conflict

def swapBit (cut left right : Bool) : Bool :=
  if cut then right else left

def differentBits (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

theorem leftOnly_swap (cut left right : Bool) :
    leftOnly (swapBit cut left right) (swapBit cut right left) =
      if cut then rightOnly left right else leftOnly left right := by
  cases cut <;> cases left <;> cases right <;> rfl

theorem rightOnly_swap (cut left right : Bool) :
    rightOnly (swapBit cut left right) (swapBit cut right left) =
      if cut then leftOnly left right else rightOnly left right := by
  cases cut <;> cases left <;> cases right <;> rfl

/-- The scalar core of graph invariance.  Closure says an old disagreement
edge cannot cross the cut.  Independence says same-side occupied vertices
cannot conflict, which prevents switching one endpoint from creating a new
edge. -/
theorem disagreementBits_swap_invariant
    (li ri lj rj ci cj conflict : Bool)
    (hleft : ((li && lj) && conflict) = false)
    (hright : ((ri && rj) && conflict) = false)
    (hclosed : (disagreementBits li ri lj rj conflict &&
      differentBits ci cj) = false) :
    disagreementBits
        (swapBit ci li ri) (swapBit ci ri li)
        (swapBit cj lj rj) (swapBit cj rj lj) conflict =
      disagreementBits li ri lj rj conflict := by
  cases li <;> cases ri <;> cases lj <;> cases rj <;>
    cases ci <;> cases cj <;> cases conflict <;>
    simp_all [disagreementBits, leftOnly, rightOnly, swapBit, differentBits]

theorem sameSide_guard (a b conflict : Bool)
    (h : a = true → b = true → conflict = false) :
    ((a && b) && conflict) = false := by
  cases a with
  | false => rfl
  | true =>
      cases b with
      | false => rfl
      | true =>
          have hc := h rfl rfl
          rw [hc]
          rfl

theorem closedCut_guard (edge ci cj : Bool)
    (h : edge = true → ci = cj) :
    (edge && differentBits ci cj) = false := by
  cases edge with
  | false => rfl
  | true =>
      have hc := h rfl
      subst cj
      cases ci <;> rfl

/-! ## 2. The finite occurrence graph and its Warshall component -/

/-- Symmetrized conflict test; the underlying polymer `compatibleB` instance
will be substituted downstream. -/
def symConflict (inc : Nat → Nat → Bool) (i j : Nat) : Bool :=
  inc i j || inc j i

def disagreementEdge (N : Nat) (inc : Nat → Nat → Bool)
    (left right : Nat → Bool) (i j : Nat) : Bool :=
  (decide (i < N) && decide (j < N)) &&
    disagreementBits (left i) (right i) (left j) (right j)
      (symConflict inc i j)

def forwardSeed (N : Nat) (left right bad : Nat → Bool) (i : Nat) : Bool :=
  decide (i < N) && (leftOnly (left i) (right i) && bad i)

def reverseSeed (N : Nat) (left right bad : Nat → Bool) (i : Nat) : Bool :=
  decide (i < N) && (rightOnly (left i) (right i) && bad i)

/-- We reuse `SwitchVertex.root` and its `left i` constructor as, respectively,
the artificial root and the untagged occurrence vertex. -/
def occurrenceReachEdge (seed : Nat → Bool) (edge : Nat → Nat → Bool) :
    SwitchVertex Nat → SwitchVertex Nat → Bool
  | .root, .left i => seed i
  | .left i, .left j => edge i j
  | _, _ => false

def occurrenceUniverse (N : Nat) : List (SwitchVertex Nat) :=
  .root :: (List.range N).map SwitchVertex.left

def occurrenceComponent (N : Nat) (seed : Nat → Bool)
    (edge : Nat → Nat → Bool) (i : Nat) : Bool :=
  warshall (occurrenceReachEdge seed edge) (occurrenceUniverse N)
    .root (.left i)

def forwardComponent (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) (i : Nat) : Bool :=
  occurrenceComponent N (forwardSeed N left right bad)
    (disagreementEdge N inc left right) i

def reverseComponent (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) (i : Nat) : Bool :=
  occurrenceComponent N (reverseSeed N left right bad)
    (disagreementEdge N inc left right) i

theorem occurrence_mem_universe {N i : Nat} (hi : i < N) :
    SwitchVertex.left i ∈ occurrenceUniverse N := by
  unfold occurrenceUniverse
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem disagreementEdge_symm (N : Nat) (inc : Nat → Nat → Bool)
    (left right : Nat → Bool) (i j : Nat) :
    disagreementEdge N inc left right i j =
      disagreementEdge N inc left right j i := by
  unfold disagreementEdge symConflict disagreementBits leftOnly rightOnly
  cases decide (i < N) <;> cases decide (j < N) <;>
    cases left i <;> cases right i <;> cases left j <;> cases right j <;>
    cases inc i j <;> cases inc j i <;> rfl

theorem forwardSeed_reached (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) {i : Nat}
    (hseed : forwardSeed N left right bad i = true) :
    forwardComponent N inc left right bad i = true := by
  unfold forwardComponent occurrenceComponent
  apply warshall_edge
  exact hseed

theorem component_closed_right (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) {i j : Nat}
    (hreach : forwardComponent N inc left right bad i = true)
    (hedge : disagreementEdge N inc left right i j = true) :
    forwardComponent N inc left right bad j = true := by
  have hiB : decide (i < N) = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hedge).1).1
  have hi : i < N := of_decide_eq_true hiB
  unfold forwardComponent occurrenceComponent at hreach ⊢
  apply warshall_trans_of_mem
    (occurrenceReachEdge (forwardSeed N left right bad)
      (disagreementEdge N inc left right))
    (occurrenceUniverse N) .root (.left i) (.left j)
    (occurrence_mem_universe hi) hreach
  apply warshall_edge
  exact hedge

theorem component_closed_left (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) {i j : Nat}
    (hreach : forwardComponent N inc left right bad j = true)
    (hedge : disagreementEdge N inc left right i j = true) :
    forwardComponent N inc left right bad i = true := by
  exact component_closed_right N inc left right bad hreach
    (by rw [← disagreementEdge_symm N inc left right i j]; exact hedge)

theorem component_cut_closed (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) {i j : Nat}
    (hedge : disagreementEdge N inc left right i j = true) :
    forwardComponent N inc left right bad i =
      forwardComponent N inc left right bad j := by
  cases hi : forwardComponent N inc left right bad i with
  | true =>
      rw [component_closed_right N inc left right bad hi hedge]
  | false =>
      cases hj : forwardComponent N inc left right bad j with
      | false => rfl
      | true =>
          have := component_closed_left N inc left right bad hj hedge
          rw [hi] at this
          exact absurd this (by decide)

/-! ## 3. Graph and root invariance under the reached-component switch -/

def switchedLeft (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) : Nat → Bool :=
  swapLeftMask (forwardComponent N inc left right bad) left right

def switchedRight (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool) : Nat → Bool :=
  swapRightMask (forwardComponent N inc left right bad) left right

/-- Switching the reached component leaves the untagged disagreement graph
exactly unchanged. -/
theorem disagreementEdge_switch_invariant
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    (i j : Nat) :
    disagreementEdge N inc
        (switchedLeft N inc left right bad)
        (switchedRight N inc left right bad) i j =
      disagreementEdge N inc left right i j := by
  unfold disagreementEdge switchedLeft switchedRight swapLeftMask swapRightMask
  cases hiN : decide (i < N) with
  | false => simp [hiN]
  | true =>
      cases hjN : decide (j < N) with
      | false => simp [hiN, hjN]
      | true =>
          simp only [hiN, hjN, Bool.true_and]
          apply disagreementBits_swap_invariant
          · exact sameSide_guard _ _ _ (hleft i j)
          · exact sameSide_guard _ _ _ (hright i j)
          · exact closedCut_guard _ _ _ (fun hedge =>
              component_cut_closed N inc left right bad
                ((Bool.and_eq_true _ _).mpr ⟨
                  (Bool.and_eq_true _ _).mpr ⟨hiN, hjN⟩, hedge⟩))

/-- In the left-product domain, the right family is head-compatible; hence it
contains no bad occurrence.  Under that hypothesis, reverse roots of the
switched pair are exactly the original forward roots. -/
theorem reverseSeed_switch_eq_forwardSeed
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hrightGood : ∀ i, right i = true → bad i = false)
    (i : Nat) :
    reverseSeed N
        (switchedLeft N inc left right bad)
        (switchedRight N inc left right bad) bad i =
      forwardSeed N left right bad i := by
  unfold reverseSeed forwardSeed switchedLeft switchedRight
    swapLeftMask swapRightMask
  cases hiN : decide (i < N) with
  | false => simp [hiN]
  | true =>
      simp only [hiN, Bool.true_and]
      cases hl : left i <;> cases hr : right i <;> cases hb : bad i <;>
        cases hc : forwardComponent N inc left right bad i <;>
        simp_all [leftOnly, rightOnly]
      have hs : forwardSeed N left right bad i = true := by
        simp [forwardSeed, hiN, leftOnly, hl, hr, hb]
      have hreach := forwardSeed_reached N inc left right bad hs
      rw [hc] at hreach
      exact absurd hreach (by decide)

theorem occurrenceReachEdge_reverse_eq
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    (hrightGood : ∀ i, right i = true → bad i = false) :
    occurrenceReachEdge
        (reverseSeed N
          (switchedLeft N inc left right bad)
          (switchedRight N inc left right bad) bad)
        (disagreementEdge N inc
          (switchedLeft N inc left right bad)
          (switchedRight N inc left right bad)) =
      occurrenceReachEdge (forwardSeed N left right bad)
        (disagreementEdge N inc left right) := by
  funext u v
  cases u <;> cases v
  · rfl
  · exact reverseSeed_switch_eq_forwardSeed N inc left right bad hrightGood _
  · rfl
  · rfl
  · exact disagreementEdge_switch_invariant N inc left right bad
      hleft hright _ _
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## 4. Generic reverse-component recovery -/

/-- **Reverse recovery.**  Switching the forward disagreement component and
then searching from bad right-only occurrences returns exactly the original
component, at every occurrence index. -/
theorem reverse_component_recovers
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    (hrightGood : ∀ i, right i = true → bad i = false)
    (i : Nat) :
    reverseComponent N inc
        (switchedLeft N inc left right bad)
        (switchedRight N inc left right bad) bad i =
      forwardComponent N inc left right bad i := by
  unfold reverseComponent forwardComponent occurrenceComponent
  rw [occurrenceReachEdge_reverse_eq N inc left right bad
    hleft hright hrightGood]

#print axioms leftOnly_swap
#print axioms rightOnly_swap
#print axioms disagreementBits_swap_invariant
#print axioms sameSide_guard
#print axioms closedCut_guard
#print axioms occurrence_mem_universe
#print axioms disagreementEdge_symm
#print axioms forwardSeed_reached
#print axioms component_closed_right
#print axioms component_closed_left
#print axioms component_cut_closed
#print axioms disagreementEdge_switch_invariant
#print axioms reverseSeed_switch_eq_forwardSeed
#print axioms occurrenceReachEdge_reverse_eq
#print axioms reverse_component_recovers

end YMGap.Continuum.XiReverseComponentRecovery
