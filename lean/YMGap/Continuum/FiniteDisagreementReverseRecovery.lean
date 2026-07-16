/-
# Reverse recovery of a finite disagreement component

For an arbitrary duplicate-free ambient atom list, two occupation masks define
left-only and right-only occurrences.  The untagged disagreement graph joins
opposite exclusive occurrences whose atoms are incompatible.  A forward root
selects bad left-only atoms.  Switching the entire reached component leaves
this graph unchanged; a reverse search from bad right-only atoms in the output
therefore recovers exactly the original cut.

The compatibility relation and masks are parameters.  No polymer-specific or
overlap-only convention is built into this theorem.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching
import YMGap.Continuum.Z4CanonicalBipartitePath

namespace YMGap.Continuum.FiniteDisagreementReverseRecovery

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath

variable {A : Type} [DecidableEq A]

/-! ## 1. Boolean disagreement algebra -/

def leftOnly (left right : Bool) : Bool := left && !right
def rightOnly (left right : Bool) : Bool := !left && right

def disagreementBits
    (leftI rightI leftJ rightJ conflict : Bool) : Bool :=
  ((leftOnly leftI rightI && rightOnly leftJ rightJ) ||
    (rightOnly leftI rightI && leftOnly leftJ rightJ)) && conflict

def swapBit (cut left right : Bool) : Bool :=
  if cut then right else left

def differentBits (left right : Bool) : Bool :=
  (left && !right) || (!left && right)

theorem disagreementBits_swap_invariant
    (leftI rightI leftJ rightJ cutI cutJ conflict : Bool)
    (hleft : ((leftI && leftJ) && conflict) = false)
    (hright : ((rightI && rightJ) && conflict) = false)
    (hclosed : (disagreementBits leftI rightI leftJ rightJ conflict &&
      differentBits cutI cutJ) = false) :
    disagreementBits
        (swapBit cutI leftI rightI) (swapBit cutI rightI leftI)
        (swapBit cutJ leftJ rightJ) (swapBit cutJ rightJ leftJ)
        conflict =
      disagreementBits leftI rightI leftJ rightJ conflict := by
  cases leftI <;> cases rightI <;> cases leftJ <;> cases rightJ <;>
    cases cutI <;> cases cutJ <;> cases conflict <;>
    simp_all [disagreementBits, leftOnly, rightOnly, swapBit,
      differentBits]

theorem sameSide_guard (left right conflict : Bool)
    (h : left = true → right = true → conflict = false) :
    ((left && right) && conflict) = false := by
  cases left with
  | false => rfl
  | true =>
      cases right with
      | false => rfl
      | true => rw [h rfl rfl]; rfl

theorem closedCut_guard (edge cutLeft cutRight : Bool)
    (h : edge = true → cutLeft = cutRight) :
    (edge && differentBits cutLeft cutRight) = false := by
  cases edge with
  | false => rfl
  | true =>
      have hsame := h rfl
      subst cutRight
      cases cutLeft <;> rfl

/-! ## 2. Ambient-guarded disagreement reachability -/

def disagreementEdge (ambient : List A)
    (compat : A → A → Bool)
    (left right : A → Bool) (first second : A) : Bool :=
  (memberB ambient first && memberB ambient second) &&
    disagreementBits (left first) (right first)
      (left second) (right second) (!(compat first second))

def forwardSeed (ambient : List A)
    (left right bad : A → Bool) (atom : A) : Bool :=
  memberB ambient atom &&
    (leftOnly (left atom) (right atom) && bad atom)

def reverseSeed (ambient : List A)
    (left right bad : A → Bool) (atom : A) : Bool :=
  memberB ambient atom &&
    (rightOnly (left atom) (right atom) && bad atom)

inductive ReachVertex (A : Type)
  | root
  | atom : A → ReachVertex A
deriving DecidableEq

def reachEdge (seed : A → Bool) (edge : A → A → Bool) :
    ReachVertex A → ReachVertex A → Bool
  | .root, .atom atom => seed atom
  | .atom first, .atom second => edge first second
  | _, _ => false

def reachUniverse (ambient : List A) : List (ReachVertex A) :=
  .root :: ambient.map ReachVertex.atom

def reachComponent (ambient : List A)
    (seed : A → Bool) (edge : A → A → Bool)
    (atom : A) : Bool :=
  warshall (reachEdge seed edge) (reachUniverse ambient)
    .root (.atom atom)

def forwardComponent (ambient : List A)
    (compat : A → A → Bool)
    (left right bad : A → Bool) (atom : A) : Bool :=
  reachComponent ambient (forwardSeed ambient left right bad)
    (disagreementEdge ambient compat left right) atom

def reverseComponent (ambient : List A)
    (compat : A → A → Bool)
    (left right bad : A → Bool) (atom : A) : Bool :=
  reachComponent ambient (reverseSeed ambient left right bad)
    (disagreementEdge ambient compat left right) atom

theorem atom_mem_reachUniverse (ambient : List A)
    {atom : A} (hatom : atom ∈ ambient) :
    ReachVertex.atom atom ∈ reachUniverse ambient := by
  unfold reachUniverse
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨atom, hatom, rfl⟩

theorem disagreementEdge_symm
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right : A → Bool) (first second : A) :
    disagreementEdge ambient compat left right first second =
      disagreementEdge ambient compat left right second first := by
  unfold disagreementEdge disagreementBits leftOnly rightOnly
  rw [hsymm first second]
  cases memberB ambient first <;> cases memberB ambient second <;>
    cases left first <;> cases right first <;>
    cases left second <;> cases right second <;>
    cases compat second first <;> rfl

theorem forwardSeed_reached
    (ambient : List A) (compat : A → A → Bool)
    (left right bad : A → Bool) {atom : A}
    (hseed : forwardSeed ambient left right bad atom = true) :
    forwardComponent ambient compat left right bad atom = true := by
  unfold forwardComponent reachComponent
  apply warshall_edge
  exact hseed

theorem component_closed_right
    (ambient : List A) (compat : A → A → Bool)
    (left right bad : A → Bool) {first second : A}
    (hreach : forwardComponent ambient compat left right bad first = true)
    (hedge : disagreementEdge ambient compat left right first second = true) :
    forwardComponent ambient compat left right bad second = true := by
  have hfirstB : memberB ambient first = true :=
    ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp hedge).1).1
  have hfirst : first ∈ ambient :=
    (memberB_eq_true_iff _ _).1 hfirstB
  unfold forwardComponent reachComponent at hreach ⊢
  apply warshall_trans_of_mem
    (reachEdge (forwardSeed ambient left right bad)
      (disagreementEdge ambient compat left right))
    (reachUniverse ambient) .root (.atom first) (.atom second)
    (atom_mem_reachUniverse ambient hfirst) hreach
  apply warshall_edge
  exact hedge

theorem component_closed_left
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right bad : A → Bool) {first second : A}
    (hreach : forwardComponent ambient compat left right bad second = true)
    (hedge : disagreementEdge ambient compat left right first second = true) :
    forwardComponent ambient compat left right bad first = true := by
  exact component_closed_right ambient compat left right bad hreach
    (by rw [← disagreementEdge_symm ambient compat hsymm
      left right first second]; exact hedge)

theorem component_cut_closed
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right bad : A → Bool) {first second : A}
    (hedge : disagreementEdge ambient compat left right first second = true) :
    forwardComponent ambient compat left right bad first =
      forwardComponent ambient compat left right bad second := by
  cases hfirst : forwardComponent ambient compat left right bad first with
  | true =>
      rw [component_closed_right ambient compat left right bad hfirst hedge]
  | false =>
      cases hsecond : forwardComponent ambient compat left right bad second with
      | false => rfl
      | true =>
          have hreach := component_closed_left ambient compat hsymm
            left right bad hsecond hedge
          rw [hfirst] at hreach
          exact False.elim (Bool.false_ne_true hreach)

/-! ## 3. Graph invariance and reverse recovery -/

def switchedLeft (ambient : List A)
    (compat : A → A → Bool)
    (left right bad : A → Bool) : A → Bool :=
  swapLeftMask (forwardComponent ambient compat left right bad)
    left right

def switchedRight (ambient : List A)
    (compat : A → A → Bool)
    (left right bad : A → Bool) : A → Bool :=
  swapRightMask (forwardComponent ambient compat left right bad)
    left right

theorem disagreementEdge_switch_invariant
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right bad : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (first second : A) :
    disagreementEdge ambient compat
        (switchedLeft ambient compat left right bad)
        (switchedRight ambient compat left right bad) first second =
      disagreementEdge ambient compat left right first second := by
  unfold disagreementEdge switchedLeft switchedRight
    swapLeftMask swapRightMask
  cases hfirstAmbient : memberB ambient first with
  | false => simp [hfirstAmbient]
  | true =>
      cases hsecondAmbient : memberB ambient second with
      | false => simp [hfirstAmbient, hsecondAmbient]
      | true =>
          simp only [hfirstAmbient, hsecondAmbient, Bool.true_and]
          cases heq : decide (first = second) with
          | true =>
              have hsame : first = second := of_decide_eq_true heq
              subst second
              unfold disagreementBits leftOnly rightOnly
              cases left first <;> cases right first <;>
                cases forwardComponent ambient compat left right bad first <;>
                cases compat first first <;> rfl
          | false =>
              have hne : first ≠ second := of_decide_eq_false heq
              apply disagreementBits_swap_invariant
              · apply sameSide_guard
                intro hfirst hsecond
                rw [hleft first second hne hfirst hsecond]
                rfl
              · apply sameSide_guard
                intro hfirst hsecond
                rw [hright first second hne hfirst hsecond]
                rfl
              · apply closedCut_guard
                intro hedge
                apply component_cut_closed ambient compat hsymm left right bad
                exact (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                    ⟨hfirstAmbient, hsecondAmbient⟩, hedge⟩

theorem reverseSeed_switch_eq_forwardSeed
    (ambient : List A) (compat : A → A → Bool)
    (left right bad : A → Bool)
    (hrightGood : ∀ atom, right atom = true → bad atom = false)
    (atom : A) :
    reverseSeed ambient
        (switchedLeft ambient compat left right bad)
        (switchedRight ambient compat left right bad) bad atom =
      forwardSeed ambient left right bad atom := by
  unfold reverseSeed forwardSeed switchedLeft switchedRight
    swapLeftMask swapRightMask
  cases hambient : memberB ambient atom with
  | false => simp [hambient]
  | true =>
      simp only [hambient, Bool.true_and]
      cases hleft : left atom <;> cases hright : right atom <;>
        cases hbad : bad atom <;>
        cases hcut : forwardComponent ambient compat left right bad atom <;>
        simp_all [leftOnly, rightOnly]
      have hseed : forwardSeed ambient left right bad atom = true := by
        simp [forwardSeed, hambient, leftOnly, hleft, hright, hbad]
      have hreach := forwardSeed_reached
        ambient compat left right bad hseed
      rw [hcut] at hreach
      exact False.elim (Bool.false_ne_true hreach)

theorem reachEdge_reverse_eq
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right bad : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (hrightGood : ∀ atom, right atom = true → bad atom = false) :
    reachEdge
        (reverseSeed ambient
          (switchedLeft ambient compat left right bad)
          (switchedRight ambient compat left right bad) bad)
        (disagreementEdge ambient compat
          (switchedLeft ambient compat left right bad)
          (switchedRight ambient compat left right bad)) =
      reachEdge (forwardSeed ambient left right bad)
        (disagreementEdge ambient compat left right) := by
  funext source target
  cases source <;> cases target
  · rfl
  · exact reverseSeed_switch_eq_forwardSeed
      ambient compat left right bad hrightGood _
  · rfl
  · exact disagreementEdge_switch_invariant
      ambient compat hsymm left right bad hleft hright _ _

/-- Reverse-oriented reachability on the switched masks recovers the complete
source-dependent forward component at every atom. -/
theorem reverse_component_recovers
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right bad : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (hrightGood : ∀ atom, right atom = true → bad atom = false)
    (atom : A) :
    reverseComponent ambient compat
        (switchedLeft ambient compat left right bad)
        (switchedRight ambient compat left right bad) bad atom =
      forwardComponent ambient compat left right bad atom := by
  unfold reverseComponent forwardComponent reachComponent
  rw [reachEdge_reverse_eq ambient compat hsymm left right bad
    hleft hright hrightGood]

/-- The component switch is injective even though its cut depends on the
source pair.  The output pair determines the cut by reverse reachability;
with that cut fixed, the pointwise bit swap is its own inverse. -/
theorem component_switched_masks_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (bad left₁ right₁ left₂ right₂ : A → Bool)
    (hleft₁ : ∀ first second, first ≠ second →
      left₁ first = true → left₁ second = true →
      compat first second = true)
    (hright₁ : ∀ first second, first ≠ second →
      right₁ first = true → right₁ second = true →
      compat first second = true)
    (hrightGood₁ : ∀ atom, right₁ atom = true → bad atom = false)
    (hleft₂ : ∀ first second, first ≠ second →
      left₂ first = true → left₂ second = true →
      compat first second = true)
    (hright₂ : ∀ first second, first ≠ second →
      right₂ first = true → right₂ second = true →
      compat first second = true)
    (hrightGood₂ : ∀ atom, right₂ atom = true → bad atom = false)
    (hleftOutput :
      switchedLeft ambient compat left₁ right₁ bad =
        switchedLeft ambient compat left₂ right₂ bad)
    (hrightOutput :
      switchedRight ambient compat left₁ right₁ bad =
        switchedRight ambient compat left₂ right₂ bad) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hcut :
      forwardComponent ambient compat left₁ right₁ bad =
        forwardComponent ambient compat left₂ right₂ bad := by
    funext atom
    rw [← reverse_component_recovers ambient compat hsymm
      left₁ right₁ bad hleft₁ hright₁ hrightGood₁ atom]
    rw [← reverse_component_recovers ambient compat hsymm
      left₂ right₂ bad hleft₂ hright₂ hrightGood₂ atom]
    rw [hleftOutput, hrightOutput]
  have hbits : ∀ atom,
      left₁ atom = left₂ atom ∧ right₁ atom = right₂ atom := by
    intro atom
    have hleftAt := congrFun hleftOutput atom
    have hrightAt := congrFun hrightOutput atom
    have hcutAt := congrFun hcut atom
    cases hcut₁ : forwardComponent ambient compat left₁ right₁ bad atom <;>
      cases hcut₂ : forwardComponent ambient compat left₂ right₂ bad atom <;>
      simp_all [switchedLeft, switchedRight, swapLeftMask, swapRightMask]
  constructor
  · funext atom
    exact (hbits atom).1
  · funext atom
    exact (hbits atom).2

/-! ## 4. Literal ambient-family form -/

/-- The source-dependent component switch returned as a literal subfamily of
the ambient atom enumeration. -/
def componentSwitchedLeft (ambient : List A) (compat : A → A → Bool)
    (bad : A → Bool) (left right : List A) : List A :=
  FiniteCompatibilitySwitching.switchedLeft ambient
    (forwardComponent ambient compat (memberB left) (memberB right) bad)
    left right

def componentSwitchedRight (ambient : List A) (compat : A → A → Bool)
    (bad : A → Bool) (left right : List A) : List A :=
  FiniteCompatibilitySwitching.switchedRight ambient
    (forwardComponent ambient compat (memberB left) (memberB right) bad)
    left right

theorem componentSwitchedLeft_mask
    (ambient : List A) (compat : A → A → Bool)
    (bad : A → Bool) {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (componentSwitchedLeft ambient compat bad left right) =
      switchedLeft ambient compat (memberB left) (memberB right) bad := by
  unfold componentSwitchedLeft
  rw [memberB_switchedLeft_eq ambient _ hleft hright]
  rfl

theorem componentSwitchedRight_mask
    (ambient : List A) (compat : A → A → Bool)
    (bad : A → Bool) {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (componentSwitchedRight ambient compat bad left right) =
      switchedRight ambient compat (memberB left) (memberB right) bad := by
  unfold componentSwitchedRight
  rw [memberB_switchedRight_eq ambient _ hleft hright]
  rfl

/-- Literal-family injectivity for the source-dependent disagreement-component
switch.  Unlike fixed-cut injectivity, the two source pairs may induce
different forward cuts; equality of their outputs forces those cuts equal by
reverse recovery. -/
theorem component_switched_families_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (bad : A → Bool)
    {left₁ right₁ left₂ right₂ : List A}
    (hambient : ambient.Nodup)
    (hleftSub₁ : left₁ ∈ sublists ambient)
    (hrightSub₁ : right₁ ∈ sublists ambient)
    (hleftSub₂ : left₂ ∈ sublists ambient)
    (hrightSub₂ : right₂ ∈ sublists ambient)
    (hleftCompat₁ : familyCompatibleB compat left₁ = true)
    (hrightCompat₁ : familyCompatibleB compat right₁ = true)
    (hleftCompat₂ : familyCompatibleB compat left₂ = true)
    (hrightCompat₂ : familyCompatibleB compat right₂ = true)
    (hrightGood₁ : ∀ atom, memberB right₁ atom = true →
      bad atom = false)
    (hrightGood₂ : ∀ atom, memberB right₂ atom = true →
      bad atom = false)
    (hleftOutput :
      componentSwitchedLeft ambient compat bad left₁ right₁ =
        componentSwitchedLeft ambient compat bad left₂ right₂)
    (hrightOutput :
      componentSwitchedRight ambient compat bad left₁ right₁ =
        componentSwitchedRight ambient compat bad left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hleftPairs₁ : ∀ first second, first ≠ second →
      memberB left₁ first = true → memberB left₁ second = true →
      compat first second = true := by
    intro first second hne hfirst hsecond
    exact familyCompatibleB_pairwise compat hsymm hleftCompat₁
      ((memberB_eq_true_iff left₁ first).1 hfirst)
      ((memberB_eq_true_iff left₁ second).1 hsecond) hne
  have hrightPairs₁ : ∀ first second, first ≠ second →
      memberB right₁ first = true → memberB right₁ second = true →
      compat first second = true := by
    intro first second hne hfirst hsecond
    exact familyCompatibleB_pairwise compat hsymm hrightCompat₁
      ((memberB_eq_true_iff right₁ first).1 hfirst)
      ((memberB_eq_true_iff right₁ second).1 hsecond) hne
  have hleftPairs₂ : ∀ first second, first ≠ second →
      memberB left₂ first = true → memberB left₂ second = true →
      compat first second = true := by
    intro first second hne hfirst hsecond
    exact familyCompatibleB_pairwise compat hsymm hleftCompat₂
      ((memberB_eq_true_iff left₂ first).1 hfirst)
      ((memberB_eq_true_iff left₂ second).1 hsecond) hne
  have hrightPairs₂ : ∀ first second, first ≠ second →
      memberB right₂ first = true → memberB right₂ second = true →
      compat first second = true := by
    intro first second hne hfirst hsecond
    exact familyCompatibleB_pairwise compat hsymm hrightCompat₂
      ((memberB_eq_true_iff right₂ first).1 hfirst)
      ((memberB_eq_true_iff right₂ second).1 hsecond) hne
  have hleftMaskOutput :
      switchedLeft ambient compat (memberB left₁) (memberB right₁) bad =
        switchedLeft ambient compat (memberB left₂) (memberB right₂) bad := by
    rw [← componentSwitchedLeft_mask ambient compat bad
      hleftSub₁ hrightSub₁]
    rw [← componentSwitchedLeft_mask ambient compat bad
      hleftSub₂ hrightSub₂]
    rw [hleftOutput]
  have hrightMaskOutput :
      switchedRight ambient compat (memberB left₁) (memberB right₁) bad =
        switchedRight ambient compat (memberB left₂) (memberB right₂) bad := by
    rw [← componentSwitchedRight_mask ambient compat bad
      hleftSub₁ hrightSub₁]
    rw [← componentSwitchedRight_mask ambient compat bad
      hleftSub₂ hrightSub₂]
    rw [hrightOutput]
  have hmasks := component_switched_masks_injective
    ambient compat hsymm bad
    (memberB left₁) (memberB right₁)
    (memberB left₂) (memberB right₂)
    hleftPairs₁ hrightPairs₁ hrightGood₁
    hleftPairs₂ hrightPairs₂ hrightGood₂
    hleftMaskOutput hrightMaskOutput
  have hleftFilter₁ := filter_memberB_eq_of_mem_sublists
    hambient hleftSub₁
  have hrightFilter₁ := filter_memberB_eq_of_mem_sublists
    hambient hrightSub₁
  have hleftFilter₂ := filter_memberB_eq_of_mem_sublists
    hambient hleftSub₂
  have hrightFilter₂ := filter_memberB_eq_of_mem_sublists
    hambient hrightSub₂
  constructor
  · rw [← hleftFilter₁, ← hleftFilter₂, hmasks.1]
  · rw [← hrightFilter₁, ← hrightFilter₂, hmasks.2]

/-! ## 5. A single distinguished root without an auxiliary vertex

For a singleton event, the component may be rooted directly at the marked
atom.  This form is equivalent to the usual disagreement-component mechanism
on its intended domain, but exposes an ordinary atom-to-atom Warshall walk.
That makes geometric path extraction immediate in model-specific adapters.
-/

def rootedComponent (ambient : List A) (compat : A → A → Bool)
    (left right : A → Bool) (root atom : A) : Bool :=
  warshall (disagreementEdge ambient compat left right)
    ambient root atom

theorem rootedComponent_closed_right
    (ambient : List A) (compat : A → A → Bool)
    (left right : A → Bool) (root : A) {first second : A}
    (hreach : rootedComponent ambient compat left right root first = true)
    (hedge : disagreementEdge ambient compat left right first second = true) :
    rootedComponent ambient compat left right root second = true := by
  have hfirstB : memberB ambient first = true :=
    ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp hedge).1).1
  have hfirst : first ∈ ambient :=
    (memberB_eq_true_iff _ _).1 hfirstB
  unfold rootedComponent at hreach ⊢
  exact warshall_trans_of_mem
    (disagreementEdge ambient compat left right)
    ambient root first second hfirst hreach
    (warshall_edge _ hedge ambient)

theorem rootedComponent_closed_left
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right : A → Bool) (root : A) {first second : A}
    (hreach : rootedComponent ambient compat left right root second = true)
    (hedge : disagreementEdge ambient compat left right first second = true) :
    rootedComponent ambient compat left right root first = true := by
  exact rootedComponent_closed_right ambient compat left right root hreach
    (by rw [← disagreementEdge_symm ambient compat hsymm
      left right first second]; exact hedge)

theorem rootedComponent_cut_closed
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (left right : A → Bool) (root : A) {first second : A}
    (hedge : disagreementEdge ambient compat left right first second = true) :
    rootedComponent ambient compat left right root first =
      rootedComponent ambient compat left right root second := by
  cases hfirst : rootedComponent ambient compat left right root first with
  | true =>
      rw [rootedComponent_closed_right ambient compat left right root
        hfirst hedge]
  | false =>
      cases hsecond : rootedComponent ambient compat left right root second with
      | false => rfl
      | true =>
          have hreach := rootedComponent_closed_left ambient compat hsymm
            left right root hsecond hedge
          rw [hfirst] at hreach
          exact False.elim (Bool.false_ne_true hreach)

def rootedSwitchedLeft (ambient : List A) (compat : A → A → Bool)
    (root : A) (left right : A → Bool) : A → Bool :=
  swapLeftMask (rootedComponent ambient compat left right root)
    left right

def rootedSwitchedRight (ambient : List A) (compat : A → A → Bool)
    (root : A) (left right : A → Bool) : A → Bool :=
  swapRightMask (rootedComponent ambient compat left right root)
    left right

theorem disagreementEdge_rooted_switch_invariant
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (root : A) (left right : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (first second : A) :
    disagreementEdge ambient compat
        (rootedSwitchedLeft ambient compat root left right)
        (rootedSwitchedRight ambient compat root left right) first second =
      disagreementEdge ambient compat left right first second := by
  unfold disagreementEdge rootedSwitchedLeft rootedSwitchedRight
    swapLeftMask swapRightMask
  cases hfirstAmbient : memberB ambient first with
  | false => simp [hfirstAmbient]
  | true =>
      cases hsecondAmbient : memberB ambient second with
      | false => simp [hfirstAmbient, hsecondAmbient]
      | true =>
          simp only [hfirstAmbient, hsecondAmbient, Bool.true_and]
          cases heq : decide (first = second) with
          | true =>
              have hsame : first = second := of_decide_eq_true heq
              subst second
              unfold disagreementBits leftOnly rightOnly
              cases left first <;> cases right first <;>
                cases rootedComponent ambient compat left right root first <;>
                cases compat first first <;> rfl
          | false =>
              have hne : first ≠ second := of_decide_eq_false heq
              apply disagreementBits_swap_invariant
              · apply sameSide_guard
                intro hfirst hsecond
                rw [hleft first second hne hfirst hsecond]
                rfl
              · apply sameSide_guard
                intro hfirst hsecond
                rw [hright first second hne hfirst hsecond]
                rfl
              · apply closedCut_guard
                intro hedge
                apply rootedComponent_cut_closed ambient compat hsymm
                  left right root
                exact (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                    ⟨hfirstAmbient, hsecondAmbient⟩, hedge⟩

/-- The switched disagreement graph reconstructs the original rooted cut. -/
theorem rooted_component_recovers
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (root : A) (left right : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (atom : A) :
    rootedComponent ambient compat
        (rootedSwitchedLeft ambient compat root left right)
        (rootedSwitchedRight ambient compat root left right)
        root atom =
      rootedComponent ambient compat left right root atom := by
  unfold rootedComponent
  have hedge : disagreementEdge ambient compat
      (rootedSwitchedLeft ambient compat root left right)
      (rootedSwitchedRight ambient compat root left right) =
      disagreementEdge ambient compat left right := by
    funext first second
    exact disagreementEdge_rooted_switch_invariant
      ambient compat hsymm root left right hleft hright first second
  rw [hedge]

theorem rooted_component_switched_masks_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (root : A) (left₁ right₁ left₂ right₂ : A → Bool)
    (hleft₁ : ∀ first second, first ≠ second →
      left₁ first = true → left₁ second = true →
      compat first second = true)
    (hright₁ : ∀ first second, first ≠ second →
      right₁ first = true → right₁ second = true →
      compat first second = true)
    (hleft₂ : ∀ first second, first ≠ second →
      left₂ first = true → left₂ second = true →
      compat first second = true)
    (hright₂ : ∀ first second, first ≠ second →
      right₂ first = true → right₂ second = true →
      compat first second = true)
    (hleftOutput :
      rootedSwitchedLeft ambient compat root left₁ right₁ =
        rootedSwitchedLeft ambient compat root left₂ right₂)
    (hrightOutput :
      rootedSwitchedRight ambient compat root left₁ right₁ =
        rootedSwitchedRight ambient compat root left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hcut : rootedComponent ambient compat left₁ right₁ root =
      rootedComponent ambient compat left₂ right₂ root := by
    funext atom
    rw [← rooted_component_recovers ambient compat hsymm
      root left₁ right₁ hleft₁ hright₁ atom]
    rw [← rooted_component_recovers ambient compat hsymm
      root left₂ right₂ hleft₂ hright₂ atom]
    rw [hleftOutput, hrightOutput]
  have hbits : ∀ atom,
      left₁ atom = left₂ atom ∧ right₁ atom = right₂ atom := by
    intro atom
    have hleftAt := congrFun hleftOutput atom
    have hrightAt := congrFun hrightOutput atom
    have hcutAt := congrFun hcut atom
    cases hcut₁ : rootedComponent ambient compat left₁ right₁ root atom <;>
      cases hcut₂ : rootedComponent ambient compat left₂ right₂ root atom <;>
      simp_all [rootedSwitchedLeft, rootedSwitchedRight,
        swapLeftMask, swapRightMask]
  exact ⟨funext (fun atom => (hbits atom).1),
    funext (fun atom => (hbits atom).2)⟩

def rootedComponentSwitchedLeft (ambient : List A)
    (compat : A → A → Bool) (root : A)
    (left right : List A) : List A :=
  FiniteCompatibilitySwitching.switchedLeft ambient
    (rootedComponent ambient compat (memberB left) (memberB right) root)
    left right

def rootedComponentSwitchedRight (ambient : List A)
    (compat : A → A → Bool) (root : A)
    (left right : List A) : List A :=
  FiniteCompatibilitySwitching.switchedRight ambient
    (rootedComponent ambient compat (memberB left) (memberB right) root)
    left right

theorem rootedComponentSwitchedLeft_mask
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (rootedComponentSwitchedLeft ambient compat root left right) =
      rootedSwitchedLeft ambient compat root (memberB left) (memberB right) := by
  unfold rootedComponentSwitchedLeft
  rw [memberB_switchedLeft_eq ambient _ hleft hright]
  rfl

theorem rootedComponentSwitchedRight_mask
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (rootedComponentSwitchedRight ambient compat root left right) =
      rootedSwitchedRight ambient compat root (memberB left) (memberB right) := by
  unfold rootedComponentSwitchedRight
  rw [memberB_switchedRight_eq ambient _ hleft hright]
  rfl

theorem rooted_component_switched_families_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (root : A) {left₁ right₁ left₂ right₂ : List A}
    (hambient : ambient.Nodup)
    (hleftSub₁ : left₁ ∈ sublists ambient)
    (hrightSub₁ : right₁ ∈ sublists ambient)
    (hleftSub₂ : left₂ ∈ sublists ambient)
    (hrightSub₂ : right₂ ∈ sublists ambient)
    (hleftCompat₁ : familyCompatibleB compat left₁ = true)
    (hrightCompat₁ : familyCompatibleB compat right₁ = true)
    (hleftCompat₂ : familyCompatibleB compat left₂ = true)
    (hrightCompat₂ : familyCompatibleB compat right₂ = true)
    (hleftOutput :
      rootedComponentSwitchedLeft ambient compat root left₁ right₁ =
        rootedComponentSwitchedLeft ambient compat root left₂ right₂)
    (hrightOutput :
      rootedComponentSwitchedRight ambient compat root left₁ right₁ =
        rootedComponentSwitchedRight ambient compat root left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have pairwise : ∀ {family : List A},
      familyCompatibleB compat family = true →
      ∀ first second, first ≠ second →
        memberB family first = true → memberB family second = true →
        compat first second = true := by
    intro family hfamily first second hne hfirst hsecond
    exact familyCompatibleB_pairwise compat hsymm hfamily
      ((memberB_eq_true_iff _ _).1 hfirst)
      ((memberB_eq_true_iff _ _).1 hsecond) hne
  have hleftMaskOutput :
      rootedSwitchedLeft ambient compat root (memberB left₁) (memberB right₁) =
        rootedSwitchedLeft ambient compat root (memberB left₂) (memberB right₂) := by
    rw [← rootedComponentSwitchedLeft_mask ambient compat root
      hleftSub₁ hrightSub₁]
    rw [← rootedComponentSwitchedLeft_mask ambient compat root
      hleftSub₂ hrightSub₂]
    rw [hleftOutput]
  have hrightMaskOutput :
      rootedSwitchedRight ambient compat root (memberB left₁) (memberB right₁) =
        rootedSwitchedRight ambient compat root (memberB left₂) (memberB right₂) := by
    rw [← rootedComponentSwitchedRight_mask ambient compat root
      hleftSub₁ hrightSub₁]
    rw [← rootedComponentSwitchedRight_mask ambient compat root
      hleftSub₂ hrightSub₂]
    rw [hrightOutput]
  have hmasks := rooted_component_switched_masks_injective
    ambient compat hsymm root
    (memberB left₁) (memberB right₁)
    (memberB left₂) (memberB right₂)
    (pairwise hleftCompat₁) (pairwise hrightCompat₁)
    (pairwise hleftCompat₂) (pairwise hrightCompat₂)
    hleftMaskOutput hrightMaskOutput
  have hleftFilter₁ := filter_memberB_eq_of_mem_sublists
    hambient hleftSub₁
  have hrightFilter₁ := filter_memberB_eq_of_mem_sublists
    hambient hrightSub₁
  have hleftFilter₂ := filter_memberB_eq_of_mem_sublists
    hambient hleftSub₂
  have hrightFilter₂ := filter_memberB_eq_of_mem_sublists
    hambient hrightSub₂
  exact ⟨by rw [← hleftFilter₁, ← hleftFilter₂, hmasks.1],
    by rw [← hrightFilter₁, ← hrightFilter₂, hmasks.2]⟩

end YMGap.Continuum.FiniteDisagreementReverseRecovery

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.disagreementBits_swap_invariant
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.component_cut_closed
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.disagreementEdge_switch_invariant
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.reverse_component_recovers
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.component_switched_masks_injective
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.component_switched_families_injective
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.rooted_component_recovers
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.rooted_component_switched_masks_injective
#print axioms YMGap.Continuum.FiniteDisagreementReverseRecovery.rooted_component_switched_families_injective
