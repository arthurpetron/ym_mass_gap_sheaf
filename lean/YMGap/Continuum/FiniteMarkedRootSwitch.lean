/-
# Simultaneous switching of finitely many rooted disagreement components

For a finite list of marked atoms, take the union of every disagreement
component meeting that list and swap the two occupation masks on the union.
The union is a closed cut, so the disagreement graph is unchanged.  It can
therefore be reconstructed from the output pair, making the source-dependent
switch injective.  Every marked membership bit is swapped literally.

This is the realizable replacement for changing Boolean fingerprint
coordinates independently: several marked atoms in one connected component
are switched together, exactly as the hard-core geometry requires.
-/

import YMGap.Continuum.FiniteRootedSwitchFingerprint

namespace YMGap.Continuum.FiniteMarkedRootSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteRootedSwitchFingerprint
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath

variable {A : Type} [DecidableEq A]

/-- Union of the disagreement components rooted at the marked atoms. -/
def markedRootCut (ambient : List A) (compat : A → A → Bool)
    (roots : List A) (left right : A → Bool) (atom : A) : Bool :=
  roots.any (fun root =>
    rootedComponent ambient compat left right root atom)

def markedRootSwitchedLeft (ambient : List A)
    (compat : A → A → Bool) (roots : List A)
    (left right : A → Bool) : A → Bool :=
  swapLeftMask (markedRootCut ambient compat roots left right) left right

def markedRootSwitchedRight (ambient : List A)
    (compat : A → A → Bool) (roots : List A)
    (left right : A → Bool) : A → Bool :=
  swapRightMask (markedRootCut ambient compat roots left right) left right

/-- Every listed root belongs to the union cut by reflexive reachability. -/
theorem markedRootCut_true_of_mem
    (ambient : List A) (compat : A → A → Bool)
    (roots : List A) (left right : A → Bool) {root : A}
    (hroot : root ∈ roots) :
    markedRootCut ambient compat roots left right root = true := by
  unfold markedRootCut
  apply List.any_eq_true.mpr
  refine ⟨root, hroot, ?_⟩
  unfold rootedComponent
  exact warshall_refl _ _ root

/-- A union of graph components is constant across every disagreement edge. -/
theorem markedRootCut_closed
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (roots : List A) (left right : A → Bool)
    {first second : A}
    (hedge : disagreementEdge ambient compat left right first second = true) :
    markedRootCut ambient compat roots left right first =
      markedRootCut ambient compat roots left right second := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hfirst
    obtain ⟨root, hroot, hreach⟩ := List.any_eq_true.mp hfirst
    apply List.any_eq_true.mpr
    refine ⟨root, hroot, ?_⟩
    rw [← rootedComponent_cut_closed ambient compat hsymm
      left right root hedge]
    exact hreach
  · intro hsecond
    obtain ⟨root, hroot, hreach⟩ := List.any_eq_true.mp hsecond
    apply List.any_eq_true.mpr
    refine ⟨root, hroot, ?_⟩
    rw [rootedComponent_cut_closed ambient compat hsymm
      left right root hedge]
    exact hreach

/-- Simultaneously switching all marked components preserves the complete
disagreement graph. -/
theorem disagreementEdge_marked_root_switch_invariant
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (roots : List A) (left right : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (first second : A) :
    disagreementEdge ambient compat
        (markedRootSwitchedLeft ambient compat roots left right)
        (markedRootSwitchedRight ambient compat roots left right)
        first second =
      disagreementEdge ambient compat left right first second := by
  unfold disagreementEdge markedRootSwitchedLeft markedRootSwitchedRight
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
                cases markedRootCut ambient compat roots left right first <;>
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
                apply markedRootCut_closed ambient compat hsymm
                  roots left right
                exact (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                    ⟨hfirstAmbient, hsecondAmbient⟩, hedge⟩

/-- The switched graph reconstructs the entire union cut. -/
theorem markedRootCut_recovers
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (roots : List A) (left right : A → Bool)
    (hleft : ∀ first second, first ≠ second →
      left first = true → left second = true →
      compat first second = true)
    (hright : ∀ first second, first ≠ second →
      right first = true → right second = true →
      compat first second = true)
    (atom : A) :
    markedRootCut ambient compat roots
        (markedRootSwitchedLeft ambient compat roots left right)
        (markedRootSwitchedRight ambient compat roots left right) atom =
      markedRootCut ambient compat roots left right atom := by
  unfold markedRootCut rootedComponent
  have hedge : disagreementEdge ambient compat
      (markedRootSwitchedLeft ambient compat roots left right)
      (markedRootSwitchedRight ambient compat roots left right) =
      disagreementEdge ambient compat left right := by
    funext first second
    exact disagreementEdge_marked_root_switch_invariant
      ambient compat hsymm roots left right hleft hright first second
  rw [hedge]

/-- The source-dependent simultaneous switch is injective at mask level. -/
theorem marked_root_switched_masks_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (roots : List A)
    (left₁ right₁ left₂ right₂ : A → Bool)
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
      markedRootSwitchedLeft ambient compat roots left₁ right₁ =
        markedRootSwitchedLeft ambient compat roots left₂ right₂)
    (hrightOutput :
      markedRootSwitchedRight ambient compat roots left₁ right₁ =
        markedRootSwitchedRight ambient compat roots left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hcut : markedRootCut ambient compat roots left₁ right₁ =
      markedRootCut ambient compat roots left₂ right₂ := by
    funext atom
    rw [← markedRootCut_recovers ambient compat hsymm roots
      left₁ right₁ hleft₁ hright₁ atom]
    rw [← markedRootCut_recovers ambient compat hsymm roots
      left₂ right₂ hleft₂ hright₂ atom]
    rw [hleftOutput, hrightOutput]
  have hbits : ∀ atom,
      left₁ atom = left₂ atom ∧ right₁ atom = right₂ atom := by
    intro atom
    have hleftAt := congrFun hleftOutput atom
    have hrightAt := congrFun hrightOutput atom
    have hcutAt := congrFun hcut atom
    cases hcut₁ : markedRootCut ambient compat roots left₁ right₁ atom <;>
      cases hcut₂ : markedRootCut ambient compat roots left₂ right₂ atom <;>
      simp_all [markedRootSwitchedLeft, markedRootSwitchedRight,
        swapLeftMask, swapRightMask]
  exact ⟨funext (fun atom => (hbits atom).1),
    funext (fun atom => (hbits atom).2)⟩

def markedRootComponentSwitchedLeft (ambient : List A)
    (compat : A → A → Bool) (roots : List A)
    (left right : List A) : List A :=
  switchedLeft ambient
    (markedRootCut ambient compat roots (memberB left) (memberB right))
    left right

def markedRootComponentSwitchedRight (ambient : List A)
    (compat : A → A → Bool) (roots : List A)
    (left right : List A) : List A :=
  switchedRight ambient
    (markedRootCut ambient compat roots (memberB left) (memberB right))
    left right

theorem markedRootComponentSwitchedLeft_mask
    (ambient : List A) (compat : A → A → Bool) (roots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB
        (markedRootComponentSwitchedLeft ambient compat roots left right) =
      markedRootSwitchedLeft ambient compat roots
        (memberB left) (memberB right) := by
  unfold markedRootComponentSwitchedLeft markedRootSwitchedLeft
  rw [memberB_switchedLeft_eq ambient _ hleft hright]
  rfl

theorem markedRootComponentSwitchedRight_mask
    (ambient : List A) (compat : A → A → Bool) (roots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB
        (markedRootComponentSwitchedRight ambient compat roots left right) =
      markedRootSwitchedRight ambient compat roots
        (memberB left) (memberB right) := by
  unfold markedRootComponentSwitchedRight markedRootSwitchedRight
  rw [memberB_switchedRight_eq ambient _ hleft hright]
  rfl

/-- All marked bits of the left output are the original right bits. -/
theorem familyMembershipFingerprint_markedRootSwitchedLeft
    (ambient : List A) (compat : A → A → Bool) (allRoots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    ∀ roots : List A,
      (∀ atom, atom ∈ roots → atom ∈ allRoots) →
      familyMembershipFingerprint roots
          (markedRootComponentSwitchedLeft ambient compat allRoots left right) =
        familyMembershipFingerprint roots right
  | [], _ => rfl
  | atom :: roots, hsubset => by
      have hcut := markedRootCut_true_of_mem ambient compat allRoots
        (memberB left) (memberB right)
        (hsubset atom List.mem_cons_self)
      have hmask := congrFun
        (markedRootComponentSwitchedLeft_mask ambient compat allRoots
          hleft hright) atom
      have hbit : memberB
          (markedRootComponentSwitchedLeft ambient compat allRoots left right)
          atom = memberB right atom := by
        simpa only [markedRootSwitchedLeft, swapLeftMask, hcut,
          ↓reduceIte] using hmask
      have htail : ∀ tailAtom, tailAtom ∈ roots → tailAtom ∈ allRoots :=
        fun tailAtom htailAtom =>
          hsubset tailAtom (List.mem_cons_of_mem atom htailAtom)
      simp only [familyMembershipFingerprint, List.map_cons]
      rw [hbit]
      exact congrArg (List.cons (memberB right atom))
        (familyMembershipFingerprint_markedRootSwitchedLeft
          ambient compat allRoots hleft hright roots htail)

/-- All marked bits of the right output are the original left bits. -/
theorem familyMembershipFingerprint_markedRootSwitchedRight
    (ambient : List A) (compat : A → A → Bool) (allRoots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    ∀ roots : List A,
      (∀ atom, atom ∈ roots → atom ∈ allRoots) →
      familyMembershipFingerprint roots
          (markedRootComponentSwitchedRight ambient compat allRoots left right) =
        familyMembershipFingerprint roots left
  | [], _ => rfl
  | atom :: roots, hsubset => by
      have hcut := markedRootCut_true_of_mem ambient compat allRoots
        (memberB left) (memberB right)
        (hsubset atom List.mem_cons_self)
      have hmask := congrFun
        (markedRootComponentSwitchedRight_mask ambient compat allRoots
          hleft hright) atom
      have hbit : memberB
          (markedRootComponentSwitchedRight ambient compat allRoots left right)
          atom = memberB left atom := by
        simpa only [markedRootSwitchedRight, swapRightMask, hcut,
          ↓reduceIte] using hmask
      have htail : ∀ tailAtom, tailAtom ∈ roots → tailAtom ∈ allRoots :=
        fun tailAtom htailAtom =>
          hsubset tailAtom (List.mem_cons_of_mem atom htailAtom)
      simp only [familyMembershipFingerprint, List.map_cons]
      rw [hbit]
      exact congrArg (List.cons (memberB left atom))
        (familyMembershipFingerprint_markedRootSwitchedRight
          ambient compat allRoots hleft hright roots htail)

theorem familyMembershipFingerprint_markedRootSwitchedLeft_self
    (ambient : List A) (compat : A → A → Bool) (roots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    familyMembershipFingerprint roots
        (markedRootComponentSwitchedLeft ambient compat roots left right) =
      familyMembershipFingerprint roots right := by
  exact familyMembershipFingerprint_markedRootSwitchedLeft
    ambient compat roots hleft hright roots (fun _ h => h)

theorem familyMembershipFingerprint_markedRootSwitchedRight_self
    (ambient : List A) (compat : A → A → Bool) (roots : List A)
    {left right : List A} (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    familyMembershipFingerprint roots
        (markedRootComponentSwitchedRight ambient compat roots left right) =
      familyMembershipFingerprint roots left := by
  exact familyMembershipFingerprint_markedRootSwitchedRight
    ambient compat roots hleft hright roots (fun _ h => h)

/-- The simultaneous family switch is injective on compatible ambient
subfamilies. -/
theorem marked_root_switched_families_injective
    (ambient : List A) (compat : A → A → Bool)
    (hsymm : ∀ first second,
      compat first second = compat second first)
    (roots : List A) {left₁ right₁ left₂ right₂ : List A}
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
      markedRootComponentSwitchedLeft ambient compat roots left₁ right₁ =
        markedRootComponentSwitchedLeft ambient compat roots left₂ right₂)
    (hrightOutput :
      markedRootComponentSwitchedRight ambient compat roots left₁ right₁ =
        markedRootComponentSwitchedRight ambient compat roots left₂ right₂) :
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
      markedRootSwitchedLeft ambient compat roots
          (memberB left₁) (memberB right₁) =
        markedRootSwitchedLeft ambient compat roots
          (memberB left₂) (memberB right₂) := by
    rw [← markedRootComponentSwitchedLeft_mask ambient compat roots
      hleftSub₁ hrightSub₁]
    rw [← markedRootComponentSwitchedLeft_mask ambient compat roots
      hleftSub₂ hrightSub₂]
    rw [hleftOutput]
  have hrightMaskOutput :
      markedRootSwitchedRight ambient compat roots
          (memberB left₁) (memberB right₁) =
        markedRootSwitchedRight ambient compat roots
          (memberB left₂) (memberB right₂) := by
    rw [← markedRootComponentSwitchedRight_mask ambient compat roots
      hleftSub₁ hrightSub₁]
    rw [← markedRootComponentSwitchedRight_mask ambient compat roots
      hleftSub₂ hrightSub₂]
    rw [hrightOutput]
  have hmasks := marked_root_switched_masks_injective
    ambient compat hsymm roots
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

/-- Exact pair-activity preservation needs no approximation. -/
theorem markedRootComponentSwitched_pair_weight_preserved
    (weight : A → YMGap.Constructive.Q')
    {ambient left right : List A} (compat : A → A → Bool)
    (roots : List A) (hambient : ambient.Nodup)
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    YMGap.Constructive.Q'.eqv
      (familyWeight weight
          (markedRootComponentSwitchedLeft ambient compat roots left right) *
        familyWeight weight
          (markedRootComponentSwitchedRight ambient compat roots left right))
      (familyWeight weight left * familyWeight weight right) := by
  exact switched_pair_weight_preserved weight
    (markedRootCut ambient compat roots (memberB left) (memberB right))
    hambient hleft hright

end YMGap.Continuum.FiniteMarkedRootSwitch

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.markedRootCut_closed
#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.disagreementEdge_marked_root_switch_invariant
#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.markedRootCut_recovers
#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.marked_root_switched_families_injective
#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.familyMembershipFingerprint_markedRootSwitchedLeft_self
#print axioms YMGap.Continuum.FiniteMarkedRootSwitch.markedRootComponentSwitched_pair_weight_preserved
