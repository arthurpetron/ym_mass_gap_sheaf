/-
# Ambient-order switching for a finite compatibility gas

This module proves the algebraic and hard-core part of a two-replica
component switch for an arbitrary finite gas.  Both source families are
subsequences of one duplicate-free ambient list.  A Boolean cut swaps their
occupation bits pointwise in ambient order.  Hence the outputs are again
literal ambient subsequences, the product of exact rational activities is
preserved, and compatibility is preserved whenever the cut is constant
across every occupied cross-replica incompatibility edge.

No graph or geometric assumption is built in here.  A later canonical module
supplies the cut by finite Warshall reachability for the corrected SU(2)
surface-polymer compatibility relation.
-/

import YMGap.Continuum.FiniteCompatibilityGas
import YMGap.Continuum.Z4CutoffOneSupportBijection

namespace YMGap.Continuum.FiniteCompatibilitySwitching

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

variable {A : Type} [DecidableEq A]

/-! ## 1. Pointwise occupation-bit switching -/

def memberB (family : List A) (atom : A) : Bool :=
  decide (atom ∈ family)

def switchedLeftB (cut : A → Bool)
    (left right : List A) (atom : A) : Bool :=
  if cut atom then memberB right atom else memberB left atom

def switchedRightB (cut : A → Bool)
    (left right : List A) (atom : A) : Bool :=
  if cut atom then memberB left atom else memberB right atom

def switchedLeft (ambient : List A) (cut : A → Bool)
    (left right : List A) : List A :=
  ambient.filter (switchedLeftB cut left right)

def switchedRight (ambient : List A) (cut : A → Bool)
    (left right : List A) : List A :=
  ambient.filter (switchedRightB cut left right)

def swapLeftMask (cut left right : A → Bool) (atom : A) : Bool :=
  if cut atom then right atom else left atom

def swapRightMask (cut left right : A → Bool) (atom : A) : Bool :=
  if cut atom then left atom else right atom

@[simp] theorem memberB_eq_true_iff (family : List A) (atom : A) :
    memberB family atom = true ↔ atom ∈ family := by
  simp [memberB]

@[simp] theorem memberB_eq_false_iff (family : List A) (atom : A) :
    memberB family atom = false ↔ atom ∉ family := by
  simp [memberB]

theorem switchedLeft_mem_sublists (ambient : List A)
    (cut : A → Bool) (left right : List A) :
    switchedLeft ambient cut left right ∈ sublists ambient :=
  filter_mem_sublists _ _

theorem switchedRight_mem_sublists (ambient : List A)
    (cut : A → Bool) (left right : List A) :
    switchedRight ambient cut left right ∈ sublists ambient :=
  filter_mem_sublists _ _

/-- Mapping an enumerated subsequence gives an enumerated subsequence of the
mapped ambient list. -/
theorem map_mem_sublists {B : Type} (value : A → B) :
    ∀ (ambient family : List A), family ∈ sublists ambient →
      family.map value ∈ sublists (ambient.map value)
  | [], family, hfamily => by
      have hnil : family = [] := List.mem_singleton.mp hfamily
      subst family
      exact List.mem_cons_self
  | head :: tail, family, hfamily => by
      rw [sublists_cons'] at hfamily
      change family.map value ∈
        sublists (value head :: tail.map value)
      rw [sublists_cons']
      rcases List.mem_append.mp hfamily with htail | hhead
      · exact List.mem_append_left _
          (map_mem_sublists value tail family htail)
      · obtain ⟨rest, hrest, hfamilyEq⟩ := List.mem_map.mp hhead
        subst family
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨rest.map value,
          map_mem_sublists value tail rest hrest, rfl⟩

/-- A family already enumerated as an ambient subsequence is recovered by
filtering the duplicate-free ambient list by its membership bit. -/
theorem filter_memberB_eq_of_mem_sublists
    {ambient family : List A} (hambient : ambient.Nodup)
    (hfamily : family ∈ sublists ambient) :
    ambient.filter (memberB family) = family := by
  apply sublists_eq_of_mem_iff ambient _ family hambient
    (filter_mem_sublists _ _) hfamily
  intro atom
  constructor
  · intro hfiltered
    exact (memberB_eq_true_iff family atom).1
      (List.mem_filter.mp hfiltered).2
  · intro hfamilyAtom
    apply List.mem_filter.mpr
    exact ⟨mem_of_mem_sublists ambient family hfamily atom hfamilyAtom,
      (memberB_eq_true_iff family atom).2 hfamilyAtom⟩

/-! ## 2. Exact pair-activity preservation -/

/-- Product with an explicit unit factor at every unoccupied ambient atom. -/
def maskWeight (weight : A → Q') :
    List A → (A → Bool) → Q'
  | [], _ => 1
  | atom :: rest, mask =>
      (if mask atom then weight atom else 1) *
        maskWeight weight rest mask

theorem maskWeight_eqv_familyWeight_filter
    (weight : A → Q') (mask : A → Bool) :
    ∀ ambient : List A,
      maskWeight weight ambient mask ≈
        familyWeight weight (ambient.filter mask)
  | [] => Q'.eqv_refl _
  | atom :: rest => by
      cases hmask : mask atom with
      | false =>
          simp only [maskWeight, hmask, Bool.false_eq_true, ↓reduceIte,
            List.filter_cons]
          refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
          exact maskWeight_eqv_familyWeight_filter weight mask rest
      | true =>
          simp only [maskWeight, hmask, ↓reduceIte, List.filter_cons,
            familyWeight_cons]
          exact Q'.mul_eqv_congr_left _ _ _
            (maskWeight_eqv_familyWeight_filter weight mask rest)

private theorem pair_scale_same (a b left right outLeft outRight : Q')
    (h : left * right ≈ outLeft * outRight) :
    (a * left) * (b * right) ≈
      (a * outLeft) * (b * outRight) := by
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * b) _ _ h) ?_)
  · ring_qeqv
  · ring_qeqv

private theorem pair_scale_swap (a b left right outLeft outRight : Q')
    (h : left * right ≈ outLeft * outRight) :
    (b * left) * (a * right) ≈
      (a * outLeft) * (b * outRight) := by
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * b) _ _ h) ?_)
  · ring_qeqv
  · ring_qeqv

theorem maskWeight_switch_preserved (weight : A → Q')
    (cut left right : A → Bool) :
    ∀ ambient : List A,
      maskWeight weight ambient (swapLeftMask cut left right) *
        maskWeight weight ambient (swapRightMask cut left right) ≈
      maskWeight weight ambient left *
        maskWeight weight ambient right
  | [] => Q'.eqv_refl _
  | atom :: rest => by
      simp only [maskWeight]
      cases hcut : cut atom <;>
        cases hleft : left atom <;>
        cases hright : right atom <;>
        simp only [swapLeftMask, swapRightMask, hcut, hleft, hright,
          Bool.false_eq_true, ↓reduceIte]
      all_goals
        first
        | exact pair_scale_same _ _ _ _ _ _
            (maskWeight_switch_preserved weight cut left right rest)
        | exact pair_scale_swap _ _ _ _ _ _
            (maskWeight_switch_preserved weight cut left right rest)

private theorem mul_eqv_both {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- The ambient-order switch preserves the complete product of family
activities exactly. -/
theorem switched_pair_weight_preserved
    (weight : A → Q') {ambient left right : List A}
    (cut : A → Bool) (hambient : ambient.Nodup)
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    familyWeight weight (switchedLeft ambient cut left right) *
        familyWeight weight (switchedRight ambient cut left right) ≈
      familyWeight weight left * familyWeight weight right := by
  let leftMask := memberB left
  let rightMask := memberB right
  have houtLeft := Q'.eqv_symm
    (maskWeight_eqv_familyWeight_filter weight
      (switchedLeftB cut left right) ambient)
  have houtRight := Q'.eqv_symm
    (maskWeight_eqv_familyWeight_filter weight
      (switchedRightB cut left right) ambient)
  have hswitch := maskWeight_switch_preserved
    weight cut leftMask rightMask ambient
  have hinLeft := maskWeight_eqv_familyWeight_filter
    weight leftMask ambient
  have hinRight := maskWeight_eqv_familyWeight_filter
    weight rightMask ambient
  refine Q'.eqv_trans _ _ _
    (mul_eqv_both houtLeft houtRight) ?_
  refine Q'.eqv_trans _ _ _ hswitch ?_
  have hleftFilter : ambient.filter leftMask = left :=
    filter_memberB_eq_of_mem_sublists hambient hleft
  have hrightFilter : ambient.filter rightMask = right :=
    filter_memberB_eq_of_mem_sublists hambient hright
  rw [hleftFilter] at hinLeft
  rw [hrightFilter] at hinRight
  exact mul_eqv_both hinLeft hinRight

/-! ## 3. Compatibility of a closed cut -/

theorem familyCompatibleB_pairwise
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left) :
    ∀ {family : List A}, familyCompatibleB compat family = true →
      ∀ {left right : A}, left ∈ family → right ∈ family →
        left ≠ right → compat left right = true
  | [], _, _, _, hleft, _, _ => by cases hleft
  | head :: tail, hfamily, left, right, hleft, hright, hne => by
      have hparts := (Bool.and_eq_true _ _).mp hfamily
      rcases List.mem_cons.mp hleft with rfl | hleftTail
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact False.elim (hne hrightHead.symm)
        · exact List.all_eq_true.mp hparts.1 right hrightTail
      · rcases List.mem_cons.mp hright with rfl | hrightTail
        · rw [hsymm]
          exact List.all_eq_true.mp hparts.1 left hleftTail
        · exact familyCompatibleB_pairwise compat hsymm hparts.2
            hleftTail hrightTail hne

theorem familyCompatibleB_of_pairwise (compat : A → A → Bool) :
    ∀ {family : List A}, family.Nodup →
      (∀ left, left ∈ family → ∀ right, right ∈ family →
        left ≠ right → compat left right = true) →
      familyCompatibleB compat family = true
  | [], _, _ => rfl
  | head :: tail, hnodup, hpairs => by
      have hparts := List.nodup_cons.mp hnodup
      apply (Bool.and_eq_true _ _).mpr
      constructor
      · apply List.all_eq_true.mpr
        intro atom hatom
        exact hpairs head List.mem_cons_self atom
          (List.mem_cons_of_mem head hatom)
          (fun heq => hparts.1 (heq ▸ hatom))
      · exact familyCompatibleB_of_pairwise compat hparts.2
          (fun left hleft right hright hne =>
            hpairs left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne)

private theorem false_eq_true_elim {B : Prop}
    (h : false = true) : B := by cases h

/-- If the cut has the same value across every occupied incompatibility edge,
both switched ambient-order families remain compatible. -/
theorem switched_pair_compatible
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left)
    {ambient left right : List A} (cut : A → Bool)
    (hambient : ambient.Nodup)
    (hleftCompat : familyCompatibleB compat left = true)
    (hrightCompat : familyCompatibleB compat right = true)
    (hclosed : ∀ leftAtom, leftAtom ∈ left →
      ∀ rightAtom, rightAtom ∈ right →
        compat leftAtom rightAtom = false →
          cut leftAtom = cut rightAtom) :
    familyCompatibleB compat
        (switchedLeft ambient cut left right) = true ∧
      familyCompatibleB compat
        (switchedRight ambient cut left right) = true := by
  have hleftPairs : ∀ {first second : A}, first ∈ left →
      second ∈ left → first ≠ second →
        compat first second = true :=
    familyCompatibleB_pairwise compat hsymm hleftCompat
  have hrightPairs : ∀ {first second : A}, first ∈ right →
      second ∈ right → first ≠ second →
        compat first second = true :=
    familyCompatibleB_pairwise compat hsymm hrightCompat
  constructor
  · apply familyCompatibleB_of_pairwise compat
      (List.filter_sublist.nodup hambient)
    intro first hfirst second hsecond hne
    have hfirstTest := (List.mem_filter.mp hfirst).2
    have hsecondTest := (List.mem_filter.mp hsecond).2
    cases hfirstCut : cut first with
    | false =>
        have hfirstLeft : first ∈ left := by
          simpa [switchedLeft, switchedLeftB, hfirstCut, memberB]
            using hfirstTest
        cases hsecondCut : cut second with
        | false =>
            have hsecondLeft : second ∈ left := by
              simpa [switchedLeft, switchedLeftB, hsecondCut, memberB]
                using hsecondTest
            exact hleftPairs hfirstLeft hsecondLeft hne
        | true =>
            have hsecondRight : second ∈ right := by
              simpa [switchedLeft, switchedLeftB, hsecondCut, memberB]
                using hsecondTest
            cases hcomp : compat first second with
            | true => rfl
            | false =>
                have hsame := hclosed first hfirstLeft second hsecondRight hcomp
                simp [hfirstCut, hsecondCut] at hsame

    | true =>
        have hfirstRight : first ∈ right := by
          simpa [switchedLeft, switchedLeftB, hfirstCut, memberB]
            using hfirstTest
        cases hsecondCut : cut second with
        | true =>
            have hsecondRight : second ∈ right := by
              simpa [switchedLeft, switchedLeftB, hsecondCut, memberB]
                using hsecondTest
            exact hrightPairs hfirstRight hsecondRight hne
        | false =>
            have hsecondLeft : second ∈ left := by
              simpa [switchedLeft, switchedLeftB, hsecondCut, memberB]
                using hsecondTest
            cases hcomp : compat first second with
            | true => rfl
            | false =>
                have hreverse : compat second first = false := by
                  rw [← hsymm first second]
                  exact hcomp
                have hsame := hclosed second hsecondLeft first hfirstRight hreverse
                simp [hfirstCut, hsecondCut] at hsame
  · apply familyCompatibleB_of_pairwise compat
      (List.filter_sublist.nodup hambient)
    intro first hfirst second hsecond hne
    have hfirstTest := (List.mem_filter.mp hfirst).2
    have hsecondTest := (List.mem_filter.mp hsecond).2
    cases hfirstCut : cut first with
    | false =>
        have hfirstRight : first ∈ right := by
          simpa [switchedRight, switchedRightB, hfirstCut, memberB]
            using hfirstTest
        cases hsecondCut : cut second with
        | false =>
            have hsecondRight : second ∈ right := by
              simpa [switchedRight, switchedRightB, hsecondCut, memberB]
                using hsecondTest
            exact hrightPairs hfirstRight hsecondRight hne
        | true =>
            have hsecondLeft : second ∈ left := by
              simpa [switchedRight, switchedRightB, hsecondCut, memberB]
                using hsecondTest
            cases hcomp : compat first second with
            | true => rfl
            | false =>
                have hreverse : compat second first = false := by
                  rw [← hsymm first second]
                  exact hcomp
                have hsame := hclosed second hsecondLeft first hfirstRight hreverse
                simp [hfirstCut, hsecondCut] at hsame
    | true =>
        have hfirstLeft : first ∈ left := by
          simpa [switchedRight, switchedRightB, hfirstCut, memberB]
            using hfirstTest
        cases hsecondCut : cut second with
        | true =>
            have hsecondLeft : second ∈ left := by
              simpa [switchedRight, switchedRightB, hsecondCut, memberB]
                using hsecondTest
            exact hleftPairs hfirstLeft hsecondLeft hne
        | false =>
            have hsecondRight : second ∈ right := by
              simpa [switchedRight, switchedRightB, hsecondCut, memberB]
                using hsecondTest
            cases hcomp : compat first second with
            | true => rfl
            | false =>
                have hsame := hclosed first hfirstLeft second hsecondRight hcomp
                simp [hfirstCut, hsecondCut] at hsame

/-! ## 4. A fixed cut is an exact involution -/

theorem memberB_filter_of_mem (ambient : List A) (test : A → Bool)
    {atom : A} (hatom : atom ∈ ambient) :
    memberB (ambient.filter test) atom = test atom := by
  apply Bool.eq_iff_iff.mpr
  simp [memberB, hatom]

/-- On two ambient subfamilies, the literal filtered output has exactly the
pointwise left switched occupation mask, including outside the ambient list. -/
theorem memberB_switchedLeft_eq
    (ambient : List A) (cut : A → Bool) {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (switchedLeft ambient cut left right) =
      switchedLeftB cut left right := by
  funext atom
  cases hambient : decide (atom ∈ ambient) with
  | true =>
      have hatom : atom ∈ ambient := of_decide_eq_true hambient
      unfold switchedLeft
      exact memberB_filter_of_mem ambient
        (switchedLeftB cut left right) hatom
  | false =>
      have hatom : atom ∉ ambient := of_decide_eq_false hambient
      have hleftAtom : atom ∉ left := fun hmem =>
        hatom (mem_of_mem_sublists ambient left hleft atom hmem)
      have hrightAtom : atom ∉ right := fun hmem =>
        hatom (mem_of_mem_sublists ambient right hright atom hmem)
      simp [switchedLeft, switchedLeftB, memberB,
        hatom, hleftAtom, hrightAtom]

/-- Right-hand counterpart of `memberB_switchedLeft_eq`. -/
theorem memberB_switchedRight_eq
    (ambient : List A) (cut : A → Bool) {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (switchedRight ambient cut left right) =
      switchedRightB cut left right := by
  funext atom
  cases hambient : decide (atom ∈ ambient) with
  | true =>
      have hatom : atom ∈ ambient := of_decide_eq_true hambient
      unfold switchedRight
      exact memberB_filter_of_mem ambient
        (switchedRightB cut left right) hatom
  | false =>
      have hatom : atom ∉ ambient := of_decide_eq_false hambient
      have hleftAtom : atom ∉ left := fun hmem =>
        hatom (mem_of_mem_sublists ambient left hleft atom hmem)
      have hrightAtom : atom ∉ right := fun hmem =>
        hatom (mem_of_mem_sublists ambient right hright atom hmem)
      simp [switchedRight, switchedRightB, memberB,
        hatom, hleftAtom, hrightAtom]

theorem switchedLeftB_involutive_at
    (ambient : List A) (cut : A → Bool)
    (left right : List A) {atom : A} (hatom : atom ∈ ambient) :
    switchedLeftB cut
        (switchedLeft ambient cut left right)
        (switchedRight ambient cut left right) atom =
      memberB left atom := by
  cases hcut : cut atom with
  | false =>
      simp only [switchedLeftB, hcut, Bool.false_eq_true, ↓reduceIte]
      unfold switchedLeft
      rw [memberB_filter_of_mem ambient
        (switchedLeftB cut left right) hatom]
      simp [switchedLeftB, hcut]
  | true =>
      simp only [switchedLeftB, hcut, ↓reduceIte]
      unfold switchedRight
      rw [memberB_filter_of_mem ambient
        (switchedRightB cut left right) hatom]
      simp [switchedRightB, hcut]

theorem switchedRightB_involutive_at
    (ambient : List A) (cut : A → Bool)
    (left right : List A) {atom : A} (hatom : atom ∈ ambient) :
    switchedRightB cut
        (switchedLeft ambient cut left right)
        (switchedRight ambient cut left right) atom =
      memberB right atom := by
  cases hcut : cut atom with
  | false =>
      simp only [switchedRightB, hcut, Bool.false_eq_true, ↓reduceIte]
      unfold switchedRight
      rw [memberB_filter_of_mem ambient
        (switchedRightB cut left right) hatom]
      simp [switchedRightB, hcut]
  | true =>
      simp only [switchedRightB, hcut, ↓reduceIte]
      unfold switchedLeft
      rw [memberB_filter_of_mem ambient
        (switchedLeftB cut left right) hatom]
      simp [switchedLeftB, hcut]

/-- Applying the same ambient-order cut twice recovers both source families
literally, including ambient order. -/
theorem switched_pair_involutive_fixed_cut
    {ambient left right : List A} (cut : A → Bool)
    (hambient : ambient.Nodup)
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    switchedLeft ambient cut
        (switchedLeft ambient cut left right)
        (switchedRight ambient cut left right) = left ∧
      switchedRight ambient cut
        (switchedLeft ambient cut left right)
        (switchedRight ambient cut left right) = right := by
  constructor
  · apply sublists_eq_of_mem_iff ambient _ left hambient
      (switchedLeft_mem_sublists _ _ _ _) hleft
    intro atom
    constructor
    · intro houtput
      have hparts := List.mem_filter.mp houtput
      have htest : memberB left atom = true := by
        rw [← switchedLeftB_involutive_at
          ambient cut left right hparts.1]
        exact hparts.2
      exact (memberB_eq_true_iff _ _).1 htest
    · intro hsource
      have hatomAmbient :=
        mem_of_mem_sublists ambient left hleft atom hsource
      apply List.mem_filter.mpr
      constructor
      · exact hatomAmbient
      · rw [switchedLeftB_involutive_at
          ambient cut left right hatomAmbient]
        exact (memberB_eq_true_iff _ _).2 hsource
  · apply sublists_eq_of_mem_iff ambient _ right hambient
      (switchedRight_mem_sublists _ _ _ _) hright
    intro atom
    constructor
    · intro houtput
      have hparts := List.mem_filter.mp houtput
      have htest : memberB right atom = true := by
        rw [← switchedRightB_involutive_at
          ambient cut left right hparts.1]
        exact hparts.2
      exact (memberB_eq_true_iff _ _).1 htest
    · intro hsource
      have hatomAmbient :=
        mem_of_mem_sublists ambient right hright atom hsource
      apply List.mem_filter.mpr
      constructor
      · exact hatomAmbient
      · rw [switchedRightB_involutive_at
          ambient cut left right hatomAmbient]
        exact (memberB_eq_true_iff _ _).2 hsource

/-- Consequently a fixed-cut switch is injective on pairs of enumerated
ambient subfamilies. -/
theorem switched_pair_injective_fixed_cut
    {ambient left₁ right₁ left₂ right₂ : List A}
    (cut : A → Bool) (hambient : ambient.Nodup)
    (hleft₁ : left₁ ∈ sublists ambient)
    (hright₁ : right₁ ∈ sublists ambient)
    (hleft₂ : left₂ ∈ sublists ambient)
    (hright₂ : right₂ ∈ sublists ambient)
    (hleftOutput : switchedLeft ambient cut left₁ right₁ =
      switchedLeft ambient cut left₂ right₂)
    (hrightOutput : switchedRight ambient cut left₁ right₁ =
      switchedRight ambient cut left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hinv₁ := switched_pair_involutive_fixed_cut
    cut hambient hleft₁ hright₁
  have hinv₂ := switched_pair_involutive_fixed_cut
    cut hambient hleft₂ hright₂
  constructor
  · rw [← hinv₁.1, ← hinv₂.1, hleftOutput, hrightOutput]
  · rw [← hinv₁.2, ← hinv₂.2, hleftOutput, hrightOutput]

end YMGap.Continuum.FiniteCompatibilitySwitching

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.filter_memberB_eq_of_mem_sublists
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.maskWeight_switch_preserved
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.switched_pair_weight_preserved
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.switched_pair_compatible
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.memberB_switchedLeft_eq
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.memberB_switchedRight_eq
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.switched_pair_involutive_fixed_cut
#print axioms YMGap.Continuum.FiniteCompatibilitySwitching.switched_pair_injective_fixed_cut
