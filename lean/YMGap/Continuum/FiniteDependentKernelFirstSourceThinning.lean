/-
# Canonical first-source thinning of a finite dependent kernel

A deterministic realization can identify channels from several source rows.
When no useful decoder exists, finite column capacity can still be obtained
constructively: for each realized target, retain channels only from the first
listed source row which reaches that target.  All retained channels in that
one row are kept.  Nonnegative row mass at most one then bounds every thinned
column by one.

This operation deliberately sacrifices source-dependent row mass.  It is
therefore suited to an aggregate coercivity argument, where a later theorem
proves that the retained weighted mass is positive.  It makes no such
positivity claim itself.

Constructive contract: explicit list recursion, Boolean finite search, and
exact `Q'` inequalities only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.FiniteDependentKernelCapacity

namespace YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The first source row reaching a target -/

def sourceReachesTargetB
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target) : Bool :=
  (choices source).any fun choice =>
    decide (target = realize source choice)

def firstSourceForTarget
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (realize : (source : Source) → Choice source → Target)
    (target : Target) : List Source → Option Source
  | [] => none
  | source :: sources =>
      if sourceReachesTargetB Choice choices realize source target
      then some source
      else firstSourceForTarget Choice choices realize target sources

theorem firstSourceForTarget_mem
    {Source Target : Type} [DecidableEq Target]
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (realize : (source : Source) → Choice source → Target)
    (target : Target) : ∀ {sources : List Source} {source : Source},
    firstSourceForTarget Choice choices realize target sources = some source →
      source ∈ sources
  | [], _, h => by cases h
  | head :: tail, source, h => by
      unfold firstSourceForTarget at h
      cases hreach : sourceReachesTargetB
          Choice choices realize head target with
      | false =>
          simp only [hreach, Bool.false_eq_true, ↓reduceIte] at h
          exact List.mem_cons_of_mem head
            (firstSourceForTarget_mem
              Choice choices realize target h)
      | true =>
          simp only [hreach, ↓reduceIte] at h
          have hhead : head = source := Option.some.inj h
          exact hhead ▸ List.mem_cons_self

/-! ## 2. Thin every row by the global first-source selector -/

def firstSourceThinnedWeight
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (sources : List Source)
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (choice : Choice source) : Q' :=
  if firstSourceForTarget Choice choices realize
      (realize source choice) sources = some source
  then localWeight source choice
  else 0

theorem firstSourceThinnedWeight_nonnegative
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (sources : List Source)
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (choice : Choice source)
    (hweight : (0 : Q') ≤ localWeight source choice) :
    (0 : Q') ≤ firstSourceThinnedWeight
      sources Choice choices localWeight realize source choice := by
  unfold firstSourceThinnedWeight
  split
  · exact hweight
  · exact Q'.le_refl' 0

private theorem listQSum_filter_le_local
    {A : Type} (weight : A → Q') (test : A → Bool)
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ items : List A,
      listQSum weight (items.filter test) ≤ listQSum weight items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local weight test hweight tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hhead : listQSum weight tail ≤
              weight head + listQSum weight tail := by
            have h := Q'.add_le_add_right
              (0 : Q') (weight head) (listQSum weight tail)
              (hweight head)
            rwa [Q'.zero_add'] at h
          exact Q'.le_trans' _ _ _ ih hhead
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left _ _ _ ih

theorem kernelPushforwardWeight_le_rowMass
    {Choice Target : Type} [DecidableEq Target]
    (choices : List Choice) (localWeight : Choice → Q')
    (realize : Choice → Target) (target : Target)
    (hweight : ∀ choice, (0 : Q') ≤ localWeight choice) :
    kernelPushforwardWeight choices localWeight realize target ≤
      listQSum localWeight choices := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (kernelPushforwardWeight_eqv_fiberWeight
        localWeight realize target choices))
    (listQSum_filter_le_local localWeight
      (fun choice => decide (target = realize choice)) hweight choices)

/-! ## 3. Exact description of one thinned pushforward row -/

theorem firstSourceThinnedPushforward_eqv
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (sources : List Source)
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target) :
    dependentKernelPushforwardWeight Choice choices
        (firstSourceThinnedWeight
          sources Choice choices localWeight realize)
        realize source target ≈
      if firstSourceForTarget Choice choices realize target sources =
          some source
      then dependentKernelPushforwardWeight
        Choice choices localWeight realize source target
      else 0 := by
  by_cases hfirst : firstSourceForTarget
      Choice choices realize target sources = some source
  · rw [if_pos hfirst]
    unfold dependentKernelPushforwardWeight kernelPushforwardWeight
    apply listQSum_congr
    intro choice
    by_cases htarget : target = realize source choice
    · have hselected : firstSourceForTarget Choice choices realize
          (realize source choice) sources = some source := by
        rw [← htarget]
        exact hfirst
      rw [deterministicKernel, if_pos htarget]
      unfold firstSourceThinnedWeight
      rw [if_pos hselected]
      exact Q'.eqv_refl _
    · rw [deterministicKernel_off_image htarget]
      exact Q'.eqv_trans _ 0 _
        (Q'.mul_zero_eqv _)
        (Q'.eqv_symm (Q'.mul_zero_eqv _))
  · rw [if_neg hfirst]
    unfold dependentKernelPushforwardWeight kernelPushforwardWeight
    exact Q'.eqv_trans _
      (listQSum (fun _ => (0 : Q')) (choices source)) 0
      (listQSum_congr (fun choice => by
        by_cases htarget : target = realize source choice
        · have hnotSelected : firstSourceForTarget Choice choices realize
              (realize source choice) sources ≠ some source := by
            intro hselected
            apply hfirst
            rw [htarget]
            exact hselected
          rw [deterministicKernel, if_pos htarget]
          unfold firstSourceThinnedWeight
          rw [if_neg hnotSelected]
          exact Q'.mul_one_eqv 0
        · rw [deterministicKernel_off_image htarget]
          exact Q'.mul_zero_eqv _)
        (choices source))
      (listQSum_zero (choices source))

private theorem listQSum_single_eqv
    {A : Type} [DecidableEq A] (selected : A) (weight : A → Q') :
    ∀ {items : List A}, items.Nodup → selected ∈ items →
      listQSum (fun item => if selected = item then weight item else 0)
        items ≈ weight selected
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, if_true]
        have hzero :
            listQSum
                (fun item => if selected = item then weight item else 0)
                tail ≈ 0 := by
          exact Q'.eqv_trans _
            (listQSum (fun _ => (0 : Q')) tail) 0
            (listQSum_congr_on
              (fun item => if selected = item then weight item else 0)
              (fun _ => (0 : Q')) tail (fun item hitem => by
              have hne : selected ≠ item := by
                intro heq
                exact hparts.1 (heq ▸ hitem)
              change (if selected = item then weight item else 0) ≈ 0
              rw [if_neg hne]
              exact Q'.eqv_refl 0))
            (listQSum_zero tail)
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl (weight selected)) hzero)
          (Q'.eqv_of_eq (Q'.add_zero' (weight selected)))
      · have hne : selected ≠ head := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_single_eqv selected weight hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (weight selected)))

/-! ## 4. Canonical thinning gives column capacity -/

/-- **First-source column theorem.**  If every original row has total mass at
most one, the canonically thinned dependent kernel has every column at most
one. -/
theorem firstSourceThinnedColumn_le_one
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (sources : List Source) (hsources : sources.Nodup)
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (hweight : ∀ source, source ∈ sources → ∀ choice,
      (0 : Q') ≤ localWeight source choice)
    (hrow : ∀ source, source ∈ sources →
      listQSum (localWeight source) (choices source) ≤ 1)
    (target : Target) :
    listQSum
        (fun source => dependentKernelPushforwardWeight Choice choices
          (firstSourceThinnedWeight
            sources Choice choices localWeight realize)
          realize source target)
        sources ≤ 1 := by
  cases hfirst : firstSourceForTarget
      Choice choices realize target sources with
  | none =>
      have hsum :
          listQSum
              (fun source => dependentKernelPushforwardWeight Choice choices
                (firstSourceThinnedWeight
                  sources Choice choices localWeight realize)
                realize source target)
              sources ≈ 0 := by
        exact Q'.eqv_trans _
          (listQSum (fun _ => (0 : Q')) sources) 0
          (listQSum_congr (fun source =>
            Q'.eqv_trans _ _ _
              (firstSourceThinnedPushforward_eqv
                sources Choice choices localWeight realize source target)
              (by rw [hfirst]; exact Q'.eqv_refl 0)) sources)
          (listQSum_zero sources)
      exact Q'.le_trans' _ 0 1
        (Q'.le_of_eqv hsum) Q'.zero_le_one
  | some selected =>
      have hselected : selected ∈ sources :=
        firstSourceForTarget_mem
          Choice choices realize target hfirst
      have hsum :
          listQSum
              (fun source => dependentKernelPushforwardWeight Choice choices
                (firstSourceThinnedWeight
                  sources Choice choices localWeight realize)
                realize source target)
              sources ≈
            dependentKernelPushforwardWeight
              Choice choices localWeight realize selected target := by
        exact Q'.eqv_trans _
          (listQSum
            (fun source =>
              if selected = source
              then dependentKernelPushforwardWeight
                Choice choices localWeight realize source target
              else 0)
            sources)
          _
          (listQSum_congr (fun source => by
            refine Q'.eqv_trans _ _ _
              (firstSourceThinnedPushforward_eqv
                sources Choice choices localWeight realize source target) ?_
            rw [hfirst]
            by_cases heq : selected = source
            · rw [if_pos heq, if_pos (congrArg some heq)]
              exact Q'.eqv_refl _
            · rw [if_neg heq]
              have hsome : some selected ≠ some source := by
                intro h
                exact heq (Option.some.inj h)
              rw [if_neg hsome]
              exact Q'.eqv_refl 0) sources)
          (listQSum_single_eqv selected
            (fun source => dependentKernelPushforwardWeight
              Choice choices localWeight realize source target)
            hsources hselected)
      have hpush :
          dependentKernelPushforwardWeight
              Choice choices localWeight realize selected target ≤
            listQSum (localWeight selected) (choices selected) :=
        kernelPushforwardWeight_le_rowMass
          (choices selected) (localWeight selected)
          (realize selected) target
          (hweight selected hselected)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsum)
        (Q'.le_trans' _ _ _ hpush (hrow selected hselected))

end YMGap.Continuum.FiniteDependentKernelFirstSourceThinning

#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourceThinning.firstSourceForTarget_mem
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourceThinning.firstSourceThinnedWeight_nonnegative
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourceThinning.kernelPushforwardWeight_le_rowMass
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourceThinning.firstSourceThinnedPushforward_eqv
#print axioms YMGap.Continuum.FiniteDependentKernelFirstSourceThinning.firstSourceThinnedColumn_le_one
