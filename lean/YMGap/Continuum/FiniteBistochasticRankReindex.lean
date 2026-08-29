/-
# Constructive positional reindexing of balanced finite carriers

The elements of two recoupling bases need not have the same meaning.  Once
their duplicate-free complete lists have equal length, however, they admit a
canonical finite reindexing: match equal written ranks.  This module builds
that map by structural recursion, proves that it lands in the source list,
and proves injectivity.

Applied to a finite bistochastic kernel, carrier balance supplies the length
equality automatically.  Thus a complete target basis can be encoded in the
source carrier without identifying right-tree and left-tree channel labels.

Constructive contract: decidable equality, finite lists, and structural
recursion only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticCarrierBalance

namespace YMGap.Continuum.FiniteBistochasticRankReindex

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticCarrierBalance

/-! ## 1. First-occurrence rank and total list lookup -/

def listRank {A : Type} [DecidableEq A] (needle : A) : List A → Nat
  | [] => 0
  | head :: tail =>
      if needle = head then 0 else listRank needle tail + 1

def listAtRank {A : Type} (fallback : A) : List A → Nat → A
  | [], _ => fallback
  | head :: _, 0 => head
  | _ :: tail, rank + 1 => listAtRank fallback tail rank

theorem listRank_lt_length_of_mem {A : Type} [DecidableEq A]
    (needle : A) : ∀ {items : List A},
      needle ∈ items → listRank needle items < items.length
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : needle = head
      · simp [listRank, hhead]
      · have htail : needle ∈ tail := by
          rcases List.mem_cons.mp hmem with heq | hmemTail
          · exact False.elim (hhead heq)
          · exact hmemTail
        simp only [listRank, hhead, if_false, List.length_cons]
        exact Nat.succ_lt_succ (listRank_lt_length_of_mem needle htail)

theorem listAtRank_mem_of_lt {A : Type} (fallback : A) :
    ∀ (items : List A) (rank : Nat),
      rank < items.length → listAtRank fallback items rank ∈ items
  | [], rank, hlt => False.elim (Nat.not_lt_zero rank hlt)
  | _ :: _, 0, _ => List.mem_cons_self
  | head :: tail, rank + 1, hlt =>
      List.mem_cons_of_mem head
      (listAtRank_mem_of_lt fallback tail rank
          (Nat.lt_of_succ_lt_succ hlt))

/-- Below the written length, positional lookup never inspects its fallback. -/
theorem listAtRank_fallback_independent {A : Type}
    (leftFallback rightFallback : A) :
    ∀ (items : List A) (rank : Nat), rank < items.length →
      listAtRank leftFallback items rank =
        listAtRank rightFallback items rank
  | [], rank, hlt => False.elim (Nat.not_lt_zero rank hlt)
  | _ :: _, 0, _ => rfl
  | _ :: tail, rank + 1, hlt =>
      listAtRank_fallback_independent leftFallback rightFallback
        tail rank (Nat.lt_of_succ_lt_succ hlt)

theorem listAtRank_listRank_eq_of_mem {A : Type} [DecidableEq A]
    (fallback needle : A) : ∀ {items : List A},
      needle ∈ items →
        listAtRank fallback items (listRank needle items) = needle
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : needle = head
      · simp [listRank, listAtRank, hhead]
      · have htail : needle ∈ tail := by
          rcases List.mem_cons.mp hmem with heq | hmemTail
          · exact False.elim (hhead heq)
          · exact hmemTail
        simp only [listRank, hhead, if_false, listAtRank]
        exact listAtRank_listRank_eq_of_mem fallback needle htail

theorem listRank_listAtRank_eq_of_lt {A : Type} [DecidableEq A]
    (fallback : A) : ∀ {items : List A},
      items.Nodup → ∀ rank,
        rank < items.length →
          listRank (listAtRank fallback items rank) items = rank
  | [], _, rank, hlt => False.elim (Nat.not_lt_zero rank hlt)
  | head :: tail, hnodup, 0, _ => by
      simp [listAtRank, listRank]
  | head :: tail, hnodup, rank + 1, hlt => by
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have htailLt : rank < tail.length := Nat.lt_of_succ_lt_succ hlt
      have htailMem : listAtRank fallback tail rank ∈ tail :=
        listAtRank_mem_of_lt fallback tail rank htailLt
      have hne : listAtRank fallback tail rank ≠ head := by
        intro heq
        exact (List.nodup_cons.mp hnodup).1 (heq ▸ htailMem)
      simp only [listAtRank, listRank, hne, if_false]
      rw [listRank_listAtRank_eq_of_lt fallback htailNodup rank htailLt]

/-! ## 2. Equal-rank reindexing -/

def equalRankReindex {Source Target : Type}
    [DecidableEq Target]
    (fallback : Source) (sources : List Source) (targets : List Target)
    (target : Target) : Source :=
  listAtRank fallback sources (listRank target targets)

theorem equalRankReindex_mem {Source Target : Type}
    [DecidableEq Target]
    (fallback : Source) (sources : List Source) (targets : List Target)
    (hlength : sources.length = targets.length)
    (target : Target) (htarget : target ∈ targets) :
    equalRankReindex fallback sources targets target ∈ sources := by
  apply listAtRank_mem_of_lt
  rw [hlength]
  exact listRank_lt_length_of_mem target htarget

theorem equalRankReindex_injective {Source Target : Type}
    [DecidableEq Source] [DecidableEq Target]
    (fallback : Source) (sources : List Source) (targets : List Target)
    (hsourceNodup : sources.Nodup)
    (hlength : sources.length = targets.length)
    {left right : Target}
    (hleft : left ∈ targets) (hright : right ∈ targets)
    (heq : equalRankReindex fallback sources targets left =
      equalRankReindex fallback sources targets right) :
    left = right := by
  have hleftRankLt : listRank left targets < sources.length := by
    rw [hlength]
    exact listRank_lt_length_of_mem left hleft
  have hrightRankLt : listRank right targets < sources.length := by
    rw [hlength]
    exact listRank_lt_length_of_mem right hright
  have hranks : listRank left targets = listRank right targets := by
    calc
      listRank left targets =
          listRank
            (listAtRank fallback sources (listRank left targets)) sources :=
        (listRank_listAtRank_eq_of_lt fallback hsourceNodup
          (listRank left targets) hleftRankLt).symm
      _ = listRank
          (listAtRank fallback sources (listRank right targets)) sources := by
        exact congrArg (fun source => listRank source sources) heq
      _ = listRank right targets :=
        listRank_listAtRank_eq_of_lt fallback hsourceNodup
          (listRank right targets) hrightRankLt
  calc
    left = listAtRank left targets (listRank left targets) :=
      (listAtRank_listRank_eq_of_mem left left hleft).symm
    _ = listAtRank left targets (listRank right targets) := by rw [hranks]
    _ = right := listAtRank_listRank_eq_of_mem left right hright

/-- Equal-rank reindexing is canonical on the enumerated target carrier: the
source fallback is used only outside that carrier. -/
theorem equalRankReindex_fallback_independent
    {Source Target : Type} [DecidableEq Target]
    (leftFallback rightFallback : Source)
    (sources : List Source) (targets : List Target)
    (hlength : sources.length = targets.length)
    (target : Target) (htarget : target ∈ targets) :
    equalRankReindex leftFallback sources targets target =
      equalRankReindex rightFallback sources targets target := by
  apply listAtRank_fallback_independent
  rw [hlength]
  exact listRank_lt_length_of_mem target htarget

/-! ## 3. Canonical recoding supplied by a bistochastic kernel -/

def FiniteBistochasticQKernel.targetToSourceAtEqualRank
    {Source Target : Type} [DecidableEq Target]
    (kernel : FiniteBistochasticQKernel Source Target)
    (fallback : Source) (target : Target) : Source :=
  equalRankReindex fallback kernel.sources kernel.targets target

theorem FiniteBistochasticQKernel.targetToSourceAtEqualRank_mem
    {Source Target : Type} [DecidableEq Target]
    (kernel : FiniteBistochasticQKernel Source Target)
    (fallback : Source) (target : Target)
    (htarget : target ∈ kernel.targets) :
    FiniteBistochasticQKernel.targetToSourceAtEqualRank
      kernel fallback target ∈ kernel.sources := by
  exact equalRankReindex_mem fallback kernel.sources kernel.targets
    (FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
      kernel) target htarget

theorem FiniteBistochasticQKernel.targetToSourceAtEqualRank_injective
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (kernel : FiniteBistochasticQKernel Source Target)
    (fallback : Source) (hsourceNodup : kernel.sources.Nodup)
    {left right : Target}
    (hleft : left ∈ kernel.targets) (hright : right ∈ kernel.targets)
    (heq : FiniteBistochasticQKernel.targetToSourceAtEqualRank
        kernel fallback left =
      FiniteBistochasticQKernel.targetToSourceAtEqualRank
        kernel fallback right) :
    left = right := by
  exact equalRankReindex_injective fallback kernel.sources kernel.targets
    hsourceNodup
    (FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
      kernel)
    hleft hright heq

/-- The kernel-level equal-rank target code does not depend on the supplied
source fallback at any literal target column. -/
theorem FiniteBistochasticQKernel.targetToSourceAtEqualRank_fallback_independent
    {Source Target : Type} [DecidableEq Target]
    (kernel : FiniteBistochasticQKernel Source Target)
    (leftFallback rightFallback : Source)
    (target : Target) (htarget : target ∈ kernel.targets) :
    FiniteBistochasticQKernel.targetToSourceAtEqualRank
        kernel leftFallback target =
      FiniteBistochasticQKernel.targetToSourceAtEqualRank
        kernel rightFallback target :=
  equalRankReindex_fallback_independent
    leftFallback rightFallback kernel.sources kernel.targets
    (FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
      kernel)
    target htarget

/-! ## 4. The inverse rank compiler from a written source -/

/-- Select the target carrier at the written rank of one source carrier. -/
def FiniteBistochasticQKernel.sourceToTargetAtEqualRank
    {Source Target : Type} [DecidableEq Source]
    (kernel : FiniteBistochasticQKernel Source Target)
    (fallback : Target) (source : Source) : Target :=
  equalRankReindex fallback kernel.targets kernel.sources source

theorem FiniteBistochasticQKernel.sourceToTargetAtEqualRank_mem
    {Source Target : Type} [DecidableEq Source]
    (kernel : FiniteBistochasticQKernel Source Target)
    (fallback : Target) (source : Source)
    (hsource : source ∈ kernel.sources) :
    FiniteBistochasticQKernel.sourceToTargetAtEqualRank
        kernel fallback source ∈ kernel.targets := by
  exact equalRankReindex_mem fallback kernel.targets kernel.sources
    (FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
      kernel).symm source hsource

/-- On a duplicate-free written target carrier, source-rank selection followed
by target-rank decoding returns the original listed source exactly. -/
theorem FiniteBistochasticQKernel.targetToSource_sourceToTargetAtEqualRank
    {Source Target : Type} [DecidableEq Source] [DecidableEq Target]
    (kernel : FiniteBistochasticQKernel Source Target)
    (sourceFallback : Source) (targetFallback : Target)
    (htargets : kernel.targets.Nodup)
    (source : Source) (hsource : source ∈ kernel.sources) :
    FiniteBistochasticQKernel.targetToSourceAtEqualRank kernel
        sourceFallback
        (FiniteBistochasticQKernel.sourceToTargetAtEqualRank
          kernel targetFallback source) = source := by
  have hlength :=
    FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
      kernel
  have hrankLtSources : listRank source kernel.sources <
      kernel.sources.length :=
    listRank_lt_length_of_mem source hsource
  have hrankLtTargets : listRank source kernel.sources <
      kernel.targets.length := by
    rw [← hlength]
    exact hrankLtSources
  have htargetRank :
      listRank
          (listAtRank targetFallback kernel.targets
            (listRank source kernel.sources)) kernel.targets =
        listRank source kernel.sources :=
    listRank_listAtRank_eq_of_lt targetFallback htargets
      (listRank source kernel.sources) hrankLtTargets
  unfold FiniteBistochasticQKernel.targetToSourceAtEqualRank
    FiniteBistochasticQKernel.sourceToTargetAtEqualRank
    equalRankReindex
  rw [htargetRank]
  exact listAtRank_listRank_eq_of_mem
    sourceFallback source hsource

#print axioms listRank_lt_length_of_mem
#print axioms listAtRank_mem_of_lt
#print axioms listAtRank_fallback_independent
#print axioms listAtRank_listRank_eq_of_mem
#print axioms listRank_listAtRank_eq_of_lt
#print axioms equalRankReindex_mem
#print axioms equalRankReindex_injective
#print axioms equalRankReindex_fallback_independent
#print axioms FiniteBistochasticQKernel.targetToSourceAtEqualRank_mem
#print axioms FiniteBistochasticQKernel.targetToSourceAtEqualRank_injective
#print axioms FiniteBistochasticQKernel.targetToSourceAtEqualRank_fallback_independent
#print axioms FiniteBistochasticQKernel.sourceToTargetAtEqualRank_mem
#print axioms FiniteBistochasticQKernel.targetToSource_sourceToTargetAtEqualRank

end YMGap.Continuum.FiniteBistochasticRankReindex
