/-
# Constructive finite pushforward through a deterministic kernel

This module isolates the finite algebra needed by concrete lattice blocking
maps.  A function `code : A -> B` induces a zero--one kernel concentrated at
`code source`.  On any finite, duplicate-free target list containing every
image, its rows have mass one.  Summing an arbitrary nonnegative source
weight through the kernel is exactly the sum over the corresponding finite
fiber, and the total weight is preserved.

The statements are purely finite and use the repository's exact rational
setoid.  They do not assert that any particular Yang--Mills amplitude is
compatible with a proposed blocking map; concrete modules must prove that
separate comparison.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.FiniteDeterministicKernelPushforward

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## Generic exact finite sums -/

theorem listQSum_congr_on {A : Type} (f g : A -> Q') :
    forall xs : List A,
      (forall x, x ∈ xs -> f x ≈ g x) ->
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, hagree => by
      exact Q'.add_eqv_congr'
        (hagree x List.mem_cons_self)
        (listQSum_congr_on f g xs
          (fun y hy => hagree y (List.mem_cons_of_mem x hy)))

theorem listQSum_zero {A : Type} : forall xs : List A,
    listQSum (fun _ => (0 : Q')) xs ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: xs => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0) (listQSum_zero xs))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem listQSum_add {A : Type} (f g : A -> Q') : forall xs : List A,
    listQSum (fun x => f x + g x) xs ≈
      listQSum f xs + listQSum g xs
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | x :: xs => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (f x + g x))
          (listQSum_add f g xs))
        (Q'.add_swap_inner (f x) (g x)
          (listQSum f xs) (listQSum g xs))

theorem listQSum_mul_left {A : Type} (a : Q') (f : A -> Q') :
    forall xs : List A,
      listQSum (fun x => a * f x) xs ≈ a * listQSum f xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | x :: xs => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (a * f x))
          (listQSum_mul_left a f xs))
        (Q'.eqv_symm (Q'.mul_add_eqv a (f x) (listQSum f xs)))

/-- Finite Fubini for exact rational list sums. -/
theorem listQSum_swap {A B : Type} (f : A -> B -> Q') :
    forall (xs : List A) (ys : List B),
      listQSum (fun y => listQSum (fun x => f x y) xs) ys ≈
        listQSum (fun x => listQSum (fun y => f x y) ys) xs
  | [], ys => listQSum_zero ys
  | x :: xs, ys => by
      refine Q'.eqv_trans _ _ _
        (listQSum_add (fun y => f x y)
          (fun y => listQSum (fun z => f z y) xs) ys) ?_
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl (listQSum (fun y => f x y) ys))
        (listQSum_swap f xs ys)

theorem listQSum_nonnegative_on {A : Type} (weight : A -> Q') :
    forall xs : List A,
      (forall x, x ∈ xs -> (0 : Q') ≤ weight x) ->
      (0 : Q') ≤ listQSum weight xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h =>
      Q'.zero_le_add _ _
        (h x List.mem_cons_self)
        (listQSum_nonnegative_on weight xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-! ## The zero--one deterministic kernel and its fibers -/

/-- Dirac mass at the deterministic image `code source`. -/
def deterministicKernel {A B : Type} [DecidableEq B]
    (code : A -> B) (source : A) (target : B) : Q' :=
  if target = code source then 1 else 0

theorem deterministicKernel_nonnegative {A B : Type} [DecidableEq B]
    (code : A -> B) (source : A) (target : B) :
    (0 : Q') ≤ deterministicKernel code source target := by
  unfold deterministicKernel
  by_cases h : target = code source
  · rw [if_pos h]
    exact Q'.zero_le_one
  · rw [if_neg h]
    exact Q'.le_refl' 0

theorem deterministicKernel_on_image {A B : Type} [DecidableEq B]
    (code : A -> B) (source : A) :
    deterministicKernel code source (code source) = 1 := by
  simp [deterministicKernel]

theorem deterministicKernel_off_image {A B : Type} [DecidableEq B]
    {code : A -> B} {source : A} {target : B}
    (hne : target ≠ code source) :
    deterministicKernel code source target = 0 := by
  simp [deterministicKernel, hne]

private theorem listQSum_dirac_zero_of_not_mem
    {B : Type} [DecidableEq B] (selected : B) :
    forall targets : List B, selected ∉ targets ->
      listQSum
        (fun target => if target = selected then (1 : Q') else 0)
        targets ≈ 0
  | [], _ => Q'.eqv_refl 0
  | target :: targets, hnot => by
      have hhead : target ≠ selected := by
        intro heq
        subst target
        exact hnot List.mem_cons_self
      have htail : selected ∉ targets := by
        intro hmem
        exact hnot (List.mem_cons_of_mem target hmem)
      simp only [listQSum, if_neg hhead]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (listQSum_dirac_zero_of_not_mem selected targets htail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_dirac_one_of_mem_nodup
    {B : Type} [DecidableEq B] (selected : B) :
    forall targets : List B, targets.Nodup -> selected ∈ targets ->
      listQSum
        (fun target => if target = selected then (1 : Q') else 0)
        targets ≈ 1
  | [], _, hmem => absurd hmem List.not_mem_nil
  | target :: targets, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst target
        simp only [listQSum, if_true]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 1)
            (listQSum_dirac_zero_of_not_mem selected targets hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      · have hheadNe : target ≠ selected := by
          intro heq
          subst target
          exact hparts.1 htail
        simp only [listQSum, if_neg hheadNe]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_dirac_one_of_mem_nodup selected targets
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' 1))

/-- A deterministic row has exact mass one on any duplicate-free target
enumeration containing its image. -/
theorem deterministicKernel_row_normalized
    {A B : Type} [DecidableEq B]
    (code : A -> B) (source : A) (targets : List B)
    (hnodup : targets.Nodup) (hmem : code source ∈ targets) :
    listQSum (deterministicKernel code source) targets ≈ 1 := by
  unfold deterministicKernel
  exact listQSum_dirac_one_of_mem_nodup
    (code source) targets hnodup hmem

/-- Exact source mass lying over a target key. -/
def fiberWeight {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (target : B) : Q' :=
  listQSum weight
    (source.filter (fun item => decide (target = code item)))

/-- The same pushforward mass written as matrix multiplication by the
deterministic kernel. -/
def kernelPushforwardWeight {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (target : B) : Q' :=
  listQSum
    (fun item => weight item * deterministicKernel code item target)
    source

/-- Matrix multiplication by the zero--one kernel is exactly fiber
summation, including duplicate source entries with their multiplicity. -/
theorem kernelPushforwardWeight_eqv_fiberWeight
    {A B : Type} [DecidableEq B]
    (weight : A -> Q') (code : A -> B) (target : B) :
    forall source : List A,
      kernelPushforwardWeight source weight code target ≈
        fiberWeight source weight code target
  | [] => Q'.eqv_refl 0
  | item :: source => by
      by_cases h : target = code item
      · simpa [kernelPushforwardWeight, fiberWeight,
            deterministicKernel, listQSum, h] using
          Q'.add_eqv_congr'
            (Q'.mul_one_eqv (weight item))
            (kernelPushforwardWeight_eqv_fiberWeight
              weight code target source)
      · simpa [kernelPushforwardWeight, fiberWeight,
            deterministicKernel, listQSum, h] using
          Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.mul_zero_eqv (weight item))
              (kernelPushforwardWeight_eqv_fiberWeight
                weight code target source))
            (Q'.eqv_of_eq (Q'.zero_add'
              (fiberWeight source weight code target)))

theorem fiberWeight_nonnegative
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (target : B)
    (hweight : forall item, item ∈ source -> (0 : Q') ≤ weight item) :
    (0 : Q') ≤ fiberWeight source weight code target := by
  unfold fiberWeight
  apply listQSum_nonnegative_on
  intro item hitem
  exact hweight item (List.mem_filter.mp hitem).1

theorem kernelPushforwardWeight_nonnegative
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (target : B)
    (hweight : forall item, item ∈ source -> (0 : Q') ≤ weight item) :
    (0 : Q') ≤ kernelPushforwardWeight source weight code target := by
  unfold kernelPushforwardWeight
  apply listQSum_nonnegative_on
  intro item hitem
  exact Q'.mul_nonneg _ _ (hweight item hitem)
    (deterministicKernel_nonnegative code item target)

/-! ## Preservation of the finite partition sum -/

/-- Summing the kernel pushforward over a complete duplicate-free target
enumeration preserves the exact total source mass. -/
theorem kernelPushforwardWeight_total
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (targets : List B) (hnodup : targets.Nodup)
    (hcoverage : forall item, item ∈ source -> code item ∈ targets) :
    listQSum (kernelPushforwardWeight source weight code) targets ≈
      listQSum weight source := by
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun item target =>
        weight item * deterministicKernel code item target)
      source targets) ?_
  apply listQSum_congr_on
  intro item hitem
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_left (weight item)
      (deterministicKernel code item) targets) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (weight item) _ _
      (deterministicKernel_row_normalized code item targets
        hnodup (hcoverage item hitem)))
    (Q'.mul_one_eqv (weight item))

/-- Equivalent fiber formulation of total partition preservation. -/
theorem fiberWeight_total
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (targets : List B) (hnodup : targets.Nodup)
    (hcoverage : forall item, item ∈ source -> code item ∈ targets) :
    listQSum (fiberWeight source weight code) targets ≈
      listQSum weight source := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target => Q'.eqv_symm
        (kernelPushforwardWeight_eqv_fiberWeight
          weight code target source)) targets)
    (kernelPushforwardWeight_total source weight code targets
      hnodup hcoverage)

#print axioms listQSum_swap
#print axioms deterministicKernel_nonnegative
#print axioms deterministicKernel_row_normalized
#print axioms kernelPushforwardWeight_eqv_fiberWeight
#print axioms fiberWeight_nonnegative
#print axioms kernelPushforwardWeight_nonnegative
#print axioms kernelPushforwardWeight_total
#print axioms fiberWeight_total

end YMGap.Continuum.FiniteDeterministicKernelPushforward
