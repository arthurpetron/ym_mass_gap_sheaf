/-
# Exact finite coefficient zero extension and quadratic reindexing

A coefficient on a finite source list is pushed to a larger finite target
chart by summing it over the fibers of a deterministic code.  It is literally
zero off the coded image, allows repeated source entries without silently
discarding multiplicity, and reindexes every finite joint quadratic exactly.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.FiniteCoefficientZeroExtension

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Fiber aggregation is the exact zero extension of a coefficient through a
finite deterministic code.  Repeated source entries retain their list
multiplicity. -/
def finiteCoefficientZeroExtension
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (coefficient : Source → Q')
    (code : Source → Target) (target : Target) : Q' :=
  fiberWeight source coefficient code target

private theorem filter_decide_eq_empty
    {Source Target : Type} [DecidableEq Target]
    (target : Target) (code : Source → Target) :
    ∀ source : List Source,
      (∀ item, item ∈ source → target ≠ code item) →
      source.filter (fun item => decide (target = code item)) = []
  | [], _ => rfl
  | head :: tail, houtside => by
      have hhead : target ≠ code head :=
        houtside head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → target ≠ code item :=
        fun item hitem =>
          houtside item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, decide_eq_false hhead,
        Bool.false_eq_true, if_false]
      exact filter_decide_eq_empty target code tail htail

/-- Outside the finite coded image the extended coefficient is exactly zero. -/
theorem finiteCoefficientZeroExtension_eqv_zero_of_not_image
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (coefficient : Source → Q')
    (code : Source → Target) (target : Target)
    (houtside : ∀ item, item ∈ source → target ≠ code item) :
    finiteCoefficientZeroExtension source coefficient code target ≈ 0 := by
  unfold finiteCoefficientZeroExtension fiberWeight
  have hempty :
      source.filter (fun item => decide (target = code item)) = [] := by
    exact filter_decide_eq_empty target code source houtside
  rw [hempty]
  exact Q'.eqv_refl 0

private theorem coefficient_mul_fiberWeight_eqv_local
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (weight : Source → Q')
    (code : Source → Target) (coefficient : Target → Q')
    (target : Target) :
    coefficient target * fiberWeight source weight code target ≈
      fiberWeight source
        (fun item => coefficient (code item) * weight item)
        code target := by
  unfold fiberWeight
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_mul_left (coefficient target) weight
        (source.filter (fun item => decide (target = code item))))) ?_
  apply listQSum_congr_on
  intro item hitem
  have hcode : target = code item :=
    of_decide_eq_true (List.mem_filter.mp hitem).2
  rw [hcode]
  exact Q'.eqv_refl _

/-- Linear reindexing through the zero extension. -/
theorem finiteCoefficientZeroExtension_reindex_mul
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (coefficient : Source → Q')
    (code : Source → Target) (targets : List Target)
    (hnodup : targets.Nodup)
    (hcoverage : ∀ item, item ∈ source → code item ∈ targets)
    (value : Target → Q') :
    listQSum
        (fun target =>
          finiteCoefficientZeroExtension source coefficient code target *
            value target)
        targets ≈
      listQSum
        (fun item => coefficient item * value (code item)) source := by
  refine Q'.eqv_trans _
    (listQSum
      (fiberWeight source
        (fun item => value (code item) * coefficient item) code)
      targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    refine Q'.eqv_trans _
      (value target *
        fiberWeight source coefficient code target) _
      (Q'.mul_comm_eqv
        (finiteCoefficientZeroExtension source coefficient code target)
        (value target)) ?_
    exact coefficient_mul_fiberWeight_eqv_local
      source coefficient code value target
  · refine Q'.eqv_trans _
      (listQSum
        (fun item => value (code item) * coefficient item) source) _
      (fiberWeight_total source
        (fun item => value (code item) * coefficient item)
        code targets hnodup hcoverage) ?_
    apply listQSum_congr
    intro item
    exact Q'.mul_comm_eqv (value (code item)) (coefficient item)

/-- Exact quadratic reindexing.  No injectivity or source-list `Nodup`
hypothesis is required: coincident target codes are combined by fiber sum. -/
theorem finiteJointQuadratic_zeroExtension_eqv
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (coefficient : Source → Q')
    (code : Source → Target) (targets : List Target)
    (hnodup : targets.Nodup)
    (hcoverage : ∀ item, item ∈ source → code item ∈ targets)
    (joint : Target → Target → Q') :
    finiteJointQuadratic targets
        (finiteCoefficientZeroExtension source coefficient code) joint ≈
      finiteJointQuadratic source coefficient
        (fun left right => joint (code left) (code right)) := by
  let extended := finiteCoefficientZeroExtension source coefficient code
  let rightSum : Target → Q' := fun left =>
    listQSum
      (fun item => coefficient item * joint left (code item)) source
  have hinner : ∀ left,
      listQSum
          (fun right =>
            (extended left * extended right) * joint left right)
          targets ≈
        extended left * rightSum left := by
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          extended right * (extended left * joint left right))
        targets) _ ?_ ?_
    · apply listQSum_congr
      intro right
      refine Q'.eqv_trans _
        (extended left * (extended right * joint left right)) _
        (Q'.mul_assoc_eqv
          (extended left) (extended right) (joint left right)) ?_
      refine Q'.eqv_trans _
        ((extended right * joint left right) * extended left) _
        (Q'.mul_comm_eqv
          (extended left) (extended right * joint left right)) ?_
      refine Q'.eqv_trans _
        (extended right * (joint left right * extended left)) _
        (Q'.mul_assoc_eqv
          (extended right) (joint left right) (extended left)) ?_
      exact Q'.mul_eqv_congr_left (extended right) _ _
        (Q'.mul_comm_eqv (joint left right) (extended left))
    · refine Q'.eqv_trans _
        (listQSum
          (fun item =>
            coefficient item *
              (extended left * joint left (code item))) source) _
        (finiteCoefficientZeroExtension_reindex_mul
          source coefficient code targets hnodup hcoverage
          (fun right => extended left * joint left right)) ?_
      refine Q'.eqv_trans _
        (listQSum
          (fun item =>
            extended left *
              (coefficient item * joint left (code item))) source) _ ?_ ?_
      · apply listQSum_congr
        intro item
        refine Q'.eqv_trans _
          ((extended left * joint left (code item)) * coefficient item) _
          (Q'.mul_comm_eqv
            (coefficient item)
            (extended left * joint left (code item))) ?_
        refine Q'.eqv_trans _
          (extended left *
            (joint left (code item) * coefficient item)) _
          (Q'.mul_assoc_eqv
            (extended left) (joint left (code item))
              (coefficient item)) ?_
        exact Q'.mul_eqv_congr_left (extended left) _ _
          (Q'.mul_comm_eqv
            (joint left (code item)) (coefficient item))
      · exact Q'.eqv_trans _ _ _
          (listQSum_mul_left (extended left)
            (fun item => coefficient item * joint left (code item))
            source)
          (Q'.eqv_refl _)
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum (fun left => extended left * rightSum left) targets) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact hinner left
  · refine Q'.eqv_trans _
      (listQSum
        (fun item => coefficient item * rightSum (code item)) source) _
      (finiteCoefficientZeroExtension_reindex_mul
        source coefficient code targets hnodup hcoverage rightSum) ?_
    apply listQSum_congr
    intro left
    unfold rightSum
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          coefficient left *
            (coefficient right * joint (code left) (code right)))
        source) _
      (Q'.eqv_symm
        (listQSum_mul_left (coefficient left)
          (fun right =>
            coefficient right * joint (code left) (code right))
          source)) ?_
    apply listQSum_congr
    intro right
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficient left) (coefficient right)
        (joint (code left) (code right)))

#print axioms finiteCoefficientZeroExtension_eqv_zero_of_not_image
#print axioms finiteCoefficientZeroExtension_reindex_mul
#print axioms finiteJointQuadratic_zeroExtension_eqv

end YMGap.Continuum.FiniteCoefficientZeroExtension
