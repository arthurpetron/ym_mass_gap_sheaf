/-
# Finite weighted fractional-kernel capacity

Normalized finite rational rows and source-weighted column capacities imply
total weighted mass domination.  This is exact finite Fubini for an arbitrary
fractional kernel and an arbitrary common ceiling.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteWeightedFractionalKernelCapacity

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

/-- Exact finite Fubini: normalized kernel rows and scaled weighted column
capacity bound the total source mass by the scaled target mass. -/
theorem sourceWeight_total_le_of_fractionalKernelCapacity
    {Source Target : Type}
    (sources : List Source) (sourceWeight : Source → Q')
    (targets : List Target) (targetWeight : Target → Q')
    (kernel : Source → Target → Q') (ceiling : Q')
    (row_normalized : ∀ source, source ∈ sources →
      listQSum (kernel source) targets ≈ 1)
    (column_capacity : ∀ target, target ∈ targets →
      listQSum
          (fun source => sourceWeight source * kernel source target)
          sources ≤
        ceiling * targetWeight target) :
    listQSum sourceWeight sources ≤
      ceiling * listQSum targetWeight targets := by
  have hsourceRows :
      listQSum sourceWeight sources ≈
        listQSum
          (fun source =>
            listQSum
              (fun target => sourceWeight source * kernel source target)
              targets)
          sources := by
    apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_symm
      (Q'.eqv_trans _
        (sourceWeight source * listQSum (kernel source) targets) _
        (listQSum_mul_left
          (sourceWeight source) (kernel source) targets)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (sourceWeight source) _ _
            (row_normalized source hsource))
          (Q'.mul_one_eqv (sourceWeight source))))
  have hsourceColumns :
      listQSum sourceWeight sources ≈
        listQSum
          (fun target =>
            listQSum
              (fun source => sourceWeight source * kernel source target)
              sources)
          targets :=
    Q'.eqv_trans _ _ _ hsourceRows
      (Q'.eqv_symm
        (listQSum_swap
          (fun source target =>
            sourceWeight source * kernel source target)
          sources targets))
  have hcolumns :
      listQSum
          (fun target =>
            listQSum
              (fun source => sourceWeight source * kernel source target)
              sources)
          targets ≤
        listQSum (fun target => ceiling * targetWeight target) targets := by
    apply listQSum_le_termwise_local
    intro target htarget
    exact column_capacity target htarget
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsourceColumns)
    (Q'.le_trans' _ _ _ hcolumns
      (Q'.le_of_eqv
        (listQSum_mul_left ceiling targetWeight targets)))

end YMGap.Continuum.FiniteWeightedFractionalKernelCapacity

#print axioms
  YMGap.Continuum.FiniteWeightedFractionalKernelCapacity.sourceWeight_total_le_of_fractionalKernelCapacity
