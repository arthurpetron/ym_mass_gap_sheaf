/-
# Order independence of the completed final residual energy

`finalEnergy` is a finite sum of residual norms evaluated on one fixed
completed vector. Reordering its test list changes neither that vector nor
the energy. This says nothing about reordering the sweep operators themselves.
-/

import YMGap.Continuum.GNSProjectionSweepEnergy

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

private theorem rc_swap (a b c : RC) :
    RCadd a (RCadd b c) = RCadd b (RCadd a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
        (Q'.add_assoc_eqv _ _ _))))

/-- The existing `sumOn` depends on multiplicities, but not list order. -/
theorem sumOn_perm {A : Type} (f : A → RC) :
    ∀ {left right : List A}, left.Perm right →
      sumOn left f = sumOn right f
  | _, _, List.Perm.nil => rfl
  | _, _, List.Perm.cons item hperm =>
      congrArg (fun value => RCadd (f item) value) (sumOn_perm f hperm)
  | _, _, List.Perm.swap first second rest => by
      change RCadd (f second) (RCadd (f first) (sumOn rest f)) =
        RCadd (f first) (RCadd (f second) (sumOn rest f))
      exact rc_swap _ _ _
  | _, _, List.Perm.trans hleft hright =>
      (sumOn_perm f hleft).trans (sumOn_perm f hright)

theorem sumOn_reverse {A : Type} (xs : List A) (f : A → RC) :
    sumOn xs.reverse f = sumOn xs f :=
  sumOn_perm f (List.reverse_perm xs)

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- The same final completed state and all the same residual tests. -/
theorem finalEnergy_perm {left right : List Index}
    (h : left.Perm right) (x : GNSCompletionSpace D) :
    P.finalEnergy left x = P.finalEnergy right x :=
  sumOn_perm (fun i => normSq (P.residual i x)) h

theorem finalEnergy_reverse (tests : List Index) (x : GNSCompletionSpace D) :
    P.finalEnergy tests.reverse x = P.finalEnergy tests x :=
  P.finalEnergy_perm (List.reverse_perm tests) x

#print axioms sumOn_perm
#print axioms sumOn_reverse
#print axioms finalEnergy_perm
#print axioms finalEnergy_reverse

end YMGap.Continuum.GNSProjectionSweep.Family
