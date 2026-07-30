/-
# Constructive finite signed-kernel L1 operator bound

For finite lists, the row `L1` norm of a signed kernel controls its action
on every signed source weight:

    ||v K||_1 <= (sup_row ||K(row,-)||_1) ||v||_1.

The proof is finite Tonelli/Fubini and the rational triangle inequality.
It does not choose a maximizing row and therefore remains intuitionistic.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.ConstructiveRefreshContraction

namespace YMGap.Continuum.FiniteSignedKernelL1

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-- Finite `L1` norm of a possibly signed weight. -/
def finiteL1Norm
    {State : Type}
    (states : List State) (value : State → Q') : Q' :=
  listQSum (fun state => Q'.abs (value state)) states

theorem finiteL1Norm_nonnegative
    {State : Type}
    (states : List State) (value : State → Q') :
    (0 : Q') ≤ finiteL1Norm states value := by
  unfold finiteL1Norm
  exact listQSum_nonnegative_on _ states
    (fun state _ => Q'.abs_nonneg (value state))

private theorem abs_listQSum_le_sum_abs_local
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      Q'.abs (listQSum value states) ≤
        listQSum (fun state => Q'.abs (value state)) states
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      change
        Q'.abs (value head + listQSum value tail) ≤
          Q'.abs (value head) +
            listQSum
              (fun state => Q'.abs (value state)) tail
      exact Q'.le_trans' _ _ _
        (abs_add_le (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs_local value tail))

/-- A uniform finite signed row bound controls the `L1` norm of every
pushforward. -/
theorem finiteKernelPushforward_l1_le
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (value : Source → Q')
    (kernel : Source → Target → Q')
    (bound : Q')
    (row_bound :
      ∀ source, source ∈ sources →
        finiteL1Norm targets (kernel source) ≤ bound) :
    finiteL1Norm targets
        (finiteKernelPushforward sources value kernel) ≤
      bound * finiteL1Norm sources value := by
  have htriangle :
      finiteL1Norm targets
          (finiteKernelPushforward sources value kernel) ≤
        listQSum
          (fun target =>
            listQSum
              (fun source =>
                Q'.abs (value source) *
                  Q'.abs (kernel source target))
              sources)
          targets := by
    unfold finiteL1Norm finiteKernelPushforward
    apply listQSum_mono
    intro target _
    refine Q'.le_trans' _ _ _
      (abs_listQSum_le_sum_abs_local
        (fun source =>
          value source * kernel source target)
        sources) ?_
    apply listQSum_mono
    intro source _
    exact abs_mul_le
      (value source) (kernel source target)
  have hfubini :
      listQSum
          (fun target =>
            listQSum
              (fun source =>
                Q'.abs (value source) *
                  Q'.abs (kernel source target))
              sources)
          targets ≈
        listQSum
          (fun source =>
            Q'.abs (value source) *
              finiteL1Norm targets (kernel source))
          sources := by
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          listQSum
            (fun target =>
              Q'.abs (value source) *
                Q'.abs (kernel source target))
            targets)
        sources) _ ?_ ?_
    · exact listQSum_swap
        (fun source target =>
          Q'.abs (value source) *
            Q'.abs (kernel source target))
        sources targets
    apply listQSum_congr_on
    intro source _
    unfold finiteL1Norm
    exact listQSum_mul_left
      (Q'.abs (value source))
      (fun target =>
        Q'.abs (kernel source target))
      targets
  have hrows :
      listQSum
          (fun source =>
            Q'.abs (value source) *
              finiteL1Norm targets (kernel source))
          sources ≤
        listQSum
          (fun source =>
            Q'.abs (value source) * bound)
          sources := by
    apply listQSum_mono
    intro source hsource
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (row_bound source hsource)
      (Q'.abs_nonneg (value source))
  have hfactor :
      listQSum
          (fun source =>
            Q'.abs (value source) * bound)
          sources ≈
        bound * finiteL1Norm sources value := by
    refine Q'.eqv_trans _
      (finiteL1Norm sources value * bound) _ ?_ ?_
    · unfold finiteL1Norm
      exact listQSum_mul_right
        (fun source => Q'.abs (value source))
        bound sources
    · exact Q'.mul_comm_eqv
        (finiteL1Norm sources value) bound
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfubini)
      (Q'.le_trans' _ _ _ hrows
        (Q'.le_of_eqv hfactor)))

end YMGap.Continuum.FiniteSignedKernelL1

/-! ## Axiom-dependency gate -/

#print axioms YMGap.Continuum.FiniteSignedKernelL1.finiteKernelPushforward_l1_le
