/-
# Equal carrier sizes for a finite bistochastic kernel

A finite matrix with unit mass in every written row and every written column
cannot be rectangular.  This module proves that elementary fact directly in
the project's exact rational arithmetic.  The proof is finite Fubini: summing
all rows gives the number of sources, while summing all columns gives the
number of targets.

The result is useful for physical recoupling without identifying unlike
bases.  A right-tree carrier and a left-tree carrier joined by a complete
bistochastic matrix have equal finite capacity, even though their elements
are not definitionally or semantically the same channels.

Constructive contract: structural finite sums and exact `Q'`; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernel
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteBistochasticCarrierBalance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Counting a finite list by unit rational mass -/

theorem listQSum_one_eqv_ofNat_length {A : Type} :
    ∀ items : List A,
      listQSum (fun _ => (1 : Q')) items ≈ Q'.ofNat items.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _ :: tail => by
      refine Q'.eqv_trans _ (1 + Q'.ofNat tail.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _
          (listQSum_one_eqv_ofNat_length tail)
      · change 1 + Q'.ofNat tail.length ≈
          Q'.ofNat (tail.length + 1)
        rw [Nat.add_comm tail.length 1]
        exact Q'.eqv_symm (Q'.ofNat_add_eqv 1 tail.length)

theorem Nat.eq_of_ofNat_eqv {left right : Nat}
    (h : Q'.ofNat left ≈ Q'.ofNat right) : left = right := by
  change (Int.ofNat left) * (1 : Int) =
    (Int.ofNat right) * (1 : Int) at h
  simp only [Int.mul_one] at h
  exact Int.ofNat.inj h

/-! ## 2. Finite Fubini forces a square carrier -/

theorem FiniteBistochasticQKernel.sourceCount_eqv_total
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target) :
    Q'.ofNat kernel.sources.length ≈
      listQSum
        (fun source => listQSum (kernel.weight source) kernel.targets)
        kernel.sources := by
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _
    (listQSum_congr kernel.row_normalized kernel.sources)
    (listQSum_one_eqv_ofNat_length kernel.sources))

theorem FiniteBistochasticQKernel.total_eqv_targetCount
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target) :
    listQSum
        (fun target =>
          listQSum (fun source => kernel.weight source target)
            kernel.sources)
        kernel.targets ≈
      Q'.ofNat kernel.targets.length := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr kernel.column_normalized kernel.targets)
    (listQSum_one_eqv_ofNat_length kernel.targets)

/-- **A finite bistochastic kernel has equally many written source and target
states.**  No identification of the two state types is used. -/
theorem FiniteBistochasticQKernel.sources_length_eq_targets_length
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target) :
    kernel.sources.length = kernel.targets.length := by
  apply Nat.eq_of_ofNat_eqv
  exact Q'.eqv_trans _ _ _
    (FiniteBistochasticQKernel.sourceCount_eqv_total kernel)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (listQSum_swap kernel.weight kernel.sources kernel.targets))
      (FiniteBistochasticQKernel.total_eqv_targetCount kernel))

#print axioms listQSum_one_eqv_ofNat_length
#print axioms Nat.eq_of_ofNat_eqv
#print axioms FiniteBistochasticQKernel.sourceCount_eqv_total
#print axioms FiniteBistochasticQKernel.total_eqv_targetCount
#print axioms FiniteBistochasticQKernel.sources_length_eq_targets_length

end YMGap.Continuum.FiniteBistochasticCarrierBalance
