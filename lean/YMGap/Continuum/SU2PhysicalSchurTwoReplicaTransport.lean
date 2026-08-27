/-
# Finite observable transport for physical SU(2) recoupling

The physical Schur kernel is already normalized as a head-recursive indexed
sum.  This module places exactly that kernel on the repository's concrete
duplicate-free list of right channels.  It then forms the literal Cartesian
two-replica law and proves finite Fubini for product observables.

This is the first recoupling object that can be inserted into the component
switching carrier without pretending that a fractional Schur row is a
deterministic permutation.  It is finite and local: no lattice Gibbs weight,
component peel, strict form bound, thermodynamic limit, or continuum limit is
claimed here.

Constructive contract: Mathlib-free, exact `Q'` arithmetic, structural finite
lists, no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. From indexed Parseval rows to literal finite channel lists -/

/-- Total list lookup summed through `finiteHeadSum` is exactly structural
`listQSum`.  The fallback is never observed inside the list length. -/
theorem finiteHeadSum_fixedRightChannelAt_eq_listQSum
    {a b c d : Nat} (fallback : FixedRightCGChannel a b c d)
    (f : FixedRightCGChannel a b c d → Q') :
    ∀ qs : List (FixedRightCGChannel a b c d),
      finiteHeadSum qs.length
          (fun q => f (fixedRightChannelAt fallback qs q)) ≈
        listQSum f qs
  | [] => Q'.eqv_refl 0
  | q :: qs => by
      simp only [List.length_cons, finiteHeadSum, listQSum]
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (by simpa only [fixedRightChannelAt, List.getElem?_cons_succ] using
          finiteHeadSum_fixedRightChannelAt_eq_listQSum fallback f qs)

/-- The concrete finite target list for one physical Schur row. -/
def physicalSchurRightTargets {a b c d : Nat}
    (_qL : FixedLeftCGChannel a b c d) :
    List (FixedRightCGChannel a b c d) :=
  fixedRightChannels a b c d

theorem physicalSchurRightTargets_nodup {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    (physicalSchurRightTargets qL).Nodup := by
  exact fixedRightChannels_nodup a b c d

theorem physicalSchurRightTargets_complete {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    qR ∈ physicalSchurRightTargets qL := by
  exact fixedRightChannels_complete qR

/-- The indexed Parseval row is the literal sum over the complete right
channel list. -/
theorem physicalSchurRecoupling_list_row_normalized {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    listQSum (physicalSchurRecouplingKernelAt qL)
        (physicalSchurRightTargets qL) ≈ 1 := by
  have hbridge := finiteHeadSum_fixedRightChannelAt_eq_listQSum
    (fixedRightFallbackOfFixedLeft qL)
    (physicalSchurRecouplingKernelAt qL)
    (fixedRightChannels a b c d)
  exact Q'.eqv_trans _ (physicalSchurRecouplingRowMass qL) _
    (Q'.eqv_symm (by
      simpa only [physicalSchurRightTargets,
        physicalSchurRecouplingRowMass, enumeratedRightChannel] using hbridge))
    (physicalSchurRecouplingKernel_row_normalized qL)

/-! ## 2. Observable transport by the finite Schur law -/

/-- Finite expectation of a right-channel observable after recoupling one
left channel. -/
def physicalSchurExpectation {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (observable : FixedRightCGChannel a b c d → Q') : Q' :=
  listQSum
    (fun qR => physicalSchurRecouplingKernelAt qL qR * observable qR)
    (physicalSchurRightTargets qL)

/-- The physical Schur transport preserves the constant observable one. -/
theorem physicalSchurExpectation_one {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    physicalSchurExpectation qL (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (physicalSchurRecouplingKernelAt qL)
      (physicalSchurRightTargets qL)) _ ?_
    (physicalSchurRecoupling_list_row_normalized qL)
  exact listQSum_congr
    (fun qR => Q'.mul_one_eqv (physicalSchurRecouplingKernelAt qL qR))
    (physicalSchurRightTargets qL)

/-! ## 3. The exact two-replica Cartesian transport law -/

/-- Literal pair carrier for two independently recoupled copies of the same
four external SU(2) labels. -/
def physicalSchurTwoReplicaTargets {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d) :
    List (FixedRightCGChannel a b c d × FixedRightCGChannel a b c d) :=
  cartesian (physicalSchurRightTargets qL₁)
    (physicalSchurRightTargets qL₂)

/-- Product weight on the concrete two-replica target carrier. -/
def physicalSchurTwoReplicaKernelAt {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d)
    (target : FixedRightCGChannel a b c d ×
      FixedRightCGChannel a b c d) : Q' :=
  physicalSchurRecouplingKernelAt qL₁ target.1 *
    physicalSchurRecouplingKernelAt qL₂ target.2

theorem physicalSchurTwoReplicaTargets_nodup {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d) :
    (physicalSchurTwoReplicaTargets qL₁ qL₂).Nodup := by
  exact cartesian_nodup _ _
    (physicalSchurRightTargets_nodup qL₁)
    (physicalSchurRightTargets_nodup qL₂)

theorem physicalSchurTwoReplicaKernelAt_nonnegative {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d)
    (target : FixedRightCGChannel a b c d ×
      FixedRightCGChannel a b c d) :
    (0 : Q') ≤ physicalSchurTwoReplicaKernelAt qL₁ qL₂ target := by
  exact Q'.mul_nonneg _ _
    (physicalSchurRecouplingKernelAt_nonnegative qL₁ target.1)
    (physicalSchurRecouplingKernelAt_nonnegative qL₂ target.2)

/-- The Cartesian product of two physical Schur rows has exact total mass
one. -/
theorem physicalSchurTwoReplicaKernel_row_normalized {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d) :
    listQSum (physicalSchurTwoReplicaKernelAt qL₁ qL₂)
        (physicalSchurTwoReplicaTargets qL₁ qL₂) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (physicalSchurRecouplingKernelAt qL₁)
        (physicalSchurRightTargets qL₁) *
      listQSum (physicalSchurRecouplingKernelAt qL₂)
        (physicalSchurRightTargets qL₂)) _ ?_ ?_
  · exact listQSum_cartesian_product
      (physicalSchurRecouplingKernelAt qL₁)
      (physicalSchurRecouplingKernelAt qL₂)
      (physicalSchurRightTargets qL₁)
      (physicalSchurRightTargets qL₂)
  · exact Q'.eqv_trans _ ((1 : Q') * 1) _
      (Q'.eqv_trans _
        ((1 : Q') *
          listQSum (physicalSchurRecouplingKernelAt qL₂)
            (physicalSchurRightTargets qL₂)) _
        (Q'.mul_eqv_congr_right _ _ _
          (physicalSchurRecoupling_list_row_normalized qL₁))
        (Q'.mul_eqv_congr_left 1 _ _
          (physicalSchurRecoupling_list_row_normalized qL₂)))
      (Q'.one_mul_eqv 1)

/-- Finite expectation of a two-replica observable after physical
recoupling. -/
def physicalSchurTwoReplicaExpectation {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d)
    (observable : FixedRightCGChannel a b c d ×
      FixedRightCGChannel a b c d → Q') : Q' :=
  listQSum
    (fun target => physicalSchurTwoReplicaKernelAt qL₁ qL₂ target *
      observable target)
    (physicalSchurTwoReplicaTargets qL₁ qL₂)

theorem physicalSchurTwoReplicaExpectation_one {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d) :
    physicalSchurTwoReplicaExpectation qL₁ qL₂ (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (physicalSchurTwoReplicaKernelAt qL₁ qL₂)
      (physicalSchurTwoReplicaTargets qL₁ qL₂)) _ ?_
    (physicalSchurTwoReplicaKernel_row_normalized qL₁ qL₂)
  exact listQSum_congr
    (fun target => Q'.mul_one_eqv
      (physicalSchurTwoReplicaKernelAt qL₁ qL₂ target))
    (physicalSchurTwoReplicaTargets qL₁ qL₂)

private theorem mul_four_interchange (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left a
  exact Q'.eqv_trans _ ((b * c) * d) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))
    (Q'.eqv_trans _ ((c * b) * d) _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))
      (Q'.mul_assoc_eqv c b d))

/-- **Observable Fubini law.**  Product observables transported through the
two-replica Schur carrier factor exactly into the two one-replica
expectations. -/
theorem physicalSchurTwoReplicaExpectation_product {a b c d : Nat}
    (qL₁ qL₂ : FixedLeftCGChannel a b c d)
    (leftObservable rightObservable :
      FixedRightCGChannel a b c d → Q') :
    physicalSchurTwoReplicaExpectation qL₁ qL₂
        (fun target =>
          leftObservable target.1 * rightObservable target.2) ≈
      physicalSchurExpectation qL₁ leftObservable *
        physicalSchurExpectation qL₂ rightObservable := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (physicalSchurRecouplingKernelAt qL₁ target.1 *
          leftObservable target.1) *
        (physicalSchurRecouplingKernelAt qL₂ target.2 *
          rightObservable target.2))
      (physicalSchurTwoReplicaTargets qL₁ qL₂)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact mul_four_interchange
      (physicalSchurRecouplingKernelAt qL₁ target.1)
      (physicalSchurRecouplingKernelAt qL₂ target.2)
      (leftObservable target.1) (rightObservable target.2)
  · simpa only [physicalSchurTwoReplicaTargets,
      physicalSchurExpectation] using
      listQSum_cartesian_product
        (fun qR => physicalSchurRecouplingKernelAt qL₁ qR *
          leftObservable qR)
        (fun qR => physicalSchurRecouplingKernelAt qL₂ qR *
          rightObservable qR)
        (physicalSchurRightTargets qL₁)
        (physicalSchurRightTargets qL₂)

end YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport

#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.finiteHeadSum_fixedRightChannelAt_eq_listQSum
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurRecoupling_list_row_normalized
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurExpectation_one
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurTwoReplicaTargets_nodup
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurTwoReplicaKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurTwoReplicaKernel_row_normalized
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurTwoReplicaExpectation_one
#print axioms YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurTwoReplicaExpectation_product
