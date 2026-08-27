/-
# Heterogeneous two-replica physical SU(2) recoupling

A crossed two-replica lattice switch generally leaves the two replicas with
different external representation quadruples.  The existing two-replica
Schur carrier assumes both copies have the same four labels, so it cannot be
applied to that production output without an invalid type identification.

This module takes the Cartesian product of two independently normalized
physical Schur rows with unrelated external labels.  It proves exact mass
one and finite Fubini for product observables.  The construction is the
minimal analytic transport accepted by the crossed production channels.

No lattice switch, Gibbs weight, OS form bound, spectral gap, or continuum
claim is made here.

Constructive contract: Mathlib-free, exact `Q'` arithmetic, finite lists,
no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport

namespace YMGap.Continuum.SU2PhysicalSchurHeterogeneousTwoReplicaTransport

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Product carrier for unrelated external labels -/

/-- The two target channel types retain their own external-spin quadruples. -/
def heterogeneousSchurTargets
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂) :
    List (FixedRightCGChannel a₁ b₁ c₁ d₁ ×
      FixedRightCGChannel a₂ b₂ c₂ d₂) :=
  cartesian (physicalSchurRightTargets qL₁)
    (physicalSchurRightTargets qL₂)

theorem heterogeneousSchurTargets_nodup
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂) :
    (heterogeneousSchurTargets qL₁ qL₂).Nodup := by
  exact cartesian_nodup _ _
    (physicalSchurRightTargets_nodup qL₁)
    (physicalSchurRightTargets_nodup qL₂)

/-- Product of the two exact physical Schur probabilities. -/
def heterogeneousSchurKernelAt
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂)
    (target : FixedRightCGChannel a₁ b₁ c₁ d₁ ×
      FixedRightCGChannel a₂ b₂ c₂ d₂) : Q' :=
  physicalSchurRecouplingKernelAt qL₁ target.1 *
    physicalSchurRecouplingKernelAt qL₂ target.2

theorem heterogeneousSchurKernelAt_nonnegative
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂)
    (target : FixedRightCGChannel a₁ b₁ c₁ d₁ ×
      FixedRightCGChannel a₂ b₂ c₂ d₂) :
    (0 : Q') ≤ heterogeneousSchurKernelAt qL₁ qL₂ target := by
  exact Q'.mul_nonneg _ _
    (physicalSchurRecouplingKernelAt_nonnegative qL₁ target.1)
    (physicalSchurRecouplingKernelAt_nonnegative qL₂ target.2)

/-- **Two physical Schur rows with unrelated external labels still have
exact product mass one.** -/
theorem heterogeneousSchurKernel_row_normalized
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂) :
    listQSum (heterogeneousSchurKernelAt qL₁ qL₂)
      (heterogeneousSchurTargets qL₁ qL₂) ≈ 1 := by
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

/-! ## 2. Observable transport and heterogeneous Fubini -/

def heterogeneousSchurExpectation
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂)
    (observable :
      FixedRightCGChannel a₁ b₁ c₁ d₁ ×
        FixedRightCGChannel a₂ b₂ c₂ d₂ → Q') : Q' :=
  listQSum
    (fun target => heterogeneousSchurKernelAt qL₁ qL₂ target *
      observable target)
    (heterogeneousSchurTargets qL₁ qL₂)

theorem heterogeneousSchurExpectation_one
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂) :
    heterogeneousSchurExpectation qL₁ qL₂ (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (heterogeneousSchurKernelAt qL₁ qL₂)
      (heterogeneousSchurTargets qL₁ qL₂)) _ ?_
    (heterogeneousSchurKernel_row_normalized qL₁ qL₂)
  exact listQSum_congr
    (fun target => Q'.mul_one_eqv
      (heterogeneousSchurKernelAt qL₁ qL₂ target))
    (heterogeneousSchurTargets qL₁ qL₂)

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

/-- Product observables factor through the two independently typed Schur
rows. -/
theorem heterogeneousSchurExpectation_product
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (qL₁ : FixedLeftCGChannel a₁ b₁ c₁ d₁)
    (qL₂ : FixedLeftCGChannel a₂ b₂ c₂ d₂)
    (observable₁ : FixedRightCGChannel a₁ b₁ c₁ d₁ → Q')
    (observable₂ : FixedRightCGChannel a₂ b₂ c₂ d₂ → Q') :
    heterogeneousSchurExpectation qL₁ qL₂
        (fun target => observable₁ target.1 * observable₂ target.2) ≈
      physicalSchurExpectation qL₁ observable₁ *
        physicalSchurExpectation qL₂ observable₂ := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (physicalSchurRecouplingKernelAt qL₁ target.1 *
          observable₁ target.1) *
        (physicalSchurRecouplingKernelAt qL₂ target.2 *
          observable₂ target.2))
      (heterogeneousSchurTargets qL₁ qL₂)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact mul_four_interchange
      (physicalSchurRecouplingKernelAt qL₁ target.1)
      (physicalSchurRecouplingKernelAt qL₂ target.2)
      (observable₁ target.1) (observable₂ target.2)
  · simpa only [heterogeneousSchurTargets,
      physicalSchurExpectation] using
      listQSum_cartesian_product
        (fun qR => physicalSchurRecouplingKernelAt qL₁ qR * observable₁ qR)
        (fun qR => physicalSchurRecouplingKernelAt qL₂ qR * observable₂ qR)
        (physicalSchurRightTargets qL₁)
        (physicalSchurRightTargets qL₂)

#print axioms heterogeneousSchurTargets_nodup
#print axioms heterogeneousSchurKernelAt_nonnegative
#print axioms heterogeneousSchurKernel_row_normalized
#print axioms heterogeneousSchurExpectation_one
#print axioms heterogeneousSchurExpectation_product

end YMGap.Continuum.SU2PhysicalSchurHeterogeneousTwoReplicaTransport
