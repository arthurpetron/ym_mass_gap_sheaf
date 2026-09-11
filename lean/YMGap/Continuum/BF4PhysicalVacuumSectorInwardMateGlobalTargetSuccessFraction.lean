/-
# Positive global all-target fraction from exact SU(2) normalization

The complete global first-stretched mass is at most `384/425` of the genuine
physical partition, while the preceding normalization theorem identifies the
all-target and first-stretched masses as an exact partition.  Additive order
cancellation therefore gives a complementary all-target mass of at least
`41/425` of the physical partition.

This theorem concerns one global recoupling event.  It is deliberately not
stated as a pointwise conditional-row minorization.  A support-aware
same-object posterior/Poincare argument is still required before any dense
transfer-operator form bound or spectral gap follows.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetCongestion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive complement order lemma -/

private theorem le_of_add_le_add_right_local {left right common : Q'}
    (h : left + common ≤ right + common) : left ≤ right := by
  have hshift := Q'.add_le_add_right
    (left + common) (right + common) (-common) h
  have hleft : (left + common) + -common ≈ left := by
    refine Q'.eqv_trans _ (left + (common + -common)) _
      (Q'.add_assoc_eqv left common (-common)) ?_
    refine Q'.eqv_trans _ (left + 0) _
      (Q'.add_eqv_congr_left left _ _
        (Q'.add_neg_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' left)
  have hright : (right + common) + -common ≈ right := by
    refine Q'.eqv_trans _ (right + (common + -common)) _
      (Q'.add_assoc_eqv right common (-common)) ?_
    refine Q'.eqv_trans _ (right + 0) _
      (Q'.add_eqv_congr_left right _ _
        (Q'.add_neg_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' right)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

/-- If good and bad mass exactly normalize to a total, and the bad mass is at
most a failure-rate fraction, then the complementary success-rate fraction is
contained in the good mass. -/
private theorem complement_mass_lower_local
    {good bad total successRate failureRate : Q'}
    (hrates : successRate + failureRate ≈ 1)
    (hnormalized : good + bad ≈ total)
    (hbad : bad ≤ failureRate * total) :
    successRate * total ≤ good := by
  have hbadAdded :
      successRate * total + bad ≤
        successRate * total + failureRate * total :=
    Q'.add_le_add_left (successRate * total)
      bad (failureRate * total) hbad
  have hratesScaled :
      successRate * total + failureRate * total ≈ total := by
    refine Q'.eqv_trans _ ((successRate + failureRate) * total) _
      (Q'.eqv_symm
        (Q'.add_mul_eqv successRate failureRate total)) ?_
    exact Q'.eqv_trans _ (1 * total) _
      (Q'.mul_eqv_congr_right
        (successRate + failureRate) 1 total hrates)
      (Q'.one_mul_eqv total)
  have htoNormalized :
      successRate * total + failureRate * total ≤ good + bad :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hratesScaled)
      (Q'.ge_of_eqv hnormalized)
  exact le_of_add_le_add_right_local
    (Q'.le_trans' _ _ _ hbadAdded htoNormalized)

/-! ## 2. The explicit global all-target fraction -/

/-- **Global all-target success-event lower bound.**  At every cutoff
`K >= 1`, the certified all-target recoupling carrier has at least `41/425` of
the genuine physical partition mass. -/
theorem globalCubeInwardMateCertifiedTargetFullSources_weight_ge_partition
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 41 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  exact complement_mass_lower_local
    (good :=
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK))
    (bad :=
      listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK))
    (total := slabParametricKPhysicalPartition anchorCoupling K 1)
    (successRate := Q'.mkPos 41 425 (by decide))
    (failureRate := Q'.mkPos 384 425 (by decide))
    (by decide)
    (globalCubeInwardMateFullSourceBranches_weight_total K hK)
    (globalCubeInwardMateFullSources_weight_sum_le_physicalPartition K hK)

/-! ## 3. Witness-bearing success certificate -/

/-- Type-level certificate carrying the explicit positive global all-target
rate and its partition-relative lower bound. -/
structure GlobalCubeInwardMateTargetSuccessCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  rate : Q'
  rate_positive : (0 : Q') < rate
  allTargetWeight_ge :
    rate * slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK)

/-- The explicit global all-target certificate has success rate `41/425`. -/
def globalCubeInwardMateTargetSuccessCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalCubeInwardMateTargetSuccessCertificate K hK where
  rate := Q'.mkPos 41 425 (by decide)
  rate_positive := by decide
  allTargetWeight_ge :=
    globalCubeInwardMateCertifiedTargetFullSources_weight_ge_partition K hK

#print axioms globalCubeInwardMateCertifiedTargetFullSources_weight_ge_partition
#print axioms GlobalCubeInwardMateTargetSuccessCertificate
#print axioms globalCubeInwardMateTargetSuccessCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction
