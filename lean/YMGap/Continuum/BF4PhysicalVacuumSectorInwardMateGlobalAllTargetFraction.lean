/-
# A positive retained-target fraction at the SU2 anchor

The normalized transport theorem gives

  (41/425) * Z_K
    <= 64 * (32,000,000^6 * distinctTargetMass).

This module divides constructively by the explicit positive transport cost
and returns a Type-level witness whose positive rate is

  (41/425) / (64 * 32,000,000^6).

The result is uniform in the representation cutoff `K` at the fixed coupling
`1/400`.  It is a global retained-target submeasure fraction.  It is not
called a conditional posterior, posterior variance, OS form bound, spectral
gap, or continuum estimate because no same-object two-copy identification has
yet been supplied.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetNormalization
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit positive transport cost and retained rate -/

/-- The complete congestion and six-face heat cost of the all-target map. -/
def globalInwardMateTransportCost : Q' :=
  Q'.ofNat 64 * anchorInwardMateCost ^ 6

theorem globalInwardMateTransportCost_positive :
    (0 : Q') < globalInwardMateTransportCost := by
  unfold globalInwardMateTransportCost anchorInwardMateCost
  decide

/-- The cutoff-independent retained-target fraction at coupling `1/400`. -/
def globalInwardMateRetainedTargetFraction : Q' :=
  Q'.divPos (Q'.mkPos 41 425 (by decide))
    globalInwardMateTransportCost
    globalInwardMateTransportCost_positive

theorem globalInwardMateRetainedTargetFraction_positive :
    (0 : Q') < globalInwardMateRetainedTargetFraction := by
  unfold globalInwardMateRetainedTargetFraction
  exact Q'.divPos_pos
    (Q'.mkPos 41 425 (by decide))
    globalInwardMateTransportCost
    globalInwardMateTransportCost_positive
    (by decide)

private theorem divPos_mul_right_eqv
    (p q r : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq * r ≈ Q'.divPos (p * r) q hq := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (p * (Q'.recipPos q hq * r)) _
    (Q'.mul_assoc_eqv p (Q'.recipPos q hq) r) ?_
  refine Q'.eqv_trans _
    (p * (r * Q'.recipPos q hq)) _
    (Q'.mul_eqv_congr_left p _ _
      (Q'.mul_comm_eqv (Q'.recipPos q hq) r)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv p r (Q'.recipPos q hq))

/-! ## 2. The witness-bearing retained-target lower bound -/

/-- **Positive retained-target fraction.**  At every cutoff `K >= 1`, the
sum of distinct realized all-target atoms contains at least the explicit
positive fraction of the physical partition. -/
theorem globalInwardMateRetainedTargetFraction_partition_le_targets
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateRetainedTargetFraction *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK) := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  let targetMass := listQSum
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
    (globalInwardMateTargetRepresentatives K hK)
  have hscaled :=
    globalInwardMateSuccessRate_partition_le_transportCost_mul_targets K hK
  have hcostTarget :
      Q'.mkPos 41 425 (by decide) * partition ≤
        globalInwardMateTransportCost * targetMass := by
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        unfold globalInwardMateTransportCost
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat 64) (anchorInwardMateCost ^ 6) targetMass)))
  have htargetCost :
      Q'.mkPos 41 425 (by decide) * partition ≤
        targetMass * globalInwardMateTransportCost :=
    Q'.le_trans' _ _ _ hcostTarget
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv globalInwardMateTransportCost targetMass))
  have hdiv := Q'.divPos_le_of_le_mul
    (Q'.mkPos 41 425 (by decide) * partition)
    globalInwardMateTransportCost
    globalInwardMateTransportCost_positive
    htargetCost
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      unfold globalInwardMateRetainedTargetFraction
      exact divPos_mul_right_eqv
        (Q'.mkPos 41 425 (by decide))
        globalInwardMateTransportCost partition
        globalInwardMateTransportCost_positive))
    hdiv

/-- Type-level constructive witness for the retained-target rate and its
cutoff-uniform lower bound. -/
structure GlobalInwardMateRetainedTargetFractionCertificate
    (K : Nat) (hK : 1 ≤ K) : Type where
  rate : Q'
  rate_positive : (0 : Q') < rate
  targetWeight_ge :
    rate * slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK)

/-- The explicit all-target transport constructs the retained-target
certificate at every cutoff. -/
def globalInwardMateRetainedTargetFractionCertificate
    (K : Nat) (hK : 1 ≤ K) :
    GlobalInwardMateRetainedTargetFractionCertificate K hK where
  rate := globalInwardMateRetainedTargetFraction
  rate_positive := globalInwardMateRetainedTargetFraction_positive
  targetWeight_ge :=
    globalInwardMateRetainedTargetFraction_partition_le_targets K hK

#print axioms globalInwardMateTransportCost
#print axioms globalInwardMateTransportCost_positive
#print axioms globalInwardMateRetainedTargetFraction
#print axioms globalInwardMateRetainedTargetFraction_positive
#print axioms globalInwardMateRetainedTargetFraction_partition_le_targets
#print axioms GlobalInwardMateRetainedTargetFractionCertificate
#print axioms globalInwardMateRetainedTargetFractionCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
