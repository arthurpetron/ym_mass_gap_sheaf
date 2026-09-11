/-
# A positive physical OS Dirichlet floor for central-face parity

The selected inward-mate parity demand has total energy at least `41/425`.
Its first-edge part is bounded by one copy of the full physical OS Dirichlet
form, and its second-edge part is bounded by
`globalInwardMateTransportCost` copies.  Adding those two inequalities gives

`41/425 <= (1 + globalInwardMateTransportCost) * Dirichlet(parity)`.

Division by the explicit positive cost yields a cutoff-independent positive
rational floor for this one concrete observable.  This is genuine finite OS
coercivity for central-face parity, but it is not an all-vector Poincare
inequality, spectral gap, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- The exact path-congestion multiplier paid by the two selected OS edges. -/
def globalInwardMateParityDirichletCost : Q' :=
  1 + globalInwardMateTransportCost

theorem globalInwardMateParityDirichletCost_positive :
    (0 : Q') < globalInwardMateParityDirichletCost := by
  unfold globalInwardMateParityDirichletCost
  exact Q'.add_pos (by decide) globalInwardMateTransportCost_positive

/-- The explicit positive rational Dirichlet floor obtained after dividing
the selected demand by its total path-congestion cost. -/
def globalInwardMateParityDirichletFloor : Q' :=
  Q'.divPos (Q'.mkPos 41 425 (by decide))
    globalInwardMateParityDirichletCost
    globalInwardMateParityDirichletCost_positive

theorem globalInwardMateParityDirichletFloor_positive :
    (0 : Q') < globalInwardMateParityDirichletFloor := by
  unfold globalInwardMateParityDirichletFloor
  exact Q'.divPos_pos
    (Q'.mkPos 41 425 (by decide))
    globalInwardMateParityDirichletCost
    globalInwardMateParityDirichletCost_positive
    (by decide)

/-- The selected positive demand is paid by the full physical OS Dirichlet
form with the exact two-edge congestion multiplier. -/
theorem globalInwardMateSuccessRate_le_cost_mul_parityDirichlet
    (K : Nat) (hK : 1 <= K) :
    Q'.mkPos 41 425 (by decide) <=
      globalInwardMateParityDirichletCost *
        finiteJointDirichletEnergy (centralHalfStates K 0)
          centralFaceZeroParityCoefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
  let dirichlet :=
    finiteJointDirichletEnergy (centralHalfStates K 0)
      centralFaceZeroParityCoefficient
      (centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0)
  have hedges :
      globalInwardMateSelectedFirstParityEnergy K hK +
          globalInwardMateSelectedSecondParityEnergy K hK <=
        dirichlet + globalInwardMateTransportCost * dirichlet :=
    Q'.add_le_add
      (globalInwardMateSelectedFirstParityEnergy_le_Dirichlet K hK)
      (globalInwardMateSelectedSecondParityEnergy_le_cost_mul_Dirichlet K hK)
  have hregroup :
      dirichlet + globalInwardMateTransportCost * dirichlet ≈
        globalInwardMateParityDirichletCost * dirichlet := by
    unfold globalInwardMateParityDirichletCost
    q_ring
  exact Q'.le_trans' _ _ _
    (globalInwardMateSuccessRate_le_selectedParityEnergies K hK)
    (Q'.le_trans' _ _ _ hedges (Q'.le_of_eqv hregroup))

/-- **One-observable coercivity.**  At every cutoff `K >= 1`, central-face
parity has physical OS Dirichlet energy at least the same explicit positive
rational constant. -/
theorem globalInwardMateParityDirichletFloor_le
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateParityDirichletFloor <=
      finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  apply Q'.divPos_le_of_le_mul
    (Q'.mkPos 41 425 (by decide))
    globalInwardMateParityDirichletCost
    globalInwardMateParityDirichletCost_positive
  exact Q'.le_trans' _ _ _
    (globalInwardMateSuccessRate_le_cost_mul_parityDirichlet K hK)
    (Q'.le_of_eqv (Q'.mul_comm_eqv
      globalInwardMateParityDirichletCost
      (finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0))))

structure GlobalInwardMateParityCoercivityCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  coefficient : EdgeLabelling -> Q'
  pathCost : Q'
  dirichletFloor : Q'
  coefficient_eq : coefficient = centralFaceZeroParityCoefficient
  pathCost_eq : pathCost ≈ globalInwardMateParityDirichletCost
  pathCost_positive : (0 : Q') < pathCost
  dirichletFloor_eq : dirichletFloor ≈
    globalInwardMateParityDirichletFloor
  dirichletFloor_positive : (0 : Q') < dirichletFloor
  scaled_coercivity : Q'.mkPos 41 425 (by decide) <=
    pathCost *
      finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0)
  coercivity : dirichletFloor <=
    finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
      (centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0)

def globalInwardMateParityCoercivityCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateParityCoercivityCertificate K hK :=
  { coefficient := centralFaceZeroParityCoefficient
    pathCost := globalInwardMateParityDirichletCost
    dirichletFloor := globalInwardMateParityDirichletFloor
    coefficient_eq := rfl
    pathCost_eq := Q'.eqv_refl _
    pathCost_positive := globalInwardMateParityDirichletCost_positive
    dirichletFloor_eq := Q'.eqv_refl _
    dirichletFloor_positive := globalInwardMateParityDirichletFloor_positive
    scaled_coercivity :=
      globalInwardMateSuccessRate_le_cost_mul_parityDirichlet K hK
    coercivity := globalInwardMateParityDirichletFloor_le K hK }

#print axioms globalInwardMateParityDirichletCost
#print axioms globalInwardMateParityDirichletCost_positive
#print axioms globalInwardMateParityDirichletFloor
#print axioms globalInwardMateParityDirichletFloor_positive
#print axioms globalInwardMateSuccessRate_le_cost_mul_parityDirichlet
#print axioms globalInwardMateParityDirichletFloor_le
#print axioms globalInwardMateParityCoercivityCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity
