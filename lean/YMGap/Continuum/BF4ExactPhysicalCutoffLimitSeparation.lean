/-
# A positive exact/physical discrepancy survives removal of the spin cutoff

The existing cutoff-one fence is not an early-cutoff artifact. The actual
six-face cube row gives pi(vacuum)<=1/(1+a(w)), a(w)=(coeffW w 1)^6.
Thus the same vacuum code delta separates the signed exact Haar quadratic
from the normalized positive multiplicity-product quadratic by at least
delta(w)=a(w)/(1+a(w)) at EVERY K>=1. For w>0 this is strictly positive.

The bound also passes to the already constructed normalized vacuum-pair
CReal limit. In particular cutoff removal cannot turn identity transport
of observables into the refuted exact/physical same-action theorem.

This is a route obstruction, not a proof that a correctly transformed
observable comparison, an explicit nonzero-error comparison, or a direct
signed-Haar construction is impossible. The conditional gap remains valid
for its own operator. No YM action/time, continuum, or Clay claim is made.
-/

import YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
import YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def cubeActivity (w : Q') : Q' := (coeffW w 1) ^ 6

theorem activityDenominator_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < 1 + cubeActivity w :=
  Q'.pos_add_nonneg (by decide) (Q'.pow_nonneg _ (coeffW_nonneg hw 1) 6)

def physicalVacuumUpper (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos 1 (1 + cubeActivity w) (activityDenominator_pos w hw)

/-- Explicit discrepancy floor, independent of representation cutoff K. -/
def vacuumSeparation (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (cubeActivity w) (1 + cubeActivity w) (activityDenominator_pos w hw)

theorem vacuumSeparation_pos {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < vacuumSeparation w (Q'.le_of_lt hw) :=
  Q'.divPos_pos _ _ _ (YMGap.Continuum.HKPos.pow_pos (coeffW_pos hw 1) 6)

private theorem separation_balance (w : Q') (hw : (0 : Q') ≤ w) :
    vacuumSeparation w hw + physicalVacuumUpper w hw ≈ 1 := by
  unfold vacuumSeparation physicalVacuumUpper Q'.divPos
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
      (Q'.mul_recipPos_eqv _ _))

private theorem separation_eq_one_sub (w : Q') (hw : (0 : Q') ≤ w) :
    vacuumSeparation w hw ≈ 1 + -(physicalVacuumUpper w hw) := by
  let a := vacuumSeparation w hw
  let b := physicalVacuumUpper w hw
  have hc : (a + b) + -b ≈ a :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv b))
        (Q'.eqv_of_eq (Q'.add_zero' a)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
    (Q'.add_eqv_congr_right _ _ _ (separation_balance w hw))

private theorem sum_nonnegative {A : Type} (f : A → Q') (hf : ∀ a, (0 : Q') ≤ f a) :
    ∀ xs : List A, (0 : Q') ≤ listQSum f xs
  | [] => Q'.le_refl' _
  | a :: xs => Q'.zero_le_add _ _ (hf a) (sum_nonnegative f hf xs)

private theorem member_le_sum {A : Type} (f : A → Q') (hf : ∀ a, (0 : Q') ≤ f a) :
    ∀ (xs : List A) {a : A}, a ∈ xs → f a ≤ listQSum f xs
  | [], _, h => False.elim (List.not_mem_nil h)
  | b :: xs, a, h => by
    rcases List.mem_cons.mp h with rfl | ha
    · exact Q'.add_le_self_of_nonneg _ _ (sum_nonnegative f hf xs)
    · have hs := Q'.add_le_add_right (0 : Q') (f b) (listQSum f xs) (hf b)
      rw [Q'.zero_add'] at hs
      exact Q'.le_trans' _ _ _ (member_le_sum f hf xs ha) hs

/-- The diagonal upper bound is uniform in K, not just strictly below one
separately at each finite cutoff. -/
theorem vacuum_diagonal_le_upper (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (hK : 1 ≤ K) :
    centralNormalizedPhysicalReflectedKernel w hw K 0 zeroEdgeLabelling zeroEdgeLabelling ≤
      physicalVacuumUpper w hw := by
  have hd : centralNormalizedPhysicalReflectedKernel w hw K 0 zeroEdgeLabelling zeroEdgeLabelling ≤
      centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling :=
    member_le_sum (centralNormalizedPhysicalReflectedKernel w hw K 0 zeroEdgeLabelling)
      (fun target => centralNormalizedPhysicalReflectedKernel_nonnegative hw K 0 zeroEdgeLabelling target)
      (centralHalfStates K 0) (zeroEdgeLabelling_mem_centralHalfStates K 0)
  exact Q'.le_trans' _ _ _ hd (centralVacuumRowMarginal_le_cubeActivityReciprocal hw hK)

private theorem separation_le_one_sub {w : Q'} {hw : (0 : Q') ≤ w} {p : Q'}
    (hp : p ≤ physicalVacuumUpper w hw) : vacuumSeparation w hw ≤ 1 + -p :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (separation_eq_one_sub w hw))
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp))

/-- An explicit common positive floor on the actual identity-transport
quadratic discrepancy, for every K>=1 and every positive nome. -/
theorem finite_vacuum_defect_ge (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (hK : 1 ≤ K) :
    vacuumSeparation w hw ≤
      Q'.abs (exactSlabAllCutoffQuadratic w K (vacuumCodeDelta K) +
        -centralNormalizedFullPhysicalReflectionQuadratic w hw K 0 (vacuumCodeDelta K)) := by
  have hp := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (centralNormalizedFull_vacuumCodeDelta_eqv_diagonal w hw K))
    (vacuum_diagonal_le_upper w hw K hK)
  have hlower := separation_le_one_sub hp
  have he := exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w K
  exact Q'.le_trans' _ _ _ hlower
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ _ he))
      (Q'.le_abs_self _))

/-- The old cutoff-one obstruction holds at EVERY nonzero cutoff. -/
theorem same_action_uninhabited {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) : ExactHaarPhysicalPerronSameActionAt w (Q'.le_of_lt hw) K → False := by
  intro identification
  have hsame := identification.same_action (vacuumCodeDelta K)
  have he := exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w K
  have hp := centralNormalizedFull_vacuumCodeDelta_lt_one hw K hK
  have heq := Q'.eqv_trans _ _ _ (Q'.eqv_symm hsame) he
  exact (by decide : ¬ ((1 : Q') < 1)) (Q'.lt_of_le_of_lt (Q'.ge_of_eqv heq) hp)

/-- No cofinal choice of cutoff can hide the false identity. -/
theorem cofinal_same_action_uninhabited {w : Q'} (hw : (0 : Q') < w)
    (schedule : Nat → Nat) (cofinal : ∀ request, request ≤ schedule request)
    (identification : ∀ request,
      ExactHaarPhysicalPerronSameActionAt w (Q'.le_of_lt hw) (schedule request)) : False :=
  same_action_uninhabited hw (schedule 1) (cofinal 1) (identification 1)

private theorem normalized_root_approx {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) : (normalizedKernelLimit hw0 hw1 rootState rootState).approx K ≈
      centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw0) K 0 zeroEdgeLabelling zeroEdgeLabelling :=
  Q'.eqv_symm (centralNormalizedPhysicalReflectedKernel_eq_expectation
    (hw := Q'.le_of_lt hw0) (zeroEdgeLabelling_mem_centralHalfStates K 0)
    (zeroEdgeLabelling_mem_centralHalfStates K 0))

/-- The discrepancy survives in the ORIGINAL cutoff-removed vacuum-pair
Bishop real. Its regularity modulus is the existing normalizedKernelRegularity. -/
theorem cutoff_limit_separation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leEv (CReal.ofQ' (vacuumSeparation w (Q'.le_of_lt hw0)))
      (CReal.sub (CReal.ofQ' 1) (normalizedKernelLimit hw0 hw1 rootState rootState)) := by
  intro epsilon hepsilon
  refine ⟨1, fun K hK => ?_⟩
  have hp := Q'.le_trans' _ _ _ (Q'.le_of_eqv (normalized_root_approx hw0 hw1 K))
    (vacuum_diagonal_le_upper w (Q'.le_of_lt hw0) K hK)
  exact Q'.le_trans' _ _ _ (separation_le_one_sub hp)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))

/-- In particular the actual physical vacuum-pair limit is NOT the exact
signed-Haar value one. This does not assume convergence of an entire exact
Haar family: its vacuum diagonal is already identically one. -/
theorem normalized_vacuum_limit_ne_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Quotient.mk CReal.crealSetoid (normalizedKernelLimit hw0 hw1 rootState rootState) ≠
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 1) := by
  intro heq
  have h := cutoff_limit_separation hw0 hw1
  change CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' (vacuumSeparation w (Q'.le_of_lt hw0))))
    (CReal.RCsub (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (Quotient.mk CReal.crealSetoid (normalizedKernelLimit hw0 hw1 rootState rootState))) at h
  rw [heq] at h
  have hzero : CReal.RCsub (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.add_neg_self_eqv 1))
  rw [hzero] at h
  have hbad := YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect h
  exact (by decide : ¬ ((0 : Q') < 0)) (Q'.pos_of_lt_of_le (vacuumSeparation_pos hw0) hbad)

end YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation

#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.cubeActivity
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.activityDenominator_pos
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.physicalVacuumUpper
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.vacuumSeparation
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.vacuumSeparation_pos
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.vacuum_diagonal_le_upper
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.finite_vacuum_defect_ge
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.same_action_uninhabited
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.cofinal_same_action_uninhabited
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.cutoff_limit_separation
#print axioms YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation.normalized_vacuum_limit_ne_one
