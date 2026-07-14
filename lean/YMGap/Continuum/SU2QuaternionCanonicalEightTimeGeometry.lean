/-
# Period-two geometry for the canonical quaternion Wilson datum

The strict boundary swap already preserves the exact interacting reference
state.  This file proves that it also descends through the semantic
polynomial equality used by the canonical carrier module.  The key identity
is elementary but indispensable: evaluating a swapped polynomial is the same
as evaluating the original polynomial in the environment with the two
four-coordinate boundary blocks exchanged.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightModule
import YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction

namespace YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightModule
open YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

local infix:50 " ≈ " => Q'.eqv

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, zero_num_cast, zero_den_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-- Exchange the first and second blocks of four variables in an evaluation
environment.  Values beyond the canonical eight-coordinate support are left
unchanged. -/
def swapEnvironment8 (rho : Nat → Q') : Nat → Q'
  | 0 => rho 4
  | 1 => rho 5
  | 2 => rho 6
  | 3 => rho 7
  | 4 => rho 0
  | 5 => rho 1
  | 6 => rho 2
  | 7 => rho 3
  | n => rho n

theorem evalMono_swapMono8 (rho : Nat → Q') (m : Mono8) :
    evalMono rho (mono8ToList (swapMono8 m)) ≈
      evalMono (swapEnvironment8 rho) (mono8ToList m) := by
  simp only [evalMono, mono8ToList, evalMonoFrom, swapMono8,
    swapEnvironment8, swapBoundaryIndex8]
  ring_qeqv

/-- Semantic evaluation intertwines boundary exchange with exchange of the
evaluation environment. -/
theorem evalCanonicalPoly8_swap (rho : Nat → Q') : ∀ p : Poly8,
    evalCanonicalPoly8 rho (swapPoly8 p) ≈
      evalCanonicalPoly8 (swapEnvironment8 rho) p
  | [] => Q'.eqv_refl 0
  | t :: p => by
      change
        t.2 * evalMono rho (mono8ToList (swapMono8 t.1)) +
            evalCanonicalPoly8 rho (swapPoly8 p) ≈
          t.2 * evalMono (swapEnvironment8 rho) (mono8ToList t.1) +
            evalCanonicalPoly8 (swapEnvironment8 rho) p
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_left t.2 _ _ (evalMono_swapMono8 rho t.1))
        (evalCanonicalPoly8_swap rho p)

theorem swapPoly8_neg (p : Poly8) :
    swapPoly8 (polyNeg8 p) = polyNeg8 (swapPoly8 p) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change
        (swapMono8 t.1, -t.2) :: swapPoly8 (polyNeg8 p) =
          (swapMono8 t.1, -t.2) :: polyNeg8 (swapPoly8 p)
      rw [ih]

/-- The constructed nonconstant Wilson reference weight, its exact semantic
module, and strict boundary exchange form a genuine period-two Euclidean time
geometry. -/
def canonicalRetainedBoundarySwapGeometry : GeometryEnrichedReferenceWeight
    canonicalRetainedReferenceWeight canonicalPoly8Module where
  timeExtent := 2
  timeExtent_pos := by decide
  action := canonicalRetainedBoundarySwapAction
  periodic := canonicalRetainedBoundarySwapAction_period_two
  map_veq := by
    intro a b h rho
    exact Q'.eqv_trans _ _ _ (evalCanonicalPoly8_swap rho a)
      (Q'.eqv_trans _ _ _ (h (swapEnvironment8 rho))
        (Q'.eqv_symm (evalCanonicalPoly8_swap rho b)))
  map_add := by
    intro a b rho
    change
      evalCanonicalPoly8 rho (swapPoly8 (polyAdd8 a b)) ≈
        evalCanonicalPoly8 rho (polyAdd8 (swapPoly8 a) (swapPoly8 b))
    rw [swapPoly8_add]
    exact Q'.eqv_refl _
  map_neg := by
    intro a rho
    change
      evalCanonicalPoly8 rho (swapPoly8 (polyNeg8 a)) ≈
        evalCanonicalPoly8 rho (polyNeg8 (swapPoly8 a))
    rw [swapPoly8_neg]
    exact Q'.eqv_refl _
  map_smul := by
    intro s a rho
    change
      evalCanonicalPoly8 rho (swapPoly8 (polySmul8 s a)) ≈
        evalCanonicalPoly8 rho (polySmul8 s (swapPoly8 a))
    rw [swapPoly8_smul]
    exact Q'.eqv_refl _

end YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry.evalMono_swapMono8
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry.evalCanonicalPoly8_swap
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeGeometry.canonicalRetainedBoundarySwapGeometry
