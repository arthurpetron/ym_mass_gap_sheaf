/-
# Off-diagonal four-valent intertwiner state and O(4) response

Four-valent recoupling mixes the two intertwiner coordinates, so a diagonal
spectral algebra is not closed under the physical F-move.  This file retains
the full rational `2 x 2` operator algebra in coordinates adapted to the
weighted intertwiner form `3 s^2 + d^2`.

A stored matrix `(a,b,c,d)` acts by

  `(s,t) |-> (a*s + b*t, 3*c*s + d*t)`.

In these coordinates the weighted adjoint simply swaps `b` and `c`; no square
roots or division by three are needed.  For every positive-norm intertwiner
state, the vector-state functional is proved normalized, positive on `M* M`,
additive, and rational-homogeneous.  The generic finite-functional lift then
gives the exact same-state quarter-turn response on four directional copies.

The physical pairing-A state is instantiated, and its positive partition is
proved invariant under the existing exact four-valent recoupling isometry.
Observable conjugation across overlapping F-moves remains the next gluing
step.
-/

import YMGap.Continuum.O4FiniteFunctionalLift
import YMGap.Continuum.SU2FourValentRecouplingCompleted

namespace YMGap.Continuum.SU2FourValentMatrixO4Response

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.O4FiniteFunctionalLift
open YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted
open YMGap.Continuum.SU2FourValentRecouplingCompleted

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Weighted rational `2 x 2` matrices -/

structure IntertwinerMat2 where
  a : Q'
  b : Q'
  c : Q'
  d : Q'
deriving DecidableEq, Repr

def matZero : IntertwinerMat2 := ⟨0, 0, 0, 0⟩
def matOne : IntertwinerMat2 := ⟨1, 0, 0, 1⟩

def matAdd (M N : IntertwinerMat2) : IntertwinerMat2 :=
  ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩

def matScale (q : Q') (M : IntertwinerMat2) : IntertwinerMat2 :=
  ⟨q * M.a, q * M.b, q * M.c, q * M.d⟩

/-- Composition in the weighted-coordinate representation. -/
def matMul (M N : IntertwinerMat2) : IntertwinerMat2 :=
  ⟨M.a * N.a + 3 * (M.b * N.c),
    M.a * N.b + M.b * N.d,
    M.c * N.a + M.d * N.c,
    3 * (M.c * N.b) + M.d * N.d⟩

/-- Adjoint for the metric `diag(3,1)`. -/
def matStar (M : IntertwinerMat2) : IntertwinerMat2 :=
  ⟨M.a, M.c, M.b, M.d⟩

def intertwinerMatAlg : LinearObsAlg where
  carrier := IntertwinerMat2
  zero := matZero
  add := matAdd
  one := matOne
  mul := matMul
  star := matStar
  smul := matScale

theorem intertwinerMat_one_ne_zero :
    intertwinerMatAlg.one ≠ intertwinerMatAlg.zero := by
  intro h
  have ha := congrArg IntertwinerMat2.a h
  exact (by decide : (1 : Q') ≠ 0) ha

def matApply (M : IntertwinerMat2) (x : Q' × Q') : Q' × Q' :=
  (M.a * x.1 + M.b * x.2,
    3 * (M.c * x.1) + M.d * x.2)

def intertwinerForm (x y : Q' × Q') : Q' :=
  3 * (x.1 * y.1) + x.2 * y.2

def intertwinerNorm (x : Q' × Q') : Q' := intertwinerForm x x

def matQuadratic (x : Q' × Q') (M : IntertwinerMat2) : Q' :=
  intertwinerForm x (matApply M x)

theorem intertwinerNorm_eq_gns (x : Q' × Q') :
    intertwinerNorm x ≈ intertwinerGNS.B x x := by
  change 3 * (x.1 * x.1) + x.2 * x.2 ≈
    3 * (x.1 * x.1) + 1 * (x.2 * x.2)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_symm (Q'.one_mul_eqv (x.2 * x.2)))

theorem intertwinerNorm_nonneg (x : Q' × Q') :
    (0 : Q') ≤ intertwinerNorm x := by
  unfold intertwinerNorm intertwinerForm
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg x.1))
    (q_mul_self_nonneg x.2)

theorem matQuadratic_one (x : Q' × Q') :
    matQuadratic x matOne ≈ intertwinerNorm x := by
  unfold matQuadratic matOne matApply intertwinerNorm intertwinerForm
  ring_qeqv

theorem matQuadratic_add (x : Q' × Q') (M N : IntertwinerMat2) :
    matQuadratic x (matAdd M N) ≈
      matQuadratic x M + matQuadratic x N := by
  unfold matQuadratic matAdd matApply intertwinerForm
  ring_qeqv

theorem matQuadratic_scale (x : Q' × Q') (q : Q')
    (M : IntertwinerMat2) :
    matQuadratic x (matScale q M) ≈ q * matQuadratic x M := by
  unfold matQuadratic matScale matApply intertwinerForm
  ring_qeqv

/-- Weighted-adjoint identity specialized to a vector-state square. -/
theorem matQuadratic_star_mul (x : Q' × Q') (M : IntertwinerMat2) :
    matQuadratic x (matMul (matStar M) M) ≈
      intertwinerNorm (matApply M x) := by
  unfold matQuadratic matMul matStar matApply intertwinerNorm intertwinerForm
  ring_qeqv

/-! ## Exact positive vector-state functional -/

def intertwinerStateExpectation (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) (M : IntertwinerMat2) : Q' :=
  Q'.divPos (matQuadratic x M) (intertwinerNorm x) hpos

theorem intertwinerStateExpectation_one (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) :
    intertwinerStateExpectation x hpos matOne ≈ 1 := by
  unfold intertwinerStateExpectation Q'.divPos
  refine Q'.eqv_trans _
    (intertwinerNorm x * Q'.recipPos (intertwinerNorm x) hpos) _
    (Q'.mul_eqv_congr_right _ _ _ (matQuadratic_one x)) ?_
  exact Q'.mul_recipPos_eqv (intertwinerNorm x) hpos

theorem intertwinerStateExpectation_positive (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) (M : IntertwinerMat2) :
    (0 : Q') ≤ intertwinerStateExpectation x hpos
      (matMul (matStar M) M) := by
  have hn : (0 : Q') ≤ matQuadratic x (matMul (matStar M) M) :=
    Q'.le_trans' _ _ _ (intertwinerNorm_nonneg (matApply M x))
      (Q'.ge_of_eqv (matQuadratic_star_mul x M))
  unfold intertwinerStateExpectation Q'.divPos
  exact Q'.mul_nonneg _ _ hn
    (Q'.le_of_lt (Q'.recipPos_pos (intertwinerNorm x) hpos))

theorem intertwinerStateExpectation_add (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) (M N : IntertwinerMat2) :
    intertwinerStateExpectation x hpos (matAdd M N) ≈
      intertwinerStateExpectation x hpos M +
        intertwinerStateExpectation x hpos N := by
  unfold intertwinerStateExpectation Q'.divPos
  refine Q'.eqv_trans _
    ((matQuadratic x M + matQuadratic x N) *
      Q'.recipPos (intertwinerNorm x) hpos) _
    (Q'.mul_eqv_congr_right _ _ _ (matQuadratic_add x M N)) ?_
  exact Q'.add_mul_eqv (matQuadratic x M) (matQuadratic x N)
    (Q'.recipPos (intertwinerNorm x) hpos)

theorem intertwinerStateExpectation_scale (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) (q : Q')
    (M : IntertwinerMat2) :
    intertwinerStateExpectation x hpos (matScale q M) ≈
      q * intertwinerStateExpectation x hpos M := by
  unfold intertwinerStateExpectation Q'.divPos
  refine Q'.eqv_trans _
    ((q * matQuadratic x M) * Q'.recipPos (intertwinerNorm x) hpos) _
    (Q'.mul_eqv_congr_right _ _ _ (matQuadratic_scale x q M)) ?_
  exact Q'.mul_assoc_eqv q (matQuadratic x M)
    (Q'.recipPos (intertwinerNorm x) hpos)

def intertwinerStateFunctional (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) :
    QLinearFunctional intertwinerMatAlg where
  E := intertwinerStateExpectation x hpos
  normalized := intertwinerStateExpectation_one x hpos
  positive := intertwinerStateExpectation_positive x hpos
  additive := intertwinerStateExpectation_add x hpos
  homogeneous := intertwinerStateExpectation_scale x hpos

/-! ## The physical pairing-A state and its F-move-stable partition -/

theorem pairingA_intertwinerNorm_pos :
    (0 : Q') < intertwinerNorm pairingACoord := by
  unfold intertwinerNorm intertwinerForm pairingACoord
  decide

def pairingAStateFunctional : QLinearFunctional intertwinerMatAlg :=
  intertwinerStateFunctional pairingACoord pairingA_intertwinerNorm_pos

theorem recoupled_intertwinerNorm_pos (x : Q' × Q')
    (hpos : (0 : Q') < intertwinerNorm x) :
    (0 : Q') < intertwinerNorm (intertwinerRecoupling x) := by
  exact Q'.pos_of_lt_of_le hpos
    (Q'.ge_of_eqv
      (Q'.eqv_trans _ _ _ (intertwinerNorm_eq_gns (intertwinerRecoupling x))
        (Q'.eqv_trans _ _ _ (intertwinerRecoupling_norm x)
          (Q'.eqv_symm (intertwinerNorm_eq_gns x)))))

theorem intertwiner_partition_recoupling_invariant (x : Q' × Q') :
    intertwinerNorm (intertwinerRecoupling x) ≈ intertwinerNorm x :=
  Q'.eqv_trans _ _ _ (intertwinerNorm_eq_gns (intertwinerRecoupling x))
    (Q'.eqv_trans _ _ _ (intertwinerRecoupling_norm x)
      (Q'.eqv_symm (intertwinerNorm_eq_gns x)))

/-! ## Exact directional response for the off-diagonal algebra -/

theorem pairingAQuarterTurn_same_state_response
    (o : FunctionalDir4 intertwinerMatAlg) (j : Nat) :
    ((functionalDir4Scaling pairingAStateFunctional).atSpacing j).E
        ((functionalQuarterTurnHom intertwinerMatAlg).map o) ≤
      ((functionalDir4Scaling pairingAStateFunctional).atSpacing j).E o +
        functionalDir4Response pairingAStateFunctional o *
          breakCoeff halfScalingDecay j
    /\
    ((functionalDir4Scaling pairingAStateFunctional).atSpacing j).E o ≤
      ((functionalDir4Scaling pairingAStateFunctional).atSpacing j).E
          ((functionalQuarterTurnHom intertwinerMatAlg).map o) +
        functionalDir4Response pairingAStateFunctional o *
          breakCoeff halfScalingDecay j :=
  functionalQuarterTurn_same_state_response pairingAStateFunctional
    intertwinerMat_one_ne_zero o j

theorem pairingA_limit_quarterTurn_invariant
    (o : FunctionalDir4 intertwinerMatAlg) :
    RegularCReal.Equiv
      (limitE (functionalDir4Scaling pairingAStateFunctional)
        ((functionalQuarterTurnHom intertwinerMatAlg).map o))
      (limitE (functionalDir4Scaling pairingAStateFunctional) o) :=
  functionalDir4_limit_quarterTurn_invariant pairingAStateFunctional
    intertwinerMat_one_ne_zero o

end YMGap.Continuum.SU2FourValentMatrixO4Response

#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.matQuadratic_star_mul
#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.intertwinerStateFunctional
#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.pairingAStateFunctional
#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.intertwiner_partition_recoupling_invariant
#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.pairingAQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2FourValentMatrixO4Response.pairingA_limit_quarterTurn_invariant
