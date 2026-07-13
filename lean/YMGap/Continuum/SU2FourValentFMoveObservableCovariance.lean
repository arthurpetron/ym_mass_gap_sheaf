/-
# Four-valent F-move covariance of the full observable algebra

The four-valent partition is invariant under recoupling only if observables
are transported with the state.  This file performs that transport for the
full off-diagonal weighted matrix algebra.  The rational recoupling matrix is
unitary for the `diag(3,1)` form; conjugation by it intertwines matrix action,
respects product action up to rational equivalence, and leaves the normalized
vector-state expectation unchanged when the state is recoupled.

This closes observable covariance for one four-valent F-move.  Compatibility
of conjugations assigned by overlapping cells, arbitrary labels, and the
pentagon network remains open.
-/

import YMGap.Continuum.SU2FourValentMatrixO4Response
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2FourValentFMoveObservableCovariance

set_option maxHeartbeats 1200000
set_option maxRecDepth 18000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted
open YMGap.Continuum.SU2FourValentRecouplingCompleted
open YMGap.Continuum.SU2FourValentMatrixO4Response
open YMGap.Continuum.RingNormaliser

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

/-- The physical recoupling matrix in weighted coordinates. -/
def recouplingMat : IntertwinerMat2 :=
  let h := SU2FourValentRecouplingCompleted.half
  ⟨h, -h, h, h⟩

/-- Its weighted adjoint, hence inverse. -/
def recouplingInvMat : IntertwinerMat2 :=
  matStar recouplingMat

/-- Transport an observable from the old pairing channel to the recoupled
channel. -/
def fMoveConjugate (M : IntertwinerMat2) : IntertwinerMat2 :=
  matMul recouplingMat (matMul M recouplingInvMat)

def VecEq (x y : Q' × Q') : Prop := x.1 ≈ y.1 ∧ x.2 ≈ y.2

theorem vecEq_symm {x y : Q' × Q'} (h : VecEq x y) : VecEq y x :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩

theorem vecEq_trans {x y z : Q' × Q'}
    (hxy : VecEq x y) (hyz : VecEq y z) : VecEq x z :=
  ⟨Q'.eqv_trans _ _ _ hxy.1 hyz.1,
    Q'.eqv_trans _ _ _ hxy.2 hyz.2⟩

theorem matApply_congr (M : IntertwinerMat2) {x y : Q' × Q'}
    (h : VecEq x y) : VecEq (matApply M x) (matApply M y) := by
  unfold VecEq matApply
  exact ⟨QPoly.q_add_congr
      (Q'.mul_eqv_congr_left M.a _ _ h.1)
      (Q'.mul_eqv_congr_left M.b _ _ h.2),
    QPoly.q_add_congr
      (Q'.mul_eqv_congr_left 3 _ _
        (Q'.mul_eqv_congr_left M.c _ _ h.1))
      (Q'.mul_eqv_congr_left M.d _ _ h.2)⟩

theorem matApply_mul (M N : IntertwinerMat2) (x : Q' × Q') :
    VecEq (matApply (matMul M N) x) (matApply M (matApply N x)) := by
  unfold VecEq matApply matMul
  constructor <;> ring_qeqv

theorem intertwinerRecoupling_congr {x y : Q' × Q'}
    (h : VecEq x y) :
    VecEq (intertwinerRecoupling x) (intertwinerRecoupling y) := by
  unfold VecEq intertwinerRecoupling
  exact ⟨Q'.mul_eqv_congr_left
      SU2FourValentRecouplingCompleted.half _ _
      (QPoly.q_add_congr h.1 (Q'.neg_eqv_congr _ _ h.2)),
    Q'.mul_eqv_congr_left
      SU2FourValentRecouplingCompleted.half _ _
      (QPoly.q_add_congr
        (Q'.mul_eqv_congr_left 3 _ _ h.1) h.2)⟩

theorem recouplingMat_applies (x : Q' × Q') :
    (matApply recouplingMat x).1 ≈ (intertwinerRecoupling x).1 ∧
      (matApply recouplingMat x).2 ≈ (intertwinerRecoupling x).2 := by
  unfold recouplingMat matApply intertwinerRecoupling
  constructor <;> ring_qeqv

private def inverseFirstLeft : PolyExpr :=
  let h := PolyExpr.var 0
  let s := PolyExpr.var 1
  let d := PolyExpr.var 2
  .add (.mul h (.mul h (.add s (.neg d))))
    (.mul h (.mul h (.add (.mul (.const 3) s) d)))

private def inverseFirstRight : PolyExpr :=
  let h := PolyExpr.var 0
  let s := PolyExpr.var 1
  .mul (.mul h h) (.mul (.const 4) s)

private def inverseSecondLeft : PolyExpr :=
  let h := PolyExpr.var 0
  let s := PolyExpr.var 1
  let d := PolyExpr.var 2
  .add (.mul (.const 3)
      (.mul (.neg h) (.mul h (.add s (.neg d)))))
    (.mul h (.mul h (.add (.mul (.const 3) s) d)))

private def inverseSecondRight : PolyExpr :=
  let h := PolyExpr.var 0
  let d := PolyExpr.var 2
  .mul (.mul h h) (.mul (.const 4) d)

private theorem inverseFirst_normal :
    normalize inverseFirstLeft = normalize inverseFirstRight := by decide

private theorem inverseSecond_normal :
    normalize inverseSecondLeft = normalize inverseSecondRight := by decide

private theorem inverse_first_regroup (h s d : Q') :
    h * (h * (s + -d)) + h * (h * (3 * s + d)) ≈
      (h * h) * (4 * s) := by
  have hp := poly_identity_of_normal_eq inverseFirstLeft inverseFirstRight
    inverseFirst_normal (fun | 0 => h | 1 => s | _ => d)
  simpa [inverseFirstLeft, inverseFirstRight, RingNormaliser.eval] using hp

private theorem inverse_second_regroup (h s d : Q') :
    3 * ((-h) * (h * (s + -d))) + h * (h * (3 * s + d)) ≈
      (h * h) * (4 * d) := by
  have hp := poly_identity_of_normal_eq inverseSecondLeft inverseSecondRight
    inverseSecond_normal (fun | 0 => h | 1 => s | _ => d)
  simpa [inverseSecondLeft, inverseSecondRight, RingNormaliser.eval] using hp

theorem recoupling_inverse_applies (x : Q' × Q') :
    VecEq (matApply recouplingInvMat (intertwinerRecoupling x)) x := by
  let h := SU2FourValentRecouplingCompleted.half
  change
    h * (h * (x.1 + -x.2)) + h * (h * (3 * x.1 + x.2)) ≈ x.1 ∧
      3 * ((-h) * (h * (x.1 + -x.2))) +
        h * (h * (3 * x.1 + x.2)) ≈ x.2
  constructor
  · refine Q'.eqv_trans _ ((h * h) * (4 * x.1)) _
      (inverse_first_regroup h x.1 x.2) ?_
    refine Q'.eqv_trans _ (((h * h) * 4) * x.1) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (h * h) 4 x.1)) ?_
    refine Q'.eqv_trans _ (1 * x.1) _
      (Q'.mul_eqv_congr_right _ _ x.1 half_square_four) ?_
    exact Q'.one_mul_eqv x.1
  · refine Q'.eqv_trans _ ((h * h) * (4 * x.2)) _
      (inverse_second_regroup h x.1 x.2) ?_
    refine Q'.eqv_trans _ (((h * h) * 4) * x.2) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (h * h) 4 x.2)) ?_
    refine Q'.eqv_trans _ (1 * x.2) _
      (Q'.mul_eqv_congr_right _ _ x.2 half_square_four) ?_
    exact Q'.one_mul_eqv x.2

/-- Conjugated action on the recoupled state is the recoupling of the old
action.  Both coordinates are exact rational identities. -/
theorem fMoveConjugate_action_covariant (M : IntertwinerMat2)
    (x : Q' × Q') :
    VecEq (matApply (fMoveConjugate M) (intertwinerRecoupling x))
      (intertwinerRecoupling (matApply M x)) := by
  unfold fMoveConjugate
  have h₁ := matApply_mul recouplingMat (matMul M recouplingInvMat)
    (intertwinerRecoupling x)
  have h₂ := matApply_congr recouplingMat
    (matApply_mul M recouplingInvMat (intertwinerRecoupling x))
  have h₃ := matApply_congr recouplingMat
    (matApply_congr M (recoupling_inverse_applies x))
  exact vecEq_trans h₁
    (vecEq_trans h₂ (vecEq_trans h₃ (recouplingMat_applies (matApply M x))))

/-- Product preservation in operational form on every recoupled state. -/
theorem fMoveConjugate_mul_action (M N : IntertwinerMat2)
    (x : Q' × Q') :
    VecEq
      (matApply (fMoveConjugate (matMul M N)) (intertwinerRecoupling x))
      (matApply (matMul (fMoveConjugate M) (fMoveConjugate N))
        (intertwinerRecoupling x)) := by
  have h₁ := fMoveConjugate_action_covariant (matMul M N) x
  have h₂ := intertwinerRecoupling_congr (matApply_mul M N x)
  have h₃ := vecEq_symm
    (fMoveConjugate_action_covariant M (matApply N x))
  have h₄ := matApply_congr (fMoveConjugate M)
    (vecEq_symm (fMoveConjugate_action_covariant N x))
  have h₅ := vecEq_symm
    (matApply_mul (fMoveConjugate M) (fMoveConjugate N)
      (intertwinerRecoupling x))
  exact vecEq_trans h₁
    (vecEq_trans h₂ (vecEq_trans h₃ (vecEq_trans h₄ h₅)))

theorem intertwinerForm_congr_right (x : Q' × Q') {y z : Q' × Q'}
    (h : VecEq y z) : intertwinerForm x y ≈ intertwinerForm x z := by
  unfold intertwinerForm
  exact QPoly.q_add_congr
    (Q'.mul_eqv_congr_left 3 _ _
      (Q'.mul_eqv_congr_left x.1 _ _ h.1))
    (Q'.mul_eqv_congr_left x.2 _ _ h.2)

private def formRecouplingLeft : PolyExpr :=
  let h := PolyExpr.var 0
  let s := PolyExpr.var 1
  let d := PolyExpr.var 2
  let u := PolyExpr.var 3
  let v := PolyExpr.var 4
  .add
    (.mul (.const 3)
      (.mul (.mul h (.add s (.neg d)))
        (.mul h (.add u (.neg v)))))
    (.mul (.mul h (.add (.mul (.const 3) s) d))
      (.mul h (.add (.mul (.const 3) u) v)))

private def formRecouplingRight : PolyExpr :=
  let h := PolyExpr.var 0
  let s := PolyExpr.var 1
  let d := PolyExpr.var 2
  let u := PolyExpr.var 3
  let v := PolyExpr.var 4
  .mul (.mul h h)
    (.mul (.const 4)
      (.add (.mul (.const 3) (.mul s u)) (.mul d v)))

private theorem formRecoupling_normal :
    normalize formRecouplingLeft = normalize formRecouplingRight := by decide

private theorem form_recoupling_regroup (h s d u v : Q') :
    3 * ((h * (s + -d)) * (h * (u + -v))) +
        (h * (3 * s + d)) * (h * (3 * u + v)) ≈
      (h * h) * (4 * (3 * (s * u) + d * v)) := by
  have hp := poly_identity_of_normal_eq formRecouplingLeft formRecouplingRight
    formRecoupling_normal
    (fun | 0 => h | 1 => s | 2 => d | 3 => u | _ => v)
  simpa [formRecouplingLeft, formRecouplingRight, RingNormaliser.eval] using hp

theorem intertwinerForm_recoupling (x y : Q' × Q') :
    intertwinerForm (intertwinerRecoupling x)
        (intertwinerRecoupling y) ≈ intertwinerForm x y := by
  let h := SU2FourValentRecouplingCompleted.half
  change
    3 * ((h * (x.1 + -x.2)) * (h * (y.1 + -y.2))) +
        (h * (3 * x.1 + x.2)) * (h * (3 * y.1 + y.2)) ≈
      3 * (x.1 * y.1) + x.2 * y.2
  refine Q'.eqv_trans _
    ((h * h) * (4 * (3 * (x.1 * y.1) + x.2 * y.2))) _
    (form_recoupling_regroup h x.1 x.2 y.1 y.2) ?_
  refine Q'.eqv_trans _
    (((h * h) * 4) * (3 * (x.1 * y.1) + x.2 * y.2)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (h * h) 4 _)) ?_
  refine Q'.eqv_trans _
    (1 * (3 * (x.1 * y.1) + x.2 * y.2)) _
    (Q'.mul_eqv_congr_right _ _ _ half_square_four) ?_
  exact Q'.one_mul_eqv _

/-- The unnormalized vector-state numerator is covariant under simultaneous
state recoupling and observable conjugation. -/
theorem matQuadratic_fMove_covariant (x : Q' × Q')
    (M : IntertwinerMat2) :
    matQuadratic (intertwinerRecoupling x) (fMoveConjugate M) ≈
      matQuadratic x M := by
  unfold matQuadratic
  refine Q'.eqv_trans _
    (intertwinerForm (intertwinerRecoupling x)
      (intertwinerRecoupling (matApply M x))) _ ?_ ?_
  · exact intertwinerForm_congr_right (intertwinerRecoupling x)
      (fMoveConjugate_action_covariant M x)
  · exact intertwinerForm_recoupling x (matApply M x)

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : (p * q') ≈ (p' * q)) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : ((c * q) * q') ≈ (p' * q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : (p * q') ≈ ((c * q) * q') :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ (c * q) := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

private theorem divPos_eqv_congr {p p' q q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hp : p ≈ p') (hden : q ≈ q') :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  apply divPos_eqv_divPos_of_cross hq hq'
  exact Q'.eqv_trans _ (p' * q') _
    (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.mul_eqv_congr_left p' _ _ (Q'.eqv_symm hden))

/-- The normalized positive state itself is covariant under the physical
F-move, not merely its partition. -/
theorem intertwinerStateExpectation_fMove_covariant
    (x : Q' × Q') (hpos : (0 : Q') < intertwinerNorm x)
    (M : IntertwinerMat2) :
    intertwinerStateExpectation (intertwinerRecoupling x)
        (recoupled_intertwinerNorm_pos x hpos) (fMoveConjugate M) ≈
      intertwinerStateExpectation x hpos M := by
  unfold intertwinerStateExpectation
  apply divPos_eqv_congr
  · exact matQuadratic_fMove_covariant x M
  · exact intertwiner_partition_recoupling_invariant x

theorem pairingAStateExpectation_fMove_covariant (M : IntertwinerMat2) :
    intertwinerStateExpectation (intertwinerRecoupling pairingACoord)
        (recoupled_intertwinerNorm_pos pairingACoord
          pairingA_intertwinerNorm_pos) (fMoveConjugate M) ≈
      pairingAStateFunctional.E M :=
  intertwinerStateExpectation_fMove_covariant pairingACoord
    pairingA_intertwinerNorm_pos M

end YMGap.Continuum.SU2FourValentFMoveObservableCovariance

#print axioms YMGap.Continuum.SU2FourValentFMoveObservableCovariance.fMoveConjugate_action_covariant
#print axioms YMGap.Continuum.SU2FourValentFMoveObservableCovariance.fMoveConjugate_mul_action
#print axioms YMGap.Continuum.SU2FourValentFMoveObservableCovariance.matQuadratic_fMove_covariant
#print axioms YMGap.Continuum.SU2FourValentFMoveObservableCovariance.intertwinerStateExpectation_fMove_covariant
#print axioms YMGap.Continuum.SU2FourValentFMoveObservableCovariance.pairingAStateExpectation_fMove_covariant
