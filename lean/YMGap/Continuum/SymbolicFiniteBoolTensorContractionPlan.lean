/-
# Constructive plans for finite Boolean-tensor contractions

`SymbolicFiniteBoolTensorContraction` proves the analytic estimate for one
binary contraction.  This module closes that estimate under an arbitrary
finite, explicitly typed contraction tree.

A leaf stores its actual symbolic Boolean tensor.  A `contract` node records
the size of the common innermost block and the two remaining free blocks, so
its indices enforce exactly the arities accepted by `boolTensorContract`.
A `rewire` node applies a certified signed Boolean wiring at any intermediate
arity.  Evaluation is therefore computational: it recursively evaluates the
children, performs the declared Gram-isometric reorderings, and applies each
contraction, without constructing Boolean assignment lists.

The mass of a plan is the product of the squared norms of its leaves.  The
main theorem says that the squared norm of the evaluated tensor is bounded by
this leaf mass.  The proof is square-root-free: at each node it composes the
one-step contraction bound with monotonicity of multiplication by
nonnegative rational quantities.

This syntax deliberately does not claim that a concrete tagged factor graph
has been compiled correctly.  That separate incidence theorem must supply a
plan whose shared blocks and port order agree with the graph.  Once supplied,
the theorem here is the complete analytic induction for that plan.

# Constructive discipline

There are no global assignment carriers, square roots, `Classical`,
`native_decide`, `sorry`/`admit`, or custom axioms.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensorContraction
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SymbolicFiniteBoolTensorContraction

/-! ## Typed contraction plans -/

/-- A finite binary contraction tree indexed by the arity of its output.

At a `contract shared leftFree rightFree left right` node, both inputs expose
the same `shared` innermost coordinates.  Evaluation contracts those
coordinates and retains `leftFree + rightFree` coordinates, with the output
convention inherited from `boolTensorContract`. -/
inductive BoolTensorContractionPlan : Nat -> Type
  | leaf (n : Nat) (tensor : BoolTensor n) :
      BoolTensorContractionPlan n
  | rewire (n : Nat) (wiring : SignedBoolWiring n)
      (child : BoolTensorContractionPlan n) :
      BoolTensorContractionPlan n
  | contract (shared leftFree rightFree : Nat)
      (left : BoolTensorContractionPlan (shared + leftFree))
      (right : BoolTensorContractionPlan (shared + rightFree)) :
      BoolTensorContractionPlan (leftFree + rightFree)

namespace BoolTensorContractionPlan

/-- Evaluate a typed contraction plan by recursively composing the structural
Boolean-tensor contraction primitive. -/
def eval : {n : Nat} -> BoolTensorContractionPlan n -> BoolTensor n
  | _, .leaf _ tensor => tensor
  | _, .rewire _ wiring child => wiring.act child.eval
  | _, .contract shared leftFree rightFree left right =>
      boolTensorContract shared leftFree rightFree left.eval right.eval

/-- Product of the squared Boolean-tensor norms of all leaves of a plan. -/
def leafMass : {n : Nat} -> BoolTensorContractionPlan n -> Q'
  | _, .leaf n tensor => boolTensorDot n tensor tensor
  | _, .rewire _ _ child => child.leafMass
  | _, .contract _ _ _ left right => left.leafMass * right.leafMass

/-- The product leaf mass is nonnegative.  This is proved simultaneously with
the contraction-tree structure and uses only positivity of the Boolean tensor
Gram form. -/
theorem leafMass_nonneg {n : Nat} (plan : BoolTensorContractionPlan n) :
    (0 : Q') <= plan.leafMass := by
  induction plan with
  | leaf n tensor =>
      exact (boolTensorForm n).self_nonneg tensor
  | rewire n wiring child childIH =>
      exact childIH
  | contract shared leftFree rightFree left right leftIH rightIH =>
      exact Q'.mul_nonneg left.leafMass right.leafMass leftIH rightIH

/-- **Finite contraction-tree Frobenius bound.**

The squared norm of the recursively evaluated output is at most the product
of the squared norms of all input leaves.  No square roots or enumeration of
the contracted Boolean assignments occurs. -/
theorem eval_normSq_le_leafMass {n : Nat}
    (plan : BoolTensorContractionPlan n) :
    boolTensorDot n plan.eval plan.eval <= plan.leafMass := by
  induction plan with
  | leaf n tensor =>
      exact Q'.le_refl' (boolTensorDot n tensor tensor)
  | rewire n wiring child childIH =>
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (wiring.gram_eqv child.eval child.eval)) childIH
  | contract shared leftFree rightFree left right leftIH rightIH =>
      have rightNormNonneg :
          (0 : Q') <=
            boolTensorDot (shared + rightFree) right.eval right.eval :=
        (boolTensorForm (shared + rightFree)).self_nonneg right.eval
      have leftMassNonneg : (0 : Q') <= left.leafMass :=
        left.leafMass_nonneg
      refine Q'.le_trans' _ _ _
        (boolTensorContract_normSq_le
          shared leftFree rightFree left.eval right.eval) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          (boolTensorDot (shared + leftFree) left.eval left.eval)
          left.leafMass
          (boolTensorDot (shared + rightFree) right.eval right.eval)
          leftIH rightNormNonneg) ?_
      exact Q'.mul_le_mul_of_nonneg_left
        (boolTensorDot (shared + rightFree) right.eval right.eval)
        right.leafMass left.leafMass rightIH leftMassNonneg

/-! ## Closed-plan specialization -/

/-- For a closed plan, the output is a rational scalar and its square is
bounded by the product of the input leaf squared norms. -/
theorem closed_eval_square_le_leafMass
    (plan : BoolTensorContractionPlan 0) :
    (show Q' from plan.eval) * (show Q' from plan.eval) <= plan.leafMass :=
  plan.eval_normSq_le_leafMass

/-- A rational whose square is at most one has absolute value at most one.
This order lemma is used only after exact channel normalization, so the
graphical estimate itself remains square-root-free. -/
theorem abs_le_one_of_square_le_one (x : Q')
    (hsquare : x * x <= (1 : Q')) :
    Q'.abs x <= (1 : Q') := by
  have honeSquare : (1 : Q') <= 1 * 1 :=
    Q'.ge_of_eqv (Q'.one_mul_eqv 1)
  refine Q'.abs_le ?_ ?_
  · by_cases hx : (0 : Q') <= x
    · exact Q'.le_trans' _ _ _ (by decide) hx
    · have hneg : (0 : Q') <= -x :=
        Q'.neg_nonneg_of_not_nonneg hx
      have hnegSquareEqv : ((-x) * (-x)).eqv (x * x) := by
        refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv x (-x)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.neg_eqv_congr (x * (-x)) (-(x * x))
            (Q'.mul_neg_eqv x x)) ?_
        exact Q'.neg_neg_eqv (x * x)
      have hnegSquare : (-x) * (-x) <= (1 : Q') * 1 :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hnegSquareEqv)
          (Q'.le_trans' _ _ _ hsquare honeSquare)
      have hnegLe : -x <= (1 : Q') :=
        CReal.le_of_sq_le_sq (by decide) hneg hnegSquare
      exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hnegLe)
        (Q'.le_of_eqv (Q'.neg_neg_eqv x))
  · by_cases hx : (0 : Q') <= x
    · have hxSquare : x * x <= (1 : Q') * 1 :=
        Q'.le_trans' _ _ _ hsquare honeSquare
      exact CReal.le_of_sq_le_sq (by decide) hx hxSquare
    · exact Q'.le_trans' _ _ _ (Q'.nonpos_of_not_nonneg hx) (by decide)

/-- A closed contraction plan of leaf mass at most one evaluates inside the
unit absolute-value interval.  This is the normalized corollary consumed by
the fixed-channel network bound. -/
theorem closed_eval_abs_le_one_of_leafMass_le_one
    (plan : BoolTensorContractionPlan 0)
    (hmass : plan.leafMass <= (1 : Q')) :
    Q'.abs (show Q' from plan.eval) <= (1 : Q') :=
  abs_le_one_of_square_le_one (show Q' from plan.eval)
    (Q'.le_trans' _ _ _ plan.closed_eval_square_le_leafMass hmass)

/-! ## Axiom audit -/

#print axioms BoolTensorContractionPlan.eval
#print axioms BoolTensorContractionPlan.leafMass
#print axioms BoolTensorContractionPlan.leafMass_nonneg
#print axioms BoolTensorContractionPlan.eval_normSq_le_leafMass
#print axioms BoolTensorContractionPlan.closed_eval_square_le_leafMass
#print axioms BoolTensorContractionPlan.abs_le_one_of_square_le_one
#print axioms BoolTensorContractionPlan.closed_eval_abs_le_one_of_leafMass_le_one

end BoolTensorContractionPlan

end YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan
