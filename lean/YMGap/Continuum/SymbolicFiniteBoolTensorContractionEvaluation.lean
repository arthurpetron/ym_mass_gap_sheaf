/-
# Pointwise semantics of finite Boolean-tensor contraction

The graphical estimate is useful for the Wilson coefficient only after its
typed contraction is identified with the literal nested Boolean sum.  This
file supplies that semantic bridge for one binary contraction.

At fixed free-coordinate words, `boolTensorContract` is exactly the structural
sum over the common Boolean word of the product of the two input evaluations.
The theorem is depth-generic and constructs no assignment list.

# Constructive discipline

There is no `Classical`, assignment carrier, square root, `native_decide`,
`sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensorContraction
import YMGap.Continuum.SymbolicFiniteBoolTensorPortReordering

namespace YMGap.Continuum.SymbolicFiniteBoolTensorContractionEvaluation

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SymbolicFiniteBoolTensorContraction

/-! ## Free-coordinate specialization -/

/-- Fix the outer `free` coordinates of a tensor and retain its innermost
`shared`-coordinate tensor. -/
def applyOuter (shared : Nat) :
    {free : Nat} ->
      BoolTensor (shared + free) -> PortTuple Bool free -> BoolTensor shared
  | 0, tensor, .nil => tensor
  | free + 1, tensor, .cons bit bits =>
      applyOuter shared (tensor bit) bits

/-- Evaluating at an outer-then-inner word is evaluation of the residual
inner tensor after the outer word has been fixed. -/
theorem evalAt_outerThenInner (shared : Nat) :
    forall {free : Nat}
      (tensor : BoolTensor (shared + free))
      (outer : PortTuple Bool free)
      (inner : PortTuple Bool shared),
      evalAt tensor (PortTuple.outerThenInner outer inner) =
        evalAt (applyOuter shared tensor outer) inner
  | 0, tensor, .nil, inner => rfl
  | free + 1, tensor, .cons bit bits, inner =>
      evalAt_outerThenInner shared (tensor bit) bits inner

/-! ## Dot product as the literal structural Boolean sum -/

/-- Sum a rational family over all Boolean tuples of a fixed arity, by
structural binding rather than by materializing a list of assignments. -/
def boolTupleSum : (n : Nat) -> (PortTuple Bool n -> Q') -> Q'
  | 0, family => family .nil
  | n + 1, family =>
      boolTupleSum n (fun tail => family (.cons false tail)) +
        boolTupleSum n (fun tail => family (.cons true tail))

/-- The recursive Boolean-tensor dot product is exactly the nested Boolean
sum of pointwise products. -/
theorem boolTensorDot_eq_boolTupleSum :
    forall (n : Nat) (left right : BoolTensor n),
      boolTensorDot n left right =
        boolTupleSum n (fun bits => evalAt left bits * evalAt right bits)
  | 0, left, right => rfl
  | n + 1, left, right => by
      change
        boolTensorDot n (left false) (right false) +
            boolTensorDot n (left true) (right true) =
          boolTupleSum n
              (fun tail => evalAt (left false) tail *
                evalAt (right false) tail) +
            boolTupleSum n
              (fun tail => evalAt (left true) tail *
                evalAt (right true) tail)
      rw [boolTensorDot_eq_boolTupleSum n (left false) (right false),
        boolTensorDot_eq_boolTupleSum n (left true) (right true)]

/-! ## Pointwise contraction semantics -/

/-- Pointwise semantics when only the left tensor has free coordinates. -/
theorem boolTensorContractLeft_evalAt (shared : Nat) :
    forall (leftFree : Nat)
      (left : BoolTensor (shared + leftFree))
      (right : BoolTensor shared)
      (leftBits : PortTuple Bool leftFree),
      evalAt (boolTensorContractLeft shared leftFree left right) leftBits =
        boolTensorDot shared (applyOuter shared left leftBits) right
  | 0, left, right, .nil => rfl
  | leftFree + 1, left, right, .cons bit bits =>
      boolTensorContractLeft_evalAt shared leftFree (left bit) right bits

/-- Fixing the two free-coordinate words in a binary contraction leaves the
dot product over the common innermost block. -/
theorem boolTensorContract_evalAt (shared leftFree : Nat) :
    forall (rightFree : Nat)
      (left : BoolTensor (shared + leftFree))
      (right : BoolTensor (shared + rightFree))
      (leftBits : PortTuple Bool leftFree)
      (rightBits : PortTuple Bool rightFree),
      evalAt (boolTensorContract shared leftFree rightFree left right)
          (PortTuple.outerThenInner rightBits leftBits) =
        boolTensorDot shared
          (applyOuter shared left leftBits)
          (applyOuter shared right rightBits)
  | 0, left, right, leftBits, .nil =>
      boolTensorContractLeft_evalAt shared leftFree left right leftBits
  | rightFree + 1, left, right, leftBits, .cons bit bits =>
      boolTensorContract_evalAt shared leftFree rightFree
        left (right bit) leftBits bits

/-- **Literal nested-sum semantics of one contraction.**

At every pair of free-coordinate words, the contraction is exactly the
structural sum over the common Boolean word of the product of the two input
tensor evaluations. -/
theorem boolTensorContract_evalAt_eq_boolTupleSum
    (shared leftFree rightFree : Nat)
    (left : BoolTensor (shared + leftFree))
    (right : BoolTensor (shared + rightFree))
    (leftBits : PortTuple Bool leftFree)
    (rightBits : PortTuple Bool rightFree) :
    evalAt (boolTensorContract shared leftFree rightFree left right)
        (PortTuple.outerThenInner rightBits leftBits) =
      boolTupleSum shared (fun sharedBits =>
        evalAt left (PortTuple.outerThenInner leftBits sharedBits) *
          evalAt right
            (PortTuple.outerThenInner rightBits sharedBits)) := by
  rw [boolTensorContract_evalAt,
    boolTensorDot_eq_boolTupleSum]
  apply congrArg (boolTupleSum shared)
  funext sharedBits
  rw [evalAt_outerThenInner, evalAt_outerThenInner]

/-! ## Axiom audit -/

#print axioms applyOuter
#print axioms evalAt_outerThenInner
#print axioms boolTupleSum
#print axioms boolTensorDot_eq_boolTupleSum
#print axioms boolTensorContractLeft_evalAt
#print axioms boolTensorContract_evalAt
#print axioms boolTensorContract_evalAt_eq_boolTupleSum

end YMGap.Continuum.SymbolicFiniteBoolTensorContractionEvaluation
