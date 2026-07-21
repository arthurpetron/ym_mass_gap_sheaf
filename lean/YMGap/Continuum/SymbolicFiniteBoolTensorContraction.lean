/-
# Structural contraction of finite Boolean tensors

This leaf supplies the square-root-free analytic primitive for finite graphical
tensor bounds.  A tensor of arity `shared + free` is read with the `free`
coordinates outermost and the `shared` coordinates innermost: natural-number
addition computes in its second argument, exactly as the recursive
`BoolTensor` carrier does.

`boolTensorContract` contracts the common innermost block of two tensors and
retains both free blocks.  Its norm-square is at most the product of the two
input norm-squares.  The proof never expands the common Boolean assignments.
It peels only free coordinates; when none remain, the result is precisely the
existing sharp Cauchy--Schwarz inequality for `boolTensorForm shared`.

The output convention is forced by the recursive arithmetic: right-free
coordinates are outermost, followed by left-free coordinates.  Downstream
tagged factor graphs may arrange their ports before applying this primitive.

# Constructive discipline

There are no assignment lists, fixed-depth expansions, square roots,
`Classical`, `native_decide`, `sorry`/`admit`, or custom axioms.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensor

namespace YMGap.Continuum.SymbolicFiniteBoolTensorContraction

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SymbolicFiniteBoolTensor

/-! ## Contracting against a tensor with no right-free coordinates -/

/-- Contract the innermost `shared` coordinates when only the left tensor has
free coordinates.  Since `BoolTensor (shared + leftFree)` exposes the free
coordinates first, this definition is structural in `leftFree`; its scalar
leaf is the existing Boolean-tensor dot product. -/
def boolTensorContractLeft (shared : Nat) :
    (leftFree : Nat) ->
      BoolTensor (shared + leftFree) ->
      BoolTensor shared ->
      BoolTensor leftFree
  | 0, left, right => boolTensorDot shared left right
  | leftFree + 1, left, right =>
      fun bit =>
        boolTensorContractLeft shared leftFree (left bit) right

/-- Contracting against a tensor with no free coordinates is norm
submultiplicative.  The scalar base case is sharp Cauchy--Schwarz; a free
Boolean fiber uses only branchwise monotonicity and right distributivity. -/
theorem boolTensorContractLeft_normSq_le (shared : Nat) :
    forall (leftFree : Nat)
      (left : BoolTensor (shared + leftFree))
      (right : BoolTensor shared),
      boolTensorDot leftFree
          (boolTensorContractLeft shared leftFree left right)
          (boolTensorContractLeft shared leftFree left right) <=
        boolTensorDot (shared + leftFree) left left *
          boolTensorDot shared right right
  | 0, left, right => by
      change
        boolTensorDot shared left right *
            boolTensorDot shared left right <=
          boolTensorDot shared left left *
            boolTensorDot shared right right
      exact (boolTensorForm shared).cauchy_schwarz left right
  | leftFree + 1, left, right => by
      change
        boolTensorDot leftFree
              (boolTensorContractLeft shared leftFree (left false) right)
              (boolTensorContractLeft shared leftFree (left false) right) +
            boolTensorDot leftFree
              (boolTensorContractLeft shared leftFree (left true) right)
              (boolTensorContractLeft shared leftFree (left true) right) <=
          (boolTensorDot (shared + leftFree)
                (left false) (left false) +
              boolTensorDot (shared + leftFree)
                (left true) (left true)) *
            boolTensorDot shared right right
      exact le_of_le_eqv
        (Q'.add_le_add
          (boolTensorContractLeft_normSq_le
            shared leftFree (left false) right)
          (boolTensorContractLeft_normSq_le
            shared leftFree (left true) right))
        (Q'.eqv_symm
          (QPoly.q_add_mul
            (boolTensorDot (shared + leftFree)
              (left false) (left false))
            (boolTensorDot (shared + leftFree)
              (left true) (left true))
            (boolTensorDot shared right right)))

/-! ## Two-sided free blocks -/

/-- Contract the common innermost `shared` Boolean block and retain the two
free blocks.  Right-free coordinates are emitted first; after they are peeled,
`boolTensorContractLeft` emits the left-free coordinates.  No shared-coordinate
assignment carrier is constructed. -/
def boolTensorContract (shared leftFree : Nat) :
    (rightFree : Nat) ->
      BoolTensor (shared + leftFree) ->
      BoolTensor (shared + rightFree) ->
      BoolTensor (leftFree + rightFree)
  | 0, left, right =>
      boolTensorContractLeft shared leftFree left right
  | rightFree + 1, left, right =>
      fun bit =>
        boolTensorContract shared leftFree rightFree left (right bit)

/-- **Square-root-free Boolean tensor contraction bound.**

The squared norm of a contraction along an arbitrary common Boolean block is
at most the product of the input squared norms.  The proof is structural only
in the free-coordinate counts.  Consequently the possibly large shared block
is consumed once by the already-proved generic Cauchy--Schwarz theorem rather
than by enumeration. -/
theorem boolTensorContract_normSq_le (shared leftFree : Nat) :
    forall (rightFree : Nat)
      (left : BoolTensor (shared + leftFree))
      (right : BoolTensor (shared + rightFree)),
      boolTensorDot (leftFree + rightFree)
          (boolTensorContract shared leftFree rightFree left right)
          (boolTensorContract shared leftFree rightFree left right) <=
        boolTensorDot (shared + leftFree) left left *
          boolTensorDot (shared + rightFree) right right
  | 0, left, right =>
      boolTensorContractLeft_normSq_le shared leftFree left right
  | rightFree + 1, left, right => by
      change
        boolTensorDot (leftFree + rightFree)
              (boolTensorContract shared leftFree rightFree
                left (right false))
              (boolTensorContract shared leftFree rightFree
                left (right false)) +
            boolTensorDot (leftFree + rightFree)
              (boolTensorContract shared leftFree rightFree
                left (right true))
              (boolTensorContract shared leftFree rightFree
                left (right true)) <=
          boolTensorDot (shared + leftFree) left left *
            (boolTensorDot (shared + rightFree)
                (right false) (right false) +
              boolTensorDot (shared + rightFree)
                (right true) (right true))
      exact le_of_le_eqv
        (Q'.add_le_add
          (boolTensorContract_normSq_le
            shared leftFree rightFree left (right false))
          (boolTensorContract_normSq_le
            shared leftFree rightFree left (right true)))
        (Q'.eqv_symm
          (Q'.mul_add_eqv
            (boolTensorDot (shared + leftFree) left left)
            (boolTensorDot (shared + rightFree)
              (right false) (right false))
            (boolTensorDot (shared + rightFree)
              (right true) (right true))))

/-! ## Axiom audit -/

#print axioms boolTensorContractLeft
#print axioms boolTensorContractLeft_normSq_le
#print axioms boolTensorContract
#print axioms boolTensorContract_normSq_le

end YMGap.Continuum.SymbolicFiniteBoolTensorContraction
