/-
# Symbolic finite Boolean tensors and Gram-preserving wirings

This module supplies a depth-generic Boolean tensor carrier and proves its
positive pre-inner form recursively.  The coordinate operators below are
compiled from local Gram isometries; consequently downstream finite tensor
kernels can use their invariance laws without unfolding a concrete Boolean
depth or enumerating assignments.

The epsilon operator is purely the two-coordinate antisymmetric wiring.  Its
laws here are independent of SU(2); representation-theoretic consumers only
need to identify their chosen coordinates with this generic calculus.

# Constructive discipline

Every proof is structural in the tensor depth.  There are no assignment
lists, concrete-depth Boolean expansions, broad simplification calls,
`Classical`, `native_decide`, `sorry`/`admit`, or custom axioms.
-/

import YMGap.Continuum.PositiveChannelTraceBound

namespace YMGap.Continuum.OSReconstructionProgress.PreInnerForm

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-- Regroup two three-term quadratics and distribute their three common
coefficients.  This fixed structural interchange is the entire algebraic
content of positivity for a Boolean direct sum. -/
private theorem boolFiberQuadratic_eqv
    (alpha beta gamma A0 A1 M0 M1 C0 C1 : Q') :
    (((alpha * A0 + beta * M0) + gamma * C0) +
        ((alpha * A1 + beta * M1) + gamma * C1)) ≈
      ((alpha * (A0 + A1) + beta * (M0 + M1)) +
        gamma * (C0 + C1)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner
      (alpha * A0 + beta * M0) (gamma * C0)
      (alpha * A1 + beta * M1) (gamma * C1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      ((alpha * A0 + beta * M0) + (alpha * A1 + beta * M1))
      ((alpha * A0 + alpha * A1) + (beta * M0 + beta * M1))
      (gamma * C0 + gamma * C1)
      (Q'.add_swap_inner
        (alpha * A0) (beta * M0) (alpha * A1) (beta * M1))) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_congr
      (Q'.eqv_symm (Q'.mul_add_eqv alpha A0 A1))
      (Q'.eqv_symm (Q'.mul_add_eqv beta M0 M1)))
    (Q'.eqv_symm (Q'.mul_add_eqv gamma C0 C1))

/-- Orthogonal direct sum over one Boolean coordinate. -/
def boolFiber {V : Type} (F : PreInnerForm V) :
    PreInnerForm (Bool -> V) where
  B := fun x y => F.B (x false) (y false) + F.B (x true) (y true)
  nonnegQuad := by
    intro s r a b
    have hFalse := F.nonnegQuad s r (a false) (b false)
    have hTrue := F.nonnegQuad s r (a true) (b true)
    refine le_of_le_eqv (Q'.zero_le_add _ _ hFalse hTrue) ?_
    exact boolFiberQuadratic_eqv
      (s * s) (2 * (s * r)) (r * r)
      (F.B (a false) (a false)) (F.B (a true) (a true))
      (F.B (a false) (b false)) (F.B (a true) (b true))
      (F.B (b false) (b false)) (F.B (b true) (b true))

end YMGap.Continuum.OSReconstructionProgress.PreInnerForm

namespace YMGap.Continuum.PositiveChannelTraceBound.GramIsometry

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

/-- Composition of Gram isometries, in map-composition order. -/
def comp {V : Type} {F : PreInnerForm V}
    (outer inner : GramIsometry F) : GramIsometry F where
  map := fun x => outer.map (inner.map x)
  gram_eqv := fun x y =>
    Q'.eqv_trans _ _ _
      (outer.gram_eqv (inner.map x) (inner.map y))
      (inner.gram_eqv x y)

end YMGap.Continuum.PositiveChannelTraceBound.GramIsometry

namespace YMGap.Continuum.SymbolicFiniteBoolTensor

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveChannelTraceBound

local infix:50 " ≈ " => Q'.eqv

/-! ## Recursive carrier and pre-inner form -/

/-- Curried functions on `n` ordered Boolean coordinates, with rational
leaves.  The outermost function is the first coordinate. -/
def BoolTensor : Nat -> Type
  | 0 => Q'
  | n + 1 => Bool -> BoolTensor n

/-- Scalar multiplication, defined recursively without materializing a
finite assignment family. -/
def tensorScale : (n : Nat) -> Q' -> BoolTensor n -> BoolTensor n
  | 0, q, x => q * (show Q' from x)
  | n + 1, q, x => fun bit => tensorScale n q (x bit)

/-- Exact scalar dot product at a tensor leaf. -/
def scalarDotForm : PreInnerForm Q' where
  B := fun x y => x * y
  nonnegQuad := by
    intro s r x y
    exact le_of_le_eqv
      (SumOfSquares.q_mul_self_nonneg (s * x + r * y))
      (unweighted_quad_eqv s r x y)

/-- The unweighted Boolean tensor dot product as an iterated orthogonal
direct sum. -/
def boolTensorForm : (n : Nat) -> PreInnerForm (BoolTensor n)
  | 0 => scalarDotForm
  | n + 1 => (boolTensorForm n).boolFiber

/-- Rational dot product on the symbolic Boolean tensor carrier. -/
def boolTensorDot (n : Nat) (x y : BoolTensor n) : Q' :=
  (boolTensorForm n).B x y

/-- Leaf equation for the tensor dot product. -/
theorem boolTensorDot_zero (x y : Q') :
    boolTensorDot 0 x y = x * y := rfl

/-- One-step fiber equation for the tensor dot product. -/
theorem boolTensorDot_succ (n : Nat) (x y : BoolTensor (n + 1)) :
    boolTensorDot (n + 1) x y =
      boolTensorDot n (x false) (y false) +
        boolTensorDot n (x true) (y true) := rfl

/-- Scaling both tensor arguments pulls out the product of the two scalars.
The proof follows the recursive carrier and never unfolds a fixed depth. -/
theorem boolTensorDot_scale
    (n : Nat) (a b : Q') (x y : BoolTensor n) :
    boolTensorDot n (tensorScale n a x) (tensorScale n b y) ≈
      (a * b) * boolTensorDot n x y := by
  induction n with
  | zero =>
      change
        (a * (show Q' from x)) * (b * (show Q' from y)) ≈
          (a * b) * ((show Q' from x) * (show Q' from y))
      exact mul4_rearrange a (show Q' from x) b (show Q' from y)
  | succ n ih =>
      refine Q'.eqv_trans _ _ _
        (QPoly.q_add_congr
          (ih (x := x false) (y := y false))
          (ih (x := x true) (y := y true))) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv (a * b)
          (boolTensorDot n (x false) (y false))
          (boolTensorDot n (x true) (y true)))

/-! ## Structural tensor product -/

/-- Transport a symbolic tensor along an equality of arities.  This is the
only transport needed below: Lean's natural-number addition computes in its
second argument, whereas tensor concatenation is structurally recursive in
the first tensor. -/
def tensorCast {m n : Nat} (h : m = n) (x : BoolTensor m) : BoolTensor n :=
  h ▸ x

/-- Simultaneous arity transport of both entries does not change their dot
product. -/
theorem boolTensorDot_tensorCast {m n : Nat} (h : m = n)
    (x y : BoolTensor m) :
    boolTensorDot n (tensorCast h x) (tensorCast h y) =
      boolTensorDot m x y := by
  cases h
  rfl

/-- Concatenate an `m`-coordinate tensor with an `n`-coordinate tensor.
At the scalar leaf of the first tensor, its value scales the entire second
tensor; a Boolean fiber of the first tensor is prepended recursively. -/
def tensorProduct :
    (m n : Nat) -> BoolTensor m -> BoolTensor n -> BoolTensor (m + n)
  | 0, n, x, y =>
      tensorCast (Nat.zero_add n).symm
        (tensorScale n (show Q' from x) y)
  | m + 1, n, x, y =>
      tensorCast (Nat.succ_add m n).symm
        (fun bit : Bool => tensorProduct m n (x bit) y)

/-- Scalar-left unit equation for structural tensor concatenation. -/
theorem tensorProduct_zero (n : Nat) (x : BoolTensor 0) (y : BoolTensor n) :
    tensorProduct 0 n x y =
      tensorCast (Nat.zero_add n).symm
        (tensorScale n (show Q' from x) y) := rfl

/-- One-fiber equation for structural tensor concatenation. -/
theorem tensorProduct_succ (m n : Nat)
    (x : BoolTensor (m + 1)) (y : BoolTensor n) :
    tensorProduct (m + 1) n x y =
      tensorCast (Nat.succ_add m n).symm
        (fun bit : Bool => tensorProduct m n (x bit) y) := rfl

/-- The recursively defined Boolean tensor Gram form is multiplicative under
structural tensor concatenation.  The proof is list-free: its leaf is the
scaling law, and its only inductive algebra is right distributivity over the
two Boolean fibers. -/
theorem boolTensorDot_tensorProduct
    (m n : Nat) (x1 x2 : BoolTensor m) (y1 y2 : BoolTensor n) :
    boolTensorDot (m + n)
        (tensorProduct m n x1 y1) (tensorProduct m n x2 y2) ≈
      boolTensorDot m x1 x2 * boolTensorDot n y1 y2 := by
  induction m with
  | zero =>
      rw [tensorProduct_zero, tensorProduct_zero,
        boolTensorDot_tensorCast]
      change
        boolTensorDot n
            (tensorScale n (show Q' from x1) y1)
            (tensorScale n (show Q' from x2) y2) ≈
          ((show Q' from x1) * (show Q' from x2)) *
            boolTensorDot n y1 y2
      exact boolTensorDot_scale n
        (show Q' from x1) (show Q' from x2) y1 y2
  | succ m ih =>
      rw [tensorProduct_succ, tensorProduct_succ,
        boolTensorDot_tensorCast]
      refine Q'.eqv_trans _ _ _
        (QPoly.q_add_congr
          (ih (x1 := x1 false) (x2 := x2 false))
          (ih (x1 := x1 true) (x2 := x2 true))) ?_
      exact Q'.eqv_symm
        (QPoly.q_add_mul
          (boolTensorDot m (x1 false) (x2 false))
          (boolTensorDot m (x1 true) (x2 true))
          (boolTensorDot n y1 y2))

/-! ## Primitive Gram isometries -/

/-- Apply a Gram isometry independently in both fibers of a new leading
Boolean coordinate. -/
def tailLiftIsometry {n : Nat}
    (W : GramIsometry (boolTensorForm n)) :
    GramIsometry (boolTensorForm (n + 1)) where
  map := fun x bit => W.map (x bit)
  gram_eqv := fun x y =>
    QPoly.q_add_congr
      (W.gram_eqv (x false) (y false))
      (W.gram_eqv (x true) (y true))

/-- Swap the first two coordinates and leave the `n`-coordinate tail fixed. -/
def adjacentSwapIsometry (n : Nat) :
    GramIsometry (boolTensorForm (n + 2)) where
  map := fun x first second => x second first
  gram_eqv := fun x y =>
    Q'.add_swap_inner
      (boolTensorDot n (x false false) (y false false))
      (boolTensorDot n (x true false) (y true false))
      (boolTensorDot n (x false true) (y false true))
      (boolTensorDot n (x true true) (y true true))

/-! ## The coordinate epsilon operator -/

/-- Coordinate sign in the standard epsilon matrix
`epsilon(false,true)=1`, `epsilon(true,false)=-1`. -/
def epsilonCoordinateSign : Bool -> Q'
  | false => 1
  | true => -1

/-- Both nonzero epsilon coordinates have square one. -/
theorem epsilonCoordinateSign_square (bit : Bool) :
    epsilonCoordinateSign bit * epsilonCoordinateSign bit ≈ 1 := by
  cases bit <;> decide

/-- Complementary epsilon coordinates multiply to minus one.  This is the
coordinate statement behind `epsilon^2 = -I`; it is independent of SU(2). -/
theorem epsilonCoordinateSign_complement (bit : Bool) :
    epsilonCoordinateSign bit * epsilonCoordinateSign (!bit) ≈ -1 := by
  cases bit <;> decide

/-- Applying the same epsilon coordinate sign to both tensor arguments
preserves their dot product. -/
theorem boolTensorDot_epsilon_scale
    (n : Nat) (bit : Bool) (x y : BoolTensor n) :
    boolTensorDot n
        (tensorScale n (epsilonCoordinateSign bit) x)
        (tensorScale n (epsilonCoordinateSign bit) y) ≈
      boolTensorDot n x y := by
  refine Q'.eqv_trans _ _ _
    (boolTensorDot_scale n
      (epsilonCoordinateSign bit) (epsilonCoordinateSign bit) x y) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (epsilonCoordinateSign bit * epsilonCoordinateSign bit) 1
      (boolTensorDot n x y)
      (epsilonCoordinateSign_square bit)) ?_
  exact Q'.one_mul_eqv (boolTensorDot n x y)

/-- Signed complement on a leading Boolean coordinate.  It is an isometry
because the signs square to one and complement merely exchanges the two
orthogonal fibers. -/
def epsilonComplementIsometry (n : Nat) :
    GramIsometry (boolTensorForm (n + 1)) where
  map := fun x bit =>
    tensorScale n (epsilonCoordinateSign bit) (x (!bit))
  gram_eqv := by
    intro x y
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr
        (boolTensorDot_epsilon_scale n false (x true) (y true))
        (boolTensorDot_epsilon_scale n true (x false) (y false))) ?_
    exact Q'.add_comm_eqv
      (boolTensorDot n (x true) (y true))
      (boolTensorDot n (x false) (y false))

/-! ## A compositional signed-wiring language -/

/-- Syntax generated by the Gram-preserving local coordinate moves. -/
inductive SignedBoolWiring : Nat -> Type
  | identity (n : Nat) : SignedBoolWiring n
  | compose {n : Nat} :
      SignedBoolWiring n -> SignedBoolWiring n -> SignedBoolWiring n
  | tailLift {n : Nat} : SignedBoolWiring n -> SignedBoolWiring (n + 1)
  | adjacentSwap (n : Nat) : SignedBoolWiring (n + 2)
  | epsilonComplement (n : Nat) : SignedBoolWiring (n + 1)

/-- Compile signed-wiring syntax to its certified Gram isometry. -/
def SignedBoolWiring.toGramIsometry :
    {n : Nat} -> SignedBoolWiring n -> GramIsometry (boolTensorForm n)
  | _, .identity n => GramIsometry.id (boolTensorForm n)
  | _, .compose outer inner =>
      GramIsometry.comp
        (SignedBoolWiring.toGramIsometry outer)
        (SignedBoolWiring.toGramIsometry inner)
  | _, .tailLift wiring =>
      tailLiftIsometry (SignedBoolWiring.toGramIsometry wiring)
  | _, .adjacentSwap n => adjacentSwapIsometry n
  | _, .epsilonComplement n => epsilonComplementIsometry n

/-- Action of a compiled signed wiring on its symbolic tensor carrier. -/
def SignedBoolWiring.act {n : Nat}
    (W : SignedBoolWiring n) (x : BoolTensor n) : BoolTensor n :=
  W.toGramIsometry.map x

/-- Every syntactically generated wiring preserves the full tensor Gram
form, by construction. -/
theorem SignedBoolWiring.gram_eqv {n : Nat}
    (W : SignedBoolWiring n) (x y : BoolTensor n) :
    boolTensorDot n (W.act x) (W.act y) ≈ boolTensorDot n x y :=
  W.toGramIsometry.gram_eqv x y

/-! ## Positioning local moves behind arbitrary leading coordinates -/

/-- Put a wiring behind `leading` untouched leading coordinates.  Since a
tail lift adds one leading coordinate, this is structural recursion in the
leading length rather than arithmetic transport of tensor types. -/
def SignedBoolWiring.prefixLift {n : Nat} :
    (leading : Nat) -> SignedBoolWiring n -> SignedBoolWiring (n + leading)
  | 0, W => W
  | leading + 1, W =>
      .tailLift (SignedBoolWiring.prefixLift leading W)

/-- Swap two adjacent coordinates after `leading` untouched coordinates and
before a tail of length `suffix`. -/
def SignedBoolWiring.swapAt (leading suffix : Nat) :
    SignedBoolWiring ((suffix + 2) + leading) :=
  SignedBoolWiring.prefixLift leading (.adjacentSwap suffix)

/-- Apply signed epsilon-complement after `leading` untouched coordinates and
before a tail of length `suffix`. -/
def SignedBoolWiring.epsilonAt (leading suffix : Nat) :
    SignedBoolWiring ((suffix + 1) + leading) :=
  SignedBoolWiring.prefixLift leading (.epsilonComplement suffix)

/-! ## Public one-step certificates -/

theorem tailLiftIsometry_gram_eqv {n : Nat}
    (W : GramIsometry (boolTensorForm n))
    (x y : BoolTensor (n + 1)) :
    boolTensorDot (n + 1)
        ((tailLiftIsometry W).map x) ((tailLiftIsometry W).map y) ≈
      boolTensorDot (n + 1) x y :=
  (tailLiftIsometry W).gram_eqv x y

theorem adjacentSwapIsometry_gram_eqv (n : Nat)
    (x y : BoolTensor (n + 2)) :
    boolTensorDot (n + 2)
        ((adjacentSwapIsometry n).map x) ((adjacentSwapIsometry n).map y) ≈
      boolTensorDot (n + 2) x y :=
  (adjacentSwapIsometry n).gram_eqv x y

theorem epsilonComplementIsometry_gram_eqv (n : Nat)
    (x y : BoolTensor (n + 1)) :
    boolTensorDot (n + 1)
        ((epsilonComplementIsometry n).map x)
        ((epsilonComplementIsometry n).map y) ≈
      boolTensorDot (n + 1) x y :=
  (epsilonComplementIsometry n).gram_eqv x y

/-! ## Axiom audit -/

#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.boolFiber
#print axioms YMGap.Continuum.PositiveChannelTraceBound.GramIsometry.comp
#print axioms scalarDotForm
#print axioms boolTensorForm
#print axioms boolTensorDot_scale
#print axioms tensorCast
#print axioms tensorProduct
#print axioms tensorProduct_zero
#print axioms tensorProduct_succ
#print axioms boolTensorDot_tensorProduct
#print axioms adjacentSwapIsometry
#print axioms epsilonCoordinateSign_complement
#print axioms epsilonComplementIsometry
#print axioms SignedBoolWiring.toGramIsometry
#print axioms SignedBoolWiring.gram_eqv

end YMGap.Continuum.SymbolicFiniteBoolTensor
