/-
# Structural epsilon transport for oriented fundamental occurrences

An oriented fundamental coefficient stores its matrix indices differently in
the forward and reverse conventions.  This leaf separates that storage detail
from the semantic operator coordinates `(target, source)`, and then packages
orientation normalization as a signed Boolean-tensor wiring.

The construction is structural in a list of coordinate masks.  In particular,
it never materializes or enumerates a Boolean assignment family.  The generic
evaluation theorem says exactly what the compiled wiring does at one supplied
coordinate word, while the Gram theorem records that the same wiring is an
isometry.  The final occurrence lemmas identify both the complemented word and
the accumulated epsilon sign needed by the oriented Haar kernels.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensor
import YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization
import YMGap.Continuum.SU2QuaternionBivalentOperatorKernel

namespace YMGap.Continuum.SymbolicFiniteBoolTensor

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Evaluation at one structurally supplied Boolean word -/

namespace BoolTensor

/-- Evaluate a curried Boolean tensor on one supplied coordinate word.

The total definition uses `false` only when a word is shorter than the tensor
arity, and ignores surplus bits at a scalar leaf.  The proof-carrying word
interface below makes both fallbacks unreachable in the transport theorem.
-/
def eval : (n : Nat) -> BoolTensor n -> List Bool -> Q'
  | 0, x, _ => show Q' from x
  | n + 1, x, [] => eval n (x false) []
  | n + 1, x, bit :: bits => eval n (x bit) bits

/-- Tensor scaling is pointwise at every structurally supplied word. -/
theorem eval_tensorScale
    (n : Nat) (q : Q') (x : BoolTensor n) (bits : List Bool) :
    eval n (tensorScale n q x) bits ≈ q * eval n x bits := by
  induction n generalizing bits with
  | zero =>
      change q * (show Q' from x) ≈ q * (show Q' from x)
      exact Q'.eqv_refl _
  | succ n ih =>
      cases bits with
      | nil =>
          change
            eval n (tensorScale n q (x false)) [] ≈
              q * eval n (x false) []
          exact ih (x := x false) (bits := [])
      | cons bit bits =>
          change
            eval n (tensorScale n q (x bit)) bits ≈
              q * eval n (x bit) bits
          exact ih (x := x bit) (bits := bits)

end BoolTensor

/-! ## 2. Proof-carrying coordinate words -/

/-- A Boolean coordinate word whose shape is data, indexed by its exact
length.  The recursive product mirrors `BoolTensor`: a zero-coordinate word
is `Unit`, and a successor word stores its head and exact-shape tail.

Using this carrier removes the impossible list-length branches and dependent
equality transports that can contaminate a public proof term with choice. -/
def BoolWord : Nat -> Type
  | 0 => Unit
  | n + 1 => Bool × BoolWord n

namespace BoolWord

/-- Forget the exact-shape witness and recover the ordinary coordinate list. -/
def toList : (n : Nat) -> BoolWord n -> List Bool
  | 0, _ => []
  | n + 1, word => word.1 :: toList n word.2

/-- Forgetting shape produces a list of exactly the indexed length. -/
theorem toList_length : ∀ (n : Nat) (word : BoolWord n),
    (toList n word).length = n
  | 0, _ => rfl
  | n + 1, word =>
      congrArg Nat.succ (toList_length n word.2)

/-- Every ordinary Boolean list has a canonical exact-shape word. -/
def ofList : (bits : List Bool) -> BoolWord bits.length
  | [] => ()
  | bit :: bits => (bit, ofList bits)

/-- Forgetting the canonical exact-shape word recovers the supplied list
definitionally at each constructor. -/
theorem toList_ofList : ∀ bits : List Bool,
    toList bits.length (ofList bits) = bits
  | [] => rfl
  | bit :: bits => by
      change bit :: toList bits.length (ofList bits) = bit :: bits
      exact congrArg (List.cons bit) (toList_ofList bits)

end BoolWord

/-! ## 3. A structural epsilon mask and its pointwise semantics -/

/-- Complement one coordinate exactly when its mask bit is true. -/
def complementIf : Bool -> Bool -> Bool
  | false, bit => bit
  | true, bit => !bit

/-- Apply an epsilon-complement mask to one coordinate word.

The mismatched-length clauses make the function total.  The certified use
below supplies its coordinate list through an exact-shape `BoolWord`.
-/
def applyEpsilonMask : List Bool -> List Bool -> List Bool
  | [], _ => []
  | _ :: _, [] => []
  | maskBit :: mask, bit :: bits =>
      complementIf maskBit bit :: applyEpsilonMask mask bits

/-- Product of the epsilon-coordinate signs selected by a mask along one
supplied coordinate word. -/
def epsilonMaskSign : List Bool -> List Bool -> Q'
  | [], _ => 1
  | _ :: _, [] => 1
  | false :: mask, _ :: bits => epsilonMaskSign mask bits
  | true :: mask, bit :: bits =>
      epsilonCoordinateSign bit * epsilonMaskSign mask bits

namespace SignedBoolWiring

/-- Compile an arbitrary coordinate epsilon mask to signed-wiring syntax.

At a false head, the tail wiring is merely lifted.  At a true head, the tail
is wired first and the leading epsilon-complement is applied afterward, in
the map-composition order fixed by `SignedBoolWiring.compose`.
-/
def epsilonMask : (mask : List Bool) -> SignedBoolWiring mask.length
  | [] => .identity 0
  | false :: mask => .tailLift (epsilonMask mask)
  | true :: mask =>
      .compose (.epsilonComplement mask.length) (.tailLift (epsilonMask mask))

/-- Pointwise semantics of a compiled epsilon mask at one supplied word.

The output is the input tensor evaluated at the masked-complement word,
multiplied by exactly the product of epsilon-coordinate signs selected at the
original coordinates.  The proof recurses only through the supplied mask and
word; it does not enumerate Boolean assignments.
-/
theorem epsilonMask_eval :
    ∀ (mask : List Bool)
      (bits : BoolWord mask.length)
      (x : BoolTensor mask.length),
        BoolTensor.eval mask.length ((epsilonMask mask).act x)
            (BoolWord.toList mask.length bits) ≈
          epsilonMaskSign mask (BoolWord.toList mask.length bits) *
            BoolTensor.eval mask.length x
              (applyEpsilonMask mask (BoolWord.toList mask.length bits))
  | [], _, x => by
      change (show Q' from x) ≈ 1 * (show Q' from x)
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | false :: mask, bits, x => by
      change
        BoolTensor.eval mask.length
            ((epsilonMask mask).act (x bits.1))
            (BoolWord.toList mask.length bits.2) ≈
          epsilonMaskSign mask (BoolWord.toList mask.length bits.2) *
            BoolTensor.eval mask.length (x bits.1)
              (applyEpsilonMask mask
                (BoolWord.toList mask.length bits.2))
      exact epsilonMask_eval mask bits.2 (x bits.1)
  | true :: mask, bits, x => by
      change
        BoolTensor.eval mask.length
            (tensorScale mask.length (epsilonCoordinateSign bits.1)
              ((epsilonMask mask).act (x (!bits.1))))
            (BoolWord.toList mask.length bits.2) ≈
          (epsilonCoordinateSign bits.1 *
              epsilonMaskSign mask
                (BoolWord.toList mask.length bits.2)) *
            BoolTensor.eval mask.length (x (!bits.1))
              (applyEpsilonMask mask
                (BoolWord.toList mask.length bits.2))
      refine Q'.eqv_trans _ _ _
        (BoolTensor.eval_tensorScale mask.length
          (epsilonCoordinateSign bits.1)
          ((epsilonMask mask).act (x (!bits.1)))
          (BoolWord.toList mask.length bits.2)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (epsilonCoordinateSign bits.1)
          (BoolTensor.eval mask.length
            ((epsilonMask mask).act (x (!bits.1)))
            (BoolWord.toList mask.length bits.2))
          (epsilonMaskSign mask (BoolWord.toList mask.length bits.2) *
            BoolTensor.eval mask.length (x (!bits.1))
              (applyEpsilonMask mask
                (BoolWord.toList mask.length bits.2)))
          (epsilonMask_eval mask bits.2 (x (!bits.1)))) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (epsilonCoordinateSign bits.1)
          (epsilonMaskSign mask (BoolWord.toList mask.length bits.2))
          (BoolTensor.eval mask.length (x (!bits.1))
            (applyEpsilonMask mask
              (BoolWord.toList mask.length bits.2))))

/-- Every compiled epsilon mask preserves the full Boolean-tensor Gram form. -/
theorem epsilonMask_gram_eqv
    (mask : List Bool) (x y : BoolTensor mask.length) :
    boolTensorDot mask.length
        ((epsilonMask mask).act x) ((epsilonMask mask).act y) ≈
      boolTensorDot mask.length x y :=
  SignedBoolWiring.gram_eqv (epsilonMask mask) x y

end SignedBoolWiring

end YMGap.Continuum.SymbolicFiniteBoolTensor

namespace YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 3. Recovering semantic operator coordinates from stored occurrences -/

/-- Semantic target/output coordinate of an oriented stored occurrence. -/
def operatorTarget (occurrence : FundamentalOccurrence) : Bool :=
  match occurrence.orientation with
  | .forward => occurrence.row
  | .reverse => occurrence.column

/-- Semantic source/input coordinate of an oriented stored occurrence. -/
def operatorSource (occurrence : FundamentalOccurrence) : Bool :=
  match occurrence.orientation with
  | .forward => occurrence.column
  | .reverse => occurrence.row

/-- Repackaging the recovered semantic coordinates reconstructs the original
stored occurrence exactly. -/
theorem operatorOccurrence_operatorTarget_operatorSource
    (occurrence : FundamentalOccurrence) :
    operatorOccurrence occurrence.orientation
        occurrence.operatorTarget occurrence.operatorSource = occurrence := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- The occurrence duality sign factors through its semantic operator target
and source coordinates, independently of the storage transpose. -/
theorem fundamentalDualitySign_operatorCoordinates
    (occurrence : FundamentalOccurrence) :
    fundamentalDualitySign occurrence.row occurrence.column ≈
      epsilonCoordinateSign occurrence.operatorTarget *
        epsilonCoordinateSign occurrence.operatorSource := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation with
  | forward =>
      exact fundamentalDualitySign_row_column_factorization row column
  | reverse =>
      refine Q'.eqv_trans _ _ _
        (fundamentalDualitySign_row_column_factorization row column) ?_
      change
        epsilonCoordinateSign row * epsilonCoordinateSign column ≈
          epsilonCoordinateSign column * epsilonCoordinateSign row
      exact Q'.mul_comm_eqv _ _

end YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence

namespace YMGap.Continuum.SU2QuaternionOccurrenceBoolTensorTransport

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 4. Orientation normalization as a two-coordinate epsilon mask -/

/-- Whether an occurrence orientation differs from a desired convention. -/
def orientationMismatch :
    FundamentalLinkOrientation -> FundamentalLinkOrientation -> Bool
  | .forward, .forward => false
  | .forward, .reverse => true
  | .reverse, .forward => true
  | .reverse, .reverse => false

/-- Normalize one occurrence to a specified orientation convention. -/
def normalizeOccurrence
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) : FundamentalOccurrence :=
  match desired with
  | .forward => occurrence.toForward
  | .reverse => occurrence.toReverse

/-- The two semantic operator coordinates of an occurrence. -/
def occurrenceOperatorBits (occurrence : FundamentalOccurrence) : List Bool :=
  [occurrence.operatorTarget, occurrence.operatorSource]

/-- Epsilon-complement both operator coordinates exactly when normalization
must dualize the occurrence. -/
def occurrenceEpsilonMask
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) : List Bool :=
  [orientationMismatch desired occurrence.orientation,
    orientationMismatch desired occurrence.orientation]

/-- The occurrence coordinates as a proof-carrying word of exactly the mask
shape.  Its value is independent of `desired`; that argument records the
shape against which the word will be transported. -/
def occurrenceOperatorWord
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    BoolWord (occurrenceEpsilonMask desired occurrence).length :=
  (occurrence.operatorTarget, (occurrence.operatorSource, ()))

/-- Forgetting the proof-carrying occurrence word recovers the original
two-entry operator-coordinate list exactly. -/
theorem occurrenceOperatorWord_toList
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    BoolWord.toList (occurrenceEpsilonMask desired occurrence).length
        (occurrenceOperatorWord desired occurrence) =
      occurrenceOperatorBits occurrence := rfl

/-- The occurrence coordinate word and its normalization mask have the same
fixed arity two. -/
theorem occurrenceOperatorBits_length_eq_occurrenceEpsilonMask_length
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    (occurrenceOperatorBits occurrence).length =
      (occurrenceEpsilonMask desired occurrence).length := rfl

/-- Occurrence normalization is exactly reconstruction at the semantic
operator coordinates selected by the two-coordinate epsilon mask. -/
theorem normalizeOccurrence_eq_operatorOccurrence
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    normalizeOccurrence desired occurrence =
      operatorOccurrence desired
        (complementIf
          (orientationMismatch desired occurrence.orientation)
          occurrence.operatorTarget)
        (complementIf
          (orientationMismatch desired occurrence.orientation)
          occurrence.operatorSource) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases desired <;> cases orientation <;> rfl

/-- Applying the structural mask to the old semantic coordinates gives
exactly the semantic coordinates of the normalized occurrence. -/
theorem applyEpsilonMask_occurrenceEpsilonMask
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    applyEpsilonMask
        (occurrenceEpsilonMask desired occurrence)
        (occurrenceOperatorBits occurrence) =
      occurrenceOperatorBits (normalizeOccurrence desired occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases desired <;> cases orientation <;> rfl

/-- Rational sign introduced by normalizing one occurrence. -/
def occurrenceNormalizationSign
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) : Q' :=
  match orientationMismatch desired occurrence.orientation with
  | false => 1
  | true => fundamentalDualitySign occurrence.row occurrence.column

/-- The one-occurrence normalization sign is exactly the sign accumulated by
its two-coordinate epsilon mask. -/
theorem occurrenceNormalizationSign_eq_epsilonMaskSign
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence) :
    occurrenceNormalizationSign desired occurrence ≈
      epsilonMaskSign
        (occurrenceEpsilonMask desired occurrence)
        (occurrenceOperatorBits occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases desired with
  | forward =>
      cases orientation with
      | forward =>
          exact Q'.eqv_refl 1
      | reverse =>
          refine Q'.eqv_trans _ _ _
            (FundamentalOccurrence.fundamentalDualitySign_operatorCoordinates
              ⟨.reverse, row, column⟩) ?_
          exact Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_one_eqv _))
  | reverse =>
      cases orientation with
      | forward =>
          refine Q'.eqv_trans _ _ _
            (FundamentalOccurrence.fundamentalDualitySign_operatorCoordinates
              ⟨.forward, row, column⟩) ?_
          exact Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_one_eqv _))
      | reverse =>
          exact Q'.eqv_refl 1

/-- Combined pointwise transport law for one occurrence: the compiled mask
evaluates the original operator-coordinate word as the exact normalization
sign times the untransported tensor at the normalized operator coordinates. -/
theorem occurrenceEpsilonMask_eval
    (desired : FundamentalLinkOrientation)
    (occurrence : FundamentalOccurrence)
    (x : BoolTensor (occurrenceEpsilonMask desired occurrence).length) :
    BoolTensor.eval (occurrenceEpsilonMask desired occurrence).length
        ((SignedBoolWiring.epsilonMask
          (occurrenceEpsilonMask desired occurrence)).act x)
        (occurrenceOperatorBits occurrence) ≈
      occurrenceNormalizationSign desired occurrence *
        BoolTensor.eval (occurrenceEpsilonMask desired occurrence).length x
          (occurrenceOperatorBits
            (normalizeOccurrence desired occurrence)) := by
  refine Q'.eqv_trans _ _ _
    (SignedBoolWiring.epsilonMask_eval
      (occurrenceEpsilonMask desired occurrence)
      (occurrenceOperatorWord desired occurrence)
      x) ?_
  rw [occurrenceOperatorWord_toList]
  rw [applyEpsilonMask_occurrenceEpsilonMask]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (occurrenceNormalizationSign_eq_epsilonMaskSign desired occurrence))

/-! ## Axiom audit -/

#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.BoolTensor.eval
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.BoolTensor.eval_tensorScale
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.BoolWord.toList_length
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.BoolWord.toList_ofList
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.SignedBoolWiring.epsilonMask
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.SignedBoolWiring.epsilonMask_eval
#print axioms YMGap.Continuum.SymbolicFiniteBoolTensor.SignedBoolWiring.epsilonMask_gram_eqv
#print axioms YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence.operatorOccurrence_operatorTarget_operatorSource
#print axioms YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence.fundamentalDualitySign_operatorCoordinates
#print axioms normalizeOccurrence_eq_operatorOccurrence
#print axioms applyEpsilonMask_occurrenceEpsilonMask
#print axioms occurrenceNormalizationSign_eq_epsilonMaskSign
#print axioms occurrenceOperatorWord_toList
#print axioms occurrenceEpsilonMask_eval

end YMGap.Continuum.SU2QuaternionOccurrenceBoolTensorTransport
