/-
# Literal time embeddings of ORIGINAL plaquette observables

Every character is sent to the actual translated face in the enlarged
boundary-complete slab. The map preserves the expression operations and
all-spin lower/upper evaluation, with the complementary reflected shift
2*n-s. In particular, centered enlargement (s=n) and outward displacement
(s=0) must not be conflated. At zero enlargement the original expression
is returned, not merely a new expression with the same expectation.

These are geometric algebra maps before null quotient/completion. Their
existence supplies no comparison of the two original slab functionals.
-/

import YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

namespace YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

private theorem congrTwo {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

/-- The lower-half membership proof is produced from geometric shift bounds. -/
def translate {half : Nat} (n s : Nat) (hs : s ≤ n) : PlaquetteExpression half → PlaquetteExpression (half+n)
  | .unit => .unit
  | .character id hi spin => .character (faceId (centralExtent half) (centralExtent (half+n)) s id) (faceId_lower hs hi) spin
  | .add e f => .add (translate n s hs e) (translate n s hs f)
  | .mul e f => .mul (translate n s hs e) (translate n s hs f)
  | .smul c e => .smul c (translate n s hs e)

theorem translate_unit {half : Nat} (n s : Nat) (hs : s ≤ n) :
    translate (half := half) n s hs .unit = .unit := rfl

theorem translate_add {half : Nat} (n s : Nat) (hs : s ≤ n) (e f : PlaquetteExpression half) :
    translate n s hs (.add e f) = .add (translate n s hs e) (translate n s hs f) := rfl

theorem translate_mul {half : Nat} (n s : Nat) (hs : s ≤ n) (e f : PlaquetteExpression half) :
    translate n s hs (.mul e f) = .mul (translate n s hs e) (translate n s hs f) := rfl

theorem translate_smul {half : Nat} (n s : Nat) (hs : s ≤ n) (c : Q') (e : PlaquetteExpression half) :
    translate n s hs (.smul c e) = .smul c (translate n s hs e) := rfl

theorem translate_zero {half : Nat} : ∀ e : PlaquetteExpression half, translate 0 0 (Nat.le_refl 0) e = e
  | .unit => rfl
  | .character id hi spin => by
      simp only [translate, Nat.add_zero, faceId_zero (mem_centralLowerFaceIds.mp hi).1]
  | .add e f => congrTwo PlaquetteExpression.add (translate_zero e) (translate_zero f)
  | .mul e f => congrTwo PlaquetteExpression.mul (translate_zero e) (translate_zero f)
  | .smul c e => congrArg (PlaquetteExpression.smul c) (translate_zero e)

/-- Exact naturality of evaluation, retaining the target numerical face IDs. -/
theorem evaluate_translate {half : Nat} (n s : Nat) (hs : s ≤ n) (f : Nat → Nat → RatPoly) :
    ∀ e : PlaquetteExpression half, evaluate f (translate n s hs e) =
      evaluate (fun id spin => f (faceId (centralExtent half) (centralExtent (half+n)) s id) spin) e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e g => congrTwo polyAdd (evaluate_translate n s hs f e) (evaluate_translate n s hs f g)
  | .mul e g => congrTwo polyMul (evaluate_translate n s hs f e) (evaluate_translate n s hs f g)
  | .smul c e => congrArg (polySmul c) (evaluate_translate n s hs f e)

theorem evaluate_congr {half : Nat} (f g : Nat → Nat → RatPoly)
    (h : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, f id spin = g id spin) :
    ∀ e : PlaquetteExpression half, evaluate f e = evaluate g e
  | .unit => rfl
  | .character id hi spin => h id hi spin
  | .add e q => congrTwo polyAdd (evaluate_congr f g h e) (evaluate_congr f g h q)
  | .mul e q => congrTwo polyMul (evaluate_congr f g h e) (evaluate_congr f g h q)
  | .smul c e => congrArg (polySmul c) (evaluate_congr f g h e)

/-- The ORIGINAL lower polynomial is evaluated on literal translated faces,
not an auxiliary character-coordinate carrier. -/
theorem lower_translate {half : Nat} (n s : Nat) (hs : s ≤ n) (e : PlaquetteExpression half) :
    lower (translate n s hs e) =
      evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+n))
        (timeShiftPlaquette s (slabPlaquetteAt (centralExtent half) id))).scalar spin) e := by
  unfold lower
  rw [evaluate_translate]
  apply evaluate_congr
  intro id hi spin
  exact congrArg (fun p => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+n)) p).scalar spin)
    (faceId_pin (central_room (half := half) (show s ≤ n+n by omega)) (mem_centralLowerFaceIds.mp hi).1)

/-- The reflected upper polynomial shifts by 2*n-s. This equation is at
the actual noncommutative plaquette-word polynomial, for every spin. -/
theorem upper_translate {half : Nat} (n s : Nat) (hs : s ≤ n) (e : PlaquetteExpression half) :
    upper (translate n s hs e) =
      evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+n))
        (timeShiftPlaquette (n+n-s) (timeReflectPlaquette (centralExtent half)
          (slabPlaquetteAt (centralExtent half) id)))).scalar spin) e := by
  unfold upper
  rw [evaluate_translate]
  apply evaluate_congr
  intro id hi spin
  apply congrArg (fun p => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+n)) p).scalar spin)
  have hp := (mem_centralLowerFaceIds.mp hi).1
  have hr := central_room (half := half) (show s ≤ n+n by omega)
  rw [slabPlaquetteAt_slabFaceReflectId (faceId_physical hr hp), faceId_pin hr hp]
  exact reflection_shift (show s ≤ n+n by omega)
    ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hp)).2

/-- Both sides move by n: the observable stays at the same distance from
the reflection plane while the finite stage is enlarged. -/
def centered {half : Nat} (n : Nat) : PlaquetteExpression half → PlaquetteExpression (half+n) :=
  translate n n (Nat.le_refl n)

/-- The lower face stays at its coordinate time, the reflection plane moves
n steps away, and the reflected upper face moves by 2*n. -/
def outward {half : Nat} (n : Nat) : PlaquetteExpression half → PlaquetteExpression (half+n) :=
  translate n 0 (Nat.zero_le n)

theorem centered_zero {half : Nat} (e : PlaquetteExpression half) : centered 0 e = e := translate_zero e

theorem outward_zero {half : Nat} (e : PlaquetteExpression half) : outward 0 e = e := translate_zero e

/-- Keep stage padding and time lag independent. The guard prevents truncated
Nat subtraction from silently turning an out-of-range lag into another one. -/
def displaced {half : Nat} (padding lag : Nat) (_hlag : lag ≤ padding) :
    PlaquetteExpression half → PlaquetteExpression (half+padding) :=
  translate padding (padding-lag) (Nat.sub_le padding lag)

theorem displaced_zero {half : Nat} (padding : Nat) (e : PlaquetteExpression half) :
    displaced padding 0 (Nat.zero_le padding) e = centered padding e := rfl

theorem displaced_full {half : Nat} (padding : Nat) (e : PlaquetteExpression half) :
    displaced padding padding (Nat.le_refl padding) e = outward padding e := by
  simp only [displaced, Nat.sub_self, outward]

theorem upper_displaced {half : Nat} (padding lag : Nat) (hlag : lag ≤ padding) (e : PlaquetteExpression half) :
    upper (displaced padding lag hlag e) =
      evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding))
        (timeShiftPlaquette (padding+lag) (timeReflectPlaquette (centralExtent half)
          (slabPlaquetteAt (centralExtent half) id)))).scalar spin) e := by
  unfold displaced
  rw [upper_translate, show padding+padding-(padding-lag) = padding+lag by omega]

end YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate_mul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.translate_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.evaluate_translate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.evaluate_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.lower_translate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.upper_translate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.centered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.outward
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.centered_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.outward_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.displaced
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.displaced_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.displaced_full
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding.upper_displaced
