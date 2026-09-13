/-
# Geometry-independent square certificates for ORIGINAL plaquette expressions

The rational cap is computed from the expression's spins, coefficients and
algebraic operations only. It does not use the nome, action cutoff, slab
extent, face positions or bulk padding. Both actual lower and reflected
upper polynomials receive the same cap, using the literal ordered SU(2)
holonomies. These are positive-polynomial certificates, not a mass gap.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.BF4ExactSlabBulkExpectationComparison

namespace YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- Explicit syntactic cap; no parameters of the interacting action occur. -/
def bound {half : Nat} : PlaquetteExpression half → Q'
  | .unit => 1
  | .character _ _ spin => characterBound spin
  | .add e f => sumBound (bound e) (bound f)
  | .mul e f => bound e * bound f
  | .smul c e => (c*c)*bound e

private def evaluateBound {half blocks : Nat} (f : Nat → Nat → RatPoly)
    (h : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, SquareBound blocks (f id spin) (characterBound spin)) :
    ∀ e : PlaquetteExpression half, SquareBound blocks (evaluate f e) (bound e)
  | .unit => .one blocks
  | .character id hi spin => h id hi spin
  | .add e g => (evaluateBound f h e).add (evaluateBound f h g)
  | .mul e g => (evaluateBound f h e).mul (evaluateBound f h g)
  | .smul c e => (evaluateBound f h e).smul c

def lowerBound {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (boundaryCompleteSlabLinks (centralExtent half)).length (lower e) (bound e) :=
  evaluateBound _ (fun _ hi spin => character_squareBound
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1))) spin) e

def upperBound {half : Nat} (e : PlaquetteExpression half) :
    SquareBound (boundaryCompleteSlabLinks (centralExtent half)).length (upper e) (bound e) :=
  evaluateBound _ (fun _ hi spin => character_squareBound
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette
      (slabPlaquetteAt_mem (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hi).1)))) spin) e

theorem bound_nonnegative {half : Nat} (e : PlaquetteExpression half) : (0 : Q') ≤ bound e :=
  (lowerBound e).nonnegative

/-- A certificate for the actual reflected product, not ordinary variance. -/
def reflectedBound {half : Nat} (e : PlaquetteExpression half) :
    Certificate (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyAdd (cap (bound e)) (polyNeg (polyMul (upper e) (lower e)))) :=
  (upperBound e).cross (lowerBound e)

theorem bound_bulkAtTime {half : Nat} (padding : Nat) (s : Fin (padding+1)) :
    ∀ e : PlaquetteExpression half, bound (bulkAtTime padding s e) = bound e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e f => by simp only [bulkAtTime, bound, bound_bulkAtTime padding s e, bound_bulkAtTime padding s f]
  | .mul e f => by simp only [bulkAtTime, bound, bound_bulkAtTime padding s e, bound_bulkAtTime padding s f]
  | .smul _ e => by simp only [bulkAtTime, bound, bound_bulkAtTime padding s e]

end YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.lowerBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.upperBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.bound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.reflectedBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound.bound_bulkAtTime
