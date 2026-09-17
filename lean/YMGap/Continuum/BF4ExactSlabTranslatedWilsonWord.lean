/-
# Exact original Wilson-word transport between slab Haar carriers

The existing Placement sends every original physical source link to its
literal translated target link. Ordered recursion retains all reversed
edges, repeated links and quaternion multiplication order. The all-spin
character identity uses the SAME block embedding, with its explicit prefix
padding, and not a product of individual plaquette characters.

This is the observable pin consumed by translated selected-action and
aligned filtered-action finiteValue identities. It does not identify the
translated source action with the complete target action or assert spatial
invariance of an interacting state.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

namespace YMGap.Continuum.BF4ExactSlabTranslatedWilsonWord

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The same ordered word under the computed physical Placement. -/
theorem word_pin (P : Placement) : ∀ edges : List OrientedBF4Link,
    (∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks P.source) →
    QuaternionPrefixPolyQuaternionEqv (B P.target)
      (P.embedding.quaternion (word P.source edges))
      (word P.target (edges.map P.shiftOriented))
  | [], _ => P.embedding.quaternion_one
  | e :: es, hp => by
      change QuaternionPrefixPolyQuaternionEqv (B P.target)
        (P.embedding.quaternion (PolyQuaternion.mul
          (orientedCorrectedSlabLinkPolynomial P.source e) (word P.source es)))
        (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial P.target (P.shiftOriented e))
          (word P.target (es.map P.shiftOriented)))
      rw [BlockEmbedding.quaternion_mul]
      exact (P.oriented_link_pin (hp e List.mem_cons_self)).mul
        (word_pin P es (fun f hf => hp f (List.mem_cons_of_mem e hf)))

/-- Every spin, with no change in polynomial, observable normalization or action. -/
theorem character_pin (P : Placement) (edges : List OrientedBF4Link)
    (hp : ∀ e, e ∈ edges → e.link ∈ boundaryCompleteSlabLinks P.source) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (character P.source edges spin))
      (character P.target (edges.map P.shiftOriented) spin) :=
  P.embedding.character_of_quaternion (word_pin P edges hp) spin

#print axioms word_pin
#print axioms character_pin

end YMGap.Continuum.BF4ExactSlabTranslatedWilsonWord
