/-
# Identification of ordered associator channels with direct-right channels

The fixed ordered right chart was derived by transposing the cyclic chart's
outer physical channel.  This file makes the resulting dependent-index
identification explicit and proves that its raw coordinates are exactly the
pre-existing direct-right coordinates used by the fixed-output `triRight`
analysis path.
-/

import YMGap.Continuum.SU2OrderedRightNormalizationBridge
import YMGap.Continuum.SU2DirectRightFixedOutputSections

namespace YMGap.Continuum.SU2OrderedDirectRightIdentification

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2OrderedRightNormalizationBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections

local infix:50 " ≈ " => Q'.eqv

/-- A choice-free two-sided equivalence of index types. -/
structure ConstructiveIndexEquiv (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Transpose the outer physical channel of a cyclicly indexed right chart
to obtain the direct fixed-ordered right channel. -/
def orderedToDirectChannel {m n p : Nat}
    (q : LeftNestedCGChannel n p m) :
    DirectRightNestedCGChannel m n p where
  k := q.k
  k_le := q.k_le
  outer := transposePhysicalChannel q.outer

/-- Transpose the direct channel back to the cyclicly indexed carrier used by
the ordered associator package. -/
def directToOrderedChannel {m n p : Nat}
    (q : DirectRightNestedCGChannel m n p) :
    LeftNestedCGChannel n p m where
  k := q.k
  k_le := q.k_le
  outer := transposePhysicalChannel q.outer

/-- **Constructive dependent-index equivalence for the ordered right chart.** -/
def orderedDirectChannelEquiv (m n p : Nat) :
    ConstructiveIndexEquiv (LeftNestedCGChannel n p m)
      (DirectRightNestedCGChannel m n p) where
  toFun := orderedToDirectChannel
  invFun := directToOrderedChannel
  left_inv := by
    intro q
    cases q with
    | mk k hk outer =>
        cases outer
        rfl
  right_inv := by
    intro q
    cases q with
    | mk k hk outer =>
        cases outer
        rfl

/-- The transposed first-pair tensor in the ordered associator definition is
pointwise the direct last-pair tensor. -/
theorem transpose_firstPairOutput_eq_lastPairOutput (n p : Nat)
    (x : TriForm) (k : Nat) :
    BForm2Eqv
      (transpose2 (firstPairOutput n p (rotateTri x) k))
      (lastPairOutput n p x k) := by
  intro i s
  exact Q'.eqv_refl _

/-- **The fixed-ordered associator coordinate is exactly the direct-right
coordinate under the explicit channel equivalence.** -/
theorem orderedRightNestedCoordinates_eq_direct (m n p : Nat)
    (x : TriForm) (q : LeftNestedCGChannel n p m) :
    orderedRightNestedCoordinates m n p x q ≈
      directRightNestedCoordinates m n p x
        ((orderedDirectChannelEquiv m n p).toFun q) := by
  exact Q'.eqv_refl _

/-- The same coordinate identification in the inverse index direction. -/
theorem directRightNestedCoordinates_eq_ordered (m n p : Nat)
    (x : TriForm) (q : DirectRightNestedCGChannel m n p) :
    directRightNestedCoordinates m n p x q ≈
      orderedRightNestedCoordinates m n p x
        ((orderedDirectChannelEquiv m n p).invFun q) := by
  exact Q'.eqv_refl _

/-- A fixed-output right channel and output coefficient as an ordered
associator channel. -/
def fixedRightOrderedChannel {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    LeftNestedCGChannel b c a :=
  (orderedDirectChannelEquiv a b c).invFun
    (fixedRightNestedChannel q s hs)

/-- The fixed-output direct analysis is pointwise the ordered associator
coordinate on the explicitly corresponding dependent channel. -/
theorem fixedRightAnalysis_eq_orderedCoordinate {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (x : TriForm)
    (s : Nat) (hs : s ≤ d) :
    fixedRightAnalysis q x s ≈
      orderedRightNestedCoordinates a b c x
        (fixedRightOrderedChannel q s hs) := by
  unfold fixedRightAnalysis
  rw [dif_pos hs]
  exact directRightNestedCoordinates_eq_ordered a b c x
    (fixedRightNestedChannel q s hs)

/-- On every physical pure monomial, the ordered associator coordinate is
the repository's raw `triRight` coefficient, with no unstated sign. -/
theorem orderedCoordinate_pure_monomial_eq_triRight {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c)
    (s : Nat) (hs : s ≤ d) :
    orderedRightNestedCoordinates a b c
        (pureTri (mono i) (mono j) (mono l))
        (fixedRightOrderedChannel q s hs) ≈
      triRight a b c d q.intermediate
        (mono i) (mono j) (mono l) s := by
  have hdirect := orderedRightNestedCoordinates_eq_direct a b c
    (pureTri (mono i) (mono j) (mono l))
    (fixedRightOrderedChannel q s hs)
  have hraw := fixedRightAnalysis_pure_monomial_eq_triRight
    q i j l hi hj hl s (by omega)
  exact Q'.eqv_trans _ _ _ hdirect
    (by simpa only [fixedRightOrderedChannel, fixedRightAnalysis,
      dif_pos hs] using hraw)

end YMGap.Continuum.SU2OrderedDirectRightIdentification

#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.orderedDirectChannelEquiv
#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.transpose_firstPairOutput_eq_lastPairOutput
#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.orderedRightNestedCoordinates_eq_direct
#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.directRightNestedCoordinates_eq_ordered
#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.fixedRightAnalysis_eq_orderedCoordinate
#print axioms YMGap.Continuum.SU2OrderedDirectRightIdentification.orderedCoordinate_pure_monomial_eq_triRight
