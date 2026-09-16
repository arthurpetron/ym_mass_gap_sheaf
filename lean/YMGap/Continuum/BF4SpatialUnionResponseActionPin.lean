/-
# The filtered current response action is the translated ORIGINAL full slab

Use the concrete response placement, including its actual physical face
permutation, to transport normalized finite moments and their cutoff limits.
Both numerator and partition use the SAME cutoff headCutoff(w)+stage.
Two individually pinned observables give the corresponding connected pin;
their product pin is derived from the actual polynomial embedding.

The source is the original full response slab. The target law here contains
only the current chain factors retained by the response membership mask.
No equality, positivity transfer, or error estimate for the unfiltered
current action is asserted. That boundary comparison remains separate.
-/

import YMGap.Continuum.BF4SpatialUnionResponseGeometry
import YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
import YMGap.Continuum.BF4ExactSlabMixedAction
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4SpatialUnionResponseActionPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4SpatialUnionResponseGeometry
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (eqv_close)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Exactly the filtered current chain used in the boundary comparison. -/
def insideIds (s : Nat) : List Nat := (ambientIds s).filter (keep s)

theorem insideIds_physical (s id : Nat) (hi : id ∈ insideIds s) :
    id ∈ slabPhysicalFaceEdges (targetExtent s) :=
  ambientIds_physical s (List.mem_filter.mp hi).1

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem finiteValue_perm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (xs ys : List Nat)
    (hx : ∀ id, id ∈ xs → id ∈ slabPhysicalFaceEdges extent)
    (hy : ∀ id, id ∈ ys → id ∈ slabPhysicalFaceEdges extent)
    (hperm : xs.Perm ys) (p : RatPoly) (stage : Nat) :
    finiteValue w hw0 hw1 extent xs hx p stage ≈
      finiteValue w hw0 hw1 extent ys hy p stage := by
  unfold finiteValue
  apply qmul (BF4ExactSlabMixedAction.moment_perm w _ extent p hperm)
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact Q'.recipPos_eqv_congr _ _ _ _
    (BF4ExactSlabMixedAction.partition_perm w _ extent hperm)

/-- Exact normalized transport at one shared original cutoff. -/
theorem finiteValue_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (targetExtent s)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) q) (stage : Nat) :
    finiteValue w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) q stage ≈
      finiteValue w hw0 hw1 (sourceExtent s) (slabPhysicalFaceEdges (sourceExtent s))
        (fun _ hi => hi) p stage :=
  Q'.eqv_trans _ _ _
    (finiteValue_perm hw0 hw1 (targetExtent s) (insideIds s) (translatedIds s)
      (insideIds_physical s) (fun _ hi => translatedIds_physical s hi) (filter_perm s) q stage)
    (BF4ExactSlabTranslatedSelectedAction.finiteValue_pin_of_prefix
      (responsePlacement s) hw0 hw1 (slabPhysicalFaceEdges (sourceExtent s))
      (fun _ hi => hi) p hp q hq he stage)

/-- The existing explicit cutoff-limit states preserve the same action pin. -/
theorem expectation_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (targetExtent s)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) q) :
    Equiv (expectation w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) q)
      (expectation w hw0 hw1 (sourceExtent s) (slabPhysicalFaceEdges (sourceExtent s))
        (fun _ hi => hi) p) :=
  Equiv_of_ofQ'_limit_close (finite_converges w hw0 hw1 _ _ _ _)
    (finite_converges w hw0 hw1 _ _ _ _)
    (fun epsilon hepsilon => ⟨0, fun stage _ => eqv_close
      (finiteValue_pin hw0 hw1 s p hp q hq he stage) epsilon hepsilon⟩)

private theorem product_pin (s : Nat) {p q a b : RatPoly}
    (ha : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) a)
    (hb : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial q) b) :
    QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial (polyMul p q)) (polyMul a b) := by
  rw [BlockEmbedding.polynomial_mul]
  exact ha.mul hb

/-- The connected subtraction is transported, not discarded or re-centered
in a different law. The product pin follows from the two individual pins. -/
theorem finiteCovariance_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (hq : SupportedQuaternionBlocks (blocks (sourceExtent s)) q)
    (a b : RatPoly)
    (ha : SupportedQuaternionBlocks (blocks (targetExtent s)) a)
    (hb : SupportedQuaternionBlocks (blocks (targetExtent s)) b)
    (hea : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) a)
    (heb : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial q) b) (stage : Nat) :
    finiteCovariance w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) a b stage ≈
      finiteCovariance w hw0 hw1 (sourceExtent s) (slabPhysicalFaceEdges (sourceExtent s))
        (fun _ hi => hi) p q stage :=
  Q'.add_eqv_congr'
    (finiteValue_pin hw0 hw1 s (polyMul p q) (supported_polyMul hp hq)
      (polyMul a b) (supported_polyMul ha hb) (product_pin s hea heb) stage)
    (Q'.neg_eqv_congr _ _ (qmul (finiteValue_pin hw0 hw1 s p hp a ha hea stage)
      (finiteValue_pin hw0 hw1 s q hq b hb heb stage)))

theorem covariance_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (hq : SupportedQuaternionBlocks (blocks (sourceExtent s)) q)
    (a b : RatPoly)
    (ha : SupportedQuaternionBlocks (blocks (targetExtent s)) a)
    (hb : SupportedQuaternionBlocks (blocks (targetExtent s)) b)
    (hea : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) a)
    (heb : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial q) b) :
    Equiv (covariance w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) a b)
      (covariance w hw0 hw1 (sourceExtent s) (slabPhysicalFaceEdges (sourceExtent s))
        (fun _ hi => hi) p q) :=
  Equiv_of_ofQ'_limit_close (finite_covariance_converges w hw0 hw1 _ _ _ _ _)
    (finite_covariance_converges w hw0 hw1 _ _ _ _ _)
    (fun epsilon hepsilon => ⟨0, fun stage _ => eqv_close
      (finiteCovariance_pin hw0 hw1 s p q hp hq a b ha hb hea heb stage) epsilon hepsilon⟩)

private theorem allNome_finiteValue_eq_legacy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (stage : Nat) :
    finiteValue w hw0 hw1 extent ids hids p stage =
      BF4ExactSlabFaceSetExpectation.finiteValue w hw0 hw1 hsmall hd extent ids hids p
        (headCutoff w+stage) := rfl

/-- The small-nome source wrapper uses the very same original numerator
and reciprocal at headCutoff(w)+stage, despite its different floor proof. -/
theorem finiteValue_legacy_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (s : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (targetExtent s)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) q) (stage : Nat) :
    finiteValue w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) q stage ≈
      BF4ExactSlabFaceSetExpectation.finiteValue w hw0 hw1 hsmall hd (sourceExtent s)
        (slabPhysicalFaceEdges (sourceExtent s)) (fun _ hi => hi) p (headCutoff w+stage) :=
  Q'.eqv_trans _ _ _ (finiteValue_pin hw0 hw1 s p hp q hq he stage)
    (Q'.eqv_of_eq (allNome_finiteValue_eq_legacy hw0 hw1 hsmall hd _ _ _ p stage))

/-- The old original odd-slab covariance is exactly the source law,
not a separate positive model or a differently normalized covariance. -/
theorem covariance_original_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks (sourceExtent s)) p)
    (hq : SupportedQuaternionBlocks (blocks (sourceExtent s)) q)
    (a b : RatPoly)
    (ha : SupportedQuaternionBlocks (blocks (targetExtent s)) a)
    (hb : SupportedQuaternionBlocks (blocks (targetExtent s)) b)
    (hea : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial p) a)
    (heb : QuaternionPrefixPolynomialEqv (blocks (targetExtent s))
      ((responsePlacement s).embedding.polynomial q) b) :
    Equiv (covariance w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s) a b)
      (BF4ExactSlabTwoProbeCovariance.covariance w hw0 hw1 (1+s) p q) :=
  (covariance_pin hw0 hw1 s p q hp hq a b ha hb hea heb).trans
    ((CReal.sub_congr_left (odd_expectation_pin w hw0 hw1 (1+s) (polyMul p q))).trans
      (CReal.sub_congr_right
        ((Pivot2.mul_congr_left (odd_expectation_pin w hw0 hw1 (1+s) p)).trans
          (Pivot2.mul_congr_right (odd_expectation_pin w hw0 hw1 (1+s) q)))))

end YMGap.Continuum.BF4SpatialUnionResponseActionPin

#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.insideIds
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.insideIds_physical
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.finiteValue_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.expectation_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.finiteCovariance_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.covariance_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.finiteValue_legacy_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseActionPin.covariance_original_pin
