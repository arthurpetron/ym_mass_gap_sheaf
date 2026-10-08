/-
# Literal Wilson windows in the SAME represented gauge completion

The actual placed polynomial supplies its support and every common-auxiliary
vertex-ledger invariant. It therefore has an explicit constant Cauchy
representative inside the existing full-action completion. The existing
completed conditional projection constructs a represented gauge witness
for its actual image; neither a new completion nor an invariance premise
is supplied.

This finite weighted GNS carrier is not identified here with the all-nome
OS carrier or a continuum QFT. There is no signed-cost, survival or mass claim.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord
import YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion

namespace YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabVertexGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

/-- The literal original placed insertion, with produced carrier support. -/
def windowPolynomial {width : Nat} (start : Nat) (e : WindowExpression width) : (F).V :=
  ⟨placedPolynomial extent start e, placed_supported extent start e⟩

theorem windowPolynomial_val {width : Nat} (start : Nat) (e : WindowExpression width) :
    (windowPolynomial hw0 hw1 K extent hK start e).val = placedPolynomial extent start e := rfl

/-- Physical room and the original window guard produce the existing property. -/
theorem window_gaugePolynomial {width start L : Nat} (hw : width ≤ extent)
    (ht : start+L ≤ extent) (e : WindowExpression width) (he : Within L e) :
    GaugePolynomial hw0 hw1 K extent hK
      (windowPolynomial hw0 hw1 K extent hK start e) :=
  fun tags => placedWindow_invariant hw ht tags e he

/-- A witnessed point in the ORIGINAL full-action completion, with its
constant Cauchy representative; no representative is selected from Prop. -/
def windowRepresentative {width start L : Nat} (hw : width ≤ extent)
    (ht : start+L ≤ extent) (e : WindowExpression width) (he : Within L e) :
    Witness hw0 hw1 K extent hK
      (embedV F (windowPolynomial hw0 hw1 K extent hK start e)) :=
  ofPolynomial hw0 hw1 K extent hK _ (window_gaugePolynomial hw0 hw1 K extent hK hw ht e he)

/-- The actual completed block conditional projection of this Wilson point
has a produced invariant representative in the SAME full-action carrier. -/
def blockWindowRepresentative {width start L : Nat} (hw : width ≤ extent)
    (ht : start+L ≤ extent) (e : WindowExpression width) (he : Within L e)
    (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    Witness hw0 hw1 K extent hK
      (conditionalProjection hw0 hw1 K extent hK links hl
        (embedV F (windowPolynomial hw0 hw1 K extent hK start e))) :=
  block hw0 hw1 K extent hK links hl
    (windowRepresentative hw0 hw1 K extent hK hw ht e he)

end YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion

#print axioms YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion.windowPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion.windowPolynomial_val
#print axioms YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion.window_gaugePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion.windowRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabGaugeWilsonCompletion.blockWindowRepresentative
