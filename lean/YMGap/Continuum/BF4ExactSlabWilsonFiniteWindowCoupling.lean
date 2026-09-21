/-
# Finite Wilson-window coupling adapter

This file identifies one finite original Wilson window with the existing
all-nome normalized expectation at the corresponding ambient extent.  It
also transports the existing finite-face two-nome comparison to that
window.  The ambient extent, time pivot and coupling cap remain explicit;
no width-, time-, or coupling-uniform conclusion is asserted here.
-/
import YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
import YMGap.Continuum.BF4ExactSlabSpatialWilsonControl

namespace YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
open YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The existing all-nome normalized expectation at the finite Wilson-window
ambient extent determined by the time pivot. -/
def finiteWindowExpectation {w : Q'} {width : Nat} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (L : Nat) (e : WindowExpression width) (t : Nat) : CReal :=
  expectation w hw0 hw1 (width+(t+(L+t)))
    (chainIds (width+(t+(L+t))) width 0 (t+(L+t)))
    (fun _ hi => chainIds_physical hi)
    (placedPolynomial (width+(t+(L+t))) t e)

/-- The cutoff-removed stream is exactly the original window scalar at the
same finite time pivot. -/
theorem finiteWindow_converges {w : Q'} {width : Nat} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (L : Nat) (e : WindowExpression width) (t : Nat) :
    ConvergesTo
      (fun stage => ofQ' (originalWindowScalar hw0 hw1 L e stage t t))
      (finiteWindowExpectation hw0 hw1 L e t) := by
  unfold originalWindowScalar finiteWindowExpectation
  exact finite_converges w hw0 hw1 (width+(t+(L+t)))
    (chainIds (width+(t+(L+t))) width 0 (t+(L+t)))
    (fun _ hi => chainIds_physical hi)
    (placedPolynomial (width+(t+(L+t))) t e)

/-- The finite-face cap inherited from the existing two-nome comparison. -/
def finiteWindowCap {width : Nat} (W u v : Q') (L : Nat)
    (e : WindowExpression width) (t : Nat) : Q' :=
  finiteSetCap W u v (windowCap e)
    (chainIds (width+(t+(L+t))) width 0 (t+(L+t)))

theorem finiteWindow_difference_bound {width : Nat}
    {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
    (hvW : v ≤ W) (hW1 : W < (1 : Q'))
    (L : Nat) (e : WindowExpression width) (he : Within L e) (t : Nat) :
    leEv
      (CReal.abs (CReal.sub
        (finiteWindowExpectation (w := v) (Q'.pos_of_lt_of_le hu0 huv)
          (Q'.lt_of_le_of_lt hvW hW1) L e t)
        (finiteWindowExpectation (w := u) hu0
          (Q'.lt_of_le_of_lt huv (Q'.lt_of_le_of_lt hvW hW1)) L e t)))
      (ofQ' (finiteWindowCap W u v L e t)) := by
  let extent := width+(t+(L+t))
  let ids := chainIds extent width 0 (t+(L+t))
  have hwidth : width ≤ extent := by
    dsimp [extent]
    omega
  have htime : t+L ≤ extent := by
    dsimp [extent]
    omega
  have hplaced : Interval (B extent)
      (placedPolynomial extent t e) (windowCap e) :=
    placed_interval hwidth htime e he
  have hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent :=
    fun _ hi => chainIds_physical hi
  exact expectation_difference_bound hu0 huv hvW hW1 extent ids hids hplaced

end YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling

#print axioms YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling.finiteWindowExpectation
#print axioms YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling.finiteWindow_converges
#print axioms YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling.finiteWindowCap
#print axioms YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling.finiteWindow_difference_bound
