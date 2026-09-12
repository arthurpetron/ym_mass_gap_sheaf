/-
# Reflection positivity of the ORIGINAL signed slab quadratic, every cutoff

The actual global channels are proved lower-local. Their reflected Haar
pairings factor into explicit rational squares; the original heat and
binomial weights are nonnegative for w >= 0. The original extent-one
signed quadratic is therefore a computable finite sum of weighted squares.

This theorem concerns the literal exact-Haar law, not the distinct positive
multiplicity-product law. It gives no strict spectral bound, physical time
semigroup, arbitrary-volume positivity, cutoff-limit modulus or continuum
QFT. No such conclusion is built into its hypotheses.
-/

import YMGap.Continuum.BF4ExactSlabLowerChannelLocality

namespace YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Explicit finite sum of squares of the channels' own Haar integrals.
All weights and rational values are retained as data; no square root is used. -/
def haarSquareSum (blocks : Nat) : SquareTree → Q'
  | .zero => 0
  | .term w p => w * (quaternionHaar blocks p * quaternionHaar blocks p)
  | .add p q => haarSquareSum blocks p + haarSquareSum blocks q

theorem treeHaar_eq_squareSum (half : Nat) : ∀ t : SquareTree,
    SquareTreeSupported (boundaryCompleteSlabLinks (centralExtent half)).length t →
    LowerSquareTree half t →
    (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (t.eval (centralExtent half))).eqv
      (haarSquareSum (boundaryCompleteSlabLinks (centralExtent half)).length t)
  | .zero, _, _ => Q'.eqv_refl 0
  | .term w _, hp, hl => Q'.eqv_trans _ _ _
      (quaternionHaar_polySmul _ w _)
      (Q'.mul_eqv_congr_left _ _ _ (lower_reflected_haar_square hp hl))
  | .add p q, hp, hl => Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (treeHaar_eq_squareSum half p hp.1 hl.1) (treeHaar_eq_squareSum half q hp.2 hl.2))

theorem haarSquareSum_nonnegative (blocks : Nat) : ∀ t : SquareTree,
    t.Nonnegative → (0 : Q') ≤ haarSquareSum blocks t
  | .zero, _ => show (0 : Q') ≤ 0 by decide
  | .term w _, hw => Q'.mul_nonneg w _ hw (SumOfSquares.q_mul_self_nonneg _)
  | .add p q, h => Q'.zero_le_add _ _ (haarSquareSum_nonnegative blocks p h.1) (haarSquareSum_nonnegative blocks q h.2)

/-- Constructive weighted-square value of the SAME signed observable. -/
def exactSlabSquareSum (w : Q') (K : Nat) (c : EdgeLabelling → Q') : Q' :=
  haarSquareSum 116 (observableSquares w K c)

theorem treeHaar_eq_squareSum_one (t : SquareTree)
    (hs : SquareTreeSupported 116 t) (hl : LowerSquareTree 0 t) :
    (quaternionHaar 116 (t.eval 1)).eqv (haarSquareSum 116 t) := by
  have h := treeHaar_eq_squareSum 0 t
  change SquareTreeSupported (boundaryCompleteSlabLinks 1).length t → LowerSquareTree 0 t →
    (quaternionHaar (boundaryCompleteSlabLinks 1).length (t.eval 1)).eqv
      (haarSquareSum (boundaryCompleteSlabLinks 1).length t) at h
  rw [correctedSlabLinks_extent_one_length] at h
  exact h hs hl

/-- This algebraic identity needs no sign restriction on w or c. -/
theorem exact_quadratic_eq_squareSum (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    (exactSlabAllCutoffQuadratic w K c).eqv (exactSlabSquareSum w K c) :=
  Q'.eqv_trans _ _ _ (exact_quadratic_eq_squareTreeHaar w K c)
    (treeHaar_eq_squareSum_one _ (observableSquares_support w K c) (observableSquares_lower w K c))

/-- Reflection positivity of the ORIGINAL signed exact-Haar slab form,
extent one, every spin cutoff and arbitrary signed boundary observable. -/
theorem exact_quadratic_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ exactSlabAllCutoffQuadratic w K c :=
  Q'.le_trans' _ _ _
    (haarSquareSum_nonnegative 116 _ (observableSquares_nonnegative hw K c))
    (Q'.le_of_eqv (Q'.eqv_symm (exact_quadratic_eq_squareSum w K c)))

end YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity

#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.haarSquareSum
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.treeHaar_eq_squareSum
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.haarSquareSum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.exactSlabSquareSum
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.treeHaar_eq_squareSum_one
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.exact_quadratic_eq_squareSum
#print axioms YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity.exact_quadratic_nonnegative
