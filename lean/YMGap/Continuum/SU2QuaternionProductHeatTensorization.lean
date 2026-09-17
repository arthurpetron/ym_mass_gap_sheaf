/-
# Width-independent centered contraction of the ORIGINAL product heat kernel

Induct over the actual list of active link pairs. At its first link, split
the input into its conditional Haar projection and its genuine fluctuation.
The projected input uses the remaining original factors; the fluctuation is
bounded by the positive residual of that ONE factor times ALL other factors.
The two outputs are Haar-orthogonal, so exact Pythagoras avoids a volume loss.

The empty product integrates every original lower coordinate. In particular,
unused fringe links are averaged, not declared identity channels. Sphere
normalization is used through supported Haar pairings, never strengthened to
coefficient equality. The final consumer is the original fixed-spatial
kineticMap. No spatial potential, interacting vacuum, OS comparison, or
physical mass calibration is removed or supplied by this ordinary-Haar bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.PositiveTimeCompressedTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction

namespace YMGap.Continuum.SU2QuaternionProductHeatTensorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem square_congr {n : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : SupportedHaarEqv n p q) :
    H n (polyMul p p) ≈ H n (polyMul q q) :=
  Q'.eqv_trans _ _ _ (h p hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm p q)) (h q hq))

private theorem unweighted_pair (n : Nat) (p q : RatPoly) :
    weightedPair n polyOne p q ≈ H n (polyMul p q) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul p q))

private theorem orthogonal_square (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : H n (polyMul p q) ≈ 0) :
    H n (polyMul (polyAdd p q) (polyAdd p q)) ≈
      H n (polyMul p p) + H n (polyMul q q) := by
  let D := weightedGNSData n polyOne (Certificate.one n)
  have hpq : D.B ⟨p,hp⟩ ⟨q,hq⟩ ≈ 0 :=
    Q'.eqv_trans _ _ _ (unweighted_pair n p q) h
  have hs := PositiveTimeCompressedTransfer.PositiveTimeCompression.diag_add_of_orthogonal D
    ⟨p,hp⟩ ⟨q,hq⟩ hpq
  change weightedPair n polyOne (polyAdd p q) (polyAdd p q) ≈
    weightedPair n polyOne p p + weightedPair n polyOne q q at hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (unweighted_pair n _ _))
    (Q'.eqv_trans _ _ _ hs
      (Q'.add_eqv_congr' (unweighted_pair n p p) (unweighted_pair n q q)))

/-- Exact output Pythagoras; only the projected summand loses the selected
factor, and that removal is justified at the supported-Haar level. -/
theorem productMap_square_split (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    H n (polyMul (productMap n w K (i::ids) f) (productMap n w K (i::ids) f)) ≈
      H n (polyMul (productMap n w K ids (project i f))
        (productMap n w K ids (project i f))) +
      H n (polyMul (productMap n w K (i::ids) (fluctuation i f))
        (productMap n w K (i::ids) (fluctuation i f))) := by
  have hall : ∀ j, j ∈ i::ids → j < n := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hids j hj
  have hp := productMap_supported n w K ids hids (project_supported i hf)
  have hq := productMap_supported n w K (i::ids) hall (fluctuation_supported i hf)
  have hdecomp : RatPolyCoeffEqv f (polyAdd (project i f) (fluctuation i f)) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => f | _ => project i f)
  have hlinear := (productMap_congr n w K (i::ids) hdecomp).trans
    (productMap_add n w K (i::ids) (project i f) (fluctuation i f))
  have hout : SupportedHaarEqv n (productMap n w K (i::ids) f)
      (polyAdd (productMap n w K ids (project i f))
        (productMap n w K (i::ids) (fluctuation i f))) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hlinear)).trans
      ((head_removal n w K i ids hi hnot hids f hf).add
        (SupportedHaarEqv.refl n _))
  exact Q'.eqv_trans _ _ _
    (square_congr (productMap_supported n w K (i::ids) hall hf)
      (supported_add hp hq) hout)
    (orthogonal_square n _ _ hp hq
      (cross_orthogonal n w K i ids hi hnot hids f hf))

/-- The SAME computed product map contracts every globally Haar-centered
input by the one-link squared rate, independently of the active-list length. -/
theorem productMap_centered_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) :
    ∀ (ids : List Nat), ids.Nodup → (∀ i, i ∈ ids → i < n) →
      ∀ {f : RatPoly}, SupportedQuaternionBlocks n f → H n f ≈ 0 →
      H n (polyMul (productMap n w K ids f) (productMap n w K ids f)) ≤
        squaredHeatRate w * H n (polyMul f f)
  | [], _, _, f, hf, hc => by
      have hz : RatPolyCoeffEqv (productMap n w K [] f) polyZero :=
        (productMap_nil n w K f hf).trans
          ((RatPolyCoeffEqv.smul_coefficient hc polyOne).trans (RatPolyCoeffEqv.zero_smul polyOne))
      have hs : H n (polyMul (productMap n w K [] f) (productMap n w K [] f)) ≈ 0 :=
        haar_of_coeff (hz.mul hz)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
        (Q'.mul_nonneg _ _ (squaredHeatRate_nonnegative hw0 hw1)
          (Certificate.haar_nonnegative (.square f hf)))
  | i::ids, hn, hids, f, hf, hc => by
      have hnd := List.nodup_cons.mp hn
      have hi := hids i List.mem_cons_self
      have ht (j : Nat) (hj : j ∈ ids) : j < n := hids j (List.mem_cons_of_mem i hj)
      have hp := productMap_centered_square_bound n hw0 hw1 K hK ids hnd.2 ht
        (project_supported i hf) (Q'.eqv_trans _ _ _ (project_mean n i hi f) hc)
      have hq := productMap_conditional_square_bound n hw0 hw1 K hK i ids hnd.2
        hi hnd.1 ht (fluctuation_supported i hf) (project_fluctuation_zero i f)
      have hsum := Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hp)
        (Q'.add_le_add_left _ _ _ hq)
      have hbudget : squaredHeatRate w * H n (polyMul (project i f) (project i f)) +
          squaredHeatRate w * H n (polyMul (fluctuation i f) (fluctuation i f)) ≈
          squaredHeatRate w * H n (polyMul f f) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (square_decomposition n i hi f)))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (productMap_square_split n w K i ids hi hnd.1 ht hf))
        (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hbudget))

/-- Actual fixed-spatial kinetic consumer, including width zero and every
original fringe coordinate. This is not the spatially weighted transfer. -/
theorem kineticMap_centered_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hc : H (N width) f ≈ 0) :
    H (N width) (polyMul (kineticMap w K width f) (kineticMap w K width f)) ≤
      squaredHeatRate w * H (N width) (polyMul f f) := by
  have h := productMap_centered_square_bound (N width) hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) hf hc
  simpa only [kineticMap, productMap, productHeat, kineticWeight_eq_indexedProduct] using h

end YMGap.Continuum.SU2QuaternionProductHeatTensorization

#print axioms YMGap.Continuum.SU2QuaternionProductHeatTensorization.productMap_square_split
#print axioms YMGap.Continuum.SU2QuaternionProductHeatTensorization.productMap_centered_square_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatTensorization.kineticMap_centered_square_bound
