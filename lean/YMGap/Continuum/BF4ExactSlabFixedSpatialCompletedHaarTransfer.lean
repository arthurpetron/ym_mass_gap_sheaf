/-
# Complete the actual fixed-spatial weighted step in ordinary Haar norm

The dense map is the original T f = integral K(x,y)V(x)f(x) dH(x).
Its proved cutoff-independent norm cap constructs a map on the existing
ordinary-Haar GNS completion, with explicit representative moduli. The
dense pin and completed linearity retain that SAME T, without rescaling.

This is a completed ordinary-Haar operator at each late finite cutoff.
Neither operator convergence in the heat cutoff nor a stationary vacuum,
physical reflected OS identification, strict contraction, volume/spacing
uniformity, or continuum Yang--Mills is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

local notation:max "N" width:arg => List.length (baseLinks width)

/-- The existing ordinary-Haar datum with its proved rational module action. -/
def sliceData (width : Nat) : SmulGNSData where
  toGNSData := haarData (N width)
  smul_sub := by
    intro c p q
    change RatPolyCoeffEqv (polySmul c (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (polySmul c p.val) (polySmul (-1) (polySmul c q.val)))
    exact (RatPolyCoeffEqv.smul_add c p.val _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.smul_assoc c (-1) q.val).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) q.val).trans
            (RatPolyCoeffEqv.smul_assoc (-1) c q.val).symm)))

/-- All hypotheses of the generic completion consumer are proved for actual T. -/
def denseTransfer {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    BoundedMap (sliceData width).toGNSData (stepCap w width) :=
  ofPolynomial (N width) (transferStep w K width) (stepCap w width)
    (stepCap_nonnegative hw0 hw1 width)
    (transferStep_supported w K width)
    (fun p q _ _ => transferStep_add w K width p q)
    (fun c p _ => transferStep_smul w K width c p)
    (fun _ hp => transferStep_square_bound hw0 hw1 K width hK hp)

/-- Same finite-cutoff step on the original ordinary-Haar completion. -/
def completedTransfer {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    GNSCompletionSpace (sliceData width).toGNSData →
      GNSCompletionSpace (sliceData width).toGNSData :=
  (denseTransfer hw0 hw1 K width hK).completionMap

/-- Output Cauchy representatives keep the explicit inherited input tolerance. -/
theorem transfer_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K)
    (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') :
    ((denseTransfer hw0 hw1 K width hK).mapCauchy X).modulus epsilon =
      X.modulus (tolerance (stepCap w width) epsilon) := rfl

/-- Exact dense pin to the pre-existing original transfer polynomial. -/
theorem completedTransfer_embed {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K)
    (f : (sliceData width).toGNSData.V) :
    completedTransfer hw0 hw1 K width hK (embedV (sliceData width).toGNSData f) =
      embedV (sliceData width).toGNSData
        ⟨transferStep w K width f.val, transferStep_supported w K width f.property⟩ :=
  (denseTransfer hw0 hw1 K width hK).completionMap_embed f

theorem completedTransfer_norm_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K)
    (x : GNSCompletionSpace (sliceData width).toGNSData) :
    CReal.RCle
      ((sliceData width).toGNSData.cinnerCompl
        (completedTransfer hw0 hw1 K width hK x) (completedTransfer hw0 hw1 K width hK x))
      (CReal.RCscale (stepCap w width * stepCap w width)
        ((sliceData width).toGNSData.cinnerCompl x x)) :=
  (denseTransfer hw0 hw1 K width hK).completionMap_norm_bound x

/-- Linearity is proved on arbitrary completion points, not just on dense inputs. -/
theorem completedTransfer_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K)
    (x y : GNSCompletionSpace (sliceData width).toGNSData) :
    completedTransfer hw0 hw1 K width hK ((sliceData width).toGNSData.cAdd x y) =
      (sliceData width).toGNSData.cAdd
        (completedTransfer hw0 hw1 K width hK x) (completedTransfer hw0 hw1 K width hK y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  intro epsilon he
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (rad_of_veq (sliceData width).toGNSData
      (transferStep_add w K width (X.seq n).val (Y.seq n).val))) (Q'.le_of_lt he)

theorem completedTransfer_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (c : Q')
    (x : GNSCompletionSpace (sliceData width).toGNSData) :
    completedTransfer hw0 hw1 K width hK ((sliceData width).cSmul c x) =
      (sliceData width).cSmul c (completedTransfer hw0 hw1 K width hK x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  intro epsilon he
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (rad_of_veq (sliceData width).toGNSData
      (transferStep_smul w K width c (X.seq n).val))) (Q'.le_of_lt he)

private theorem haar_inner_embed (blocks : Nat) (f g : (haarData blocks).V) :
    (haarData blocks).cinnerCompl (embedV (haarData blocks) f) (embedV (haarData blocks) g) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (quaternionHaar blocks (polyMul f.val g.val))) :=
  ((haarData blocks).cinnerCompl_embed f g).trans
    (Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => haarData_pair blocks f g)))

/-- The completed pairing is the SAME rational Haar pairing of actual T. -/
theorem completedTransfer_pair_dense {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K)
    (f g : (sliceData width).toGNSData.V) :
    (sliceData width).toGNSData.cinnerCompl
        (completedTransfer hw0 hw1 K width hK (embedV (sliceData width).toGNSData f))
        (embedV (sliceData width).toGNSData g) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (quaternionHaar (N width) (polyMul (transferStep w K width f.val) g.val))) := by
  rw [completedTransfer_embed]
  exact haar_inner_embed (N width)
    ⟨transferStep w K width f.val, transferStep_supported w K width f.property⟩ g

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.sliceData
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.denseTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.transfer_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer_embed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer.completedTransfer_pair_dense
