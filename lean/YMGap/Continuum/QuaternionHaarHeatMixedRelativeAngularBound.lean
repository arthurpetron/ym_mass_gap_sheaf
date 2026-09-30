/-
# Mixed relative angular bounds for ORIGINAL heat prefixes

Remove the finite Jacobi weights with explicit value and mixed-derivative
deficit moduli. The original positive heat floor pays the approximation
precision, not the final relative derivative cost. The ordered derivatives
may use different angular planes; their scalar intervals are explicit inputs.

The resulting constants are cutoff- and carrier-independent at each strict
nome, not uniform near nome one. No full collar score, global signed-family
variance improvement, or physical mass calibration is claimed here.
-/

import YMGap.Continuum.JacobiHeatMixedRelativeAngularBound
import YMGap.Continuum.QuaternionHaarHeatMixedAngularDeficit
import YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound

namespace YMGap.Continuum.QuaternionHaarHeatMixedRelativeAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier (intervalNeg)
open YMGap.Continuum.QuaternionHaarRelativePolynomialInterval
open YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
open YMGap.Continuum.JacobiHeatMixedRelativeAngularBound (mixedRelativeCost)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCap relativeCutoff)

private def relativeApproximation {blocks : Nat} {p f e v u z : RatPoly} {a b c : Q'}
    (h : RatPolyCoeffEqv p (polyAdd f e))
    (hv : RatPolyCoeffEqv v (polyAdd u z))
    (hc0 : (0 : Q') ≤ c) (F : RelativeInterval blocks f u c)
    (E : Interval blocks e a) (Z : Interval blocks z b)
    (floor : Certificate blocks (polyAdd p (polyNeg (cap (c*a+b))))) :
    RelativeInterval blocks p v (c+1) := by
  let total := polyAdd f e
  let budget := cap (c*a+b)
  have hf : Certificate blocks (polyAdd total (polyNeg budget)) :=
    .ofCoeff (h.symm.add (.refl _)) floor
  have hu : Certificate blocks (polyAdd budget
      (polyAdd (polyMul (cap c) e) (polyNeg z))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add ((cap_mul_left c e).add (.refl _)))
      (((E.smul c hc0).add (intervalNeg Z)).lower)
  have hl : Certificate blocks (polyAdd budget
      (polyAdd (polyMul (cap c) e) z)) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add ((cap_mul_left c e).add (.refl _)))
      (((E.smul c hc0).add Z).lower)
  have hc : RatPolyCoeffEqv (cap (c+1)) (polyAdd (cap c) polyOne) :=
    (cap_add c 1).symm.trans ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul polyOne))
  refine RelativeInterval.baseOfCoeff h (RelativeInterval.ofCoeff hv ?_)
  constructor
  · exact .ofCoeff
      (((hc.mul_right total).add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.const 1)) (.add (.var 1) (.var 2)))
            (.add (.var 3) (.var 4)))
          (.add (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
              (.add (.var 5) (.add (.mul (.var 0) (.var 2)) (.var 4))))
            (.add (.add (.var 1) (.var 2)) (.neg (.var 5))))
          (by decide) (fun
            | 0 => cap c | 1 => f | 2 => e | 3 => u | 4 => z | _ => budget)))
      ((F.lower.add hl).add hf)
  · exact .ofCoeff
      (((hc.mul_right total).add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.const 1)) (.add (.var 1) (.var 2)))
            (.neg (.add (.var 3) (.var 4))))
          (.add (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
              (.add (.var 5) (.add (.mul (.var 0) (.var 2)) (.neg (.var 4)))))
            (.add (.add (.var 1) (.var 2)) (.neg (.var 5))))
          (by decide) (fun
            | 0 => cap c | 1 => f | 2 => e | 3 => u | 4 => z | _ => budget)))
      ((F.upper.add hu).add hf)

/-- Mixed cost `m R + d e R^2 + 1`; no reciprocal heat minimum. -/
def mixedRelativeCap (w d e m : Q') : Q' := mixedRelativeCost w d e m + 1

/-- The heat minimum enters only this required approximation precision. -/
def errorTolerance (w d e m : Q') : Q' :=
  HKConv.divPos (headFloor w) (mixedRelativeCap w d e m)

/-- One explicit cutoff supplies both first bounds and the mixed bound. -/
def mixedRelativeCutoff (w d e m : Q') : Nat :=
  relativeCutoff w d + relativeCutoff w e + headCutoff w +
    BF4ExactSlabJacobiDeficitInterval.deficitCutoff w (errorTolerance w d e m) +
    QuaternionHaarHeatMixedAngularDeficit.deficitCutoff w d e m (errorTolerance w d e m)

theorem mixedRelativeCost_nonnegative {w d e m : Q'}
    (hw0 : (0 : Q') < w) (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e)
    (hm : (0 : Q') ≤ m) : (0 : Q') ≤ mixedRelativeCost w d e m := by
  have hR := JacobiShiftedRelativeSlope.budget_nonnegative hw0
  exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hm hR)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hd he) (Q'.mul_nonneg _ _ hR hR))

theorem mixedRelativeCap_positive {w d e m : Q'}
    (hw0 : (0 : Q') < w) (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e)
    (hm : (0 : Q') ≤ m) : (0 : Q') < mixedRelativeCap w d e m :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 _ (mixedRelativeCost_nonnegative hw0 hd he hm))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem errorTolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (d e m : Q') :
    (0 : Q') < errorTolerance w d e m :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (headFloor_positive hw0 hw1))

theorem error_budget {w d e m : Q'} (hw0 : (0 : Q') < w)
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e) (hm : (0 : Q') ≤ m) :
    Q'.eqv (mixedRelativeCost w d e m * errorTolerance w d e m + errorTolerance w d e m)
      (headFloor w) :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.var 1) (.add (.var 0) (.const 1))) (by decide)
      (fun | 0 => mixedRelativeCost w d e m | _ => errorTolerance w d e m))
    (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (mixedRelativeCap_positive hw0 hd he hm)))

/-- SAME original heat prefix, for arbitrary ordered angular planes at all
sufficiently late cutoffs. The nome and the three scalar caps are explicit;
carrier size and cutoff do not occur in the three resulting relative costs. -/
def heatPrefixMixedRelativeBoundAt {blocks oi oj ii ij : Nat} {p : PolyQuaternion}
    {w d e m : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (hp : Supported blocks p) (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (DX : Interval blocks (angularDerivative oi oj p.scalar) d)
    (DY : Interval blocks (angularDerivative ii ij p.scalar) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij p.scalar)) m)
    (K : Nat) (hK : mixedRelativeCutoff w d e m ≤ K) :
    MixedBound blocks oi oj ii ij (heatPrefix w K p.scalar)
      (relativeCap w d) (relativeCap w e) (mixedRelativeCap w d e m) := by
  have ho : relativeCutoff w d ≤ K := by unfold mixedRelativeCutoff at hK; omega
  have hi : relativeCutoff w e ≤ K := by unfold mixedRelativeCutoff at hK; omega
  have hh : headCutoff w ≤ K := by unfold mixedRelativeCutoff at hK; omega
  have hv : BF4ExactSlabJacobiDeficitInterval.deficitCutoff w (errorTolerance w d e m) ≤ K+1 := by
    unfold mixedRelativeCutoff at hK
    omega
  have hm : QuaternionHaarHeatMixedAngularDeficit.deficitCutoff w d e m
      (errorTolerance w d e m) ≤ K+1 := by
    unfold mixedRelativeCutoff at hK
    omega
  let F := JacobiHeatMixedRelativeAngularBound.weightedHeatBound hw0 hw1 hoi hoj hii hij
    hp hu DX DY DXY (K+1)
  let E := deficitInterval hw0 hw1 (SquareBound.scalar hp hu) (errorTolerance w d e m)
    (errorTolerance_positive hw0 hw1 d e m) (K+1) hv
  let DE := QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval hoi hoj hii hij
    hw0 hw1 (SquareBound.scalar hp hu) DX DY DXY
    (errorTolerance_positive hw0 hw1 d e m) (K+1) hm
  have floor : Certificate blocks (polyAdd (heatPrefix w K p.scalar)
      (polyNeg (cap (mixedRelativeCost w d e m * errorTolerance w d e m +
        errorTolerance w d e m)))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
      (RatPolyCoeffEqv.smul_coefficient
        (error_budget hw0 DX.nonnegative DY.nonnegative DXY.nonnegative) polyOne)))
      (prefixFloorCertificate hw0 hw1 hp hu K hh)
  have hvalue := prefix_eq_weighted_add_deficit w K p.scalar
  have hder := (angularDerivative_congr oi oj (angularDerivative_congr ii ij hvalue)).trans
    ((angularDerivative_congr oi oj (angularDerivative_add ii ij _ _)).trans
      (angularDerivative_add oi oj _ _))
  exact ⟨QuaternionHaarHeatRelativeAngularBound.heatPrefixRelativeBoundAt
      hw0 hw1 hoi hoj hp hu DX K ho,
    QuaternionHaarHeatRelativeAngularBound.heatPrefixRelativeBoundAt
      hw0 hw1 hii hij hp hu DY K hi,
    Q'.le_of_lt (mixedRelativeCap_positive hw0 DX.nonnegative DY.nonnegative DXY.nonnegative),
    relativeApproximation hvalue hder F.mixedNonnegative F.mixed E DE floor⟩

#print axioms mixedRelativeCap
#print axioms errorTolerance
#print axioms mixedRelativeCutoff
#print axioms mixedRelativeCost_nonnegative
#print axioms mixedRelativeCap_positive
#print axioms errorTolerance_positive
#print axioms error_budget
#print axioms heatPrefixMixedRelativeBoundAt

end YMGap.Continuum.QuaternionHaarHeatMixedRelativeAngularBound
