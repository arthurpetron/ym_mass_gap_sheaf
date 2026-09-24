/-
# Full weighted energy on the computed cyclic degree tree

Expand BOTH actual pairings before estimating. Their zeroth-order terms
cancel exactly; the difference of the computed Casimir pairings is the
first-order coefficient. Both signed remainders remain, with a computed
two-sided quadratic budget. No orthogonal joint spectral resolution,
angular identification, source stationarity or scaling estimate is assumed.
-/

import YMGap.Continuum.SU2QuaternionCyclicModeTaylor
import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Computed first-order coefficient; its angular interpretation is not
supplied as a premise or asserted here. -/
def sourceFirstOrder (tail : Nat) (a f : RatPoly) : Q' :=
  pairCasimir tail (polyMul a f) (polyMul a f) +
    -(pairCasimir tail a (polyMul a (polyMul f f)))

/-- Sum of the TWO absolute leaf budgets, with all source and carrier
dependence retained. It has no explicit nome/cutoff argument for fixed a,f. -/
def sourceTaylorBudget (tail : Nat) (a f : RatPoly) : Q' :=
  pairBudget tail a (polyMul a (polyMul f f)) +
    pairBudget tail (polyMul a f) (polyMul a f)

/-- Exact full-energy Taylor identity, including the signed source correction
already contained in `sourceEnergy`. There is no additional correction term. -/
theorem sourceEnergy_taylor (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≈
      ((1 : Q')-w)*sourceFirstOrder tail a f +
        (pairRemainder tail w K a (polyMul a (polyMul f f)) +
          -(pairRemainder tail w K (polyMul a f) (polyMul a f))) := by
  have hz : quaternionHaar (tail+1) (polyMul (polyMul a (polyMul f f)) a) ≈
      quaternionHaar (tail+1) (polyMul (polyMul a f) (polyMul a f)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => a | _ => f))
  have hfirst := Q'.eqv_trans _ _ _
    (productPair_taylor tail w K a (polyMul a (polyMul f f)) ha)
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hz (Q'.eqv_refl _)) (Q'.eqv_refl _))
  have hsecond := productPair_taylor tail w K (polyMul a f) (polyMul a f)
    (supported_polyMul ha hf)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hsecond))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (.var 4))
        (.neg (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 3)))) (.var 5))))
      (.add (.mul (.var 1) (.add (.var 3) (.neg (.var 2))))
        (.add (.var 4) (.neg (.var 5))))
      (by decide) (fun
        | 0 => quaternionHaar (tail+1) (polyMul (polyMul a f) (polyMul a f))
        | 1 => (1 : Q')-w
        | 2 => pairCasimir tail a (polyMul a (polyMul f f))
        | 3 => pairCasimir tail (polyMul a f) (polyMul a f)
        | 4 => pairRemainder tail w K a (polyMul a (polyMul f f))
        | _ => pairRemainder tail w K (polyMul a f) (polyMul a f)))

/-- Upper estimate retains both remainder budgets; no signed leaf contribution
is discarded as if it were a nonnegative orthogonal diagonal. -/
theorem sourceEnergy_le_firstOrder_add_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*sourceFirstOrder tail a f +
        (((1 : Q')-w)*((1 : Q')-w))*sourceTaylorBudget tail a f := by
  have hr := Q'.add_le_add
    (pairRemainder_le_quadratic tail hw0 hw1 K hK a (polyMul a (polyMul f f)))
    (neg_pairRemainder_le_quadratic tail hw0 hw1 K hK (polyMul a f) (polyMul a f))
  have hb := Q'.le_trans' _ _ _ hr (Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_add_eqv (((1 : Q')-w)*((1 : Q')-w)) _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sourceEnergy_taylor tail w K a f ha hf))
    (Q'.add_le_add_left _ _ _ hb)

end YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor.sourceEnergy_taylor
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor.sourceEnergy_le_firstOrder_add_quadratic
