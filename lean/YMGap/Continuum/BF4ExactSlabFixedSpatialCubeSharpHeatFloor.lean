/-
# Sharp actual small-nome heat and six-face intervals

Keep the exact fundamental term and the constructed label-two tail.
At w=1/16 EVERY prefix K>=1 has heat remainder cap 1/1000. The
actual six-face action remainder has cap 1/128. The first bound constructs
the one-link floor used by certified-floor tensor contraction; the second
retains every shared face variable for normalized terminal estimates.

No pointwise-to-certificate inference, terminal estimate, interacting
spectral gap or changing-family conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
import YMGap.Continuum.SU2QuaternionProductHeatContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_coeff_nonneg)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval
  (heatTailInterval heatRemainderInterval cubeDifferenceInterval cubeRemainderInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
  (cubeFundamentalInterval cubeFundamentalRemainder cubeFundamentalDelta)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt scalarAt)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix heatRemainder heatPrefix_split)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState (coeffAt_heatKernelPacket)

local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks cubeWeight characterPolynomial

def heatDeviation : Q' := Q'.mkPos 1 1000 (by decide)
def actionDeviation : Q' := Q'.mkPos 1 128 (by decide)

private theorem remainder_telescope (p q : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg polyOne))
      (polyAdd (polyAdd p (polyNeg q)) (polyAdd q (polyNeg polyOne))) :=
  coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.const 1)))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.const 1))))
    (by decide) (fun | 0 => p | _ => q)

private theorem fundamental_remainder (x : RatPoly) :
    RatPolyCoeffEqv (polyAdd (heatPrefix smallNome 1 x) (polyNeg polyOne))
      (polySmul (coeffW smallNome 1) (characterPolynomial x 1)) := by
  have hr : RatPolyCoeffEqv (heatRemainder smallNome 1 x)
      (polySmul (coeffW smallNome 1) (characterPolynomial x 1)) := by
    unfold heatRemainder
    change RatPolyCoeffEqv (polyAdd
      (polySmul (coeffW smallNome 1) (characterPolynomial x 1)) polyZero) _
    exact RatPolyCoeffEqv.add_zero _
  exact (((heatPrefix_split smallNome 1 x).trans
    ((RatPolyCoeffEqv.refl polyOne).add hr)).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.const 1) (.var 0)) (.neg (.const 1))) (.var 0)
      (by decide) (fun _ => polySmul (coeffW smallNome 1) (characterPolynomial x 1)))

/-- Constructed endpoints, with no late-cutoff restriction beyond K>=1. -/
def sharpHeatRemainder {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) :
    Interval blocks (polyAdd (heatPrefix smallNome K x) (polyNeg polyOne)) heatDeviation := by
  let C := ((sharpCharacterInterval P 1).smul (coeffW smallNome 1)
    smallNome_coeff_nonneg).changeCap (Q'.mul_comm_eqv _ _)
  let F := Interval.ofCoeff (heatRemainderInterval P 1 (by decide)).support
    (fundamental_remainder x) C
  let T := heatTailInterval P K hK
  exact (Interval.ofCoeff (heatRemainderInterval P K hK).support
    (remainder_telescope (heatPrefix smallNome K x) (heatPrefix smallNome 1 x))
    (T.add F)).weaken (by decide)

/-- The ORIGINAL six shared action factors, not independent face copies. -/
def sharpCubeRemainder (K : Nat) (hK : 1 ≤ K) :
    Interval N (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) actionDeviation := by
  let D := cubeDifferenceInterval K hK
  let F := cubeFundamentalInterval smallNome smallNome_coeff_nonneg
  have hF : Interval N (polyAdd (cubeWeight smallNome 1) (polyNeg polyOne))
      (cubeFundamentalDelta smallNome) := F
  exact (Interval.ofCoeff (cubeRemainderInterval K hK).support
    (remainder_telescope (cubeWeight smallNome K) (cubeWeight smallNome 1))
    (D.add hF)).weaken (by decide)

private theorem constant_one : RatPolyCoeffEqv (cap (1 : Q')) polyOne :=
  RatPolyCoeffEqv.one_smul polyOne

private theorem floor_remainder (p : RatPoly) (d : Q') :
    RatPolyCoeffEqv (polyAdd p (polyNeg (cap (1-d))))
      (polyAdd (cap d) (polyAdd p (polyNeg polyOne))) := by
  have hconst : RatPolyCoeffEqv (cap (1-d)) (polyAdd polyOne (polyNeg (cap d))) :=
    ((cap_add 1 (-d)).symm.trans (constant_one.add (RatPolyCoeffEqv.refl _))).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 d) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv d)))) polyOne).trans
          ((RatPolyCoeffEqv.smul_assoc (-1) d polyOne).symm.trans
            ((cap_mul_left (-1) (cap d)).symm.trans
              (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0))
                (.neg (.var 0)) (by decide) (fun _ => cap d))))))
  exact ((RatPolyCoeffEqv.refl p).add (RatPolyCoeffEqv.neg hconst)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.add (.const 1) (.neg (.var 1)))))
      (.add (.var 1) (.add (.var 0) (.neg (.const 1))))
      (by decide) (fun | 0 => p | _ => cap d))

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ i, i ∈ xs → f i = g i) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | i::xs, h => by
      simp only [finitePolySum, h i List.mem_cons_self,
        sum_congr f g xs (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem heatAt_prefix (a b : Nat) (K : Nat) :
    heatAt a b smallNome K = heatPrefix smallNome K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply sum_congr
  intro spin hspin
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]

/-- Actual one-link input for the certified-floor centered contraction.
The floor is 999/1000 at EVERY finite K>=1, on the original doubled carrier. -/
def heatAtSharpFloor {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    (K : Nat) (hK : 1 ≤ K) :
    Certificate blocks (polyAdd (heatAt a b smallNome K) (polyNeg (cap (1-heatDeviation)))) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  let P := SquareBound.scalar ((Supported.coordinate ha).mul (Supported.coordinate hb).conj)
    (haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb)))
  rw [heatAt_prefix]
  exact .ofCoeff (floor_remainder (heatPrefix smallNome K (scalarAt a b)) heatDeviation)
    (sharpHeatRemainder P K hK).lower

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor.sharpHeatRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor.sharpCubeRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor.heatAtSharpFloor
