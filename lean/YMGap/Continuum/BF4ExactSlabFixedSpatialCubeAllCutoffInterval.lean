/-
# Uniform finite-cutoff intervals for the ORIGINAL small-nome cube action

Keep the six shared original face variables. Splitting each heat prefix after
label one leaves a constructed tail interval beginning at label two. At the
fixed nome 1/16 this tail is at most 2^-20, at EVERY finite cutoff K>=1.
The actual cube action differs from its cutoff-one action by at most 2^-17.
These are Haar certificates, not pointwise-to-certificate assertions.

The constants are independent of K, not of coupling or width. No terminal
depth, completed-state, scaling-family or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.PolynomialWeightedSumBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (cubeFaces cubeWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos smallNome_coeff_nonneg baseCap deltaCap)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.PolynomialProductRemainder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix heatRemainder heatPrefix_split)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)

local infix:50 " ≈ " => Q'.eqv
local notation "N" => List.length (baseLinks 2)
attribute [local irreducible] baseLinks plaquette cubeWeight characterPolynomial

def faceTailCap : Q' := Q'.mkPos 1 1048576 (by decide)
def actionDifferenceCap : Q' := Q'.mkPos 1 131072 (by decide)

private def term (x : RatPoly) (j : Nat) : RatPoly :=
  polySmul (coeffW smallNome j) (characterPolynomial x j)

private def termInterval {blocks : Nat} {x : RatPoly}
    (P : SquareBound blocks x 1) (j : Nat) :
    Interval blocks (term x j) (heatTermBound smallNome j) :=
  (characterInterval P j).smul (coeffW smallNome j)
    (coeffW_nonneg (Q'.le_of_lt smallNome_pos) j)

private theorem tail_geometric (j : Nat) :
    heatTermBound smallNome (2+j) ≤ heatTermBound smallNome 2 * HalfPow.half^j := by
  apply CharacterTail.geom_dom (fun i => heatTermBound smallNome (2+i)) _ _
    HalfPow.half_nonneg (Q'.le_refl' _)
  intro i
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _
    (heatTermBound_step (Q'.le_of_lt smallNome_pos) (by decide) _)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (by decide : heatRatio smallNome ≤ HalfPow.half)
      (heatTermBound_nonnegative (Q'.le_of_lt smallNome_pos) _))

private theorem tail_sum_le (count : Nat) :
    finSum (fun j => heatTermBound smallNome (2+j)) count ≤ faceTailCap := by
  have hterm := ExpNeg.finSum_le_finSum_of_termwise _ _ tail_geometric count
  have hgeo : finSum (fun j => heatTermBound smallNome 2 * HalfPow.half^j) count ≤
      geoTailBase (heatTermBound smallNome 2) HalfPow.half 0 := by
    simpa only [geoIncrBase, Nat.zero_add] using
      (geoTailBase_series_le (heatTermBound_nonnegative (Q'.le_of_lt smallNome_pos) 2)
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0 count)
  exact Q'.le_trans' _ _ _ hterm (Q'.le_trans' _ _ _ hgeo (by decide))

private def tailPolynomial (x : RatPoly) (count : Nat) : RatPoly :=
  finitePolySum (fun j => term x (2+j)) (List.range count)

private def tailInterval {blocks : Nat} {x : RatPoly}
    (P : SquareBound blocks x 1) (count : Nat) :
    Interval blocks (tailPolynomial x count) faceTailCap :=
  (Interval.finiteRange (fun j => term x (2+j))
    (fun j => heatTermBound smallNome (2+j)) (fun j => termInterval P (2+j)) count).weaken
      (tail_sum_le count)

private theorem split_two (x : RatPoly) (K : Nat) (hK : 1 ≤ K) :
    heatPrefix smallNome K x =
      polyAdd (heatPrefix smallNome 1 x) (tailPolynomial x (K-1)) := by
  unfold heatPrefix tailPolynomial term
  rw [show K+1 = 2+(K-1) by omega,
    PolynomialWeightedSumBounds.sum_range_add]

private def prefixSupported {blocks : Nat} {x : RatPoly}
    (P : SquareBound blocks x 1) (K : Nat) :
    SupportedQuaternionBlocks blocks (heatPrefix smallNome K x) :=
  (Interval.finiteRange (term x) (heatTermBound smallNome) (termInterval P) (K+1)).support

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Original heat-prefix tail with BOTH endpoint certificates, for arbitrary
supported Haar-unit scalars. The coupling is the witnessed fixed small nome. -/
def heatTailInterval {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) :
    Interval blocks (polyAdd (heatPrefix smallNome K x)
      (polyNeg (heatPrefix smallNome 1 x))) faceTailCap := by
  have hp := supported_add (prefixSupported P K) (neg_supported (prefixSupported P 1))
  have he : RatPolyCoeffEqv
      (polyAdd (heatPrefix smallNome K x) (polyNeg (heatPrefix smallNome 1 x)))
      (tailPolynomial x (K-1)) := by
    rw [split_two x K hK]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => heatPrefix smallNome 1 x | _ => tailPolynomial x (K-1))
  exact Interval.ofCoeff hp he (tailInterval P (K-1))

private theorem first_split (x : RatPoly) :
    RatPolyCoeffEqv (heatPrefix smallNome 1 x) (polyAdd polyOne (term x 1)) := by
  have hr : RatPolyCoeffEqv (heatRemainder smallNome 1 x) (term x 1) := by
    unfold heatRemainder term
    change RatPolyCoeffEqv (polyAdd
      (polySmul (coeffW smallNome 1) (characterPolynomial x 1)) polyZero)
      (polySmul (coeffW smallNome 1) (characterPolynomial x 1))
    exact RatPolyCoeffEqv.add_zero _
  exact (heatPrefix_split smallNome 1 x).trans ((RatPolyCoeffEqv.refl _).add hr)

/-- Cutoff-independent original heat remainder; the low character is sharp
and ONLY labels >=2 pay the coarse geometric envelope. -/
def heatRemainderInterval {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) :
    Interval blocks (polyAdd (heatPrefix smallNome K x) (polyNeg polyOne)) (baseCap-1) := by
  let F : Interval blocks (term x 1) (2*coeffW smallNome 1) :=
    ((sharpCharacterInterval P 1).smul (coeffW smallNome 1) smallNome_coeff_nonneg).changeCap
      (Q'.mul_comm_eqv _ _)
  let T := tailInterval P (K-1)
  have hs := supported_add (prefixSupported P K) (neg_supported (supported_one blocks))
  have he : RatPolyCoeffEqv (polyAdd (heatPrefix smallNome K x) (polyNeg polyOne))
      (polyAdd (term x 1) (tailPolynomial x (K-1))) := by
    rw [split_two x K hK]
    exact (((first_split x).add (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.add (.const 1) (.var 0)) (.var 1)) (.neg (.const 1)))
        (.add (.var 0) (.var 1)) (by decide)
        (fun | 0 => term x 1 | _ => tailPolynomial x (K-1)))
  exact (Interval.ofCoeff hs he (F.add T)).weaken (by decide)

def heatInterval {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) : Interval blocks (heatPrefix smallNome K x) baseCap := by
  let R := heatRemainderInterval P K hK
  have he : RatPolyCoeffEqv (heatPrefix smallNome K x)
      (polyAdd polyOne (polyAdd (heatPrefix smallNome K x) (polyNeg polyOne))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.const 1) (.add (.var 0) (.neg (.const 1))))
      (by decide) (fun _ => heatPrefix smallNome K x)
  exact (Interval.ofCoeff (prefixSupported P K) he ((Interval.one blocks).add R)).changeCap
    (by decide)

private def faceSquare (face : Z4Plaq) : SquareBound N (plaquette 2 face).scalar 1 :=
  .scalar (plaquette_supported 2 N (Nat.le_refl _) face)
    (plaquette_unit 2 N (Nat.le_refl _) face)

def cubeInterval (K : Nat) (hK : 1 ≤ K) : Interval N (cubeWeight smallNome K) (baseCap^6) := by
  unfold cubeWeight
  exact Interval.productUniform _ baseCap cubeFaces (fun face _ => heatInterval (faceSquare face) K hK)

private theorem add_difference (p q : RatPoly) :
    RatPolyCoeffEqv q (polyAdd p (polyAdd q (polyNeg p))) :=
  coeffEvalExpr_eqv_of_normalize_eq (.var 1)
    (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (by decide)
    (fun | 0 => p | _ => q)

private theorem one_product : ∀ fs : List Z4Plaq,
    RatPolyCoeffEqv (polynomialProduct (fun _ => polyOne) fs) polyOne
  | [] => .refl _
  | _::fs => ((one_product fs).mul_left polyOne).trans (RatPolyCoeffEqv.one_mul polyOne)

private def uniformRemainder (K : Nat) (hK : 1 ≤ K) :
    (fs : List Z4Plaq) → Interval N
      (productRemainder (fun _ => polyOne)
        (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
        (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar) (polyNeg polyOne)) fs)
      (baseCap^fs.length-1)
  | [] => (Interval.zero N).changeCap (by decide)
  | face::fs => by
      have he : 1*(baseCap^fs.length-1)+(baseCap-1)*baseCap^fs.length ≈
          baseCap^(fs.length+1)-1 := by
        rw [Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.add (.mul (.const 1) (.add (.var 1) (.neg (.const 1))))
            (.mul (.add (.var 0) (.neg (.const 1))) (.var 1)))
          (.add (.mul (.var 0) (.var 1)) (.neg (.const 1))) (by decide)
          (fun | 0 => baseCap | _ => baseCap^fs.length)
      exact (((Interval.one N).mul (uniformRemainder K hK fs)).add
        ((heatRemainderInterval (faceSquare face) K hK).mul
          (Interval.productUniform _ baseCap fs
            (fun face _ => heatInterval (faceSquare face) K hK)))).changeCap he

/-- Actual six-face action remains close to one at every cutoff. -/
def cubeRemainderInterval (K : Nat) (hK : 1 ≤ K) :
    Interval N (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) deltaCap := by
  let r := productRemainder (fun _ => polyOne)
    (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
    (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar) (polyNeg polyOne)) cubeFaces
  have he := polynomialProduct_remainder (fun _ : Z4Plaq => polyOne)
    (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
    (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar) (polyNeg polyOne))
    (fun face => add_difference _ _) cubeFaces
  have hv : RatPolyCoeffEqv (cubeWeight smallNome K) (polyAdd polyOne r) := by
    unfold cubeWeight
    exact he.trans ((one_product cubeFaces).add (.refl r))
  have hp : RatPolyCoeffEqv (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) r :=
    (hv.add (.refl (polyNeg polyOne))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.const 1) (.var 0)) (.neg (.const 1))) (.var 0)
        (by decide) (fun _ => r))
  exact (Interval.ofCoeff
    (supported_add (cubeInterval K hK).support (neg_supported (supported_one N))) hp
    (uniformRemainder K hK cubeFaces)).weaken (by decide)

private def differenceCap : Nat → Q'
  | 0 => 0
  | n+1 => baseCap*differenceCap n+faceTailCap*baseCap^n

private def uniformDifference (K : Nat) (hK : 1 ≤ K) :
    (fs : List Z4Plaq) → Interval N
      (productRemainder
        (fun face => heatPrefix smallNome 1 (plaquette 2 face).scalar)
        (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
        (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar)
          (polyNeg (heatPrefix smallNome 1 (plaquette 2 face).scalar))) fs)
      (differenceCap fs.length)
  | [] => Interval.zero N
  | face::fs => ((heatInterval (faceSquare face) 1 (by decide)).mul (uniformDifference K hK fs)).add
      ((heatTailInterval (faceSquare face) K hK).mul
        (Interval.productUniform _ baseCap fs
          (fun face _ => heatInterval (faceSquare face) K hK)))

/-- The tested source difference is small uniformly over ALL finite cutoffs;
the subsequent face test will retain its exact kinetic factor w^12. -/
def cubeDifferenceInterval (K : Nat) (hK : 1 ≤ K) :
    Interval N (polyAdd (cubeWeight smallNome K) (polyNeg (cubeWeight smallNome 1)))
      actionDifferenceCap := by
  let r := productRemainder
    (fun face => heatPrefix smallNome 1 (plaquette 2 face).scalar)
    (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
    (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar)
      (polyNeg (heatPrefix smallNome 1 (plaquette 2 face).scalar))) cubeFaces
  have he := polynomialProduct_remainder
    (fun face => heatPrefix smallNome 1 (plaquette 2 face).scalar)
    (fun face => heatPrefix smallNome K (plaquette 2 face).scalar)
    (fun face => polyAdd (heatPrefix smallNome K (plaquette 2 face).scalar)
      (polyNeg (heatPrefix smallNome 1 (plaquette 2 face).scalar)))
    (fun face => add_difference _ _) cubeFaces
  have hv : RatPolyCoeffEqv (cubeWeight smallNome K) (polyAdd (cubeWeight smallNome 1) r) := by
    unfold cubeWeight
    exact he
  have hp : RatPolyCoeffEqv
      (polyAdd (cubeWeight smallNome K) (polyNeg (cubeWeight smallNome 1))) r :=
    (hv.add (.refl (polyNeg (cubeWeight smallNome 1)))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun | 0 => cubeWeight smallNome 1 | _ => r))
  exact (Interval.ofCoeff
    (supported_add (cubeInterval K hK).support (neg_supported (cubeInterval 1 (by decide)).support))
    hp (uniformDifference K hK cubeFaces)).weaken (by decide)

/-- A constructed half-floor for the SAME original cube action. -/
def cubeHalfCertificate (K : Nat) (hK : 1 ≤ K) :
    Certificate N (polyAdd (cubeWeight smallNome K) (polyNeg (cap HalfPow.half))) := by
  let R := (cubeRemainderInterval K hK).weaken (by decide : deltaCap ≤ HalfPow.half)
  have he : RatPolyCoeffEqv
      (polyAdd (cap HalfPow.half) (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)))
      (polyAdd (cubeWeight smallNome K) (polyNeg (cap HalfPow.half))) := by
    have hc : RatPolyCoeffEqv polyOne (polyAdd (cap HalfPow.half) (cap HalfPow.half)) :=
      ((cap_add _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half+HalfPow.half ≈ 1) polyOne).trans
          (RatPolyCoeffEqv.one_smul polyOne))).symm
    exact ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 1) (.add (.var 0) (.neg (.add (.var 1) (.var 1)))))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => cubeWeight smallNome K | _ => cap HalfPow.half))
  exact .ofCoeff he.symm R.lower

def cubeCertificate (K : Nat) (hK : 1 ≤ K) : Certificate N (cubeWeight smallNome K) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => cubeWeight smallNome K | _ => cap HalfPow.half))
    ((cubeHalfCertificate K hK).add (.constant N HalfPow.half HalfPow.half_nonneg))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.heatTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.heatRemainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.cubeRemainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.cubeDifferenceInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.cubeHalfCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval.cubeCertificate
