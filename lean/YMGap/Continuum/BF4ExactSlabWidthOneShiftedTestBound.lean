/-
# A shrinking shifted-tester norm in the original width-one marginal

The full three-face fundamental moment and the unit-word certificate
4 - hex^2 give a bound for the actual odd marginal at terminal depth zero.
Every original action factor is retained. The auxiliary tester is not
gauge-invariant; this is not a physical excitation or a spectral-gap bound.
-/

import YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment
import YMGap.Continuum.QuaternionHaarFiniteSquareBudget

namespace YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq qpow)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry (baseLinks_length)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair marginalCertificate)
open YMGap.Continuum.BF4ExactSlabWidthOneSource (probe probe_supported probe_norm marginal_haar)
open YMGap.Continuum.BF4ExactSlabWidthOnePacketMoment (tester packet_moment insertion_supported)
open YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment (shiftedTester)
open YMGap.Continuum.SU2QuaternionCornerFundamentalMoment (hexQuaternion hex insertion)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarFiniteSquareBudget (squareHaar)

local notation "N" => List.length (baseLinks 1)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight marginalWeight

private theorem conj_unit {blocks : Nat} {p : PolyQuaternion}
    (hp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv blocks (polyQuaternionNorm (PolyQuaternion.conj p)) polyOne :=
  (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj p)).trans hp

private theorem hex_support : Supported N hexQuaternion := by
  rw [baseLinks_length]
  exact (((((Supported.coordinate (by decide : 3 < 24)).mul
    (Supported.coordinate (by decide : 2 < 24)).conj).mul
    (Supported.coordinate (by decide : 8 < 24))).mul
    (Supported.coordinate (by decide : 7 < 24)).conj).mul
    (Supported.coordinate (by decide : 5 < 24))).mul
    (Supported.coordinate (by decide : 6 < 24)).conj

private theorem hex_unit : HaarCarrierEqv N (polyQuaternionNorm hexQuaternion) polyOne := by
  rw [baseLinks_length]
  exact haarNorm_mul (haarNorm_mul (haarNorm_mul (haarNorm_mul (haarNorm_mul
    (haarNorm_coordinate (by decide : 3 < 24))
    (conj_unit (haarNorm_coordinate (by decide : 2 < 24))))
    (haarNorm_coordinate (by decide : 8 < 24)))
    (conj_unit (haarNorm_coordinate (by decide : 7 < 24))))
    (haarNorm_coordinate (by decide : 5 < 24)))
    (conj_unit (haarNorm_coordinate (by decide : 6 < 24)))

/-- Unit norm of the literal six-link word supplies the sharp square cap. -/
def hexSquareBound : SquareBound N hex 4 :=
  SquareBound.changeCap (by decide : ((2 : Q') * 2) * 1 ≈ 4)
    ((SquareBound.scalar hex_support hex_unit).smul 2)

private def probeSquareBound : SquareBound N probe 1 := by
  have hb : 4 < N := by rw [baseLinks_length]; decide
  exact SquareBound.scalar (Supported.coordinate hb) (haarNorm_coordinate hb)

/-- A nome-independent, unweighted cap for the subsequent approximation test. -/
def shiftedTesterSquareBound : SquareBound N shiftedTester 16 :=
  SquareBound.changeCap (by decide : sumBound (4 * 1) (((-2 : Q') * (-2)) * 1) ≈ 16)
    ((hexSquareBound.mul probeSquareBound).add (probeSquareBound.smul (-2)))

theorem shiftedTester_haar_square_le :
    quaternionHaar N (polyMul shiftedTester shiftedTester) ≤ 16 :=
  squareHaar shiftedTesterSquareBound

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Expand a small symbolic polynomial before inserting any physical weight. -/
private theorem shifted_square_comparison {blocks : Nat} {mu c p : RatPoly}
    (M : Certificate blocks mu) (C : SquareBound blocks c 4)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks (polyMul mu
      (polyMul (polyAdd (polyMul c p) (polySmul (-2) p))
        (polyAdd (polyMul c p) (polySmul (-2) p)))) ≤
      8 * quaternionHaar blocks (polyMul mu (polyMul p p)) +
        (-4) * quaternionHaar blocks (polyMul mu (polyMul c (polyMul p p))) := by
  let s := polyAdd (polyMul c p) (polySmul (-2) p)
  let sc := polyAdd (polyMul c p) (polyMul (cap (-2)) p)
  let u := polyMul mu (polyMul p p)
  let v := polyMul mu (polyMul c (polyMul p p))
  have hs : RatPolyCoeffEqv sc s := (RatPolyCoeffEqv.refl _).add (cap_mul_left (-2) p)
  have hn : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (cap 8) u) (polyMul (cap (-4)) v))
        (polyNeg (polyMul mu (polyMul sc sc))))
      (polyMul u (gap 4 c)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add
        (.mul (.const 8) (.mul (.var 0) (.mul (.var 2) (.var 2))))
        (.mul (.const (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))))
        (.neg (.mul (.var 0)
          (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.const (-2)) (.var 2)))
            (.add (.mul (.var 1) (.var 2)) (.mul (.const (-2)) (.var 2)))))))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
        (.add (.const 4) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => mu | 1 => c | _ => p)
  have he : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul 8 u) (polySmul (-4) v))
        (polyNeg (polyMul mu (polyMul s s))))
      (polyMul u (gap 4 c)) :=
    (((cap_mul_left 8 u).add (cap_mul_left (-4) v)).add
      (RatPolyCoeffEqv.neg ((hs.mul hs).mul_left mu))).symm.trans hn
  have hpositive := (Certificate.ofCoeff he
    ((M.mul (Certificate.square p hp)).mul C.certificate)).haar_nonnegative
  have hh : quaternionHaar blocks
      (polyAdd (polyAdd (polySmul 8 u) (polySmul (-4) v))
        (polyNeg (polyMul mu (polyMul s s)))) ≈
      (8 * quaternionHaar blocks u + (-4) * quaternionHaar blocks v) +
        -(quaternionHaar blocks (polyMul mu (polyMul s s))) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (quaternionHaar_polySmul blocks _ _)
            (quaternionHaar_polySmul blocks _ _)))
        (haar_neg blocks _))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpositive (Q'.le_of_eqv hh))

private theorem marginal_insertion (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar N (polyMul (marginalWeight w K 1 0) insertion) ≈
      Q'.mkPos 1 2 (by decide) * qpow w 9 := by
  have hi : SupportedQuaternionBlocks N insertion := by
    rw [baseLinks_length]
    exact insertion_supported
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (marginal_haar w K insertion hi)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (by rw [baseLinks_length]; exact packet_moment w K hK)))

private theorem scalar_pin (r : Q') :
    (8 : Q') * Q'.mkPos 1 4 (by decide) +
      (-4) * (Q'.mkPos 1 2 (by decide) * r) ≈ 2 * (1 + -r) := by
  have he : (-4 : Q') * (Q'.mkPos 1 2 (by decide) * r) ≈ (-2) * r :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _
        (by decide : (-4 : Q') * Q'.mkPos 1 2 (by decide) ≈ -2))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (by decide : (8 : Q') * Q'.mkPos 1 4 (by decide) ≈ 2) he)
    (poly_identity_of_normal_eq
      (.add (.const 2) (.mul (.const (-2)) (.var 0)))
      (.mul (.const 2) (.add (.const 1) (.neg (.var 0)))) (by decide) (fun _ => r))

/-- The unchanged original marginal has a shrinking shifted-tester norm.
The cutoff must both satisfy original positivity and contain spin one. -/
theorem shiftedTester_marginal_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) :
    marginalPair w K 1 0 shiftedTester shiftedTester ≤ 2 * (1 + -(qpow w 9)) := by
  have hb := shifted_square_comparison
    (marginalCertificate hw0 hw1 K 1 hK 0) hexSquareBound probe_supported
  have he :
      8 * quaternionHaar N (polyMul (marginalWeight w K 1 0) (polyMul probe probe)) +
        (-4) * quaternionHaar N
          (polyMul (marginalWeight w K 1 0) (polyMul hex (polyMul probe probe))) ≈
      2 * (1 + -(qpow w 9)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (probe_norm w K))
        (Q'.mul_eqv_congr_left _ _ _ (marginal_insertion w K hK1)))
      (scalar_pin (qpow w 9))
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv he)

end YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound

#print axioms YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound.hexSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound.shiftedTesterSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound.shiftedTester_haar_square_le
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound.shiftedTester_marginal_square_le
