/-
# A positive pairing of the actual finite fringe seed

The original width-one, depth-zero seed at coordinate two approximates its
actual conditional-Haar source piece. A computed finite degree makes its
pairing with the shifted hexagon tester at least w^9/4. Weighted
Cauchy--Schwarz then gives a lower bound for its original marginal norm.
The approximation degree retains the original finite regulator dependence.
The probe and tester are auxiliary polynomials, not gauge-invariant states;
no physical excitation, uniform coupling bound, or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment
import YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry (baseLinks_length)
open YMGap.Continuum.BF4ExactSlabWidthOneSource (probe probe_supported)
open YMGap.Continuum.BF4ExactSlabWidthOneFringeMoment
  (shiftedTester shiftedTester_supported shifted_source_pair)
open YMGap.Continuum.BF4ExactSlabWidthOneShiftedTestBound
  (shiftedTester_haar_square_le shiftedTester_marginal_square_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
  (test test_supported defect defect_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
  (piece piece_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation
  (pieceApproximationCutoff piece_defect_haar_square_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation "N" => List.length (baseLinks 1)
attribute [local irreducible] baseLinks marginalWeight

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem defect_pair_pin (blocks : Nat) (nu q tau r : RatPoly) :
    quaternionHaar blocks (polyMul (polyAdd (polyMul nu q) (polyNeg tau)) r) ≈
      quaternionHaar blocks (polyMul nu (polyMul q r)) +
        -(quaternionHaar blocks (polyMul tau r)) := by
  have hp : RatPolyCoeffEqv
      (polyMul (polyAdd (polyMul nu q) (polyNeg tau)) r)
      (polyAdd (polyMul nu (polyMul q r)) (polyNeg (polyMul tau r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))) (.var 3))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.neg (.mul (.var 2) (.var 3))))
      (by decide) (fun | 0 => nu | 1 => q | 2 => tau | _ => r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks _)))

private theorem haar_cauchySchwarz {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul p q) * quaternionHaar blocks (polyMul p q) ≤
      quaternionHaar blocks (polyMul p p) * quaternionHaar blocks (polyMul q q) := by
  have pin (u v : RatPoly) : weightedPair blocks polyOne u v ≈
      quaternionHaar blocks (polyMul u v) := haar_of_coeff (RatPolyCoeffEqv.mul_one _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (mul_congr (pin p q) (pin p q))))
    (Q'.le_trans' _ _ _ (weighted_cauchySchwarz blocks polyOne p q (.one blocks) hp hq)
      (Q'.le_of_eqv (mul_congr (pin p p) (pin q q))))

private theorem square_quarter (w : Q') :
    (Q'.mkPos 1 4 (by decide)*qpow w 9) * (Q'.mkPos 1 4 (by decide)*qpow w 9) ≈
      Q'.mkPos 1 16 (by decide)*qpow w 18 := by
  have h : (Q'.mkPos 1 4 (by decide)*qpow w 9) * (Q'.mkPos 1 4 (by decide)*qpow w 9) ≈
      (Q'.mkPos 1 4 (by decide)*Q'.mkPos 1 4 (by decide))*qpow w 18 :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 1) (.pow (.var 0) 9)) (.mul (.var 1) (.pow (.var 0) 9)))
      (.mul (.mul (.var 1) (.var 1)) (.pow (.var 0) 18))
      (by decide) (fun | 0 => w | _ => Q'.mkPos 1 4 (by decide))
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _ (by decide))

private theorem half_quarters (w : Q') : Q'.mkPos 1 2 (by decide)*qpow w 9 ≈
    Q'.mkPos 1 4 (by decide)*qpow w 9 + Q'.mkPos 1 4 (by decide)*qpow w 9 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (by decide : Q'.mkPos 1 2 (by decide) ≈ Q'.mkPos 1 4 (by decide)+Q'.mkPos 1 4 (by decide)))
    (poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 0)) (.var 1))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => Q'.mkPos 1 4 (by decide) | _ => qpow w 9))

private theorem lower_of_error {c d a : Q'} (ha : (0 : Q') < a)
    (hd : d ≈ c + -(a+a)) (hs : d*d ≤ a*a) : a ≤ c := by
  have hn := (Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq ha hs)).2
  have hlo : -a ≤ d := Q'.le_trans' _ _ _ (Q'.neg_le_neg hn)
    (Q'.le_of_eqv (Q'.neg_neg_eqv d))
  have hleft : -a+(a+a) ≈ a :=
    poly_identity_of_normal_eq (.add (.neg (.var 0)) (.add (.var 0) (.var 0))) (.var 0)
      (by decide) (fun _ => a)
  have hright : d+(a+a) ≈ c := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hd (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => c | _ => a+a))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (a+a) hlo) (Q'.le_of_eqv hright))

/-- Tolerance for the ordinary-Haar square of the actual seed defect. -/
def pairingTolerance (w : Q') : Q' := Q'.mkPos 1 256 (by decide)*qpow w 18

theorem pairingTolerance_positive {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < pairingTolerance w :=
  Q'.mul_pos (by decide) (qpow_positive hw 18)

private theorem tolerance_square (w : Q') : pairingTolerance w * 16 ≈
    (Q'.mkPos 1 4 (by decide)*qpow w 9)*(Q'.mkPos 1 4 (by decide)*qpow w 9) := by
  have h : pairingTolerance w*16 ≈
      (Q'.mkPos 1 256 (by decide)*16)*qpow w 18 :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.const 16))
      (.mul (.mul (.var 0) (.const 16)) (.var 1))
      (by decide) (fun | 0 => Q'.mkPos 1 256 (by decide) | _ => qpow w 18)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : Q'.mkPos 1 256 (by decide)*16 ≈ Q'.mkPos 1 16 (by decide)))
      (Q'.eqv_symm (square_quarter w)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K : Nat) (hK : headCutoff w ≤ K)

/-- The literal finite-degree seed, on the original width-one odd marginal. -/
def fringeTest (k : Nat) : RatPoly :=
  test hw0 hw1 K 1 hK 0 2 k (piece w K 1 0 2 probe)

theorem fringeTest_supported (k : Nat) : SupportedQuaternionBlocks N (fringeTest hw0 hw1 K hK k) :=
  test_supported hw0 hw1 K 1 hK 0 2 k (piece_supported w K 1 0 2 probe_supported)

/-- Explicit degree; every later finite seed satisfies the lower pairing bound. -/
def pairingDegree : Nat :=
  pieceApproximationCutoff hw0 hw1 K 1 hK 0 2 probe (pairingTolerance w)

theorem fringeTest_pairing_lower (hspin : 1 ≤ K) (k : Nat)
    (hk : pairingDegree hw0 hw1 K hK ≤ k) :
    Q'.mkPos 1 4 (by decide)*qpow w 9 ≤
      marginalPair w K 1 0 (fringeTest hw0 hw1 K hK k) shiftedTester := by
  let D := defect hw0 hw1 K 1 hK 0 2 k (piece w K 1 0 2 probe)
  let d := quaternionHaar N (polyMul D shiftedTester)
  have hD : SupportedQuaternionBlocks N D :=
    defect_supported hw0 hw1 K 1 hK 0 2 k (piece_supported w K 1 0 2 probe_supported)
  have he := piece_defect_haar_square_le hw0 hw1 K 1 hK 0 2
    (by rw [baseLinks_length]; decide) probe_supported (pairingTolerance w)
    (pairingTolerance_positive hw0) k hk
  have hcs : d*d ≤ quaternionHaar N (polyMul D D)*
      quaternionHaar N (polyMul shiftedTester shiftedTester) :=
    haar_cauchySchwarz hD shiftedTester_supported
  have hs : d*d ≤ (Q'.mkPos 1 4 (by decide)*qpow w 9)*
      (Q'.mkPos 1 4 (by decide)*qpow w 9) :=
    Q'.le_trans' _ _ _ hcs
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ he
          (Certificate.square shiftedTester shiftedTester_supported).haar_nonnegative)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ shiftedTester_haar_square_le
            (Q'.le_of_lt (pairingTolerance_positive hw0)))
          (Q'.le_of_eqv (tolerance_square w))))
  have hd : d ≈ marginalPair w K 1 0 (fringeTest hw0 hw1 K hK k) shiftedTester +
      -(Q'.mkPos 1 4 (by decide)*qpow w 9+Q'.mkPos 1 4 (by decide)*qpow w 9) :=
    Q'.eqv_trans _ _ _ (defect_pair_pin N (marginalWeight w K 1 0)
      (fringeTest hw0 hw1 K hK k) (piece w K 1 0 2 probe) shiftedTester)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (shifted_source_pair w K hspin) (half_quarters w))))
  exact lower_of_error (Q'.mul_pos (by decide) (qpow_positive hw0 9)) hd hs

theorem fringeTest_norm_product_lower (hspin : 1 ≤ K) (k : Nat)
    (hk : pairingDegree hw0 hw1 K hK ≤ k) :
    Q'.mkPos 1 16 (by decide)*qpow w 18 ≤
      marginalPair w K 1 0 (fringeTest hw0 hw1 K hK k) (fringeTest hw0 hw1 K hK k) *
        (2*(1 + -(qpow w 9))) := by
  let q := fringeTest hw0 hw1 K hK k
  have hq := fringeTest_supported hw0 hw1 K hK k
  have pin (u v : RatPoly) : weightedPair N (marginalWeight w K 1 0) u v ≈
      marginalPair w K 1 0 u v := haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hcs : marginalPair w K 1 0 q shiftedTester * marginalPair w K 1 0 q shiftedTester ≤
      marginalPair w K 1 0 q q * marginalPair w K 1 0 shiftedTester shiftedTester :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (mul_congr (pin q shiftedTester) (pin q shiftedTester)))
      (Q'.le_trans' _ _ _
        (weighted_cauchySchwarz N (marginalWeight w K 1 0) q shiftedTester
          (marginalCertificate hw0 hw1 K 1 hK 0) hq shiftedTester_supported)
        (Q'.le_of_eqv (mul_congr (pin q q) (pin shiftedTester shiftedTester))))
  have hl := fringeTest_pairing_lower hw0 hw1 K hK hspin k hk
  have ha : (0 : Q') ≤ Q'.mkPos 1 4 (by decide)*qpow w 9 :=
    Q'.le_of_lt (Q'.mul_pos (by decide) (qpow_positive hw0 9))
  have hn : (0 : Q') ≤ marginalPair w K 1 0 q q :=
    ((marginalCertificate hw0 hw1 K 1 hK 0).mul (Certificate.square q hq)).haar_nonnegative
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (square_quarter w))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hl ha)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hl (Q'.le_trans' _ _ _ ha hl))
        (Q'.le_trans' _ _ _ hcs
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (shiftedTester_marginal_square_le hw0 hw1 K hK hspin) hn))))

end YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing

#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.pairingTolerance
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.pairingTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.fringeTest
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.fringeTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.pairingDegree
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.fringeTest_pairing_lower
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.fringeTest_norm_product_lower
