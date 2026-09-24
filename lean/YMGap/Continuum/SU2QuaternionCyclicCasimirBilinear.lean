/-
# Bilinearity and symmetry of the computed cyclic Casimir pairing

The computed degree-path pairing is identified with the full differential
sweep.  Cyclic integration by parts makes that sweep symmetric; ordinary
Haar linearity supplies the test-side algebra.  No joint spectral
orthogonality is introduced.
-/

import YMGap.Continuum.SU2QuaternionCyclicSourceCancellation

namespace YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicSourceCancellation
open YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sixValue_neg_local (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem angular_pair_ibp (tail : Nat) (p q : RatPoly) :
    angularPairValue (tail+1) p q ≈
      -(H (tail+1) (polyMul p (angularLaplacian q))) := by
  let second := fun i j => H (tail+1)
    (polyMul p (angularDerivative i j (angularDerivative i j q)))
  have hplane (i j : Nat) (hi : i < 4) (hj : j < 4) :
      H (tail+1) (polyMul (angularDerivative i j p) (angularDerivative i j q)) ≈
        -(second i j) := by
    have hz := quaternionHaar_weighted_angular tail hi hj p (angularDerivative i j q)
    have he : H (tail+1)
        (polyMul (angularDerivative i j p) (angularDerivative i j q)) + second i j ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _)) hz
    apply QPoly.q_eqv_of_sub_zero
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
        (.add (.var 0) (.var 1)) (by decide)
        (fun k => if k = 0 then H (tail+1)
          (polyMul (angularDerivative i j p) (angularDerivative i j q)) else second i j)) he
  exact Q'.eqv_trans _ _ _
    (sixValue_congr _ _ (fun i j hi hj => hplane i j hi hj))
    (Q'.eqv_trans _ _ _ (sixValue_neg_local second)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_six (tail+1) p _))))

private theorem angularPair_symm (blocks : Nat) (p q : RatPoly) :
    angularPairValue blocks p q ≈ angularPairValue blocks q p :=
  sixValue_congr _ _ (fun i j _ _ =>
    haar_of_coeff (RatPolyCoeffEqv.mul_comm
      (angularDerivative i j p) (angularDerivative i j q)))

private theorem haar_mul_neg (tail : Nat) (p q : RatPoly) :
    H (tail+1) (polyMul p (polyNeg q)) ≈
      -(H (tail+1) (polyMul p q)) := by
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (((QuaternionHaarAngularCarrier.neg_smul q).mul_left p).trans
      (RatPolyCoeffEqv.polyMul_smul_right (-1) p q)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-1) _)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide)
        (fun _ => H (tail+1) (polyMul p q))))

private theorem headCasimir_pair_symm (tail : Nat) (p q : RatPoly) :
    H (tail+1) (polyMul q (polyNeg (angularLaplacian p))) ≈
      H (tail+1) (polyMul p (polyNeg (angularLaplacian q))) := by
  have hp : H (tail+1) (polyMul q (polyNeg (angularLaplacian p))) ≈
      angularPairValue (tail+1) q p := by
    exact Q'.eqv_trans _ _ _ (haar_mul_neg tail q (angularLaplacian p))
      (Q'.eqv_symm (angular_pair_ibp tail q p))
  have hq : angularPairValue (tail+1) p q ≈
      H (tail+1) (polyMul p (polyNeg (angularLaplacian q))) := by
    exact Q'.eqv_trans _ _ _ (angular_pair_ibp tail p q)
      (Q'.eqv_symm (haar_mul_neg tail p (angularLaplacian q)))
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ (angularPair_symm (tail+1) q p) hq)

private theorem sweepPair_symm (tail : Nat) : ∀ m p q,
    SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) q →
    sweepPair tail m p q ≈ sweepPair tail m q p
  | 0, p, q, _, _ => Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right q))
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p)))
  | m+1, p, q, hp, hq => by
      have hs := sweepPair_succ tail m p q hp hq
      have ht := sweepPair_succ tail m q p hq hp
      exact Q'.eqv_trans _ _ _ hs
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (headCasimir_pair_symm tail p q)
            (sweepPair_symm tail m
              (cycleRotation (tail+1) p) (cycleRotation (tail+1) q)
              (rotateIterate_supported (tail+1) 1 hp)
              (rotateIterate_supported (tail+1) 1 hq)))
          (Q'.eqv_symm ht))

private theorem pairCasimir_eq_sweepPair (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    pairCasimir tail p q ≈ sweepPair tail (tail+1) p q := by
  have hs := pairCasimir_sweep tail p q hp
  have hc := rotateIterate_period_carrier (tail+1) q hq (casimirSweep tail (tail+1) p)
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- The computed full-cycle Casimir pairing is symmetric. -/
theorem pairCasimir_symm (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    pairCasimir tail p q ≈ pairCasimir tail q p :=
  Q'.eqv_trans _ _ _ (pairCasimir_eq_sweepPair tail p q hp hq)
    (Q'.eqv_trans _ _ _ (sweepPair_symm tail (tail+1) p q hp hq)
      (Q'.eqv_symm (pairCasimir_eq_sweepPair tail q p hq hp)))

private theorem mul_add_left_coeff (left right factor : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd left right) factor)
      (polyAdd (polyMul left factor) (polyMul right factor)) :=
  (RatPolyCoeffEqv.mul_comm _ _).trans
    ((RatPolyCoeffEqv.mul_add_right factor left right).trans
      ((RatPolyCoeffEqv.mul_comm factor left).add
        (RatPolyCoeffEqv.mul_comm factor right)))

/-- Additivity in the test polynomial. -/
theorem pairCasimir_add_right (tail : Nat) (p q r : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairCasimir tail p (polyAdd q r) ≈
      pairCasimir tail p q + pairCasimir tail p r := by
  exact Q'.eqv_trans _ _ _ (pairCasimir_sweep tail p (polyAdd q r) hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (mul_add_left_coeff q r _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (tail+1) _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_symm (pairCasimir_sweep tail p q hp))
          (Q'.eqv_symm (pairCasimir_sweep tail p r hp)))))

/-- Scalar linearity in the test polynomial. -/
theorem pairCasimir_smul_right (tail : Nat) (c : Q') (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairCasimir tail p (polySmul c q) ≈ c * pairCasimir tail p q := by
  have hs := pairCasimir_sweep tail p (polySmul c q) hp
  have hl : H (tail+1) (polyMul (polySmul c q) (casimirSweep tail (tail+1) p)) ≈
      c * H (tail+1) (polyMul q (casimirSweep tail (tail+1) p)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (tail+1) c (casimirSweep tail (tail+1) p) q)
        (Q'.mul_eqv_congr_left c _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ hl
      (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm (pairCasimir_sweep tail p q hp))))

/-- Coefficient equivalence in the test polynomial. -/
theorem pairCasimir_congr_right (tail : Nat) (p : RatPoly) {q r : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p) (hqr : RatPolyCoeffEqv q r) :
    pairCasimir tail p q ≈ pairCasimir tail p r := by
  exact Q'.eqv_trans _ _ _ (pairCasimir_sweep tail p q hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hqr.mul_right (casimirSweep tail (tail+1) p)))
      (Q'.eqv_symm (pairCasimir_sweep tail p r hp)))

end YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear

#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear.pairCasimir_symm
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear.pairCasimir_add_right
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear.pairCasimir_smul_right
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear.pairCasimir_congr_right
