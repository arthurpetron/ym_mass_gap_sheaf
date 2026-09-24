/-
# Factor-one angular defect for the original full product heat

Diagonal positivity of the computed full-cycle Taylor remainder removes the
only signed loss in the unweighted product pairing.  The remaining Casimir
coefficient is identified with the sum of the original block angular energies
by the already-proved source cancellation at constant source.

This is a finite-cutoff estimate for the original product map.  It is not a
variance comparison, a changing-scale estimate, or a continuum statement.
-/

import YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder

namespace YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem neg_supported_local {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem zero_supported_local (n : Nat) :
    SupportedQuaternionBlocks n polyZero := by
  intro t ht
  contradiction

private theorem angularDerivative_zero_local (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans (RatPolyCoeffEqv.zero_smul _))

private theorem angularLaplacian_one_local :
    RatPolyCoeffEqv (angularLaplacian polyOne) polyZero := by
  have hs (i j : Nat) : RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j polyOne)) polyZero :=
    (angularDerivative_congr i j (angularDerivative_one i j)).trans
      (angularDerivative_zero_local i j)
  unfold angularLaplacian
  exact (hs 0 1).add ((hs 0 2).add ((hs 0 3).add
    ((hs 1 2).add ((hs 1 3).add (hs 2 3)))))

private theorem reindex_one_carrier {n : Nat}
    (s : QuaternionBlockInvolution n) :
    HaarCarrierEqv n (reindexQuaternionPolynomial s polyOne) polyOne :=
  carrierOfPrefix (reindex_supported s polyOne) (supported_one n)
    (by simpa [characterPolynomial] using
      reindexQuaternionPolynomial_character_prefix s polyZero 0)

private theorem cycleRotation_one_carrier (n : Nat) :
    HaarCarrierEqv n (cycleRotation n polyOne) polyOne := by
  unfold cycleRotation
  exact (reindex_carrier (reverseBlocks n) (reindex_supported _ polyOne)
    (supported_one n) (reindex_one_carrier (reverseTailBlocks n))).trans
      (reindex_one_carrier (reverseBlocks n))

private theorem casimirStep_one_carrier (tail : Nat) :
    HaarCarrierEqv (tail+1) (casimirStep tail polyOne) polyZero := by
  have hn : RatPolyCoeffEqv (polyNeg (angularLaplacian polyOne)) polyZero :=
    (RatPolyCoeffEqv.neg angularLaplacian_one_local).trans
      (RatPolyCoeffEqv.refl polyZero)
  simpa [casimirStep, cycleRotation] using cycleRotation_carrier (tail+1)
    (neg_supported_local (angularLaplacian_supported (by omega) (supported_one (tail+1))))
    (zero_supported_local (tail+1)) (RatPolyCoeffEqv.haarCarrier hn)

private theorem casimirSweep_one_carrier (tail : Nat) : ∀ m : Nat,
    HaarCarrierEqv (tail+1) (casimirSweep tail m polyOne) polyZero
  | 0 => HaarCarrierEqv.refl _ _
  | m+1 => by
      have hfirst := (rotateIterate_carrier (tail+1) m
        (casimirStep_supported tail (supported_one (tail+1))) (zero_supported_local (tail+1))
        (casimirStep_one_carrier tail)).trans (rotateIterate_zero (tail+1) m)
      have hsecond := (casimirSweep_carrier tail m
        (rotateIterate_supported (tail+1) 1 (supported_one (tail+1)))
        (supported_one (tail+1)) (cycleRotation_one_carrier (tail+1))).trans
          (casimirSweep_one_carrier tail m)
      exact (HaarCarrierEqv.add hfirst hsecond).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero polyZero))

private theorem pairCasimir_one (tail : Nat) (test : RatPoly) :
    pairCasimir tail polyOne test ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (pairCasimir_sweep tail polyOne test (supported_one (tail+1)))
    (Q'.eqv_trans _ _ _ (casimirSweep_one_carrier tail (tail+1) test)
      (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)))

private theorem pairCasimir_congr (tail : Nat) {p q test insertion : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hpq : RatPolyCoeffEqv p q) (hti : RatPolyCoeffEqv test insertion) :
    pairCasimir tail p test ≈ pairCasimir tail q insertion := by
  have hs := casimirSweep_carrier tail (tail+1) hp hq
    (RatPolyCoeffEqv.haarCarrier hpq)
  exact Q'.eqv_trans _ _ _ (pairCasimir_sweep tail p test hp)
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (hti.mul_right (casimirSweep tail (tail+1) p)))
      (Q'.eqv_trans _ _ _ (hs insertion)
        (Q'.eqv_symm (pairCasimir_sweep tail q insertion hq))))

/-- On the diagonal, the computed full-cycle Casimir coefficient is exactly
the sum of the original block angular energies. -/
theorem pairCasimir_diagonal_eq_angular (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairCasimir tail p p ≈ weightedAngularEnergy tail polyOne p := by
  have hs := sourceFirstOrder_eq_weightedAngularEnergy tail polyOne p
    (supported_one (tail+1)) hp
  have hone : RatPolyCoeffEqv (polyMul polyOne p) p := RatPolyCoeffEqv.one_mul p
  have hsq : RatPolyCoeffEqv
      (polyMul polyOne (polyMul p p)) (polyMul p p) := RatPolyCoeffEqv.one_mul _
  have hfirst : pairCasimir tail (polyMul polyOne p) (polyMul polyOne p) ≈
      pairCasimir tail p p := by
    exact pairCasimir_congr tail
      (supported_polyMul (supported_one (tail+1)) hp) hp
      hone hone
  have hzero : pairCasimir tail polyOne
      (polyMul polyOne (polyMul p p)) ≈ 0 := pairCasimir_one tail _
  have hsource : sourceFirstOrder tail polyOne p ≈ pairCasimir tail p p :=
    by
      unfold sourceFirstOrder
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hzero))
        (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
          (by decide) (fun _ => pairCasimir tail p p))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsource) hs

/-- The original full-product heat loses at most one copy of the complete
first-order angular energy.  The factor two from the earlier rotated-triangle
argument is absent. -/
theorem productMap_full_defect_le_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul p p) -
        H (tail+1) (polyMul p
          (productMap (tail+1) w K (List.range (tail+1)) p)) ≤
      ((1 : Q')-w) * weightedAngularEnergy tail polyOne p := by
  let N := H (tail+1) (polyMul p p)
  let P := H (tail+1) (polyMul p
    (productMap (tail+1) w K (List.range (tail+1)) p))
  let eps := (1 : Q')-w
  let C := pairCasimir tail p p
  let R := pairRemainder tail w K p p
  have ht : P ≈ N + -(eps*C) + R := productPair_taylor tail w K p p hp
  have hr : (0 : Q') ≤ R := pairRemainder_diagonal_nonnegative tail hw0 hw1 K hK p hp
  have he : N-P ≈ eps*C + -R :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ ht))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.add (.add (.var 0)
          (.neg (.mul (.var 1) (.var 2)))) (.var 3))))
        (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))) (by decide)
        (fun | 0 => N | 1 => eps | 2 => C | _ => R))
  have hnegzero : (-(0 : Q')) ≈ 0 := by decide
  have hneg : -R ≤ (0 : Q') := Q'.le_trans' _ _ _ (Q'.neg_le_neg hr)
    (Q'.le_of_eqv hnegzero)
  have hbound : eps*C + -R ≤ eps*C := Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ hneg) (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left _ _ _ (pairCasimir_diagonal_eq_angular tail p hp))))

end YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect.pairCasimir_diagonal_eq_angular
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect.productMap_full_defect_le_angular
