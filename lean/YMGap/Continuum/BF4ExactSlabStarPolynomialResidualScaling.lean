/-
# Rational scaling of the original conditional residual test

This module stays on the original full-action polynomial carrier.  It records
only the homogeneous scaling needed to vary the dual test; it introduces no
normalizer cap, exterior multiplier, or coercivity premise.
-/

import YMGap.Continuum.BF4ExactSlabStarPolynomialResidual

namespace YMGap.Continuum.BF4ExactSlabStarPolynomialResidualScaling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property

private theorem insertedNormalizer_smul (a : Q') (p : (F).V) :
    RatPolyCoeffEqv
      (insertedNormalizer w K extent i.val i.property (polySmul a p.val))
      (polySmul a (insertedNormalizer w K extent i.val i.property p.val)) := by
  unfold insertedNormalizer
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul,
    reindexQuaternionPolynomial_smul]
  exact (partialHaarHead_congr
      (RatPolyCoeffEqv.polyMul_smul_left a
        (reindexQuaternionPolynomial (linkHeadSwap extent i.val i.property) p.val)
        (reindexQuaternionPolynomial (linkHeadSwap extent i.val i.property)
          (incidentHeat w K extent i.val)))).trans
    (partialHaarHead_smul a
      (polyMul
        (reindexQuaternionPolynomial (linkHeadSwap extent i.val i.property) p.val)
        (reindexQuaternionPolynomial (linkHeadSwap extent i.val i.property)
          (incidentHeat w K extent i.val))))

private theorem headProbe_congr {q r : RatPoly}
    (h : RatPolyCoeffEqv q r) :
    RatPolyCoeffEqv
      (headProbe (linkHeadSwap extent i.val i.property) q)
      (headProbe (linkHeadSwap extent i.val i.property) r) := by
  simpa [headProbe] using
    (RatPolyCoeffEqv.reindex (linkHeadSwap extent i.val i.property)
      (lift_coeff 1 h))

private theorem headProbe_smul (a : Q') (q : RatPoly) :
    headProbe (linkHeadSwap extent i.val i.property) (polySmul a q) =
      polySmul a (headProbe (linkHeadSwap extent i.val i.property) q) := by
  unfold headProbe
  simp [liftHead, reindexQuaternionPolynomial, polySmul,
    List.map_map, Function.comp_def]

private theorem smul_neg_coeff (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) (polySmul a p))
      (polySmul a (polySmul (-1) p)) := by
  exact (RatPolyCoeffEqv.smul_assoc (-1) a p).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) a) p).trans
      (RatPolyCoeffEqv.smul_assoc a (-1) p).symm)

set_option maxHeartbeats 2000000 in
theorem polynomialResidual_smul (a : Q') (p : (F).V) :
    (F).veq
      (polynomialResidual hw0 hw1 K extent hK i
        ((F).smul a p))
      ((F).smul a (polynomialResidual hw0 hw1 K extent hK i p)) := by
  let d : (G).V :=
    ⟨normalizer w K extent i.val i.property,
      normalizer_supported w K extent i.val i.property⟩
  let ps : (F).V := (F).smul a p
  have hn : RatPolyCoeffEqv (N ps).val (polySmul a (N p).val) :=
    insertedNormalizer_smul hw0 hw1 K extent hK i a p
  have hj : RatPolyCoeffEqv (J (N ps)).val
      (polySmul a (J (N p)).val) := by
    have hj0 := headProbe_congr (extent := extent) (i := i) hn
    rw [headProbe_smul (extent := extent) (i := i) a (N p).val] at hj0
    exact hj0
  change RatPolyCoeffEqv
    (polyAdd (polyMul (J d).val (polySmul a p.val))
      (polySmul (-1) (J (N ps)).val))
    (polySmul a
      (polyAdd (polyMul (J d).val p.val)
        (polySmul (-1) (J (N p)).val)))
  exact (RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.polyMul_smul_right a (J d).val p.val)
      ((RatPolyCoeffEqv.smul (-1) hj).trans
        (smul_neg_coeff a (J (N p)).val))).trans
    (RatPolyCoeffEqv.smul_add a
      (polyMul (J d).val p.val) (polySmul (-1) (J (N p)).val)).symm

theorem dualValue_smul (a : Q') (p f : (F).V) :
    dualValue hw0 hw1 K extent hK i
      ((F).smul a p) f ≈
      (a * (F).B f (polynomialResidual hw0 hw1 K extent hK i p) +
        a * (F).B f (polynomialResidual hw0 hw1 K extent hK i p)) -
        (a * a) * (F).B (polynomialResidual hw0 hw1 K extent hK i p)
          (polynomialResidual hw0 hw1 K extent hK i p) := by
  unfold dualValue
  have ht := polynomialResidual_smul hw0 hw1 K extent hK i a p
  have hpair : (F).B f
      (polynomialResidual hw0 hw1 K extent hK i
        ((F).smul a p)) ≈
      a * (F).B f (polynomialResidual hw0 hw1 K extent hK i p) :=
    Q'.eqv_trans _ _ _ ((F).B_congr_right f ht)
      ((F).B_smul_right a f (polynomialResidual hw0 hw1 K extent hK i p))
  have hself : (F).B
      (polynomialResidual hw0 hw1 K extent hK i
        ((F).smul a p))
      (polynomialResidual hw0 hw1 K extent hK i
        ((F).smul a p)) ≈
      (a * a) * (F).B (polynomialResidual hw0 hw1 K extent hK i p)
        (polynomialResidual hw0 hw1 K extent hK i p) := by
    have htransport := Q'.eqv_trans _ _ _ ((F).B_congr_left
      (polynomialResidual hw0 hw1 K extent hK i
        ((F).smul a p)) ht)
      ((F).B_congr_right
        ((F).smul a (polynomialResidual hw0 hw1 K extent hK i p)) ht)
    exact Q'.eqv_trans _ _ _ htransport
      (Q'.eqv_trans _ _ _ ((F).B_smul_left a
        (polynomialResidual hw0 hw1 K extent hK i p)
        ((F).smul a (polynomialResidual hw0 hw1 K extent hK i p)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left a _ _
            ((F).B_smul_right a
              (polynomialResidual hw0 hw1 K extent hK i p)
              (polynomialResidual hw0 hw1 K extent hK i p)))
          (Q'.eqv_symm (Q'.mul_assoc_eqv a a
            ((F).B (polynomialResidual hw0 hw1 K extent hK i p)
              (polynomialResidual hw0 hw1 K extent hK i p))))))
  have hsum := Q'.add_eqv_congr' hpair hpair
  have hneg := Q'.neg_eqv_congr _ _ hself
  exact Q'.add_eqv_congr' hsum hneg

#print axioms polynomialResidual_smul
#print axioms dualValue_smul

end YMGap.Continuum.BF4ExactSlabStarPolynomialResidualScaling
