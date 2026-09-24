/-
# Constructive linearity of the cyclic heat sweep

The fresh-output heat step respects supported Haar-carrier equality: extend
the input certificate to the fresh block, multiply by the unchanged heat
kernel, and integrate the old head. Consequently every finite cyclic sweep
is additive and rational-linear on the supported carrier. The separated
coordinate rotation and all of its iterates satisfy the same laws.
-/

import YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

namespace YMGap.Continuum.SU2QuaternionCyclicHeatLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)

private theorem supported_zero (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyZero := by
  intro t ht
  exact False.elim (List.not_mem_nil ht)

/-- One fresh-output heat step preserves every supported carrier equality. -/
theorem cycleStep_carrier (n : Nat) (w : Q') (K : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : HaarCarrierEqv n p q) :
    HaarCarrierEqv n (cycleStep n w K p) (cycleStep n w K q) := by
  apply partialHaarHead_carrier
  exact HaarCarrierEqv.mul_left (heatAt 0 n w K)
    (carrier_extend 1 hp hq h)

/-- The computed one-step polynomial is additive coefficientwise. -/
theorem cycleStep_add (n : Nat) (w : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (cycleStep n w K (polyAdd p q))
      (polyAdd (cycleStep n w K p) (cycleStep n w K q)) := by
  unfold cycleStep
  have h := partialHaarHead_congr
    (RatPolyCoeffEqv.mul_add_right (heatAt 0 n w K) p q)
  rw [partialHaarHead_add] at h
  exact h

/-- Rational scaling commutes coefficientwise with one fresh-output step. -/
theorem cycleStep_smul (n : Nat) (w : Q') (K : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (cycleStep n w K (polySmul c p))
      (polySmul c (cycleStep n w K p)) := by
  unfold cycleStep
  exact (partialHaarHead_congr
    (RatPolyCoeffEqv.polyMul_smul_right c (heatAt 0 n w K) p)).trans
      (partialHaarHead_smul c _)

theorem cycleStep_zero (n : Nat) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (cycleStep n w K polyZero) polyZero := by
  unfold cycleStep
  exact partialHaarHead_congr
    (RatPolyCoeffEqv.mul_zero_right (heatAt 0 n w K))

/-- Every finite number of cyclic heat rounds preserves supported carrier
equality. -/
theorem cycleIterate_carrier (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) {p q : RatPoly}, SupportedQuaternionBlocks n p →
      SupportedQuaternionBlocks n q → HaarCarrierEqv n p q →
      HaarCarrierEqv n (cycleIterate n w K m p) (cycleIterate n w K m q)
  | 0, _, _, _, _, h => h
  | m+1, _, _, hp, hq, h =>
      cycleIterate_carrier n w K m
        (cycleStep_supported n w K hp) (cycleStep_supported n w K hq)
        (cycleStep_carrier n w K hp hq h)

/-- Every finite cyclic sweep is additive on supported inputs. -/
theorem cycleIterate_add (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p q : RatPoly), SupportedQuaternionBlocks n p →
      SupportedQuaternionBlocks n q →
      HaarCarrierEqv n (cycleIterate n w K m (polyAdd p q))
        (polyAdd (cycleIterate n w K m p) (cycleIterate n w K m q))
  | 0, p, q, _, _ => HaarCarrierEqv.refl n (polyAdd p q)
  | m+1, p, q, hp, hq => by
      change HaarCarrierEqv n
        (cycleIterate n w K m (cycleStep n w K (polyAdd p q)))
        (polyAdd (cycleIterate n w K m (cycleStep n w K p))
          (cycleIterate n w K m (cycleStep n w K q)))
      have hs := RatPolyCoeffEqv.haarCarrier (blocks := n) (cycleStep_add n w K p q)
      exact HaarCarrierEqv.trans
        (cycleIterate_carrier n w K m
          (cycleStep_supported n w K (supported_add hp hq))
          (supported_add (cycleStep_supported n w K hp) (cycleStep_supported n w K hq)) hs)
        (cycleIterate_add n w K m (cycleStep n w K p) (cycleStep n w K q)
          (cycleStep_supported n w K hp) (cycleStep_supported n w K hq))

/-- Every finite cyclic sweep is rational-linear on supported inputs. -/
theorem cycleIterate_smul (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (c : Q') (p : RatPoly), SupportedQuaternionBlocks n p →
      HaarCarrierEqv n (cycleIterate n w K m (polySmul c p))
        (polySmul c (cycleIterate n w K m p))
  | 0, c, p, _ => HaarCarrierEqv.refl n (polySmul c p)
  | m+1, c, p, hp => by
      change HaarCarrierEqv n
        (cycleIterate n w K m (cycleStep n w K (polySmul c p)))
        (polySmul c (cycleIterate n w K m (cycleStep n w K p)))
      have hs := RatPolyCoeffEqv.haarCarrier (blocks := n) (cycleStep_smul n w K c p)
      exact HaarCarrierEqv.trans
        (cycleIterate_carrier n w K m
          (cycleStep_supported n w K (supported_smul hp c))
          (supported_smul (cycleStep_supported n w K hp) c) hs)
        (cycleIterate_smul n w K m c (cycleStep n w K p)
          (cycleStep_supported n w K hp))

theorem cycleIterate_zero (n : Nat) (w : Q') (K m : Nat) :
    HaarCarrierEqv n (cycleIterate n w K m polyZero) polyZero := by
  induction m with
  | zero => exact HaarCarrierEqv.refl n polyZero
  | succ m ih =>
      exact HaarCarrierEqv.trans
        (cycleIterate_carrier n w K m
          (cycleStep_supported n w K (supported_zero n)) (supported_zero n)
          (RatPolyCoeffEqv.haarCarrier (blocks := n) (cycleStep_zero n w K))) ih

/-- The separated coordinate cycle preserves supported carrier equality. -/
theorem cycleRotation_carrier (n : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : HaarCarrierEqv n p q) :
    HaarCarrierEqv n (cycleRotation n p) (cycleRotation n q) := by
  unfold cycleRotation
  exact reindex_carrier (reverseBlocks n) (reindex_supported _ p) (reindex_supported _ q)
    (reindex_carrier (reverseTailBlocks n) hp hq h)

theorem cycleRotation_add (n : Nat) (p q : RatPoly) :
    cycleRotation n (polyAdd p q) =
      polyAdd (cycleRotation n p) (cycleRotation n q) := by
  simp only [cycleRotation, reindexQuaternionPolynomial_add]

theorem cycleRotation_smul (n : Nat) (c : Q') (p : RatPoly) :
    cycleRotation n (polySmul c p) = polySmul c (cycleRotation n p) := by
  simp only [cycleRotation, reindexQuaternionPolynomial_smul]

/-- Every finite iterate of coordinate cycling preserves supported carrier
equality. -/
theorem rotateIterate_carrier (n : Nat) :
    ∀ (m : Nat) {p q : RatPoly}, SupportedQuaternionBlocks n p →
      SupportedQuaternionBlocks n q → HaarCarrierEqv n p q →
      HaarCarrierEqv n (rotateIterate n m p) (rotateIterate n m q)
  | 0, _, _, _, _, h => h
  | m+1, _, _, hp, hq, h =>
      cycleRotation_carrier n (rotateIterate_supported n m hp)
        (rotateIterate_supported n m hq) (rotateIterate_carrier n m hp hq h)

theorem rotateIterate_add (n : Nat) : ∀ (m : Nat) (p q : RatPoly),
    rotateIterate n m (polyAdd p q) =
      polyAdd (rotateIterate n m p) (rotateIterate n m q)
  | 0, _, _ => rfl
  | m+1, p, q => by
      change cycleRotation n (rotateIterate n m (polyAdd p q)) =
        polyAdd (cycleRotation n (rotateIterate n m p))
          (cycleRotation n (rotateIterate n m q))
      rw [rotateIterate_add n m, cycleRotation_add]

theorem rotateIterate_smul (n : Nat) : ∀ (m : Nat) (c : Q') (p : RatPoly),
    rotateIterate n m (polySmul c p) = polySmul c (rotateIterate n m p)
  | 0, _, _ => rfl
  | m+1, c, p => by
      change cycleRotation n (rotateIterate n m (polySmul c p)) =
        polySmul c (cycleRotation n (rotateIterate n m p))
      rw [rotateIterate_smul n m, cycleRotation_smul]

theorem rotateIterate_zero (n m : Nat) :
    HaarCarrierEqv n (rotateIterate n m polyZero) polyZero := by
  have h : rotateIterate n m polyZero = polyZero := by
    induction m with
    | zero => rfl
    | succ m ih =>
        change cycleRotation n (rotateIterate n m polyZero) = polyZero
        rw [ih]
        rfl
  rw [h]
  exact HaarCarrierEqv.refl n polyZero

end YMGap.Continuum.SU2QuaternionCyclicHeatLinear

#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleStep_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleStep_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleStep_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleStep_zero
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleIterate_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleIterate_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleIterate_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleIterate_zero
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleRotation_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleRotation_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.cycleRotation_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.rotateIterate_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.rotateIterate_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.rotateIterate_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicHeatLinear.rotateIterate_zero
