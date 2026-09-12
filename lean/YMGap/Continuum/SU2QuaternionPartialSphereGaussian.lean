/-
# Coefficientwise sphere conversion for the original partial integral

Even head-homogeneous polynomials have one explicit positive radial
denominator relating their partial Haar and Gaussian integrals. Every tail
coefficient remains available. Odd head-homogeneous polynomials vanish.
This is an exact algebraic conversion, not a mass-gap or limit estimate.
-/

import YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct

namespace YMGap.Continuum.SU2QuaternionPartialSphereGaussian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- A tail probe preceded by the exact original sphere moment. -/
def haarHeadProbe (weight : List Nat → Q') (m : List Nat) : Q' :=
  headQuaternionMoment m * weight (m.drop 4)

theorem partialHaarHead_probe (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight (partialHaarHead p) ≈ ratWeightedSum (haarHeadProbe weight) p
  | [] => Q'.eqv_refl _
  | _ :: rest => Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (partialHaarHead_probe weight rest)

theorem partialHaarHead_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (partialHaarHead p) (partialHaarHead q) := fun weight =>
  Q'.eqv_trans _ _ _ (partialHaarHead_probe weight p)
    (Q'.eqv_trans _ _ _ (h (haarHeadProbe weight)) (Q'.eqv_symm (partialHaarHead_probe weight q)))

private theorem radial_coefficient (d c h g : Q') (hm : h * d ≈ g) :
    d * (c * h) ≈ c * g :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d (c * h))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c h d) (Q'.mul_eqv_congr_left c _ _ hm))

private theorem radial_terms (k : Nat) : ∀ p : RatPoly,
    HasQuaternionBlockDegree 0 (2 * k) p →
    RatPolyTermwiseEqv
      (polySmul (Q'.ofNat (sphereFourDenominator k)) (partialHaarHead p))
      (partialGaussianHead p)
  | [], _ => True.intro
  | term :: rest, hd =>
      ⟨rfl, radial_coefficient _ _ _ _
        (headMoment_mul_commonRadialDenominator term.1 k (hd term List.mem_cons_self)),
        radial_terms k rest (fun t ht => hd t (List.mem_cons_of_mem term ht))⟩

/-- The common radial factor is retained as an explicit natural number;
the identity holds under EVERY tail coefficient probe. -/
theorem partialHaarHead_mul_radial (k : Nat) (p : RatPoly)
    (hd : HasQuaternionBlockDegree 0 (2 * k) p) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (sphereFourDenominator k)) (partialHaarHead p))
      (partialGaussianHead p) := fun weight => ratWeightedSum_termwise_eqv weight (radial_terms k p hd)

theorem radialDenominator_positive (k : Nat) :
    (0 : Q') < Q'.ofNat (sphereFourDenominator k) := by
  cases hD : sphereFourDenominator k with
  | zero => have := sphereFourDenominator_pos k; omega
  | succ value => exact Q'.ofNat_succ_pos value

/-- Cancel a supplied strictly positive scalar coefficientwise. -/
theorem coeffEqv_of_positive_smul {a : Q'} (ha : (0 : Q') < a) {p q : RatPoly}
    (h : RatPolyCoeffEqv (polySmul a p) (polySmul a q)) : RatPolyCoeffEqv p q := by
  intro weight
  apply Q'.mul_left_cancel_of_pos ha
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (ratWeightedSum_smul weight a p))
    (Q'.eqv_trans _ _ _ (h weight) (ratWeightedSum_smul weight a q))

/-- Odd head degree annihilates the partial integral itself, before any
tail integration or specialization. -/
theorem partialHaarHead_eq_zero_of_odd : ∀ p : RatPoly,
    HeadQuaternionOdd p → RatPolyCoeffEqv (partialHaarHead p) polyZero
  | [], _ => RatPolyCoeffEqv.refl _
  | term :: rest, ho => by
      intro weight
      change (term.2 * headQuaternionMoment term.1) * weight (term.1.drop 4) +
        ratWeightedSum weight (partialHaarHead rest) ≈ 0
      rw [headQuaternionMoment_eq_zero_of_odd (ho term List.mem_cons_self)]
      have ht := partialHaarHead_eq_zero_of_odd rest (fun t ht => ho t (List.mem_cons_of_mem term ht)) weight
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv term.2))
            (Q'.zero_mul_eqv _)) ht)
        (Q'.eqv_refl 0)

end YMGap.Continuum.SU2QuaternionPartialSphereGaussian

#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.haarHeadProbe
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.partialHaarHead_probe
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.partialHaarHead_congr
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.partialHaarHead_mul_radial
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.radialDenominator_positive
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.coeffEqv_of_positive_smul
#print axioms YMGap.Continuum.SU2QuaternionPartialSphereGaussian.partialHaarHead_eq_zero_of_odd
