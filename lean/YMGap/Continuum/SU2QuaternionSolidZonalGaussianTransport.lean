/-
# Selected-link Gaussian-tail transport for solid SU(2) zonal characters

This module connects coefficient-sensitive `RatPoly` harmonicity to the
existing Gaussian/Haar annihilation consumer.  It proves that Gaussian
integration of the formal selected-head Laplacian is exactly the previously
defined termwise Gaussian-Laplacian functional, with every tail quaternion
retained.
-/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonic

namespace YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.BF4CompactActionCPOrder

local infix:50 " ≈ " => Q'.eqv

/-- The named Gaussian-tail functional is literally the arbitrary monomial
weighted sum with its Gaussian/Haar monomial weight. -/
theorem headGaussianTail_eq_ratWeightedSum
    (tailBlocks : Nat) (polynomial : RatPoly) :
    headGaussianTail tailBlocks polynomial =
      ratWeightedSum (headGaussianTailMono tailBlocks) polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term rest induction =>
      simp only [headGaussianTail, ratWeightedSum]
      rw [induction]

/-- The named Gaussian-Laplacian-tail functional is likewise a literal
monomial-weighted sum. -/
theorem headGaussianLaplacianTail_eq_ratWeightedSum
    (tailBlocks : Nat) (polynomial : RatPoly) :
    headGaussianLaplacianTail tailBlocks polynomial =
      ratWeightedSum (headGaussianLaplacianTailMono tailBlocks) polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term rest induction =>
      simp only [headGaussianLaplacianTail, ratWeightedSum]
      rw [induction]

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show ((a * b : Nat) : Int) *
      ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num *
      ((Q'.ofNat (a * b)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  push_cast
  omega

private theorem ofNat_mul_reassociate
    (a b : Nat) (value : Q') :
    Q'.ofNat a * (Q'.ofNat b * value) ≈
      Q'.ofNat (a * b) * value := by
  refine Q'.eqv_trans _
    ((Q'.ofNat a * Q'.ofNat b) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (ofNat_mul_eqv a b))

private theorem secondDerivativeProbe_zero
    (tailBlocks : Nat) (monomial : List Nat) :
    derivativeProbe 0
        (derivativeProbe 0 (headGaussianTailMono tailBlocks)) monomial ≈
      Q'.ofNat
          (exponentAt monomial 0 * (exponentAt monomial 0 - 1)) *
        (gaussianMoment4
            (exponentAt monomial 0 - 2)
            (exponentAt monomial 1)
            (exponentAt monomial 2)
            (exponentAt monomial 3) *
          quaternionHaarMono tailBlocks (monomial.drop 4)) := by
  cases monomial with
  | nil =>
      simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
        lowerExponentAt, exponentAt]
      exact ofNat_mul_reassociate 0 0 _
  | cons e0 rest =>
      cases rest with
      | nil =>
          simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
            lowerExponentAt, exponentAt]
          have hsub : e0 - 1 - 1 = e0 - 2 := by omega
          rw [hsub]
          exact ofNat_mul_reassociate e0 (e0 - 1) _
      | cons e1 rest =>
          cases rest with
          | nil =>
              simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
                lowerExponentAt, exponentAt]
              have hsub : e0 - 1 - 1 = e0 - 2 := by omega
              rw [hsub]
              exact ofNat_mul_reassociate e0 (e0 - 1) _
          | cons e2 rest =>
              cases rest with
              | nil =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e0 - 1 - 1 = e0 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e0 (e0 - 1) _
              | cons e3 tail =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e0 - 1 - 1 = e0 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e0 (e0 - 1) _

private theorem secondDerivativeProbe_one
    (tailBlocks : Nat) (monomial : List Nat) :
    derivativeProbe 1
        (derivativeProbe 1 (headGaussianTailMono tailBlocks)) monomial ≈
      Q'.ofNat
          (exponentAt monomial 1 * (exponentAt monomial 1 - 1)) *
        (gaussianMoment4
            (exponentAt monomial 0)
            (exponentAt monomial 1 - 2)
            (exponentAt monomial 2)
            (exponentAt monomial 3) *
          quaternionHaarMono tailBlocks (monomial.drop 4)) := by
  cases monomial with
  | nil =>
      simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
        lowerExponentAt, exponentAt]
      exact ofNat_mul_reassociate 0 0 _
  | cons e0 rest =>
      cases rest with
      | nil =>
          simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
            lowerExponentAt, exponentAt]
          exact ofNat_mul_reassociate 0 0 _
      | cons e1 rest =>
          cases rest with
          | nil =>
              simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
                lowerExponentAt, exponentAt]
              have hsub : e1 - 1 - 1 = e1 - 2 := by omega
              rw [hsub]
              exact ofNat_mul_reassociate e1 (e1 - 1) _
          | cons e2 rest =>
              cases rest with
              | nil =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e1 - 1 - 1 = e1 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e1 (e1 - 1) _
              | cons e3 tail =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e1 - 1 - 1 = e1 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e1 (e1 - 1) _

private theorem secondDerivativeProbe_two
    (tailBlocks : Nat) (monomial : List Nat) :
    derivativeProbe 2
        (derivativeProbe 2 (headGaussianTailMono tailBlocks)) monomial ≈
      Q'.ofNat
          (exponentAt monomial 2 * (exponentAt monomial 2 - 1)) *
        (gaussianMoment4
            (exponentAt monomial 0)
            (exponentAt monomial 1)
            (exponentAt monomial 2 - 2)
            (exponentAt monomial 3) *
          quaternionHaarMono tailBlocks (monomial.drop 4)) := by
  cases monomial with
  | nil =>
      simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
        lowerExponentAt, exponentAt]
      exact ofNat_mul_reassociate 0 0 _
  | cons e0 rest =>
      cases rest with
      | nil =>
          simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
            lowerExponentAt, exponentAt]
          exact ofNat_mul_reassociate 0 0 _
      | cons e1 rest =>
          cases rest with
          | nil =>
              simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
                lowerExponentAt, exponentAt]
              exact ofNat_mul_reassociate 0 0 _
          | cons e2 rest =>
              cases rest with
              | nil =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e2 - 1 - 1 = e2 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e2 (e2 - 1) _
              | cons e3 tail =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e2 - 1 - 1 = e2 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e2 (e2 - 1) _

private theorem secondDerivativeProbe_three
    (tailBlocks : Nat) (monomial : List Nat) :
    derivativeProbe 3
        (derivativeProbe 3 (headGaussianTailMono tailBlocks)) monomial ≈
      Q'.ofNat
          (exponentAt monomial 3 * (exponentAt monomial 3 - 1)) *
        (gaussianMoment4
            (exponentAt monomial 0)
            (exponentAt monomial 1)
            (exponentAt monomial 2)
            (exponentAt monomial 3 - 2) *
          quaternionHaarMono tailBlocks (monomial.drop 4)) := by
  cases monomial with
  | nil =>
      simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
        lowerExponentAt, exponentAt]
      exact ofNat_mul_reassociate 0 0 _
  | cons e0 rest =>
      cases rest with
      | nil =>
          simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
            lowerExponentAt, exponentAt]
          exact ofNat_mul_reassociate 0 0 _
      | cons e1 rest =>
          cases rest with
          | nil =>
              simp [derivativeProbe, headGaussianTailMono, headGaussianMoment,
                lowerExponentAt, exponentAt]
              exact ofNat_mul_reassociate 0 0 _
          | cons e2 rest =>
              cases rest with
              | nil =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  exact ofNat_mul_reassociate 0 0 _
              | cons e3 tail =>
                  simp [derivativeProbe, headGaussianTailMono,
                    headGaussianMoment, lowerExponentAt, exponentAt]
                  have hsub : e3 - 1 - 1 = e3 - 2 := by omega
                  rw [hsub]
                  exact ofNat_mul_reassociate e3 (e3 - 1) _

/-- The four transposed second-derivative probes of the selected quaternion. -/
def headGaussianSecondProbeSum
    (tailBlocks : Nat) (monomial : List Nat) : Q' :=
  derivativeProbe 0
      (derivativeProbe 0 (headGaussianTailMono tailBlocks)) monomial +
    (derivativeProbe 1
        (derivativeProbe 1 (headGaussianTailMono tailBlocks)) monomial +
      (derivativeProbe 2
          (derivativeProbe 2 (headGaussianTailMono tailBlocks)) monomial +
        derivativeProbe 3
          (derivativeProbe 3 (headGaussianTailMono tailBlocks)) monomial))

/-- Pointwise identification of the transposed formal Laplacian probe with
the already-defined Gaussian Laplacian moment, including the untouched tail
Haar factor. -/
theorem headGaussianSecondProbeSum_eq_laplacianMono
    (tailBlocks : Nat) (monomial : List Nat) :
    headGaussianSecondProbeSum tailBlocks monomial ≈
      headGaussianLaplacianTailMono tailBlocks monomial := by
  let e0 := exponentAt monomial 0
  let e1 := exponentAt monomial 1
  let e2 := exponentAt monomial 2
  let e3 := exponentAt monomial 3
  let a0 := Q'.ofNat (e0 * (e0 - 1))
  let a1 := Q'.ofNat (e1 * (e1 - 1))
  let a2 := Q'.ofNat (e2 * (e2 - 1))
  let a3 := Q'.ofNat (e3 * (e3 - 1))
  let g0 := gaussianMoment4 (e0 - 2) e1 e2 e3
  let g1 := gaussianMoment4 e0 (e1 - 2) e2 e3
  let g2 := gaussianMoment4 e0 e1 (e2 - 2) e3
  let g3 := gaussianMoment4 e0 e1 e2 (e3 - 2)
  let tail := quaternionHaarMono tailBlocks (monomial.drop 4)
  have h0 :
      derivativeProbe 0
          (derivativeProbe 0 (headGaussianTailMono tailBlocks)) monomial ≈
        a0 * (g0 * tail) :=
    secondDerivativeProbe_zero tailBlocks monomial
  have h1 :
      derivativeProbe 1
          (derivativeProbe 1 (headGaussianTailMono tailBlocks)) monomial ≈
        a1 * (g1 * tail) :=
    secondDerivativeProbe_one tailBlocks monomial
  have h2 :
      derivativeProbe 2
          (derivativeProbe 2 (headGaussianTailMono tailBlocks)) monomial ≈
        a2 * (g2 * tail) :=
    secondDerivativeProbe_two tailBlocks monomial
  have h3 :
      derivativeProbe 3
          (derivativeProbe 3 (headGaussianTailMono tailBlocks)) monomial ≈
        a3 * (g3 * tail) :=
    secondDerivativeProbe_three tailBlocks monomial
  refine Q'.eqv_trans _
    (a0 * (g0 * tail) +
      (a1 * (g1 * tail) +
        (a2 * (g2 * tail) + a3 * (g3 * tail)))) _ ?_ ?_
  · exact Q'.add_eqv_congr' h0
      (Q'.add_eqv_congr' h1 (Q'.add_eqv_congr' h2 h3))
  have h0' : a0 * (g0 * tail) ≈ (a0 * g0) * tail :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have h1' : a1 * (g1 * tail) ≈ (a1 * g1) * tail :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have h2' : a2 * (g2 * tail) ≈ (a2 * g2) * tail :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have h3' : a3 * (g3 * tail) ≈ (a3 * g3) * tail :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  refine Q'.eqv_trans _
    ((a0 * g0) * tail +
      ((a1 * g1) * tail +
        ((a2 * g2) * tail + (a3 * g3) * tail))) _
    (Q'.add_eqv_congr' h0'
      (Q'.add_eqv_congr' h1' (Q'.add_eqv_congr' h2' h3'))) ?_
  have h23 :
      (a2 * g2) * tail + (a3 * g3) * tail ≈
        (a2 * g2 + a3 * g3) * tail :=
    Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  have h123 :
      (a1 * g1) * tail +
          ((a2 * g2) * tail + (a3 * g3) * tail) ≈
        (a1 * g1 + (a2 * g2 + a3 * g3)) * tail := by
    refine Q'.eqv_trans _
      ((a1 * g1) * tail + (a2 * g2 + a3 * g3) * tail) _
      (Q'.add_eqv_congr_left _ _ _ h23) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  refine Q'.eqv_trans _
    ((a0 * g0) * tail +
      (a1 * g1 + (a2 * g2 + a3 * g3)) * tail) _
    (Q'.add_eqv_congr_left _ _ _ h123) ?_
  change _ ≈
    (a0 * g0 + (a1 * g1 + (a2 * g2 + a3 * g3))) * tail
  exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)

/-- A monomial-weighted finite sum is linear in its weight. -/
private theorem ratWeightedSum_weight_add
    (left right : List Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum (fun monomial => left monomial + right monomial) polynomial ≈
      ratWeightedSum left polynomial + ratWeightedSum right polynomial
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | term :: rest => by
      change
        term.2 * (left term.1 + right term.1) +
            ratWeightedSum
              (fun monomial => left monomial + right monomial) rest ≈
          (term.2 * left term.1 + ratWeightedSum left rest) +
            (term.2 * right term.1 + ratWeightedSum right rest)
      refine Q'.eqv_trans _
        ((term.2 * left term.1 + term.2 * right term.1) +
          (ratWeightedSum left rest + ratWeightedSum right rest)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_add_eqv _ _ _)
          (ratWeightedSum_weight_add left right rest)
      · exact Q'.add_swap_inner _ _ _ _

private theorem ratWeightedSum_weight_eqv
    {left right : List Nat → Q'}
    (h : ∀ monomial, left monomial ≈ right monomial) :
    ∀ polynomial : RatPoly,
      ratWeightedSum left polynomial ≈ ratWeightedSum right polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest =>
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left term.2 _ _ (h term.1))
        (ratWeightedSum_weight_eqv h rest)

/-- **Gaussian-tail transport of the formal selected-head Laplacian.**
The left side computes the `RatPoly` Laplacian first and then integrates;
the right side applies the pre-existing termwise Laplacian moment. -/
theorem headGaussianTail_headLaplacian
    (tailBlocks : Nat) (polynomial : RatPoly) :
    headGaussianTail tailBlocks (headLaplacian polynomial) ≈
      headGaussianLaplacianTail tailBlocks polynomial := by
  rw [headGaussianTail_eq_ratWeightedSum,
    headGaussianLaplacianTail_eq_ratWeightedSum]
  let weight := headGaussianTailMono tailBlocks
  let d0 := ratDerivative 0 (ratDerivative 0 polynomial)
  let d1 := ratDerivative 1 (ratDerivative 1 polynomial)
  let d2 := ratDerivative 2 (ratDerivative 2 polynomial)
  let d3 := ratDerivative 3 (ratDerivative 3 polynomial)
  have hsplit23 :
      ratWeightedSum weight (polyAdd d2 d3) ≈
        ratWeightedSum weight d2 + ratWeightedSum weight d3 :=
    ratWeightedSum_add weight d2 d3
  have hsplit123 :
      ratWeightedSum weight (polyAdd d1 (polyAdd d2 d3)) ≈
        ratWeightedSum weight d1 +
          (ratWeightedSum weight d2 + ratWeightedSum weight d3) :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_add weight d1 (polyAdd d2 d3))
      (Q'.add_eqv_congr_left _ _ _ hsplit23)
  have hsplit :
      ratWeightedSum weight
          (polyAdd d0 (polyAdd d1 (polyAdd d2 d3))) ≈
        ratWeightedSum weight d0 +
          (ratWeightedSum weight d1 +
            (ratWeightedSum weight d2 + ratWeightedSum weight d3)) :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_add weight d0 (polyAdd d1 (polyAdd d2 d3)))
      (Q'.add_eqv_congr_left _ _ _ hsplit123)
  have h0 :
      ratWeightedSum weight d0 ≈
        ratWeightedSum
          (derivativeProbe 0 (derivativeProbe 0 weight)) polynomial :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_derivative
        0 weight (ratDerivative 0 polynomial))
      (ratWeightedSum_derivative
        0 (derivativeProbe 0 weight) polynomial)
  have h1 :
      ratWeightedSum weight d1 ≈
        ratWeightedSum
          (derivativeProbe 1 (derivativeProbe 1 weight)) polynomial :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_derivative
        1 weight (ratDerivative 1 polynomial))
      (ratWeightedSum_derivative
        1 (derivativeProbe 1 weight) polynomial)
  have h2 :
      ratWeightedSum weight d2 ≈
        ratWeightedSum
          (derivativeProbe 2 (derivativeProbe 2 weight)) polynomial :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_derivative
        2 weight (ratDerivative 2 polynomial))
      (ratWeightedSum_derivative
        2 (derivativeProbe 2 weight) polynomial)
  have h3 :
      ratWeightedSum weight d3 ≈
        ratWeightedSum
          (derivativeProbe 3 (derivativeProbe 3 weight)) polynomial :=
    Q'.eqv_trans _ _ _
      (ratWeightedSum_derivative
        3 weight (ratDerivative 3 polynomial))
      (ratWeightedSum_derivative
        3 (derivativeProbe 3 weight) polynomial)
  let w0 := derivativeProbe 0 (derivativeProbe 0 weight)
  let w1 := derivativeProbe 1 (derivativeProbe 1 weight)
  let w2 := derivativeProbe 2 (derivativeProbe 2 weight)
  let w3 := derivativeProbe 3 (derivativeProbe 3 weight)
  have hprobe :
      ratWeightedSum weight d0 +
          (ratWeightedSum weight d1 +
            (ratWeightedSum weight d2 + ratWeightedSum weight d3)) ≈
        ratWeightedSum w0 polynomial +
          (ratWeightedSum w1 polynomial +
            (ratWeightedSum w2 polynomial +
              ratWeightedSum w3 polynomial)) :=
    Q'.add_eqv_congr' h0
      (Q'.add_eqv_congr' h1 (Q'.add_eqv_congr' h2 h3))
  have hadd23 :
      ratWeightedSum w2 polynomial + ratWeightedSum w3 polynomial ≈
        ratWeightedSum (fun monomial => w2 monomial + w3 monomial)
          polynomial :=
    Q'.eqv_symm (ratWeightedSum_weight_add w2 w3 polynomial)
  have hadd123 :
      ratWeightedSum w1 polynomial +
          (ratWeightedSum w2 polynomial + ratWeightedSum w3 polynomial) ≈
        ratWeightedSum
          (fun monomial => w1 monomial + (w2 monomial + w3 monomial))
          polynomial := by
    refine Q'.eqv_trans _
      (ratWeightedSum w1 polynomial +
        ratWeightedSum (fun monomial => w2 monomial + w3 monomial)
          polynomial) _
      (Q'.add_eqv_congr_left _ _ _ hadd23) ?_
    exact Q'.eqv_symm
      (ratWeightedSum_weight_add w1
        (fun monomial => w2 monomial + w3 monomial) polynomial)
  have hadd :
      ratWeightedSum w0 polynomial +
          (ratWeightedSum w1 polynomial +
            (ratWeightedSum w2 polynomial + ratWeightedSum w3 polynomial)) ≈
        ratWeightedSum (headGaussianSecondProbeSum tailBlocks) polynomial := by
    refine Q'.eqv_trans _
      (ratWeightedSum w0 polynomial +
        ratWeightedSum
          (fun monomial => w1 monomial + (w2 monomial + w3 monomial))
          polynomial) _
      (Q'.add_eqv_congr_left _ _ _ hadd123) ?_
    change _ ≈ ratWeightedSum
      (fun monomial =>
        w0 monomial + (w1 monomial + (w2 monomial + w3 monomial)))
      polynomial
    exact Q'.eqv_symm
      (ratWeightedSum_weight_add w0
        (fun monomial => w1 monomial + (w2 monomial + w3 monomial))
        polynomial)
  change
    ratWeightedSum weight
        (polyAdd d0 (polyAdd d1 (polyAdd d2 d3))) ≈
      ratWeightedSum (headGaussianLaplacianTailMono tailBlocks) polynomial
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ _ _ hprobe
      (Q'.eqv_trans _ _ _ hadd
        (ratWeightedSum_weight_eqv
          (headGaussianSecondProbeSum_eq_laplacianMono tailBlocks)
          polynomial)))

/-! ## Coefficient harmonicity transported to Gaussian and Haar zero -/

/-- Every coefficient-sensitive selected-head harmonic polynomial has zero
Gaussian Laplacian tail, for every number of retained quaternion blocks.
This is the exact bridge from `RatPolyCoeffEqv` to the moment functional used
by the homogeneous Gaussian/Haar annihilation theorem. -/
theorem headGaussianLaplacianTail_zero_of_coeffEqv
    (tailBlocks : Nat) (polynomial : RatPoly)
    (hharmonic : RatPolyCoeffEqv (headLaplacian polynomial) polyZero) :
    headGaussianLaplacianTail tailBlocks polynomial ≈ 0 := by
  have hweighted :
      headGaussianTail tailBlocks (headLaplacian polynomial) ≈ 0 := by
    rw [headGaussianTail_eq_ratWeightedSum]
    exact hharmonic (headGaussianTailMono tailBlocks)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (headGaussianTail_headLaplacian tailBlocks polynomial))
    hweighted

/-- The all-spin BF4 solid zonal character has zero selected-head Gaussian
Laplacian moment with an arbitrary retained tail. -/
theorem exposedSolidZonal_headGaussianLaplacianTail_zero
    (tailBlocks : Nat)
    (reverse0 reverse1 reverse2 reverse3 : Bool) (spin : Nat) :
    headGaussianLaplacianTail tailBlocks
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 spin) ≈ 0 := by
  exact headGaussianLaplacianTail_zero_of_coeffEqv tailBlocks _
    (laplacian_U_solidZonal_AUB_zero
      reverse0 reverse1 reverse2 reverse3 spin)

/-- Every positive even-spin solid BF4 zonal character has zero exact Haar
integral on the literal 116-quaternion carrier.  The selected quaternion is
the Gaussian/Haar head and all other 115 blocks remain in the tail. -/
theorem exposedSolidZonal_even_quaternionHaar_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (k : Nat) (hpositive : 0 < k) :
    quaternionHaar 116
        (exposedSolidZonalCharacter
          reverse0 reverse1 reverse2 reverse3 (2 * k)) ≈ 0 := by
  exact quaternionHaar_even_homogeneous_eq_zero_of_laplacian
    115 k _ hpositive
    (exposedSolidZonalCharacter_blockDegree
      reverse0 reverse1 reverse2 reverse3 0 (by omega) (2 * k))
    (exposedSolidZonal_headGaussianLaplacianTail_zero
      115 reverse0 reverse1 reverse2 reverse3 (2 * k))

/-- A carrier equality can be specialized to its uninserted Haar integral. -/
theorem QuaternionHaarCarrierEqv.haar
    {blocks : Nat} {left right : RatPoly}
    (h : QuaternionHaarCarrierEqv blocks left right) :
    quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  have hleft :
      quaternionHaar blocks (polyMul polyOne left) ≈
        quaternionHaar blocks left :=
    Q'.eqv_trans _
      (quaternionHaar blocks (polyMul left polyOne)) _
      (quaternionHaar_polyMul_comm blocks polyOne left)
      (quaternionHaar_polyMul_one_right blocks left)
  have hright :
      quaternionHaar blocks (polyMul polyOne right) ≈
        quaternionHaar blocks right :=
    Q'.eqv_trans _
      (quaternionHaar blocks (polyMul right polyOne)) _
      (quaternionHaar_polyMul_comm blocks polyOne right)
      (quaternionHaar_polyMul_one_right blocks right)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ (h polyOne) hright)

/-- Ordinary positive even-spin BF4 character annihilation, obtained from
the solid harmonic representative in the same arbitrary-insertion carrier. -/
theorem exposedEvenCharacter_quaternionHaar_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (k : Nat) (hpositive : 0 < k) :
    quaternionHaar 116
        (characterPolynomial
          (exposedFourWord
            reverse0 reverse1 reverse2 reverse3).scalar (2 * k)) ≈ 0 := by
  have hcarrier :=
    QuaternionHaarCarrierEqv.haar
      (exposedSolidZonalCharacter_eq_character_116
        reverse0 reverse1 reverse2 reverse3 (2 * k))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hcarrier)
    (exposedSolidZonal_even_quaternionHaar_zero
      reverse0 reverse1 reverse2 reverse3 k hpositive)

/-! ## Retaining a selected-head-independent slab multiplier -/

/-- A polynomial independent of the selected quaternion has zero formal
selected-head Laplacian.  Its tail variables remain literal coefficients. -/
theorem headLaplacian_zero_of_blockDegree_zero
    (independent : RatPoly)
    (hindependent : HasQuaternionBlockDegree 0 0 independent) :
    RatPolyCoeffEqv (headLaplacian independent) polyZero := by
  have coordinate (index : Nat) (hindex : index < 4) :
      RatPolyCoeffEqv
        (ratDerivative index (ratDerivative index independent)) polyZero := by
    have hfirst :=
      ratDerivative_eq_zero_of_headDegree_zero
        index hindex independent hindependent
    have hsecond := hfirst.derivative index
    simpa [ratDerivative, polyZero] using hsecond
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0 (by omega))
      (RatPolyCoeffEqv.add (coordinate 1 (by omega))
        (RatPolyCoeffEqv.add
          (coordinate 2 (by omega)) (coordinate 3 (by omega)))))
    (RatPolyCoeffEqv.zero_add polyZero)

/-- Multiplying a selected-head harmonic polynomial by a head-independent
right factor preserves coefficient-sensitive harmonicity. -/
theorem headLaplacian_mul_blockDegree_zero_right
    (harmonic independent : RatPoly)
    (hharmonic : RatPolyCoeffEqv (headLaplacian harmonic) polyZero)
    (hindependent : HasQuaternionBlockDegree 0 0 independent) :
    RatPolyCoeffEqv
      (headLaplacian (polyMul harmonic independent)) polyZero := by
  have hleft : RatPolyCoeffEqv
      (polyMul (headLaplacian harmonic) independent) polyZero :=
    RatPolyCoeffEqv.trans
      (hharmonic.mul_right independent)
      (RatPolyCoeffEqv.mul_zero_left independent)
  have hgradient : RatPolyCoeffEqv
      (polySmul 2 (headGradientDot harmonic independent)) polyZero :=
    RatPolyCoeffEqv.trans
      ((headGradientDot_headIndependent_right
        harmonic independent hindependent).smul 2)
      (RatPolyCoeffEqv.smul_zero 2)
  have hright : RatPolyCoeffEqv
      (polyMul harmonic (headLaplacian independent)) polyZero :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left harmonic
        (headLaplacian_zero_of_blockDegree_zero
          independent hindependent))
      (RatPolyCoeffEqv.mul_zero_right harmonic)
  exact RatPolyCoeffEqv.trans
    (headLaplacian_mul harmonic independent)
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add hleft
        (RatPolyCoeffEqv.add hgradient hright))
      (RatPolyCoeffEqv.zero_add polyZero))

/-- All positive even-spin solid BF4 zonal modes still vanish after
multiplication by an arbitrary polynomial in the other 115 quaternion
blocks. -/
theorem exposedSolidZonal_even_mul_blockDegree_zero_quaternionHaar_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (k : Nat) (hpositive : 0 < k)
    (multiplier : RatPoly)
    (hindependent : HasQuaternionBlockDegree 0 0 multiplier) :
    quaternionHaar 116
        (polyMul
          (exposedSolidZonalCharacter
            reverse0 reverse1 reverse2 reverse3 (2 * k))
          multiplier) ≈ 0 := by
  let solid := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 (2 * k)
  have hdegree : HasQuaternionBlockDegree 0 (2 * k)
      (polyMul solid multiplier) :=
    HasQuaternionBlockDegree.relabel (by omega)
      ((exposedSolidZonalCharacter_blockDegree
        reverse0 reverse1 reverse2 reverse3 0 (by omega) (2 * k)).mul
        hindependent)
  have hharmonic : RatPolyCoeffEqv
      (headLaplacian (polyMul solid multiplier)) polyZero :=
    headLaplacian_mul_blockDegree_zero_right solid multiplier
      (laplacian_U_solidZonal_AUB_zero
        reverse0 reverse1 reverse2 reverse3 (2 * k))
      hindependent
  exact quaternionHaar_even_homogeneous_eq_zero_of_laplacian
    115 k (polyMul solid multiplier) hpositive hdegree
    (headGaussianLaplacianTail_zero_of_coeffEqv
      115 (polyMul solid multiplier) hharmonic)

/-- Ordinary all-spin BF4 character form of the multiplier theorem. -/
theorem exposedEvenCharacter_mul_blockDegree_zero_quaternionHaar_zero
    (reverse0 reverse1 reverse2 reverse3 : Bool)
    (k : Nat) (hpositive : 0 < k)
    (multiplier : RatPoly)
    (hindependent : HasQuaternionBlockDegree 0 0 multiplier) :
    quaternionHaar 116
        (polyMul
          (characterPolynomial
            (exposedFourWord
              reverse0 reverse1 reverse2 reverse3).scalar (2 * k))
          multiplier) ≈ 0 := by
  let solid := exposedSolidZonalCharacter
    reverse0 reverse1 reverse2 reverse3 (2 * k)
  let ordinary := characterPolynomial
    (exposedFourWord reverse0 reverse1 reverse2 reverse3).scalar (2 * k)
  have hcarrier := exposedSolidZonalCharacter_eq_character_116
    reverse0 reverse1 reverse2 reverse3 (2 * k) multiplier
  exact Q'.eqv_trans _
    (quaternionHaar 116 (polyMul multiplier ordinary)) _
    (quaternionHaar_polyMul_comm 116 ordinary multiplier)
    (Q'.eqv_trans _
      (quaternionHaar 116 (polyMul multiplier solid)) _
      (Q'.eqv_symm hcarrier)
      (Q'.eqv_trans _
        (quaternionHaar 116 (polyMul solid multiplier)) _
        (quaternionHaar_polyMul_comm 116 multiplier solid)
        (exposedSolidZonal_even_mul_blockDegree_zero_quaternionHaar_zero
          reverse0 reverse1 reverse2 reverse3 k hpositive
          multiplier hindependent)))

end YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headGaussianTail_eq_ratWeightedSum
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headGaussianSecondProbeSum_eq_laplacianMono
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headGaussianTail_headLaplacian
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headGaussianLaplacianTail_zero_of_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.exposedSolidZonal_headGaussianLaplacianTail_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.exposedSolidZonal_even_quaternionHaar_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.exposedEvenCharacter_quaternionHaar_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headLaplacian_zero_of_blockDegree_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.headLaplacian_mul_blockDegree_zero_right
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.exposedSolidZonal_even_mul_blockDegree_zero_quaternionHaar_zero
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport.exposedEvenCharacter_mul_blockDegree_zero_quaternionHaar_zero
