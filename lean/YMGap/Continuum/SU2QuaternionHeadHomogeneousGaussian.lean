/-
# Coefficient-retaining head Haar/Gaussian bridge

For a polynomial homogeneous of even degree `2k` in the selected quaternion,
the exact `S^3` moment differs from the standard four-dimensional Gaussian
moment by the single positive radial denominator `sphereFourDenominator k`.
This file proves that statement after all remaining quaternion variables have
been left as arbitrary polynomial coefficients (and, equivalently, after any
number of tail Haar factors have been applied).

This is the radial half of the all-even character normalization.  The
successor theorem is Gaussian annihilation of a positive-degree homogeneous
head-harmonic polynomial.
-/

import YMGap.Continuum.SU2QuaternionSolidZonalCharacter
import YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence
import YMGap.Continuum.SU2QuaternionHaarHeadFubini
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

local infix:50 " ≈ " => Q'.eqv

/-- Standard four-dimensional Gaussian moment of the selected head block. -/
def headGaussianMoment (monomial : List Nat) : Q' :=
  gaussianMoment4
    (exponentAt monomial 0) (exponentAt monomial 1)
    (exponentAt monomial 2) (exponentAt monomial 3)

/-- Gaussian integration in the selected block followed by exact product Haar
integration in `tailBlocks` retained blocks. -/
def headGaussianTailMono (tailBlocks : Nat) (monomial : List Nat) : Q' :=
  headGaussianMoment monomial *
    quaternionHaarMono tailBlocks (monomial.drop 4)

def headGaussianTail (tailBlocks : Nat) : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 * headGaussianTailMono tailBlocks term.1 +
        headGaussianTail tailBlocks rest

/-- For an even homogeneous head monomial, its sphere and Gaussian moments
differ by one common radial denominator.  If any coordinate exponent is odd,
both sides vanish and no division is used. -/
theorem headMoment_mul_commonRadialDenominator
    (monomial : List Nat) (k : Nat)
    (hdegree : quaternionBlockDegree monomial 0 = 2 * k) :
    headQuaternionMoment monomial *
        Q'.ofNat (sphereFourDenominator k) ≈
      headGaussianMoment monomial := by
  let e0 := exponentAt monomial 0
  let e1 := exponentAt monomial 1
  let e2 := exponentAt monomial 2
  let e3 := exponentAt monomial 3
  by_cases heven :
      e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0
  · have hsum : e0 + e1 + e2 + e3 = 2 * k := by
      simpa [e0, e1, e2, e3, quaternionBlockDegree] using hdegree
    have hhalf : halfDegree4 e0 e1 e2 e3 = k := by
      unfold halfDegree4
      omega
    unfold headQuaternionMoment headGaussianMoment
    change sphereMoment4 e0 e1 e2 e3 *
        Q'.ofNat (sphereFourDenominator k) ≈
      gaussianMoment4 e0 e1 e2 e3
    rw [← hhalf]
    exact sphereMoment4_mul_radialDenominator e0 e1 e2 e3
  · have hsphere : sphereMoment4 e0 e1 e2 e3 = 0 := by
      simp [sphereMoment4, heven]
    have hgaussian : gaussianMoment4 e0 e1 e2 e3 = 0 := by
      simp [gaussianMoment4, heven]
    unfold headQuaternionMoment headGaussianMoment
    change sphereMoment4 e0 e1 e2 e3 *
        Q'.ofNat (sphereFourDenominator k) ≈
      gaussianMoment4 e0 e1 e2 e3
    rw [hsphere, hgaussian]
    exact Q'.zero_mul_eqv _

/-- Monomial form of the coefficient-retaining bridge. -/
theorem quaternionHaarMono_mul_commonRadialDenominator
    (tailBlocks : Nat) (monomial : List Nat) (k : Nat)
    (hdegree : quaternionBlockDegree monomial 0 = 2 * k) :
    quaternionHaarMono (tailBlocks + 1) monomial *
        Q'.ofNat (sphereFourDenominator k) ≈
      headGaussianTailMono tailBlocks monomial := by
  let tail := quaternionHaarMono tailBlocks (monomial.drop 4)
  refine Q'.eqv_trans _
    ((headQuaternionMoment monomial * tail) *
      Q'.ofNat (sphereFourDenominator k)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (headMoment_mul_tailHaarMono tailBlocks monomial))) ?_
  refine Q'.eqv_trans _
    ((headQuaternionMoment monomial *
      Q'.ofNat (sphereFourDenominator k)) * tail) _
    (Q'.eqv_trans _
      (headQuaternionMoment monomial *
        (tail * Q'.ofNat (sphereFourDenominator k))) _
      (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _
        (headQuaternionMoment monomial *
          (Q'.ofNat (sphereFourDenominator k) * tail)) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))) ?_
  unfold headGaussianTailMono tail
  exact Q'.mul_eqv_congr_right _ _ _
    (headMoment_mul_commonRadialDenominator monomial k hdegree)

/-- **Polynomial coefficient-retaining radial bridge.**  The remaining
`tailBlocks` are never specialized; all their polynomial coefficients pass
through the induction unchanged. -/
theorem quaternionHaar_mul_commonRadialDenominator
    (tailBlocks k : Nat) : ∀ polynomial : RatPoly,
    HasQuaternionBlockDegree 0 (2 * k) polynomial →
    quaternionHaar (tailBlocks + 1) polynomial *
        Q'.ofNat (sphereFourDenominator k) ≈
      headGaussianTail tailBlocks polynomial
  | [], _ => Q'.zero_mul_eqv _
  | term :: rest, hdegree => by
      have hterm := hdegree term List.mem_cons_self
      have hrest : HasQuaternionBlockDegree 0 (2 * k) rest := by
        intro other hother
        exact hdegree other (List.mem_cons_of_mem term hother)
      change
        (term.2 * quaternionHaarMono (tailBlocks + 1) term.1 +
            quaternionHaar (tailBlocks + 1) rest) *
              Q'.ofNat (sphereFourDenominator k) ≈
          term.2 * headGaussianTailMono tailBlocks term.1 +
            headGaussianTail tailBlocks rest
      refine Q'.eqv_trans _
        ((term.2 * quaternionHaarMono (tailBlocks + 1) term.1) *
            Q'.ofNat (sphereFourDenominator k) +
          quaternionHaar (tailBlocks + 1) rest *
            Q'.ofNat (sphereFourDenominator k)) _
        (Q'.add_mul_eqv _ _ _) ?_
      apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          (term.2 *
            (quaternionHaarMono (tailBlocks + 1) term.1 *
              Q'.ofNat (sphereFourDenominator k))) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        exact Q'.mul_eqv_congr_left term.2 _ _
          (quaternionHaarMono_mul_commonRadialDenominator
            tailBlocks term.1 k hterm)
      · exact quaternionHaar_mul_commonRadialDenominator
          tailBlocks k rest hrest

private theorem radialDenominator_positive (k : Nat) :
    (0 : Q') < Q'.ofNat (sphereFourDenominator k) := by
  cases hD : sphereFourDenominator k with
  | zero =>
      have := sphereFourDenominator_pos k
      omega
  | succ value => exact Q'.ofNat_succ_pos value

/-- Vanishing of the coefficient-retaining Gaussian functional implies exact
vanishing of the full product-Haar functional for every even homogeneous
head polynomial. -/
theorem quaternionHaar_eq_zero_of_headGaussianTail
    (tailBlocks k : Nat) (polynomial : RatPoly)
    (hdegree : HasQuaternionBlockDegree 0 (2 * k) polynomial)
    (hgaussian : headGaussianTail tailBlocks polynomial ≈ 0) :
    quaternionHaar (tailBlocks + 1) polynomial ≈ 0 := by
  have hbridge := quaternionHaar_mul_commonRadialDenominator
    tailBlocks k polynomial hdegree
  have hright :
      quaternionHaar (tailBlocks + 1) polynomial *
          Q'.ofNat (sphereFourDenominator k) ≈ 0 :=
    Q'.eqv_trans _ _ _ hbridge hgaussian
  apply Q'.mul_left_cancel_of_pos (radialDenominator_positive k)
  refine Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1) polynomial *
      Q'.ofNat (sphereFourDenominator k)) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.eqv_trans _ 0 _ hright
    (Q'.eqv_symm (Q'.mul_zero_eqv _))

end YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian

#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian.headMoment_mul_commonRadialDenominator
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian.quaternionHaar_mul_commonRadialDenominator
#print axioms YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian.quaternionHaar_eq_zero_of_headGaussianTail
