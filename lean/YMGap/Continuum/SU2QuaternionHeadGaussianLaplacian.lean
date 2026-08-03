/-
# Gaussian Euler--Laplacian annihilation in one quaternion block

This file lifts the four exact Gaussian moment recurrences to a polynomial
identity with every tail quaternion retained.  For a head-homogeneous
polynomial `P` of positive degree `d`,

  d E_G[P] = E_G[Delta_head P].

Consequently a zero Gaussian Laplacian moment forces the selected Gaussian
mean, and hence (by the common radial factor theorem) the exact product-Haar
mean, to vanish.  This isolates the remaining representation-theoretic task:
prove that the solid zonal BF4 character has zero head Laplacian.
-/

import YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
import YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

namespace YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian

local infix:50 " ≈ " => Q'.eqv

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

private theorem ofNat_add_eqv (a b : Nat) :
    Q'.ofNat (a + b) ≈ Q'.ofNat a + Q'.ofNat b := by
  show ((a + b : Nat) : Int) *
      ((Q'.ofNat a + Q'.ofNat b).den : Int) =
    (Q'.ofNat a + Q'.ofNat b).num *
      ((Q'.ofNat (a + b)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  push_cast
  omega

private theorem gaussian_second0 (e0 e1 e2 e3 : Nat) :
    Q'.ofNat e0 * gaussianMoment4 e0 e1 e2 e3 ≈
      Q'.ofNat (e0 * (e0 - 1)) *
        gaussianMoment4 (e0 - 2) e1 e2 e3 := by
  cases e0 with
  | zero =>
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ e0 =>
      cases e0 with
      | zero =>
          have hodd : gaussianMoment4 1 e1 e2 e3 = 0 := by
            simp [gaussianMoment4]
          rw [hodd]
          exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
            (Q'.eqv_symm (Q'.zero_mul_eqv _))
      | succ e0 =>
          have hshift := gaussianMoment4_shift0 e0 e1 e2 e3
          refine Q'.eqv_trans _
            (Q'.ofNat (e0 + 2) *
              (Q'.ofNat (e0 + 1) *
                gaussianMoment4 e0 e1 e2 e3)) _
            (Q'.mul_eqv_congr_left _ _ _ hshift) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (e0 + 2) * Q'.ofNat (e0 + 1)) *
              gaussianMoment4 e0 e1 e2 e3) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (ofNat_mul_eqv (e0 + 2) (e0 + 1)))

private theorem gaussian_second1 (e0 e1 e2 e3 : Nat) :
    Q'.ofNat e1 * gaussianMoment4 e0 e1 e2 e3 ≈
      Q'.ofNat (e1 * (e1 - 1)) *
        gaussianMoment4 e0 (e1 - 2) e2 e3 := by
  cases e1 with
  | zero =>
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ e1 =>
      cases e1 with
      | zero =>
          have hodd : gaussianMoment4 e0 1 e2 e3 = 0 := by
            simp [gaussianMoment4]
          rw [hodd]
          exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
            (Q'.eqv_symm (Q'.zero_mul_eqv _))
      | succ e1 =>
          have hshift := gaussianMoment4_shift1 e0 e1 e2 e3
          refine Q'.eqv_trans _
            (Q'.ofNat (e1 + 2) *
              (Q'.ofNat (e1 + 1) *
                gaussianMoment4 e0 e1 e2 e3)) _
            (Q'.mul_eqv_congr_left _ _ _ hshift) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (e1 + 2) * Q'.ofNat (e1 + 1)) *
              gaussianMoment4 e0 e1 e2 e3) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (ofNat_mul_eqv (e1 + 2) (e1 + 1)))

private theorem gaussian_second2 (e0 e1 e2 e3 : Nat) :
    Q'.ofNat e2 * gaussianMoment4 e0 e1 e2 e3 ≈
      Q'.ofNat (e2 * (e2 - 1)) *
        gaussianMoment4 e0 e1 (e2 - 2) e3 := by
  cases e2 with
  | zero =>
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ e2 =>
      cases e2 with
      | zero =>
          have hodd : gaussianMoment4 e0 e1 1 e3 = 0 := by
            simp [gaussianMoment4]
          rw [hodd]
          exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
            (Q'.eqv_symm (Q'.zero_mul_eqv _))
      | succ e2 =>
          have hshift := gaussianMoment4_shift2 e0 e1 e2 e3
          refine Q'.eqv_trans _
            (Q'.ofNat (e2 + 2) *
              (Q'.ofNat (e2 + 1) *
                gaussianMoment4 e0 e1 e2 e3)) _
            (Q'.mul_eqv_congr_left _ _ _ hshift) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (e2 + 2) * Q'.ofNat (e2 + 1)) *
              gaussianMoment4 e0 e1 e2 e3) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (ofNat_mul_eqv (e2 + 2) (e2 + 1)))

private theorem gaussian_second3 (e0 e1 e2 e3 : Nat) :
    Q'.ofNat e3 * gaussianMoment4 e0 e1 e2 e3 ≈
      Q'.ofNat (e3 * (e3 - 1)) *
        gaussianMoment4 e0 e1 e2 (e3 - 2) := by
  cases e3 with
  | zero =>
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ e3 =>
      cases e3 with
      | zero =>
          have hodd : gaussianMoment4 e0 e1 e2 1 = 0 := by
            simp [gaussianMoment4]
          rw [hodd]
          exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
            (Q'.eqv_symm (Q'.zero_mul_eqv _))
      | succ e3 =>
          have hshift := gaussianMoment4_shift3 e0 e1 e2 e3
          refine Q'.eqv_trans _
            (Q'.ofNat (e3 + 2) *
              (Q'.ofNat (e3 + 1) *
                gaussianMoment4 e0 e1 e2 e3)) _
            (Q'.mul_eqv_congr_left _ _ _ hshift) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (e3 + 2) * Q'.ofNat (e3 + 1)) *
              gaussianMoment4 e0 e1 e2 e3) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (ofNat_mul_eqv (e3 + 2) (e3 + 1)))

/-- Gaussian expectation of the formal head Laplacian of one monomial. -/
def headGaussianLaplacianMoment (monomial : List Nat) : Q' :=
  let e0 := exponentAt monomial 0
  let e1 := exponentAt monomial 1
  let e2 := exponentAt monomial 2
  let e3 := exponentAt monomial 3
  Q'.ofNat (e0 * (e0 - 1)) *
      gaussianMoment4 (e0 - 2) e1 e2 e3 +
    (Q'.ofNat (e1 * (e1 - 1)) *
        gaussianMoment4 e0 (e1 - 2) e2 e3 +
      (Q'.ofNat (e2 * (e2 - 1)) *
          gaussianMoment4 e0 e1 (e2 - 2) e3 +
        Q'.ofNat (e3 * (e3 - 1)) *
          gaussianMoment4 e0 e1 e2 (e3 - 2)))

/-- Monomial Euler--Gaussian-IBP identity in four coordinates. -/
theorem degree_mul_headGaussianMoment_eq_laplacian
    (monomial : List Nat) :
    Q'.ofNat (quaternionBlockDegree monomial 0) *
        headGaussianMoment monomial ≈
      headGaussianLaplacianMoment monomial := by
  let e0 := exponentAt monomial 0
  let e1 := exponentAt monomial 1
  let e2 := exponentAt monomial 2
  let e3 := exponentAt monomial 3
  let g := gaussianMoment4 e0 e1 e2 e3
  have hsum : quaternionBlockDegree monomial 0 = e0 + (e1 + (e2 + e3)) := by
    simp only [quaternionBlockDegree, e0, e1, e2, e3, Nat.mul_zero,
      Nat.zero_add]
    omega
  rw [hsum]
  unfold headGaussianMoment headGaussianLaplacianMoment
  change Q'.ofNat (e0 + (e1 + (e2 + e3))) * g ≈ _
  refine Q'.eqv_trans _
    ((Q'.ofNat e0 +
      (Q'.ofNat e1 + (Q'.ofNat e2 + Q'.ofNat e3))) * g) _ ?_ ?_
  · apply Q'.mul_eqv_congr_right
    exact Q'.eqv_trans _
      (Q'.ofNat e0 + Q'.ofNat (e1 + (e2 + e3))) _
      (ofNat_add_eqv e0 (e1 + (e2 + e3)))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _
          (Q'.ofNat e1 + Q'.ofNat (e2 + e3)) _
          (ofNat_add_eqv e1 (e2 + e3))
          (Q'.add_eqv_congr_left _ _ _ (ofNat_add_eqv e2 e3))))
  · refine Q'.eqv_trans _
      (Q'.ofNat e0 * g +
        (Q'.ofNat e1 * g +
          (Q'.ofNat e2 * g + Q'.ofNat e3 * g))) _ ?_ ?_
    · exact Q'.eqv_trans _
        (Q'.ofNat e0 * g +
          (Q'.ofNat e1 + (Q'.ofNat e2 + Q'.ofNat e3)) * g) _
        (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _
            (Q'.ofNat e1 * g +
              (Q'.ofNat e2 + Q'.ofNat e3) * g) _
            (Q'.add_mul_eqv _ _ _)
            (Q'.add_eqv_congr_left _ _ _ (Q'.add_mul_eqv _ _ _))))
    · exact Q'.add_eqv_congr'
        (gaussian_second0 e0 e1 e2 e3)
        (Q'.add_eqv_congr'
          (gaussian_second1 e0 e1 e2 e3)
          (Q'.add_eqv_congr'
            (gaussian_second2 e0 e1 e2 e3)
            (gaussian_second3 e0 e1 e2 e3)))

/-- Laplacian Gaussian moment with arbitrary retained tail Haar factors. -/
def headGaussianLaplacianTailMono
    (tailBlocks : Nat) (monomial : List Nat) : Q' :=
  headGaussianLaplacianMoment monomial *
    quaternionHaarMono tailBlocks (monomial.drop 4)

def headGaussianLaplacianTail (tailBlocks : Nat) : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 * headGaussianLaplacianTailMono tailBlocks term.1 +
        headGaussianLaplacianTail tailBlocks rest

/-- Polynomial Euler--Laplacian identity with all tail coefficients retained. -/
theorem degree_mul_headGaussianTail_eq_laplacian
    (tailBlocks degree : Nat) : ∀ polynomial : RatPoly,
    HasQuaternionBlockDegree 0 degree polynomial →
    Q'.ofNat degree * headGaussianTail tailBlocks polynomial ≈
      headGaussianLaplacianTail tailBlocks polynomial
  | [], _ => Q'.mul_zero_eqv _
  | term :: rest, hdegree => by
      have hterm := hdegree term List.mem_cons_self
      have hrest : HasQuaternionBlockDegree 0 degree rest := by
        intro other hother
        exact hdegree other (List.mem_cons_of_mem term hother)
      change Q'.ofNat degree *
          (term.2 * headGaussianTailMono tailBlocks term.1 +
            headGaussianTail tailBlocks rest) ≈
        term.2 * headGaussianLaplacianTailMono tailBlocks term.1 +
          headGaussianLaplacianTail tailBlocks rest
      refine Q'.eqv_trans _
        (Q'.ofNat degree *
            (term.2 * headGaussianTailMono tailBlocks term.1) +
          Q'.ofNat degree * headGaussianTail tailBlocks rest) _
        (Q'.mul_add_eqv _ _ _) ?_
      apply Q'.add_eqv_congr'
      · unfold headGaussianTailMono headGaussianLaplacianTailMono
        refine Q'.eqv_trans _
          (term.2 *
            ((Q'.ofNat degree * headGaussianMoment term.1) *
              quaternionHaarMono tailBlocks (term.1.drop 4))) _ ?_ ?_
        · refine Q'.eqv_trans _
            ((Q'.ofNat degree * term.2) *
              (headGaussianMoment term.1 *
                quaternionHaarMono tailBlocks (term.1.drop 4))) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _
            ((term.2 * Q'.ofNat degree) *
              (headGaussianMoment term.1 *
                quaternionHaarMono tailBlocks (term.1.drop 4))) _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
          refine Q'.eqv_trans _
            (term.2 *
              (Q'.ofNat degree *
                (headGaussianMoment term.1 *
                  quaternionHaarMono tailBlocks (term.1.drop 4)))) _
            (Q'.mul_assoc_eqv _ _ _) ?_
          exact Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        · apply Q'.mul_eqv_congr_left
          apply Q'.mul_eqv_congr_right
          rw [← hterm]
          exact degree_mul_headGaussianMoment_eq_laplacian term.1
      · exact degree_mul_headGaussianTail_eq_laplacian
          tailBlocks degree rest hrest

private theorem ofNat_positive {degree : Nat} (hdegree : 0 < degree) :
    (0 : Q') < Q'.ofNat degree := by
  cases degree with
  | zero => omega
  | succ degree => exact Q'.ofNat_succ_pos degree

/-- **Positive-degree homogeneous harmonic annihilation, in moment form.** -/
theorem headGaussianTail_eq_zero_of_laplacian
    (tailBlocks degree : Nat) (polynomial : RatPoly)
    (hpositive : 0 < degree)
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial)
    (hharmonic : headGaussianLaplacianTail tailBlocks polynomial ≈ 0) :
    headGaussianTail tailBlocks polynomial ≈ 0 := by
  apply Q'.mul_eqv_zero_of_pos (ofNat_positive hpositive)
  exact Q'.eqv_trans _ _ _
    (degree_mul_headGaussianTail_eq_laplacian
      tailBlocks degree polynomial hdegree)
    hharmonic

/-- **Even homogeneous harmonic product-Haar annihilation.**  This is the
generic coefficient-retaining theorem needed by every positive even BF4 spin;
only the concrete solid-character Laplacian certificate remains to be supplied. -/
theorem quaternionHaar_even_homogeneous_eq_zero_of_laplacian
    (tailBlocks k : Nat) (polynomial : RatPoly)
    (hpositive : 0 < k)
    (hdegree : HasQuaternionBlockDegree 0 (2 * k) polynomial)
    (hharmonic : headGaussianLaplacianTail tailBlocks polynomial ≈ 0) :
    quaternionHaar (tailBlocks + 1) polynomial ≈ 0 := by
  apply quaternionHaar_eq_zero_of_headGaussianTail tailBlocks k polynomial hdegree
  apply headGaussianTail_eq_zero_of_laplacian
    tailBlocks (2 * k) polynomial (by omega) hdegree hharmonic

end YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian

#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian.degree_mul_headGaussianMoment_eq_laplacian
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian.degree_mul_headGaussianTail_eq_laplacian
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian.quaternionHaar_even_homogeneous_eq_zero_of_laplacian
