/-
# Exact coordinate pullback for finite Gaussian rows

This leaf starts from an explicit rational coordinate factor `transform` from
independent finite Gaussian noise coordinates to physical coordinates.  It
proves that the computed Gram of two pulled rational rows is exactly the
physical bilinear form with covariance factor `transform * transform^T`.
The already checked three-color radial covariance theorem then gives the exact
factor `60` for these pulled rows.

Consumer: the finite coordinate-space alternative in the adaptive-score
audit, where a rational finite covariance factor may avoid irrational Fourier
mode rows.  This module constructs no Gaussian density or Jacobian, proves no
pushforward-law identity, and supplies no inverse/precision, cutoff-uniform,
compact-Haar, interacting, continuum, or physical mass-gap statement.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem qListSum_congr {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≈ g i) :
    qListSum (ids.map f) ≈ qListSum (ids.map g) := by
  induction ids with
  | nil => exact Q'.eqv_refl _
  | cons i ids ih =>
      exact Q'.add_eqv_congr' (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem qListSum_add {A : Type} (ids : List A) (f g : A → Q') :
    qListSum (ids.map (fun i => f i + g i)) ≈
      qListSum (ids.map f) + qListSum (ids.map g) := by
  induction ids with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => f i
            | 1 => g i
            | 2 => qListSum (ids.map f)
            | _ => qListSum (ids.map g)))

private theorem qListSum_scale_left {A : Type} (ids : List A)
    (f : A → Q') (scalar : Q') :
    qListSum (ids.map (fun i => scalar * f i)) ≈
      scalar * qListSum (ids.map f) := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv scalar)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem qListSum_scale_right {A : Type} (ids : List A)
    (f : A → Q') (scalar : Q') :
    qListSum (ids.map (fun i => f i * scalar)) ≈
      qListSum (ids.map f) * scalar := by
  exact Q'.eqv_trans _ _ _
    (qListSum_congr ids _ _ (fun i _ => Q'.mul_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (qListSum_scale_left ids f scalar)
      (Q'.mul_comm_eqv _ _))

private theorem qListSum_product {A B : Type} (left : List A) (right : List B)
    (f : A → Q') (g : B → Q') :
    qListSum (left.map f) * qListSum (right.map g) ≈
      qListSum (left.map fun i =>
        qListSum (right.map fun j => f i * g j)) := by
  refine Q'.eqv_trans _
    (qListSum (left.map fun i => f i * qListSum (right.map g))) _
    (Q'.eqv_symm (qListSum_scale_right left f (qListSum (right.map g)))) ?_
  exact qListSum_congr left _ _ (fun i _ =>
    Q'.eqv_symm (qListSum_scale_left right g (f i)))

private theorem qListSum_swap {A B : Type} (left : List A) (right : List B)
    (f : A → B → Q') :
    qListSum (left.map fun i => qListSum (right.map fun j => f i j)) ≈
      qListSum (right.map fun j => qListSum (left.map fun i => f i j)) := by
  induction left with
  | nil =>
      induction right with
      | nil => exact Q'.eqv_refl _
      | cons j rest ih =>
          change (0 : Q') ≈ 0 + qListSum (rest.map fun _ => (0 : Q'))
          exact Q'.eqv_trans _ _ _ ih
            (Q'.eqv_symm (QPoly.q_zero_add_eqv _))
  | cons i rest ih =>
      change
        qListSum (right.map fun j => f i j) +
            qListSum (rest.map fun k => qListSum (right.map fun j => f k j)) ≈
          qListSum (right.map fun j =>
            f i j + qListSum (rest.map fun k => f k j))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (Q'.eqv_symm (qListSum_add right (fun j => f i j)
          (fun j => qListSum (rest.map fun k => f k j))))

/-- Pull a physical rational row back to independent noise coordinates. -/
def pulledRow (physicalSize : Nat) (transform : Nat → Nat → Q')
    (physicalRow : Nat → Q') (noiseIndex : Nat) : Q' :=
  qListSum ((List.range physicalSize).map fun physicalIndex =>
    physicalRow physicalIndex * transform physicalIndex noiseIndex)

/-- Covariance factor induced by the explicit finite coordinate transform. -/
def factorCovariance (noiseSize : Nat) (transform : Nat → Nat → Q')
    (left right : Nat) : Q' :=
  qListSum ((List.range noiseSize).map fun noiseIndex =>
    transform left noiseIndex * transform right noiseIndex)

/-- Physical-row bilinear form generated by the covariance factor. -/
def physicalCovarianceBilinear (physicalSize noiseSize : Nat)
    (transform : Nat → Nat → Q') (leftRow rightRow : Nat → Q') : Q' :=
  qListSum ((List.range physicalSize).map fun left =>
    qListSum ((List.range physicalSize).map fun right =>
      (leftRow left * rightRow right) * factorCovariance noiseSize transform left right))

private def pullbackTerm (transform : Nat → Nat → Q')
    (leftRow rightRow : Nat → Q') (left right noise : Nat) : Q' :=
  (leftRow left * transform left noise) *
    (rightRow right * transform right noise)

/-- The noise-coordinate Gram equals the physical bilinear form with factor
`transform * transform^T`, by finite distributivity and Fubini alone. -/
theorem finiteRowGram_pulledRow (physicalSize noiseSize : Nat)
    (transform : Nat → Nat → Q') (leftRow rightRow : Nat → Q') :
    finiteRowGram noiseSize
        (pulledRow physicalSize transform leftRow)
        (pulledRow physicalSize transform rightRow) ≈
      physicalCovarianceBilinear physicalSize noiseSize
        transform leftRow rightRow := by
  let physical := List.range physicalSize
  let noise := List.range noiseSize
  have hexpand :
      finiteRowGram noiseSize
          (pulledRow physicalSize transform leftRow)
          (pulledRow physicalSize transform rightRow) ≈
        qListSum (noise.map fun k =>
          qListSum (physical.map fun i =>
            qListSum (physical.map fun j =>
              pullbackTerm transform leftRow rightRow i j k))) := by
    unfold finiteRowGram pulledRow
    exact qListSum_congr noise _ _ (fun k _ =>
      qListSum_product physical physical
        (fun i => leftRow i * transform i k)
        (fun j => rightRow j * transform j k))
  have hswapNoiseLeft :
      qListSum (noise.map fun k =>
          qListSum (physical.map fun i =>
            qListSum (physical.map fun j =>
              pullbackTerm transform leftRow rightRow i j k))) ≈
        qListSum (physical.map fun i =>
          qListSum (noise.map fun k =>
            qListSum (physical.map fun j =>
              pullbackTerm transform leftRow rightRow i j k))) :=
    qListSum_swap noise physical (fun k i =>
      qListSum (physical.map fun j =>
        pullbackTerm transform leftRow rightRow i j k))
  have hswapNoiseRight :
      qListSum (physical.map fun i =>
          qListSum (noise.map fun k =>
            qListSum (physical.map fun j =>
              pullbackTerm transform leftRow rightRow i j k))) ≈
        qListSum (physical.map fun i =>
          qListSum (physical.map fun j =>
            qListSum (noise.map fun k =>
              pullbackTerm transform leftRow rightRow i j k))) := by
    exact qListSum_congr physical _ _ (fun i _ =>
      qListSum_swap noise physical (fun k j =>
        pullbackTerm transform leftRow rightRow i j k))
  have hfactor :
      qListSum (physical.map fun i =>
          qListSum (physical.map fun j =>
            qListSum (noise.map fun k =>
              pullbackTerm transform leftRow rightRow i j k))) ≈
        physicalCovarianceBilinear physicalSize noiseSize
          transform leftRow rightRow := by
    unfold physicalCovarianceBilinear factorCovariance
    exact qListSum_congr physical _ _ (fun i _ =>
      qListSum_congr physical _ _ (fun j _ =>
        Q'.eqv_trans _ _ _
          (qListSum_congr noise _ _ (fun k _ =>
            poly_identity_of_normal_eq
              (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
              (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
              (by decide) (fun
                | 0 => leftRow i
                | 1 => transform i k
                | 2 => rightRow j
                | _ => transform j k)))
          (qListSum_scale_left noise
            (fun k => transform i k * transform j k)
            (leftRow i * rightRow j))))
  exact Q'.eqv_trans _ _ _ hexpand
    (Q'.eqv_trans _ _ _ hswapNoiseLeft
      (Q'.eqv_trans _ _ _ hswapNoiseRight hfactor))

/-- The pulled squared row norm is the corresponding physical covariance
quadratic. -/
theorem finiteRowNorm2_pulledRow (physicalSize noiseSize : Nat)
    (transform : Nat → Nat → Q') (row : Nat → Q') :
    finiteRowNorm2 noiseSize (pulledRow physicalSize transform row) ≈
      physicalCovarianceBilinear physicalSize noiseSize transform row row := by
  exact Q'.eqv_trans _ _ _ (Q'.eqv_refl _)
    (finiteRowGram_pulledRow physicalSize noiseSize transform row row)

/-- Exact three-color radial covariance for rows pulled through an explicit
finite rational coordinate factor. -/
theorem finiteGaussianRadialCovariance_threeColorPulledRows
    (physicalSize noiseSize : Nat) (transform : Nat → Nat → Q')
    (b d : Nat → Q') :
    finiteGaussianCovariance (noiseSize + (noiseSize + noiseSize))
      (polyMul
        (finiteGaussianRadialSquare (noiseSize + (noiseSize + noiseSize)) 3
          (threeColorRows noiseSize (pulledRow physicalSize transform b)))
        (finiteGaussianRadialSquare (noiseSize + (noiseSize + noiseSize)) 3
          (threeColorRows noiseSize (pulledRow physicalSize transform b))))
      (finiteGaussianRadialSquare (noiseSize + (noiseSize + noiseSize)) 3
        (threeColorRows noiseSize (pulledRow physicalSize transform d))) ≈
      60 * physicalCovarianceBilinear physicalSize noiseSize transform b b *
        (physicalCovarianceBilinear physicalSize noiseSize transform b d *
          physicalCovarianceBilinear physicalSize noiseSize transform b d) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianRadialCovariance_threeColorRows noiseSize
      (pulledRow physicalSize transform b)
      (pulledRow physicalSize transform d))
    (mul_congr
      (mul_congr (Q'.eqv_refl _)
        (finiteRowNorm2_pulledRow physicalSize noiseSize transform b))
      (mul_congr
        (finiteRowGram_pulledRow physicalSize noiseSize transform b d)
        (finiteRowGram_pulledRow physicalSize noiseSize transform b d)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback.finiteRowGram_pulledRow
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback.finiteRowNorm2_pulledRow
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback.finiteGaussianRadialCovariance_threeColorPulledRows
