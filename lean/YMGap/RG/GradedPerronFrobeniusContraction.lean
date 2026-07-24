/-
# Graded Perron--Frobenius perturbation of a uniform RG contraction

This module isolates the second half of the proposed Birkhoff--Hopf route to
RG-I7.  The unbranched activity sector supplies a uniform base contraction.
The kappa-graded sector is allowed to perturb one RG step, provided its
pairwise projective distortion is dominated by an explicit error whose
budget is

    kappaConstant * kappaScale^64.

The main constructor turns these data into the literal
`UniformContractionCertificate` consumed by the existing RG-I7--I9
composition layer, with rate

    q_total = q_base + kappaConstant * kappaScale^64 < 1.

No Birkhoff--Hopf theorem, local fusion estimate, landing theorem, or
summability estimate is assumed or manufactured here.  The base contraction
and the graded comparison are explicit input structures.  What is closed is
the dimension-free graded Perron--Frobenius algebra: once those two estimates
are supplied, the full step contracts at the stated common rational rate.

## Axiom gate

Constructive exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, quotient, or noncomputable declaration is used.
-/

import YMGap.RG.StableDynamics

namespace YMGap.RG.GradedPerronFrobeniusContraction

open YMGap.Constructive
open YMGap.RG.StableDynamics

universe u v

local infix:50 " ≈ " => Q'.eqv

private theorem add_mul_eqv_local (left right factor : Q') :
    (left + right) * factor ≈
      left * factor + right * factor := by
  refine Q'.eqv_trans _ (factor * (left + right)) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ (factor * left + factor * right) _
    (Q'.mul_add_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (left * factor + factor * right) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv _ _)
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv _ _)

/-- Proof-carrying kappa-graded perturbation of a uniform base contraction.

`gradedError` is the actual comparison error.  It may be smaller than the
visible `kappaConstant * kappaScale^64` budget.  The full step need not equal
the base step and no inverse or linearization is requested. -/
structure GradedPerronFrobeniusCertificate (X : Type u) where
  /-- The unbranched Birkhoff/Perron--Frobenius contraction. -/
  base : UniformContractionCertificate.{u, v} X
  /-- The physical step including the kappa-graded sector. -/
  fullStep : Nat → X → X
  /-- The graded small parameter. -/
  kappaScale : Q'
  kappaScaleNonnegative : (0 : Q') ≤ kappaScale
  /-- Uniform coefficient multiplying the sixty-fourth grade. -/
  kappaConstant : Q'
  kappaConstantNonnegative : (0 : Q') ≤ kappaConstant
  /-- Actual pairwise perturbation coefficient. -/
  gradedError : Q'
  gradedErrorNonnegative : (0 : Q') ≤ gradedError
  /-- The actual perturbation is dominated by the sixty-fourth-grade budget. -/
  gradedError_le :
    gradedError ≤ kappaConstant * kappaScale ^ 64
  /-- The base rate plus the visible graded budget remains strictly subunit. -/
  totalRateBelowOne :
    base.q + kappaConstant * kappaScale ^ 64 < (1 : Q')
  /-- The full physical step preserves the same admissible cone domain. -/
  fullStepAdmissible :
    ∀ n x, base.Admissible x → base.Admissible (fullStep n x)
  /-- Pairwise full-step distortion is bounded by the base image distance
  plus the actual graded error times the incoming distance. -/
  gradedComparison :
    ∀ n x y, base.Admissible x → base.Admissible y →
      base.distance (fullStep n x) (fullStep n y) ≤
        base.distance (base.step n x) (base.step n y) +
          gradedError * base.distance x y

namespace GradedPerronFrobeniusCertificate

/-- The explicit visible kappa-sector error budget. -/
def gradedBudget {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) : Q' :=
  certificate.kappaConstant * certificate.kappaScale ^ 64

theorem gradedBudget_nonnegative {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) :
    (0 : Q') ≤ certificate.gradedBudget :=
  Q'.mul_nonneg _ _
    certificate.kappaConstantNonnegative
    (Q'.pow_nonneg _ certificate.kappaScaleNonnegative 64)

/-- The full contraction rate after adding the sixty-fourth-grade sector. -/
def totalRate {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) : Q' :=
  certificate.base.q + certificate.gradedBudget

theorem totalRate_nonnegative {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) :
    (0 : Q') ≤ certificate.totalRate :=
  Q'.zero_le_add _ _
    certificate.base.qNonnegative
    certificate.gradedBudget_nonnegative

theorem totalRate_lt_one {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) :
    certificate.totalRate < (1 : Q') :=
  certificate.totalRateBelowOne

/-- The load-bearing graded Perron--Frobenius estimate. -/
theorem fullStep_contracts {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X)
    (n : Nat) (x y : X)
    (hx : certificate.base.Admissible x)
    (hy : certificate.base.Admissible y) :
    certificate.base.distance
        (certificate.fullStep n x) (certificate.fullStep n y) ≤
      certificate.totalRate *
        certificate.base.distance x y := by
  let incoming := certificate.base.distance x y
  let baseImage :=
    certificate.base.distance
      (certificate.base.step n x) (certificate.base.step n y)
  have hcomparison :
      certificate.base.distance
          (certificate.fullStep n x) (certificate.fullStep n y) ≤
        baseImage + certificate.gradedError * incoming :=
    certificate.gradedComparison n x y hx hy
  have herrorScaled :
      certificate.gradedError * incoming ≤
        certificate.gradedBudget * incoming :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      certificate.gradedError_le
      (certificate.base.distanceNonnegative x y)
  have hreplaceError :
      baseImage + certificate.gradedError * incoming ≤
        baseImage + certificate.gradedBudget * incoming :=
    Q'.add_le_add_left _ _ _
      herrorScaled
  have hbase :
      baseImage ≤ certificate.base.q * incoming :=
    certificate.base.contracts n x y hx hy
  have hreplaceBase :
      baseImage + certificate.gradedBudget * incoming ≤
        certificate.base.q * incoming +
          certificate.gradedBudget * incoming :=
    Q'.add_le_add_right _ _ _
      hbase
  have hregroup :
      certificate.base.q * incoming +
          certificate.gradedBudget * incoming ≈
        certificate.totalRate * incoming := by
    exact Q'.eqv_symm
      (add_mul_eqv_local
        certificate.base.q certificate.gradedBudget incoming)
  exact Q'.le_trans' _ _ _ hcomparison
    (Q'.le_trans' _ _ _ hreplaceError
      (Q'.le_trans' _ _ _ hreplaceBase
        (Q'.le_of_eqv hregroup)))

/-- Export the graded physical step as the exact uniform contraction
certificate consumed by `StableDynamicsCertificate`. -/
def toUniformContractionCertificate {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) :
    UniformContractionCertificate.{u, v} X where
  distance := certificate.base.distance
  Admissible := certificate.base.Admissible
  step := certificate.fullStep
  q := certificate.totalRate
  qNonnegative := certificate.totalRate_nonnegative
  qBelowOne := certificate.totalRate_lt_one
  distanceNonnegative := certificate.base.distanceNonnegative
  stepAdmissible := certificate.fullStepAdmissible
  contracts := certificate.fullStep_contracts

theorem exported_rate_eq {X : Type u}
    (certificate : GradedPerronFrobeniusCertificate.{u, v} X) :
    certificate.toUniformContractionCertificate.q =
      certificate.base.q +
        certificate.kappaConstant * certificate.kappaScale ^ 64 :=
  rfl

end GradedPerronFrobeniusCertificate

#print axioms GradedPerronFrobeniusCertificate.gradedBudget_nonnegative
#print axioms GradedPerronFrobeniusCertificate.fullStep_contracts
#print axioms GradedPerronFrobeniusCertificate.toUniformContractionCertificate
#print axioms GradedPerronFrobeniusCertificate.exported_rate_eq

end YMGap.RG.GradedPerronFrobeniusContraction
