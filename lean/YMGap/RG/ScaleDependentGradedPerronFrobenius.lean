/-
# Scale-dependent graded Perron--Frobenius contraction

This is the spacing-aware form of the graded Perron--Frobenius gate.  The
unbranched positive sector may have a microscopic Birkhoff rate `q_n` tending
to one.  At scale `n`, the kappa-graded sector contributes an actual
projective comparison error bounded by

    kappaConstant * kappaScale(n)^64.

The full microscopic rate is therefore

    q_n + kappaConstant * kappaScale(n)^64.

The constructor below exports a literal
`ScaleDependentContractionCertificate`.  Its rate products can then be
passed to `GroupedContractionDoor`, where the uniform statement is made over
fixed physical distances rather than individual lattice steps.

No local Birkhoff diameter, physical kappa comparison, grouped-product bound,
landing theorem, or summable remainder estimate is manufactured here.  Those
remain explicit analytic inputs.

## Axiom gate

Constructive exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, quotient, or noncomputable declaration is used.
-/

import YMGap.RG.ScaleDependentGroupedContraction

namespace YMGap.RG.ScaleDependentGradedPerronFrobenius

open YMGap.Constructive
open YMGap.RG.ScaleDependentGroupedContraction

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

/-- Proof-carrying graded perturbation of a scale-dependent positive
microscopic contraction. -/
structure ScaleDependentGradedCertificate (X : Type u) where
  base : ScaleDependentContractionCertificate.{u, v} X
  fullStep : Nat → X → X
  kappaScale : Nat → Q'
  kappaScaleNonnegative : ∀ n, (0 : Q') ≤ kappaScale n
  kappaConstant : Q'
  kappaConstantNonnegative : (0 : Q') ≤ kappaConstant
  gradedError : Nat → Q'
  gradedErrorNonnegative : ∀ n, (0 : Q') ≤ gradedError n
  gradedError_le :
    ∀ n, gradedError n ≤ kappaConstant * kappaScale n ^ 64
  totalRateBelowOne :
    ∀ n, base.rate n + kappaConstant * kappaScale n ^ 64 < (1 : Q')
  fullStepAdmissible :
    ∀ n x, base.Admissible x → base.Admissible (fullStep n x)
  gradedComparison :
    ∀ n x y, base.Admissible x → base.Admissible y →
      base.distance (fullStep n x) (fullStep n y) ≤
        base.distance (base.step n x) (base.step n y) +
          gradedError n * base.distance x y

namespace ScaleDependentGradedCertificate

def gradedBudget {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) : Q' :=
  certificate.kappaConstant * certificate.kappaScale n ^ 64

theorem gradedBudget_nonnegative {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) :
    (0 : Q') ≤ certificate.gradedBudget n :=
  Q'.mul_nonneg _ _
    certificate.kappaConstantNonnegative
    (Q'.pow_nonneg _
      (certificate.kappaScaleNonnegative n) 64)

def totalRate {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) : Q' :=
  certificate.base.rate n + certificate.gradedBudget n

theorem totalRate_nonnegative {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) :
    (0 : Q') ≤ certificate.totalRate n :=
  Q'.zero_le_add _ _
    (certificate.base.rateNonnegative n)
    (certificate.gradedBudget_nonnegative n)

theorem totalRate_lt_one {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) :
    certificate.totalRate n < (1 : Q') :=
  certificate.totalRateBelowOne n

/-- The full physical microscopic step contracts at the base Birkhoff rate
plus the visible sixty-fourth-grade budget. -/
theorem fullStep_contracts {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) (x y : X)
    (hx : certificate.base.Admissible x)
    (hy : certificate.base.Admissible y) :
    certificate.base.distance
        (certificate.fullStep n x) (certificate.fullStep n y) ≤
      certificate.totalRate n * certificate.base.distance x y := by
  let incoming := certificate.base.distance x y
  let baseImage :=
    certificate.base.distance
      (certificate.base.step n x) (certificate.base.step n y)
  have hcomparison :
      certificate.base.distance
          (certificate.fullStep n x) (certificate.fullStep n y) ≤
        baseImage + certificate.gradedError n * incoming :=
    certificate.gradedComparison n x y hx hy
  have herrorScaled :
      certificate.gradedError n * incoming ≤
        certificate.gradedBudget n * incoming :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (certificate.gradedError_le n)
      (certificate.base.distanceNonnegative x y)
  have hreplaceError :
      baseImage + certificate.gradedError n * incoming ≤
        baseImage + certificate.gradedBudget n * incoming :=
    Q'.add_le_add_left _ _ _ herrorScaled
  have hbase :
      baseImage ≤ certificate.base.rate n * incoming :=
    certificate.base.contracts n x y hx hy
  have hreplaceBase :
      baseImage + certificate.gradedBudget n * incoming ≤
        certificate.base.rate n * incoming +
          certificate.gradedBudget n * incoming :=
    Q'.add_le_add_right _ _ _ hbase
  have hregroup :
      certificate.base.rate n * incoming +
          certificate.gradedBudget n * incoming ≈
        certificate.totalRate n * incoming :=
    Q'.eqv_symm
      (add_mul_eqv_local
        (certificate.base.rate n)
        (certificate.gradedBudget n) incoming)
  exact Q'.le_trans' _ _ _ hcomparison
    (Q'.le_trans' _ _ _ hreplaceError
      (Q'.le_trans' _ _ _ hreplaceBase
        (Q'.le_of_eqv hregroup)))

/-- Export the full graded microscopic dynamics for exact rate-product
grouping. -/
def toScaleDependentContractionCertificate {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X) :
    ScaleDependentContractionCertificate.{u, v} X where
  distance := certificate.base.distance
  Admissible := certificate.base.Admissible
  step := certificate.fullStep
  rate := certificate.totalRate
  rateNonnegative := certificate.totalRate_nonnegative
  rateBelowOne := certificate.totalRate_lt_one
  distanceNonnegative := certificate.base.distanceNonnegative
  stepAdmissible := certificate.fullStepAdmissible
  contracts := certificate.fullStep_contracts

theorem exported_rate_eq {X : Type u}
    (certificate : ScaleDependentGradedCertificate.{u, v} X)
    (n : Nat) :
    certificate.toScaleDependentContractionCertificate.rate n =
      certificate.base.rate n +
        certificate.kappaConstant * certificate.kappaScale n ^ 64 :=
  rfl

end ScaleDependentGradedCertificate

#print axioms ScaleDependentGradedCertificate.gradedBudget_nonnegative
#print axioms ScaleDependentGradedCertificate.fullStep_contracts
#print axioms ScaleDependentGradedCertificate.toScaleDependentContractionCertificate
#print axioms ScaleDependentGradedCertificate.exported_rate_eq

end YMGap.RG.ScaleDependentGradedPerronFrobenius
