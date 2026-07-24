/-
# Core-B physical Bernstein certificate consumer

At the exact physical endpoint `wH = 1/2`, put

  `u = 4 * w^2`.

The physical coupling interval `0 ≤ w ≤ wH` becomes `0 ≤ u ≤ 1`.  Hence an
exact Bernstein presentation of a canonical cell quotient with nonnegative
integer coefficients proves that cell nonnegative on the entire physical
interval.

This file supplies the reusable typed consumer for that proof route:

* positivity of the one-dimensional Bernstein basis over `Q'`;
* positivity of a signed Bernstein evaluation whose integer row is
  coefficientwise nonnegative;
* a certificate interface for one actual canonical quotient cell, including
  a positive denominator-clearing scale and exact reconstruction; and
* the final finite-sum adapter from certificates for every canonical cell to
  `RowOneOriginSquareGapQuotientNonnegative`.

No coefficient row is manufactured here.  In particular, this module does
not inhabit a Bernstein family or close Core B.  The remaining load-bearing
theorem is the all-index nonnegativity and reconstruction of the actual
bounded-selector row.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Constructive.Soundness
import YMGap.Continuum.BernsteinMonomialReconstruction
import YMGap.Continuum.CoreBConsumerOrigin

namespace YMGap.Continuum.CoreBBernsteinConsumer

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.CoreBUniversalSquareGap
open YMGap.Continuum.CoreBConsumerOrigin

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact physical square coordinate -/

/-- The affine square coordinate carrying `[0,wH]` to `[0,1]`. -/
def physicalSquareCoordinate (w : Q') : Q' :=
  (4 : Q') * qpow w 2

theorem physicalSquareCoordinate_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ physicalSquareCoordinate w := by
  unfold physicalSquareCoordinate
  exact Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw0 2)

theorem physicalSquareCoordinate_le_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    physicalSquareCoordinate w ≤ (1 : Q') := by
  have hsq : qpow w 2 ≤ qpow wH 2 := qpow_mono hw0 hwH 2
  have hscaled :
      (4 : Q') * qpow w 2 ≤ (4 : Q') * qpow wH 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 4 hsq (by decide)
  exact Q'.le_trans' _ _ _ hscaled (by decide)

/-! ## 2. Positivity of a nonnegative Bernstein row -/

/-- Every unnormalised Bernstein basis element is nonnegative on `[0,1]`. -/
theorem bernsteinBasis_nonnegative
    (D j : Nat) {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    (0 : Q') ≤ bernsteinBasis D u j := by
  unfold bernsteinBasis
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg u hu0 j)
    (Q'.pow_nonneg (1 - u) (Q'.sub_nonneg_of_le hu1) (D - j))

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

/-- A finite sum is nonnegative when every term in its actual prefix is
nonnegative. -/
theorem finSum_nonnegative_lt (f : QSeq) :
    ∀ N, (∀ i, i < N → (0 : Q') ≤ f i) →
      (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      show (0 : Q') ≤ finSum f N + f N
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_lt f N (fun i hi => h i (by omega)))
        (h N (by omega))

/-- A signed Bernstein evaluation is nonnegative when every used integer
coefficient is nonnegative. -/
theorem signedBernsteinEval_nonnegative
    (D : Nat) (c : Nat → Int) {u : Q'}
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q'))
    (hc : ∀ j, j ≤ D → (0 : Int) ≤ c j) :
    (0 : Q') ≤ signedBernsteinEval D c u := by
  unfold signedBernsteinEval
  apply finSum_nonnegative_lt
  intro j hj
  exact Q'.mul_nonneg _ _
    (ofInt_nonnegative (hc j (by omega)))
    (bernsteinBasis_nonnegative D j hu0 hu1)

/-! ## 3. One actual canonical cell certificate -/

/-- A denominator-cleared nonnegative Bernstein presentation of one actual
canonical quotient cell

`boundaryResidualSquareGapQuotient wH w (t+1) (n-1-t)`.

The reconstruction equality is deliberately pinned to that expression.
Consequently a detached positive polynomial cannot inhabit this certificate.
The positive scale permits exact integer denominator clearing without adding
division to the sign argument. -/
structure PhysicalCanonicalCellBernsteinCertificate
    (w : Q') (n t : Nat) : Type where
  degree : Nat
  zeroOrder : Nat
  coefficient : Nat → Int
  scale : Q'
  scale_positive : (0 : Q') < scale
  coefficient_nonnegative :
    ∀ j, j ≤ degree → (0 : Int) ≤ coefficient j
  quotient_scaled_reconstruction :
    scale *
        boundaryResidualSquareGapQuotient
          wH w (t + 1) (n - 1 - t) ≈
      physicalSquareCoordinate w ^ zeroOrder *
        signedBernsteinEval degree coefficient
          (physicalSquareCoordinate w)

/-- A certified canonical cell quotient is nonnegative throughout the
physical coupling interval. -/
theorem canonicalCellQuotient_nonnegative_of_bernstein
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH)
    {n t : Nat}
    (C : PhysicalCanonicalCellBernsteinCertificate w n t) :
    (0 : Q') ≤ boundaryResidualSquareGapQuotient
      wH w (t + 1) (n - 1 - t) := by
  have hu0 : (0 : Q') ≤ physicalSquareCoordinate w :=
    physicalSquareCoordinate_nonnegative hw0
  have hu1 : physicalSquareCoordinate w ≤ (1 : Q') :=
    physicalSquareCoordinate_le_one hw0 hwH
  have hrow : (0 : Q') ≤
      signedBernsteinEval C.degree C.coefficient
        (physicalSquareCoordinate w) :=
    signedBernsteinEval_nonnegative C.degree C.coefficient
      hu0 hu1 C.coefficient_nonnegative
  have hrhs : (0 : Q') ≤
      physicalSquareCoordinate w ^ C.zeroOrder *
        signedBernsteinEval C.degree C.coefficient
          (physicalSquareCoordinate w) :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg (physicalSquareCoordinate w) hu0 C.zeroOrder)
      hrow
  have hscaled : (0 : Q') ≤
      C.scale * boundaryResidualSquareGapQuotient
        wH w (t + 1) (n - 1 - t) :=
    Q'.le_trans' _ _ _ hrhs
      (Q'.ge_of_eqv C.quotient_scaled_reconstruction)
  exact Q'.nonneg_of_mul_pos C.scale_positive hscaled

/-! ## 4. Family-to-row-one consumer -/

/-- Bernstein certificates for every actual cell in every positive canonical
diagonal. -/
structure PhysicalCanonicalBernsteinFamily (w : Q') : Type where
  certificate :
    ∀ n t, t < n →
      PhysicalCanonicalCellBernsteinCertificate w n t

/-- A finite `fsum` is nonnegative when each term in its bounded prefix is
nonnegative. -/
theorem fsum_nonnegative_lt (f : Nat → Q') :
    ∀ N, (∀ i, i < N → (0 : Q') ≤ f i) →
      (0 : Q') ≤ fsum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      show (0 : Q') ≤ fsum f N + f N
      exact Q'.zero_le_add _ _
        (fsum_nonnegative_lt f N (fun i hi => h i (by omega)))
        (h N (by omega))

/-- An all-cell physical Bernstein family directly inhabits the precise
row-one-origin quotient certificate consumed by Core B. -/
def rowOneOriginSquareGapQuotientNonnegativeOfBernstein
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH)
    (F : PhysicalCanonicalBernsteinFamily w) :
    RowOneOriginSquareGapQuotientNonnegative w where
  nonneg := by
    intro n
    unfold diagonalCumulativeSquareGapQuotient
    apply fsum_nonnegative_lt
    intro t ht
    have hcell :=
      canonicalCellQuotient_nonnegative_of_bernstein
        hw0 hwH (F.certificate n t ht)
    simpa only [Nat.add_comm, Nat.zero_add] using hcell

#print axioms physicalSquareCoordinate_nonnegative
#print axioms physicalSquareCoordinate_le_one
#print axioms bernsteinBasis_nonnegative
#print axioms finSum_nonnegative_lt
#print axioms signedBernsteinEval_nonnegative
#print axioms PhysicalCanonicalCellBernsteinCertificate
#print axioms canonicalCellQuotient_nonnegative_of_bernstein
#print axioms PhysicalCanonicalBernsteinFamily
#print axioms fsum_nonnegative_lt
#print axioms rowOneOriginSquareGapQuotientNonnegativeOfBernstein

end YMGap.Continuum.CoreBBernsteinConsumer
