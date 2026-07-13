/-
# Cleared theta residual: Bernstein pilot and a refuted tangent family

After removing the common factor `w^2`, the cutoff-one cleared residual is

  Q1(w) = (1+w)^3 (1 + 4w^6) - 16w^3.

This file gives an exact positive Bernstein decomposition of `Q1` on `[0,1]`.
It also refutes a natural proposed all-cutoff factorization: subtracting the
unique positive top-boundary monomial tangent to the residual at `w=1` does
not leave a nonnegative `(1-w)^2` remainder, already at cutoff one.
-/

import YMGap.Continuum.HarmonicThetaRepresentation
import YMGap.Continuum.CircleFourierPowerModel
import YMGap.Continuum.PNPaths

namespace YMGap.Continuum.ThetaResidualBernsteinPilot

set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.CircleFourierPowerModel

local infix:50 " ≈ " => Q'.eqv

/-- The cutoff-one cleared integer/half-integer theta residual after dividing
the common `w^2` factor. -/
def thetaResidualOneP : Poly :=
  [1, 3, 3, -15, 0, 0, 4, 12, 12, 4]

/-- Degree-eleven Bernstein coefficients (the binomial factors are included,
matching `bernTermsP`'s unnormalised basis). -/
def thetaResidualOneBern : List (Nat × Q') :=
  [(0, 1), (1, 14), (2, 88), (3, 312), (4, 678), (5, 924),
   (6, 760), (7, 320), (8, 37), (9, 30), (10, 60), (11, 24)]

/-- **Exact positive decomposition.**  `Q1` is the displayed sum of
`a_k w^k(1-w)^(11-k)` with every `a_k>=0`. -/
theorem thetaResidualOne_bernstein_identity :
    allZero (psub thetaResidualOneP
      (bernTermsP 11 thetaResidualOneBern)) := by decide

theorem thetaResidualOne_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ eval thetaResidualOneP w := by
  exact Q'.le_trans' _ _ _
    (eval_bernTermsP_nonneg hw0 hw1 11 thetaResidualOneBern (by decide))
    (Q'.ge_of_eqv
      (poly_eqv thetaResidualOneP
        (bernTermsP 11 thetaResidualOneBern) w
        thetaResidualOne_bernstein_identity))

/-- Cutoff-two cleared residual. -/
def thetaResidualTwoP : Poly :=
  [1, 3, 3, -15, 0, 0, 4, 12, 12, 4, 0, -48, 0, 0, 0, 0,
   9, 27, 27, 9]

/-- Degree-23 positive Bernstein decomposition of the cutoff-two residual.
The degree is `maxDegree + 2N = 19 + 4`, the first instance of the stable
`2N` elevation pattern. -/
def thetaResidualTwoBern : List (Nat × Q') :=
  [(0, 1), (1, 26), (2, 322), (3, 2512), (4, 13805),
   (5, 56734), (6, 180808), (7, 457448), (8, 932926),
   (9, 1548284), (10, 2101552), (11, 2336624), (12, 2126302),
   (13, 1581572), (14, 963868), (15, 487696), (16, 210842),
   (17, 79588), (18, 24712), (19, 4928), (20, 238), (21, 84),
   (22, 168), (23, 48)]

theorem thetaResidualTwo_bernstein_identity :
    allZero (psub thetaResidualTwoP
      (bernTermsP 23 thetaResidualTwoBern)) := by decide

theorem thetaResidualTwo_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ eval thetaResidualTwoP w :=
  Q'.le_trans' _ _ _
    (eval_bernTermsP_nonneg hw0 hw1 23 thetaResidualTwoBern (by decide))
    (Q'.ge_of_eqv (poly_eqv thetaResidualTwoP
      (bernTermsP 23 thetaResidualTwoBern) w
      thetaResidualTwo_bernstein_identity))

/-! A second adversarial fence: the tempting local allocation which gives
each negative half-integer monomial one half of each adjacent integer block
does not induce coefficientwise Bernstein positivity. -/

private def monoBernCoeff (D e k : Nat) : Int :=
  if e ≤ k then Int.ofNat (PNPaths.choose (D - e) (k - e)) else 0

private def diagBernCoeff (D n k : Nat) : Int :=
  Int.ofNat (n * n) *
    (monoBernCoeff D (2 * n * n - 2) k +
      3 * monoBernCoeff D (2 * n * n - 1) k +
      3 * monoBernCoeff D (2 * n * n) k +
      monoBernCoeff D (2 * n * n + 1) k)

private def offBernCoeff (D n k : Nat) : Int :=
  Int.ofNat (8 * n * (n + 1)) *
    monoBernCoeff D (2 * n * (n + 1) - 1) k

/-- The half-allocation coefficient at `(N,n,k)=(2,1,12)` is exactly
`-560482`.  Hence a proof cannot independently pay each half-integer term
with half of both neighboring integer blocks; positive reserve must move
between different `n`-cells. -/
theorem adjacent_half_allocation_coefficient_negative :
    diagBernCoeff 23 1 12 + diagBernCoeff 23 2 12 -
        2 * offBernCoeff 23 1 12 = (-560482 : Int) := by decide

theorem adjacent_half_allocation_not_nonnegative :
    ¬ ((0 : Int) ≤
      diagBernCoeff 23 1 12 + diagBernCoeff 23 2 12 -
        2 * offBernCoeff 23 1 12) := by decide

/-- The natural top-boundary term tangent to `Q1` at `w=1`:
`12 w^8(1+w)`.  Its value and first derivative match `Q1` at one, so
`Q1-boundary` is divisible by `(1-w)^2`. -/
def tangentBoundaryOneP : Poly :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 12]

/-- Exact quotient of `Q1-tangentBoundary` by `(1-w)^2`. -/
def tangentRemainderOneP : Poly :=
  [1, 5, 12, 4, -4, -12, -16, -8]

theorem tangent_factorization_one :
    allZero (psub thetaResidualOneP
      (padd tangentBoundaryOneP
        (pmul (pmul onemP onemP) tangentRemainderOneP))) := by decide

/-- **Kernel-refuted factorization family seed.**  The tangent remainder is
strictly negative at `w=9/10`; therefore the proposed certificate
`Q_N = positive tangent boundary + (1-w)^2 * nonnegative remainder` cannot
hold uniformly in `N`, since it already fails for `N=1`. -/
theorem tangent_remainder_one_negative :
    eval tangentRemainderOneP (Q'.mkPos 9 10 (by decide)) < (0 : Q') := by decide

end YMGap.Continuum.ThetaResidualBernsteinPilot

#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.thetaResidualOne_bernstein_identity
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.thetaResidualOne_nonneg
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.thetaResidualTwo_bernstein_identity
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.thetaResidualTwo_nonneg
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.adjacent_half_allocation_coefficient_negative
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.adjacent_half_allocation_not_nonnegative
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.tangent_factorization_one
#print axioms YMGap.Continuum.ThetaResidualBernsteinPilot.tangent_remainder_one_negative
