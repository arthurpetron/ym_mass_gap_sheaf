/-
# Exact rational Jacobi coefficients for the ordered Racah row

The left-pair exchange Casimir is diagonal in the left coupling order and
tridiagonal in the right contraction order.  This module records the rational
coefficient orientation selected by the repository's unnormalised ordered
transvectants.  Physical-neighbour guards make both endpoints literal zeros.

The two exact low-label blocks audit all signs and the asymmetric Gram gauge.
They also test the signed factorial candidate against the proposed recurrence;
the faithful squared kernel is deliberately not used here.
-/

import YMGap.Continuum.SU2SignedRacahSquareNormalization
import YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

namespace YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2SignedRacahFactorialCandidate
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

local infix:50 " ≈ " => Q'.eqv

/-- Right intermediate label at contraction order `p`. -/
def rightLabel (b c p : Nat) : Nat := b + c - 2 * p

/-- Outer right contraction order forced by the final label. -/
def outerOrder (a b c d p : Nat) : Nat :=
  (a + rightLabel b c p - d) / 2

/-- A physical right contraction order: the inner order is in range and the
outer face `(a,f,d)` is admissible. -/
def rightOrderOK (a b c d p : Nat) : Bool :=
  decide (p ≤ min b c) && fusionOK a (rightLabel b c p) d

theorem rightOrderOK_spec (a b c d p : Nat) :
    rightOrderOK a b c d p = true ↔
      p ≤ min b c ∧ fusionOK a (rightLabel b c p) d = true := by
  unfold rightOrderOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- The forward neighbor `p+1`, when physical, forces `f≥2`; hence the
displayed forward denominator is genuinely positive. -/
theorem two_le_rightLabel_of_forward_ok (a b c d p : Nat)
    (h : rightOrderOK a b c d (p + 1) = true) :
    2 ≤ rightLabel b c p := by
  have hp := (rightOrderOK_spec a b c d (p + 1)).1 h |>.1
  have hp' := Nat.le_min.mp hp
  unfold rightLabel
  omega

def forwardNum (a b c d p : Nat) : Nat :=
  let f := rightLabel b c p
  let q := outerOrder a b c d p
  (p + 1) * (b - p) * (c - p) * (f - q)

def forwardDen (b c p : Nat) : Nat :=
  let f := rightLabel b c p
  f * (f - 1)

theorem forwardDen_pos_of_forward_ok (a b c d p : Nat)
    (h : rightOrderOK a b c d (p + 1) = true) :
    0 < forwardDen b c p := by
  have hf := two_le_rightLabel_of_forward_ok a b c d p h
  unfold forwardDen
  exact Nat.mul_pos (by omega) (by omega)

/-- Coefficient of the next contraction order `p+1`. -/
def jacobiForward (a b c d p : Nat) : Q' :=
  if h : rightOrderOK a b c d (p + 1) = true then
    Q'.mkPos (forwardNum a b c d p) (forwardDen b c p)
      (forwardDen_pos_of_forward_ok a b c d p h)
  else 0

def backwardNum (a b c d p : Nat) : Nat :=
  let f := rightLabel b c p
  let q := outerOrder a b c d p
  (q + 1) * (a - q) * (a + f - q + 2) * (b + c - p + 2)

def backwardDen (b c p : Nat) : Nat :=
  let f := rightLabel b c p
  (f + 2) * (f + 3)

theorem backwardDen_pos (b c p : Nat) : 0 < backwardDen b c p := by
  unfold backwardDen
  exact Nat.mul_pos (by omega) (by omega)

/-- Coefficient of the previous contraction order `p-1`.  The explicit
`p=0` guard is needed because natural subtraction alone would alias it with
the zeroth channel. -/
def jacobiBackward (a b c d p : Nat) : Q' :=
  if _h : 0 < p ∧ rightOrderOK a b c d (p - 1) = true then
    Q'.mkPos (backwardNum a b c d p) (backwardDen b c p)
      (backwardDen_pos b c p)
  else 0

/-- Four times the spin Casimir `j(j+1)` for a twice-spin label. -/
def casimir4 (x : Nat) : Nat := x * (x + 2)

def diagonalNum (a b c d f : Nat) : Int :=
  ((casimir4 d : Int) - casimir4 a - casimir4 f) *
      ((casimir4 f : Int) + casimir4 b - casimir4 c) -
    (4 : Int) * a * b * casimir4 f

def diagonalDen (f : Nat) : Nat := 8 * casimir4 f

theorem diagonalDen_pos {f : Nat} (hf : f ≠ 0) : 0 < diagonalDen f := by
  unfold diagonalDen casimir4
  exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.pos_of_ne_zero hf) (by omega))

/-- Diagonal coefficient of the left exchange Casimir in a right channel.
At `f=0`, admissibility forces the removable projected-Casimir term to vanish,
leaving the exact value `-ab/2`. -/
def jacobiDiagonal (a b c d p : Nat) : Q' :=
  let f := rightLabel b c p
  if hf : f = 0 then
    Q'.mkPos (-(a * b : Int)) 2 (by decide)
  else
    Q'.mkPos (diagonalNum a b c d f) (diagonalDen f)
      (diagonalDen_pos hf)

/-- Left-channel exchange eigenvalue. -/
def leftExchangeEigenvalue (a b e : Nat) : Q' :=
  -(pairEigenvalue a b (leftInnerOrder a b e))

/-- Signed factorial candidate, indexed by the right contraction order. -/
def signedCandidateByOrder (a b c d e p : Nat) : Q' :=
  signedRacahInverseCandidate a b c d e (rightLabel b c p)

/-- The explicit pointwise Jacobi equation. -/
def CandidateJacobiAt (a b c d e p : Nat) : Prop :=
  leftExchangeEigenvalue a b e * signedCandidateByOrder a b c d e p ≈
    jacobiForward a b c d p * signedCandidateByOrder a b c d e (p + 1) +
      jacobiDiagonal a b c d p * signedCandidateByOrder a b c d e p +
      jacobiBackward a b c d p * signedCandidateByOrder a b c d e (p - 1)

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def threeHalves : Q' := Q'.mkPos 3 2 (by decide)
private def oneThird : Q' := Q'.mkPos 1 3 (by decide)
private def eightThirds : Q' := Q'.mkPos 8 3 (by decide)
private def fourteenThirds : Q' := Q'.mkPos 14 3 (by decide)
private def sixteenThirds : Q' := Q'.mkPos 16 3 (by decide)

/-- Complete coefficient audit for the fundamental two-channel window. -/
theorem fundamental_jacobi_coefficients :
    jacobiForward 1 1 1 1 0 ≈ half ∧
    jacobiDiagonal 1 1 1 1 0 ≈ -threeHalves ∧
    jacobiBackward 1 1 1 1 0 ≈ 0 ∧
    jacobiForward 1 1 1 1 1 ≈ 0 ∧
    jacobiDiagonal 1 1 1 1 1 ≈ -half ∧
    jacobiBackward 1 1 1 1 1 ≈ threeHalves := by
  decide

/-- The asymmetric mixed block detects the Gram-gauge orientation of both
off-diagonal coefficients. -/
theorem mixed221_jacobi_coefficients :
    jacobiForward 2 2 1 1 0 ≈ oneThird ∧
    jacobiDiagonal 2 2 1 1 0 ≈ -sixteenThirds ∧
    jacobiBackward 2 2 1 1 0 ≈ 0 ∧
    jacobiForward 2 2 1 1 1 ≈ 0 ∧
    jacobiDiagonal 2 2 1 1 1 ≈ -fourteenThirds ∧
    jacobiBackward 2 2 1 1 1 ≈ eightThirds := by
  decide

/-- Both fundamental signed Racah rows satisfy the proposed endpoint and
terminal equations. -/
theorem fundamental_candidate_jacobi_audit :
    CandidateJacobiAt 1 1 1 1 0 0 ∧ CandidateJacobiAt 1 1 1 1 0 1 ∧
    CandidateJacobiAt 1 1 1 1 2 0 ∧ CandidateJacobiAt 1 1 1 1 2 1 := by
  unfold CandidateJacobiAt
  decide

/-- Both mixed `(2,2,1,1)` signed rows satisfy the same oriented Jacobi law. -/
theorem mixed221_candidate_jacobi_audit :
    CandidateJacobiAt 2 2 1 1 0 0 ∧ CandidateJacobiAt 2 2 1 1 0 1 ∧
    CandidateJacobiAt 2 2 1 1 2 0 ∧ CandidateJacobiAt 2 2 1 1 2 1 := by
  unfold CandidateJacobiAt
  decide

end YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.rightOrderOK_spec
#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.forwardDen_pos_of_forward_ok
#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.fundamental_jacobi_coefficients
#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.mixed221_jacobi_coefficients
#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.fundamental_candidate_jacobi_audit
#print axioms YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients.mixed221_candidate_jacobi_audit
