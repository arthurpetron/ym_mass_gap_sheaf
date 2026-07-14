/-
# Signed rational factorial candidate for the ordered inverse Racah coefficient

The faithful `racahKernel6` is a Gram-normalized square, so it cannot itself
serve as the signed solution of the Casimir three-term recurrence.  Combining
the four triangle factorials with the two left and two right binary Gram
products cancels every square root and leaves the rational signed candidate
defined here.

For external twice-spin labels `(a,b,c,d)`, intermediate labels `(e,f)`, and
contraction orders

  k=(a+b-e)/2, r=(e+c-d)/2, p=(b+c-f)/2, q=(a+f-d)/2,

the candidate is

  (-1)^((a+b+c+d)/2) (f+1)
    k! r! (b-p)! (c-p)! (a-q)! (f-q)!
    -------------------------------------------------  RacahSum.
       (b+c-p+1)! (a+f-q+1)!

The definition is guarded by the same four fusion faces as `racahKernel6`.
The general square theorem proves that the sign disappears only after the
signed amplitude has been formed.  Exact zero-leg, fundamental, and mixed
blocks audit the orientation; they are normalization checks, not a finite-case
substitute for the remaining all-label recurrence proof.
-/

import YMGap.Continuum.SU2RacahThreeTermUniqueness

namespace YMGap.Continuum.SU2SignedRacahFactorialCandidate

open YMGap.Constructive
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.TreeGraphBoundProgress

local infix:50 " ≈ " => Q'.eqv

def leftInnerOrder (a b e : Nat) : Nat := (a + b - e) / 2
def leftOuterOrder (e c d : Nat) : Nat := (e + c - d) / 2
def rightInnerOrder (b c f : Nat) : Nat := (b + c - f) / 2
def rightOuterOrder (a f d : Nat) : Nat := (a + f - d) / 2

/-- The orientation phase selected by the repository's ordered transvectants. -/
def orderedExternalPhase (a b c d : Nat) : Q' :=
  if ((a + b + c + d) / 2) % 2 = 0 then 1 else -1

/-- Numerator of the rational factor multiplying the signed Racah sum. -/
def signedInverseFactorNum (a b c d e f : Nat) : Nat :=
  let k := leftInnerOrder a b e
  let r := leftOuterOrder e c d
  let p := rightInnerOrder b c f
  let q := rightOuterOrder a f d
  (f + 1) * fact k * fact r * fact (b - p) * fact (c - p) *
    fact (a - q) * fact (f - q)

/-- Denominator of the rational factor multiplying the signed Racah sum. -/
def signedInverseFactorDen (a b c d _e f : Nat) : Nat :=
  let p := rightInnerOrder b c f
  let q := rightOuterOrder a f d
  fact (b + c - p + 1) * fact (a + f - q + 1)

theorem signedInverseFactorDen_pos (a b c d e f : Nat) :
    0 < signedInverseFactorDen a b c d e f := by
  unfold signedInverseFactorDen
  exact Nat.mul_pos (fact_pos _) (fact_pos _)

/-- Exact rational prefactor, represented with its positive denominator. -/
def signedInverseFactor (a b c d e f : Nat) : Q' :=
  Q'.mkPos (signedInverseFactorNum a b c d e f)
    (signedInverseFactorDen a b c d e f)
    (signedInverseFactorDen_pos a b c d e f)

/-- **Signed arbitrary-label factorial candidate.**  This is the object to be
compared with the inverse Schur coordinate by a Casimir/Jacobi recurrence. -/
def signedRacahInverseCandidate (a b c d e f : Nat) : Q' :=
  if valid6 a b c d e f = true then
    orderedExternalPhase a b c d *
      (signedInverseFactor a b c d e f * racahSum a b e c d f)
  else 0

private theorem product_square_reorder (x y : Q') :
    (x * y) * (x * y) ≈ (x * x) * (y * y) := by
  show ((x * y) * (x * y)).num * (((x * x) * (y * y)).den : Int) =
    ((x * x) * (y * y)).num * ((((x * y) * (x * y)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

theorem orderedExternalPhase_square (a b c d : Nat) :
    orderedExternalPhase a b c d * orderedExternalPhase a b c d ≈ 1 := by
  unfold orderedExternalPhase
  by_cases h : ((a + b + c + d) / 2) % 2 = 0
  · rw [if_pos h]
    decide
  · rw [if_neg h]
    decide

/-- **General signed-candidate square law.**  On a physical tetrahedron the
orientation phase squares away, leaving exactly the square of the rational
factor times the square of the signed Racah sum.  This is the correct point
at which to pass from the recurrence-bearing amplitude to `racahKernel6`. -/
theorem signedRacahInverseCandidate_square_of_valid
    (a b c d e f : Nat) (hvalid : valid6 a b c d e f = true) :
    signedRacahInverseCandidate a b c d e f *
        signedRacahInverseCandidate a b c d e f ≈
      (signedInverseFactor a b c d e f *
          signedInverseFactor a b c d e f) *
        (racahSum a b e c d f * racahSum a b e c d f) := by
  unfold signedRacahInverseCandidate
  rw [if_pos hvalid]
  let P := orderedExternalPhase a b c d
  let R := signedInverseFactor a b c d e f
  let S := racahSum a b e c d f
  refine Q'.eqv_trans _
    (P * P * ((R * S) * (R * S))) _
    (product_square_reorder P (R * S)) ?_
  refine Q'.eqv_trans _
    (1 * ((R * S) * (R * S))) _
    (Q'.mul_eqv_congr_right _ _ _ (orderedExternalPhase_square a b c d)) ?_
  refine Q'.eqv_trans _ ((R * S) * (R * S)) _
    (Q'.one_mul_eqv _) ?_
  exact product_square_reorder R S

/-! ## Orientation and normalization audits -/

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def threeHalves : Q' := Q'.mkPos 3 2 (by decide)
private def oneThird : Q' := Q'.mkPos 1 3 (by decide)
private def twoThirds : Q' := Q'.mkPos 2 3 (by decide)
private def fourThirds : Q' := Q'.mkPos 4 3 (by decide)

/-- The all-label formula has the correct unsquared zero-leg boundary value. -/
theorem signedCandidate_zero_leg_boundary :
    signedRacahInverseCandidate 0 1 1 0 1 0 ≈ 1 := by
  decide

/-- Complete fundamental inverse-Schur orientation audit. -/
theorem signedCandidate_fundamental_block :
    signedRacahInverseCandidate 1 1 1 1 0 0 ≈ -half ∧
    signedRacahInverseCandidate 1 1 1 1 0 2 ≈ half ∧
    signedRacahInverseCandidate 1 1 1 1 2 0 ≈ threeHalves ∧
    signedRacahInverseCandidate 1 1 1 1 2 2 ≈ half := by
  decide

/-- The genuinely mixed `(2,2,1,1)` block fixes the external phase that the
fundamental block alone cannot detect. -/
theorem signedCandidate_mixed221_block :
    signedRacahInverseCandidate 2 2 1 1 0 1 ≈ -twoThirds ∧
    signedRacahInverseCandidate 2 2 1 1 0 3 ≈ oneThird ∧
    signedRacahInverseCandidate 2 2 1 1 2 1 ≈ fourThirds ∧
    signedRacahInverseCandidate 2 2 1 1 2 3 ≈ oneThird := by
  decide

end YMGap.Continuum.SU2SignedRacahFactorialCandidate

#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.signedInverseFactorDen_pos
#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.orderedExternalPhase_square
#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.signedRacahInverseCandidate_square_of_valid
#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.signedCandidate_zero_leg_boundary
#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.signedCandidate_fundamental_block
#print axioms YMGap.Continuum.SU2SignedRacahFactorialCandidate.signedCandidate_mixed221_block
