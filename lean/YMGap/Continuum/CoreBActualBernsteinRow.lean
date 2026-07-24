/-
# The actual Core-B bounded atom Bernstein row

This module compiles the finite bounded atom ledger of one canonical Core-B
cell into one signed integer Bernstein row.  It is tied directly to
`aAtomicMonomial`, `mAtomicMonomial`, their actual coefficient masses, and the
orientation/length of `orientedHomChain`.

The common degree is not guessed from a finite table.  It is the computable
maximum of the half-exponents over the actual bounded selectors in the cell.
Consequently every chain monomial fits the row by construction.  The exact
generic signed-monomial reconstruction theorem then proves that the compiled
row evaluates to the corresponding finite signed chain-monomial ledger.

No coefficient positivity is asserted.  The remaining seam to
`PhysicalCanonicalCellBernsteinCertificate` is the rational scaling identity
at `wH = 1/2`, `u = 4 w^2`, identifying this cleared ledger evaluation with
the actual `boundaryResidualSquareGapQuotient`.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.BernsteinSignedMonomialReconstruction
import YMGap.Continuum.CoreBBoundedMonomialNormalForm
import YMGap.Continuum.CoreBUniversalSquareGap
import YMGap.Continuum.CoreBBernsteinConsumer

namespace YMGap.Continuum.CoreBActualBernsteinRow

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CoreBBoundedMonomialNormalForm
open YMGap.Continuum.CoreBUniversalSquareGap
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinSignedMonomialReconstruction
open YMGap.Continuum.CoreBBernsteinConsumer

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Computable finite maxima and integer row sums -/

/-- Maximum of the first `N` values of a natural-valued sequence. -/
def natPrefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => max (natPrefixMax f N) (f N)

theorem le_natPrefixMax (f : Nat → Nat) (i N : Nat) (hi : i < N) :
    f i ≤ natPrefixMax f N := by
  induction N with
  | zero => omega
  | succ N ih =>
      simp only [natPrefixMax]
      by_cases hlast : i = N
      · subst i
        exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)

/-- Sum of the first `N` entries of an integer sequence. -/
def intPrefixSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | N + 1 => intPrefixSum f N + f N

/-- Pointwise finite sum of signed integer rows. -/
def signedRowPrefixSum (row : Nat → Nat → Int) (N : Nat) : Nat → Int :=
  fun b => intPrefixSum (fun i => row i b) N

/-- Signed Bernstein evaluation commutes with a finite pointwise row sum. -/
theorem signedBernsteinEval_rowPrefixSum
    (D : Nat) (row : Nat → Nat → Int) (u : Q') :
    ∀ N,
      signedBernsteinEval D (signedRowPrefixSum row N) u ≈
        finSum (fun i => signedBernsteinEval D (row i) u) N
  | 0 => by
      unfold signedRowPrefixSum signedBernsteinEval
      simp only [intPrefixSum, finSum_zero]
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr
          (fun j => Q'.ofInt 0 * bernsteinBasis D u j)
          (fun _ => (0 : Q'))
          (fun j => Q'.zero_mul_eqv (bernsteinBasis D u j))
          (D + 1)) ?_
      exact Q'.eqv_of_eq (finSum_zero_seq (D + 1))
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (signedBernsteinEval_add D
          (signedRowPrefixSum row N) (row N) u) ?_
      exact Q'.add_eqv_congr_right _ _ _
        (signedBernsteinEval_rowPrefixSum D row u N)

/-! ## 2. One actual oriented-chain ledger -/

/-- Half-exponent at the fixed endpoint side of an atom pair. -/
def numeratorHalfExponent (a : WeightMonomial) : Nat :=
  a.exponent / 2

/-- Half-exponent at the physical-coupling side of an atom pair. -/
def midpointHalfExponent (m : WeightMonomial) : Nat :=
  m.exponent / 2

/-- Base half-exponent of the homogeneous chain. -/
def actualChainBase (a m : WeightMonomial) : Nat :=
  min (numeratorHalfExponent a) (midpointHalfExponent m)

/-- Number of monomials in the actual oriented homogeneous chain. -/
def actualChainLength (a m : WeightMonomial) : Nat :=
  if midpointHalfExponent m ≤ numeratorHalfExponent a then
    numeratorHalfExponent a - midpointHalfExponent m
  else
    midpointHalfExponent m - numeratorHalfExponent a

/-- Orientation sign used by `orientedHomChain`. -/
def actualChainSign (a m : WeightMonomial) : Int :=
  if midpointHalfExponent m ≤ numeratorHalfExponent a then 1 else -1

/-- Physical-square exponent of chain monomial `ell`. -/
def actualChainPhysicalExponent
    (a m : WeightMonomial) (ell : Nat) : Nat :=
  actualChainBase a m + ell

/-- Total endpoint-plus-physical square degree after division by the square
gap.  It is independent of the chain coordinate. -/
def actualChainTotalDegree (a m : WeightMonomial) : Nat :=
  numeratorHalfExponent a + midpointHalfExponent m - 1

/-- Integer coefficient of one denominator-cleared actual chain monomial.

The factor `4^(S-totalDegree)` is the exact denominator clearing suggested by
the physical specialization `wH^2=1/4`, `w^2=u/4`.  `S` is left explicit in
this local compiler; canonical cells use twice their computable degree. -/
def actualClearedChainWeight
    (S : Nat) (a m : WeightMonomial) (_ell : Nat) : Int :=
  actualChainSign a m *
    Int.ofNat
      (a.coefficientNat * m.coefficientNat *
        4 ^ (S - actualChainTotalDegree a m))

/-- The actual finite signed monomial ledger carried by one atom pair. -/
def actualClearedChainEval
    (S : Nat) (a m : WeightMonomial) (u : Q') : Q' :=
  finiteSignedMonomialEval
    (actualClearedChainWeight S a m)
    (actualChainPhysicalExponent a m)
    u (actualChainLength a m)

/-- Compile one actual oriented-chain ledger into degree `D`. -/
def actualClearedChainBernsteinRow
    (D S : Nat) (a m : WeightMonomial) : Nat → Int :=
  finiteSignedMonomialBernsteinRow D
    (actualClearedChainWeight S a m)
    (actualChainPhysicalExponent a m)
    (actualChainLength a m)

private theorem chain_exponent_lt_max
    (p q ell : Nat)
    (hell :
      ell <
        if q ≤ p then p - q else q - p) :
    min p q + ell < max p q := by
  by_cases hqp : q ≤ p
  · simp only [if_pos hqp] at hell
    rw [Nat.min_eq_right hqp, Nat.max_eq_left hqp]
    omega
  · have hpq : p < q := by omega
    simp only [if_neg hqp] at hell
    rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
    omega

/-- Every used monomial exponent in an actual chain lies below the larger
atom half-exponent. -/
theorem actualChainPhysicalExponent_lt_max
    (a m : WeightMonomial) (ell : Nat)
    (hell : ell < actualChainLength a m) :
    actualChainPhysicalExponent a m ell <
      max (numeratorHalfExponent a) (midpointHalfExponent m) := by
  unfold actualChainPhysicalExponent actualChainBase
  apply chain_exponent_lt_max
  simpa only [actualChainLength] using hell

/-- Exact generic reconstruction of one actual bounded atom chain. -/
theorem actualClearedChainBernsteinRow_eval
    (D S : Nat) (a m : WeightMonomial) (u : Q')
    (hdegree :
      max (numeratorHalfExponent a) (midpointHalfExponent m) ≤ D) :
    signedBernsteinEval D
        (actualClearedChainBernsteinRow D S a m) u ≈
      actualClearedChainEval S a m u := by
  apply finiteSignedMonomialBernsteinRow_eval
  intro ell hell
  exact Nat.le_trans
    (Nat.le_of_lt (actualChainPhysicalExponent_lt_max a m ell hell))
    hdegree

/-! ## 3. The actual canonical-cell common degree -/

/-- Largest half-exponent in one actual bounded mixed-component family. -/
def mixedActualHalfExponentCeiling
    (s r i j : Nat) : Nat :=
  natPrefixMax (fun p =>
    natPrefixMax (fun u =>
      natPrefixMax (fun q =>
        natPrefixMax (fun v =>
          max
            (numeratorHalfExponent (aAtomicMonomial s r i p q))
            (midpointHalfExponent (mAtomicMonomial s r j u v)))
          (mRightCount s j))
        (aRightCount s i))
      (mLeftCount s j))
    (aLeftCount s i)

/-- Computable common Bernstein degree of the actual bounded selector ledger
in canonical cell `(s,r)=(t+1,n-1-t)`.  The harmless `(0,0)` family is
included in the maximum, although it is omitted from the residual row. -/
def actualCanonicalCellBernsteinDegree (n t : Nat) : Nat :=
  natPrefixMax (fun i =>
    natPrefixMax (fun j =>
      mixedActualHalfExponentCeiling
        (t + 1) (n - 1 - t) i j) 3) 4

/-- Every actual bounded selector half-exponent lies in the computable common
cell degree. -/
theorem actual_atom_half_exponents_le_degree
    (n t i j p q u v : Nat)
    (hi : i < 4) (hj : j < 3)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    max
        (numeratorHalfExponent
          (aAtomicMonomial (t + 1) (n - 1 - t) i p q))
        (midpointHalfExponent
          (mAtomicMonomial (t + 1) (n - 1 - t) j u v)) ≤
      actualCanonicalCellBernsteinDegree n t := by
  apply Nat.le_trans
    (le_natPrefixMax
      (fun v =>
        max
          (numeratorHalfExponent
            (aAtomicMonomial (t + 1) (n - 1 - t) i p q))
          (midpointHalfExponent
            (mAtomicMonomial (t + 1) (n - 1 - t) j u v)))
      v (mRightCount (t + 1) j) hv)
  apply Nat.le_trans
    (le_natPrefixMax
      (fun q =>
        natPrefixMax (fun v =>
          max
            (numeratorHalfExponent
              (aAtomicMonomial (t + 1) (n - 1 - t) i p q))
            (midpointHalfExponent
              (mAtomicMonomial (t + 1) (n - 1 - t) j u v)))
          (mRightCount (t + 1) j))
      q (aRightCount (t + 1) i) hq)
  apply Nat.le_trans
    (le_natPrefixMax
      (fun u =>
        natPrefixMax (fun q =>
          natPrefixMax (fun v =>
            max
              (numeratorHalfExponent
                (aAtomicMonomial (t + 1) (n - 1 - t) i p q))
              (midpointHalfExponent
                (mAtomicMonomial (t + 1) (n - 1 - t) j u v)))
            (mRightCount (t + 1) j))
          (aRightCount (t + 1) i))
      u (mLeftCount (t + 1) j) hu)
  apply Nat.le_trans
    (le_natPrefixMax
      (fun p =>
        natPrefixMax (fun u =>
          natPrefixMax (fun q =>
            natPrefixMax (fun v =>
              max
                (numeratorHalfExponent
                  (aAtomicMonomial (t + 1) (n - 1 - t) i p q))
                (midpointHalfExponent
                  (mAtomicMonomial (t + 1) (n - 1 - t) j u v)))
              (mRightCount (t + 1) j))
            (aRightCount (t + 1) i))
          (mLeftCount (t + 1) j))
      p (aLeftCount (t + 1) i) hp)
  apply Nat.le_trans
    (le_natPrefixMax
      (fun j =>
        mixedActualHalfExponentCeiling
          (t + 1) (n - 1 - t) i j)
      j 3 hj)
  exact le_natPrefixMax
    (fun i =>
      natPrefixMax (fun j =>
        mixedActualHalfExponentCeiling
          (t + 1) (n - 1 - t) i j) 3)
    i 4 hi

/-! ## 4. The precise actual mixed-family and cell rows -/

/-- Twice the common cell degree, used as the physical denominator-clearing
exponent. -/
def actualCanonicalCellClearingExponent (n t : Nat) : Nat :=
  2 * actualCanonicalCellBernsteinDegree n t

/-- The actual chain's total square degree fits the canonical clearing
exponent.  Thus the subtraction in `actualClearedChainWeight` is never
truncated on a valid bounded selector. -/
theorem actual_atom_total_degree_le_clearingExponent
    (n t i j p q u v : Nat)
    (hi : i < 4) (hj : j < 3)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    actualChainTotalDegree
        (aAtomicMonomial (t + 1) (n - 1 - t) i p q)
        (mAtomicMonomial (t + 1) (n - 1 - t) j u v) ≤
      actualCanonicalCellClearingExponent n t := by
  have hmax := actual_atom_half_exponents_le_degree
    n t i j p q u v hi hj hp hq hu hv
  have ha :
      numeratorHalfExponent
          (aAtomicMonomial (t + 1) (n - 1 - t) i p q) ≤
        actualCanonicalCellBernsteinDegree n t :=
    Nat.le_trans (Nat.le_max_left _ _) hmax
  have hm :
      midpointHalfExponent
          (mAtomicMonomial (t + 1) (n - 1 - t) j u v) ≤
        actualCanonicalCellBernsteinDegree n t :=
    Nat.le_trans (Nat.le_max_right _ _) hmax
  unfold actualChainTotalDegree actualCanonicalCellClearingExponent
  omega

/-- Positive rational clearing scale attached to the actual cell row. -/
def actualCanonicalCellClearingScale (n t : Nat) : Q' :=
  Q'.ofNat (4 ^ actualCanonicalCellClearingExponent n t)

private theorem ofNat_pos_of_pos {N : Nat} (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ N => exact Q'.ofNat_succ_pos N

theorem actualCanonicalCellClearingScale_positive (n t : Nat) :
    (0 : Q') < actualCanonicalCellClearingScale n t := by
  unfold actualCanonicalCellClearingScale
  exact ofNat_pos_of_pos (Nat.pow_pos (by decide : 0 < 4))

/-- Row compiled from one actual bounded mixed-component family. -/
def mixedActualCanonicalBernsteinRow
    (n t i j : Nat) : Nat → Int :=
  let D := actualCanonicalCellBernsteinDegree n t
  let S := actualCanonicalCellClearingExponent n t
  signedRowPrefixSum (fun p =>
    signedRowPrefixSum (fun u =>
      signedRowPrefixSum (fun q =>
        signedRowPrefixSum (fun v =>
          actualClearedChainBernsteinRow D S
            (aAtomicMonomial (t + 1) (n - 1 - t) i p q)
            (mAtomicMonomial (t + 1) (n - 1 - t) j u v))
          (mRightCount (t + 1) j))
        (aRightCount (t + 1) i))
      (mLeftCount (t + 1) j))
    (aLeftCount (t + 1) i)

/-- The corresponding exact finite signed monomial ledger evaluation. -/
def mixedActualCanonicalLedgerEval
    (n t i j : Nat) (u : Q') : Q' :=
  let S := actualCanonicalCellClearingExponent n t
  finSum (fun p =>
    finSum (fun x =>
      finSum (fun q =>
        finSum (fun v =>
          actualClearedChainEval S
            (aAtomicMonomial (t + 1) (n - 1 - t) i p q)
            (mAtomicMonomial (t + 1) (n - 1 - t) j x v) u)
          (mRightCount (t + 1) j))
        (aRightCount (t + 1) i))
      (mLeftCount (t + 1) j))
    (aLeftCount (t + 1) i)

/-- Evaluation of an actual bounded mixed-family row reconstructs its signed
monomial ledger exactly. -/
theorem mixedActualCanonicalBernsteinRow_eval
    (n t i j : Nat) (hi : i < 4) (hj : j < 3) (u : Q') :
    signedBernsteinEval (actualCanonicalCellBernsteinDegree n t)
        (mixedActualCanonicalBernsteinRow n t i j) u ≈
      mixedActualCanonicalLedgerEval n t i j u := by
  unfold mixedActualCanonicalBernsteinRow mixedActualCanonicalLedgerEval
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_rowPrefixSum _ _ u _) ?_
  apply finSum_eqv_congr_lt
  intro p hp
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_rowPrefixSum _ _ u _) ?_
  apply finSum_eqv_congr_lt
  intro x hx
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_rowPrefixSum _ _ u _) ?_
  apply finSum_eqv_congr_lt
  intro q hq
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_rowPrefixSum _ _ u _) ?_
  apply finSum_eqv_congr_lt
  intro v hv
  apply actualClearedChainBernsteinRow_eval
  exact actual_atom_half_exponents_le_degree
    n t i j p q x v hi hj hp hq hx hv

/-- Numerator-component selector in the residual's fixed eleven-family order:
`(0,1),(0,2),(1,0),...,(3,2)`. -/
def residualNumeratorSelector (k : Nat) : Nat :=
  (k + 1) / 3

/-- Midpoint-component selector in the residual's fixed eleven-family order:
`(0,1),(0,2),(1,0),...,(3,2)`. -/
def residualMidpointSelector (k : Nat) : Nat :=
  (k + 1) % 3

theorem residualNumeratorSelector_lt_four (k : Nat) (hk : k < 11) :
    residualNumeratorSelector k < 4 := by
  unfold residualNumeratorSelector
  omega

theorem residualMidpointSelector_lt_three (k : Nat) :
    residualMidpointSelector k < 3 := by
  unfold residualMidpointSelector
  exact Nat.mod_lt _ (by decide)

/-- Pointwise sum of the actual eleven mixed families in the residual's fixed
order.  This is the requested computable Core-B integer row `B(n,t,b)`. -/
def actualCanonicalCellBernsteinRow (n t : Nat) : Nat → Int :=
  signedRowPrefixSum (fun k =>
    mixedActualCanonicalBernsteinRow n t
      (residualNumeratorSelector k) (residualMidpointSelector k)) 11

/-- Exact signed ledger represented by the eleven-family row. -/
def actualCanonicalCellLedgerEval (n t : Nat) (u : Q') : Q' :=
  finSum (fun k =>
    mixedActualCanonicalLedgerEval n t
      (residualNumeratorSelector k) (residualMidpointSelector k) u) 11

/-- **Actual eleven-family row reconstruction.**  The precise computable
integer row `B(n,t,·)` evaluates to the finite signed monomial ledger obtained
from every actual bounded atom in the canonical cell. -/
theorem actualCanonicalCellBernsteinRow_eval
    (n t : Nat) (u : Q') :
    signedBernsteinEval (actualCanonicalCellBernsteinDegree n t)
        (actualCanonicalCellBernsteinRow n t) u ≈
      actualCanonicalCellLedgerEval n t u := by
  unfold actualCanonicalCellBernsteinRow actualCanonicalCellLedgerEval
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_rowPrefixSum _ _ u 11) ?_
  apply finSum_eqv_congr_lt
  intro k hk
  exact mixedActualCanonicalBernsteinRow_eval n t
    (residualNumeratorSelector k) (residualMidpointSelector k)
    (residualNumeratorSelector_lt_four k hk)
    (residualMidpointSelector_lt_three k) u

/-! ## 5. Direct adapter to the physical certificate -/

/-- Package the actual row into the existing physical-cell certificate once
its two genuinely open properties are supplied:

* coefficientwise nonnegativity of the computed integer row; and
* the exact rational specialization identifying the cleared actual quotient
  with the signed chain ledger at `u = 4 w²`.

All selector compilation, common-degree fitting, and Bernstein
reconstruction are discharged internally by the preceding theorems. -/
def physicalCanonicalCellBernsteinCertificateOfActualRow
    (w : Q') (n t : Nat)
    (hcoefficient :
      ∀ b, b ≤ actualCanonicalCellBernsteinDegree n t →
        (0 : Int) ≤ actualCanonicalCellBernsteinRow n t b)
    (hphysical :
      actualCanonicalCellClearingScale n t *
          boundaryResidualSquareGapQuotient
            YMGap.Continuum.FusionCoreStepRoundA.wH w
            (t + 1) (n - 1 - t) ≈
        actualCanonicalCellLedgerEval n t
          (physicalSquareCoordinate w)) :
    PhysicalCanonicalCellBernsteinCertificate w n t where
  degree := actualCanonicalCellBernsteinDegree n t
  zeroOrder := 0
  coefficient := actualCanonicalCellBernsteinRow n t
  scale := actualCanonicalCellClearingScale n t
  scale_positive := actualCanonicalCellClearingScale_positive n t
  coefficient_nonnegative := hcoefficient
  quotient_scaled_reconstruction := by
    refine Q'.eqv_trans _ _ _ hphysical ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (actualCanonicalCellBernsteinRow_eval n t
          (physicalSquareCoordinate w))) ?_
    exact Q'.eqv_symm
      (Q'.one_mul_eqv
        (signedBernsteinEval (actualCanonicalCellBernsteinDegree n t)
          (actualCanonicalCellBernsteinRow n t)
          (physicalSquareCoordinate w)))

#print axioms le_natPrefixMax
#print axioms signedBernsteinEval_rowPrefixSum
#print axioms actualChainPhysicalExponent_lt_max
#print axioms actualClearedChainBernsteinRow_eval
#print axioms actual_atom_half_exponents_le_degree
#print axioms actual_atom_total_degree_le_clearingExponent
#print axioms actualCanonicalCellClearingScale_positive
#print axioms mixedActualCanonicalBernsteinRow_eval
#print axioms residualNumeratorSelector_lt_four
#print axioms residualMidpointSelector_lt_three
#print axioms actualCanonicalCellBernsteinRow_eval
#print axioms physicalCanonicalCellBernsteinCertificateOfActualRow

end YMGap.Continuum.CoreBActualBernsteinRow
