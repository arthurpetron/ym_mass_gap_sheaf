/-
# Core-B bounded-index monomial normal form

The diagonal coefficient-mass argument must reason about every row at once;
generated declarations for individual rows would therefore encode the wrong
proof shape.  This file gives each finite-window and boundary factor a single
bounded-index monomial presentation and lifts that presentation through the
four arbitrary-offset numerator components.

The result is algebraic only.  It neither proves the diagonal reserve formula
nor the reserve-versus-adverse-mass inequality.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBDiagonalCumulative

namespace YMGap.Continuum.CoreBBoundedMonomialNormalForm

set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CoreBStructuralRecurrence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-variable coefficient monomials -/

/-- A coefficient and a heat-kernel exponent, kept as data rather than as a
row-specific polynomial declaration. -/
structure WeightMonomial where
  coefficientNat : Nat
  exponent : Nat

namespace WeightMonomial

/-- Evaluation of a coefficient monomial at the heat-kernel weight `w`. -/
def eval (w : Q') (m : WeightMonomial) : Q' :=
  Q'.ofNat m.coefficientNat * qpow w m.exponent

/-- Product in the coefficient/exponent presentation. -/
def mul (a b : WeightMonomial) : WeightMonomial where
  coefficientNat := a.coefficientNat * b.coefficientNat
  exponent := a.exponent + b.exponent

/-- Collect two identical monomials into their coefficient. -/
def twice (a : WeightMonomial) : WeightMonomial where
  coefficientNat := a.coefficientNat + a.coefficientNat
  exponent := a.exponent

/-- Evaluation respects monomial multiplication. -/
theorem eval_mul (w : Q') (a b : WeightMonomial) :
    eval w (mul a b) ≈ eval w a * eval w b := by
  unfold eval mul
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (HeatKernelRGStep.ofNat_mul_eqv a.coefficientNat b.coefficientNat)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (Q'.ofNat a.coefficientNat * Q'.ofNat b.coefficientNat) _ _
      (qpow_add w a.exponent b.exponent)) ?_
  exact RingNormaliser.q_mul4_swap
    (Q'.ofNat a.coefficientNat) (Q'.ofNat b.coefficientNat)
    (qpow w a.exponent) (qpow w b.exponent)

/-- Evaluation respects collection of a repeated monomial. -/
theorem eval_twice (w : Q') (a : WeightMonomial) :
    eval w (twice a) ≈ eval w a + eval w a := by
  unfold eval twice
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.ofNat_add_eqv a.coefficientNat a.coefficientNat)) ?_
  exact Q'.add_mul_eqv (Q'.ofNat a.coefficientNat)
    (Q'.ofNat a.coefficientNat) (qpow w a.exponent)

end WeightMonomial

/-- The primitive monomial carried by one heat-kernel coefficient. -/
def coefficientMonomial (p : Nat) : WeightMonomial where
  coefficientNat := p + 1
  exponent := c4 p

/-- A product of two heat-kernel coefficients is one explicit monomial. -/
theorem coeffW_mul_eq_eval (w : Q') (p q : Nat) :
    coeffW w p * coeffW w q ≈
      WeightMonomial.eval w
        (WeightMonomial.mul (coefficientMonomial p) (coefficientMonomial q)) := by
  exact Q'.eqv_symm (WeightMonomial.eval_mul w (coefficientMonomial p)
    (coefficientMonomial q))

/-! ## 2. Uniform finite-window and boundary presentations -/

/-- The monomial at bounded window index `p`.  The subtraction is the literal
indexing convention already used by `acN`; no side condition is hidden. -/
def windowMonomial (s k p : Nat) : WeightMonomial :=
  WeightMonomial.mul (coefficientMonomial p)
    (coefficientMonomial (s + k - p))

/-- The single endpoint monomial added by range growth. -/
def boundaryMonomial (s k : Nat) : WeightMonomial :=
  WeightMonomial.mul (coefficientMonomial (s + 1))
    (coefficientMonomial k)

/-- A window is a single bounded family of coefficient monomials, uniformly
in both the row `s` and offset `k`. -/
def windowNormalForm (w : Q') (s k : Nat) : Q' :=
  fsum (fun p => WeightMonomial.eval w (windowMonomial s k p)) (s + 1)

theorem modeWindow_eq_windowNormalForm (w : Q') (s k : Nat) :
    modeWindow w s k ≈ windowNormalForm w s k := by
  unfold modeWindow AutoconvGershgorin.acN windowNormalForm windowMonomial
  exact fsum_eqv_congr _ _
    (fun p => coeffW_mul_eq_eval w p (s + k - p)) (s + 1)

theorem boundaryTerm_eq_boundaryMonomial (w : Q') (s k : Nat) :
    boundaryTerm w s k ≈ WeightMonomial.eval w (boundaryMonomial s k) := by
  unfold boundaryTerm boundaryMonomial
  exact coeffW_mul_eq_eval w (s + 1) k

/-! ## 3. Arbitrary-offset numerator-component normal form -/

private theorem mul_eqv_congr_two {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem fsum_one (f : Nat → Q') : fsum f 1 ≈ f 0 := by
  simp only [fsum_succ, fsum_zero]
  exact q_zero_add_eqv (f 0)

/-- Number of monomials in the left factor of numerator component `i`. -/
def aLeftCount (s i : Nat) : Nat :=
  match i with
  | 0 => s + 1
  | 1 => s + 1
  | _ => 1

/-- Number of monomials in the right factor of numerator component `i`. -/
def aRightCount (s i : Nat) : Nat :=
  match i with
  | 0 => s + 1
  | 1 => 1
  | 2 => s + 1
  | _ => 1

/-- Left-factor monomial family for the four numerator components. -/
def aLeftMonomial (s r i p : Nat) : WeightMonomial :=
  match i with
  | 0 => windowMonomial s (r + 1) p
  | 1 => windowMonomial s (r + 1) p
  | _ => boundaryMonomial s r

/-- Right-factor monomial family for the four numerator components. -/
def aRightMonomial (s r i q : Nat) : WeightMonomial :=
  match i with
  | 0 => windowMonomial s (r + 3) q
  | 1 => boundaryMonomial s (r + 2)
  | 2 => windowMonomial s (r + 3) q
  | _ => boundaryMonomial s (r + 2)

/-- One numerator atom after multiplying its two factor monomials. -/
def aAtomicMonomial (s r i p q : Nat) : WeightMonomial :=
  WeightMonomial.mul (aLeftMonomial s r i p) (aRightMonomial s r i q)

/-- The whole numerator component as one double bounded monomial family. -/
def aComponentNormalForm (w : Q') (s r i : Nat) : Q' :=
  fsum (fun p => fsum (fun q => WeightMonomial.eval w
    (aAtomicMonomial s r i p q)) (aRightCount s i)) (aLeftCount s i)

private theorem aLeftFactor_eq_sum (w : Q') (s r i : Nat) :
    (match i with
      | 0 => modeWindow w s (r + 1)
      | 1 => modeWindow w s (r + 1)
      | _ => boundaryTerm w s r) ≈
      fsum (fun p => WeightMonomial.eval w (aLeftMonomial s r i p))
        (aLeftCount s i) := by
  cases i with
  | zero =>
      simpa [aLeftMonomial, aLeftCount, windowNormalForm] using
        modeWindow_eq_windowNormalForm w s (r + 1)
  | succ i =>
      cases i with
      | zero =>
          simpa [aLeftMonomial, aLeftCount, windowNormalForm] using
            modeWindow_eq_windowNormalForm w s (r + 1)
      | succ i =>
          refine Q'.eqv_trans _ _ _ (boundaryTerm_eq_boundaryMonomial w s r) ?_
          exact Q'.eqv_symm (by
            simpa [aLeftMonomial, aLeftCount] using
              fsum_one (fun _ => WeightMonomial.eval w (boundaryMonomial s r)))

private theorem aRightFactor_eq_sum (w : Q') (s r i : Nat) :
    (match i with
      | 0 => modeWindow w s (r + 3)
      | 1 => boundaryTerm w s (r + 2)
      | 2 => modeWindow w s (r + 3)
      | _ => boundaryTerm w s (r + 2)) ≈
      fsum (fun q => WeightMonomial.eval w (aRightMonomial s r i q))
        (aRightCount s i) := by
  cases i with
  | zero =>
      simpa [aRightMonomial, aRightCount, windowNormalForm] using
        modeWindow_eq_windowNormalForm w s (r + 3)
  | succ i =>
      cases i with
      | zero =>
          refine Q'.eqv_trans _ _ _
            (boundaryTerm_eq_boundaryMonomial w s (r + 2)) ?_
          exact Q'.eqv_symm (by
            simpa [aRightMonomial, aRightCount] using
              fsum_one (fun _ => WeightMonomial.eval w
                (boundaryMonomial s (r + 2))))
      | succ i =>
          cases i with
          | zero =>
              simpa [aRightMonomial, aRightCount, windowNormalForm] using
                modeWindow_eq_windowNormalForm w s (r + 3)
          | succ i =>
              refine Q'.eqv_trans _ _ _
                (boundaryTerm_eq_boundaryMonomial w s (r + 2)) ?_
              exact Q'.eqv_symm (by
                simpa [aRightMonomial, aRightCount] using
                  fsum_one (fun _ => WeightMonomial.eval w
                    (boundaryMonomial s (r + 2))))

private theorem aComponentAt_eq_factorProduct (w : Q') (s r i : Nat) :
    aComponentAt w s r i ≈
      (match i with
        | 0 => modeWindow w s (r + 1)
        | 1 => modeWindow w s (r + 1)
        | _ => boundaryTerm w s r) *
      (match i with
        | 0 => modeWindow w s (r + 3)
        | 1 => boundaryTerm w s (r + 2)
        | 2 => modeWindow w s (r + 3)
        | _ => boundaryTerm w s (r + 2)) := by
  cases i with
  | zero => exact Q'.eqv_refl _
  | succ i =>
      cases i with
      | zero => exact Q'.eqv_refl _
      | succ i =>
          cases i with
          | zero => exact Q'.eqv_refl _
          | succ i => exact Q'.eqv_refl _

/-- **Bounded-index component theorem.**  Every arbitrary-offset numerator
component is represented by the same double monomial schema; only its two
finite bounds and atom selectors depend on `i`. -/
theorem aComponentAt_eq_normalForm (w : Q') (s r i : Nat) :
    aComponentAt w s r i ≈ aComponentNormalForm w s r i := by
  have hleft := aLeftFactor_eq_sum w s r i
  have hright := aRightFactor_eq_sum w s r i
  refine Q'.eqv_trans _ _ _ (aComponentAt_eq_factorProduct w s r i) ?_
  refine Q'.eqv_trans _ _ _ (mul_eqv_congr_two hleft hright) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_mul_fsum
      (fun p => WeightMonomial.eval w (aLeftMonomial s r i p))
      (fun q => WeightMonomial.eval w (aRightMonomial s r i q))
      (aLeftCount s i) (aRightCount s i)) ?_
  unfold aComponentNormalForm
  exact fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _
    (fun q => Q'.eqv_symm (WeightMonomial.eval_mul w
      (aLeftMonomial s r i p) (aRightMonomial s r i q)))
    (aRightCount s i)) (aLeftCount s i)

/-! ## 4. Arbitrary-offset midpoint-component normal form -/

/-- Number of monomials in the left midpoint factor. -/
def mLeftCount (s j : Nat) : Nat :=
  match j with
  | 0 => s + 1
  | 1 => s + 1
  | _ => 1

/-- Number of monomials in the right midpoint factor. -/
def mRightCount (s j : Nat) : Nat :=
  match j with
  | 0 => s + 1
  | 1 => 1
  | _ => 1

def mLeftMonomial (s r j p : Nat) : WeightMonomial :=
  match j with
  | 0 => windowMonomial s (r + 2) p
  | 1 => windowMonomial s (r + 2) p
  | _ => boundaryMonomial s (r + 1)

def mRightMonomial (s r j q : Nat) : WeightMonomial :=
  match j with
  | 0 => windowMonomial s (r + 2) q
  | 1 => boundaryMonomial s (r + 1)
  | _ => boundaryMonomial s (r + 1)

/-- The middle midpoint component contains two identical cross terms; its
normal form collects them by doubling the coefficient of each monomial. -/
def mAtomicMonomial (s r j p q : Nat) : WeightMonomial :=
  let atom := WeightMonomial.mul (mLeftMonomial s r j p)
    (mRightMonomial s r j q)
  match j with
  | 1 => WeightMonomial.twice atom
  | _ => atom

/-- All three midpoint components share this double bounded-index schema. -/
def mComponentNormalForm (w : Q') (s r j : Nat) : Q' :=
  fsum (fun p => fsum (fun q => WeightMonomial.eval w
    (mAtomicMonomial s r j p q)) (mRightCount s j)) (mLeftCount s j)

private def mBaseComponentAt (w : Q') (s r j : Nat) : Q' :=
  match j with
  | 0 => modeWindow w s (r + 2) * modeWindow w s (r + 2)
  | 1 => modeWindow w s (r + 2) * boundaryTerm w s (r + 1)
  | _ => boundaryTerm w s (r + 1) * boundaryTerm w s (r + 1)

private def mBaseNormalForm (w : Q') (s r j : Nat) : Q' :=
  fsum (fun p => fsum (fun q => WeightMonomial.eval w
    (WeightMonomial.mul (mLeftMonomial s r j p)
      (mRightMonomial s r j q))) (mRightCount s j)) (mLeftCount s j)

private theorem mLeftFactor_eq_sum (w : Q') (s r j : Nat) :
    (match j with
      | 0 => modeWindow w s (r + 2)
      | 1 => modeWindow w s (r + 2)
      | _ => boundaryTerm w s (r + 1)) ≈
      fsum (fun p => WeightMonomial.eval w (mLeftMonomial s r j p))
        (mLeftCount s j) := by
  cases j with
  | zero =>
      simpa [mLeftMonomial, mLeftCount, windowNormalForm] using
        modeWindow_eq_windowNormalForm w s (r + 2)
  | succ j =>
      cases j with
      | zero =>
          simpa [mLeftMonomial, mLeftCount, windowNormalForm] using
            modeWindow_eq_windowNormalForm w s (r + 2)
      | succ j =>
          refine Q'.eqv_trans _ _ _
            (boundaryTerm_eq_boundaryMonomial w s (r + 1)) ?_
          exact Q'.eqv_symm (by
            simpa [mLeftMonomial, mLeftCount] using
              fsum_one (fun _ => WeightMonomial.eval w
                (boundaryMonomial s (r + 1))))

private theorem mRightFactor_eq_sum (w : Q') (s r j : Nat) :
    (match j with
      | 0 => modeWindow w s (r + 2)
      | _ => boundaryTerm w s (r + 1)) ≈
      fsum (fun q => WeightMonomial.eval w (mRightMonomial s r j q))
        (mRightCount s j) := by
  cases j with
  | zero =>
      simpa [mRightMonomial, mRightCount, windowNormalForm] using
        modeWindow_eq_windowNormalForm w s (r + 2)
  | succ j =>
      cases j with
      | zero =>
          refine Q'.eqv_trans _ _ _
            (boundaryTerm_eq_boundaryMonomial w s (r + 1)) ?_
          exact Q'.eqv_symm (by
            simpa [mRightMonomial, mRightCount] using
              fsum_one (fun _ => WeightMonomial.eval w
                (boundaryMonomial s (r + 1))))
      | succ j =>
          refine Q'.eqv_trans _ _ _
            (boundaryTerm_eq_boundaryMonomial w s (r + 1)) ?_
          exact Q'.eqv_symm (by
            simpa [mRightMonomial, mRightCount] using
              fsum_one (fun _ => WeightMonomial.eval w
                (boundaryMonomial s (r + 1))))

private theorem mBaseComponentAt_eq_factorProduct (w : Q') (s r j : Nat) :
    mBaseComponentAt w s r j ≈
      (match j with
        | 0 => modeWindow w s (r + 2)
        | 1 => modeWindow w s (r + 2)
        | _ => boundaryTerm w s (r + 1)) *
      (match j with
        | 0 => modeWindow w s (r + 2)
        | _ => boundaryTerm w s (r + 1)) := by
  cases j with
  | zero => exact Q'.eqv_refl _
  | succ j =>
      cases j with
      | zero => exact Q'.eqv_refl _
      | succ j => exact Q'.eqv_refl _

private theorem mBaseComponentAt_eq_normalForm (w : Q') (s r j : Nat) :
    mBaseComponentAt w s r j ≈ mBaseNormalForm w s r j := by
  refine Q'.eqv_trans _ _ _ (mBaseComponentAt_eq_factorProduct w s r j) ?_
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr_two (mLeftFactor_eq_sum w s r j)
      (mRightFactor_eq_sum w s r j)) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_mul_fsum
      (fun p => WeightMonomial.eval w (mLeftMonomial s r j p))
      (fun q => WeightMonomial.eval w (mRightMonomial s r j q))
      (mLeftCount s j) (mRightCount s j)) ?_
  unfold mBaseNormalForm
  exact fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _
    (fun q => Q'.eqv_symm (WeightMonomial.eval_mul w
      (mLeftMonomial s r j p) (mRightMonomial s r j q)))
    (mRightCount s j)) (mLeftCount s j)

private theorem doubleMonomialSum_eq_doubleBase (w : Q') (s r : Nat) :
    mComponentNormalForm w s r 1 ≈
      mBaseNormalForm w s r 1 + mBaseNormalForm w s r 1 := by
  unfold mComponentNormalForm mBaseNormalForm
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _
      (fun q => WeightMonomial.eval_twice w
        (WeightMonomial.mul (mLeftMonomial s r 1 p)
          (mRightMonomial s r 1 q)))
      (mRightCount s 1)) (mLeftCount s 1)) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun p =>
      fsum_add
        (fun q => WeightMonomial.eval w
          (WeightMonomial.mul (mLeftMonomial s r 1 p)
            (mRightMonomial s r 1 q)))
        (fun q => WeightMonomial.eval w
          (WeightMonomial.mul (mLeftMonomial s r 1 p)
            (mRightMonomial s r 1 q)))
        (mRightCount s 1)) (mLeftCount s 1)) ?_
  exact fsum_add
    (fun p => fsum (fun q => WeightMonomial.eval w
      (WeightMonomial.mul (mLeftMonomial s r 1 p)
        (mRightMonomial s r 1 q))) (mRightCount s 1))
    (fun p => fsum (fun q => WeightMonomial.eval w
      (WeightMonomial.mul (mLeftMonomial s r 1 p)
        (mRightMonomial s r 1 q))) (mRightCount s 1))
    (mLeftCount s 1)

/-- **Bounded-index midpoint theorem.**  The repeated cross term is collected
inside each coefficient, so no row- or component-specific polynomial is
needed downstream. -/
theorem mComponentAt_eq_normalForm (w : Q') (s r j : Nat) :
    mComponentAt w s r j ≈ mComponentNormalForm w s r j := by
  cases j with
  | zero =>
      simpa [mComponentAt, mComponentNormalForm, mAtomicMonomial,
        mBaseComponentAt, mBaseNormalForm] using
        mBaseComponentAt_eq_normalForm w s r 0
  | succ j =>
      cases j with
      | zero =>
          have hbase := mBaseComponentAt_eq_normalForm w s r 1
          have hadd :
              mBaseComponentAt w s r 1 + mBaseComponentAt w s r 1 ≈
                mBaseNormalForm w s r 1 + mBaseNormalForm w s r 1 :=
            Q'.add_eqv_congr' hbase hbase
          change mBaseComponentAt w s r 1 + mBaseComponentAt w s r 1 ≈
            mComponentNormalForm w s r 1
          exact Q'.eqv_trans _ _ _ hadd
            (Q'.eqv_symm (doubleMonomialSum_eq_doubleBase w s r))
      | succ j =>
          simpa [mComponentAt, mComponentNormalForm, mAtomicMonomial,
            mBaseComponentAt, mBaseNormalForm] using
            mBaseComponentAt_eq_normalForm w s r (j + 2)

/-! ## 5. Mixed-minor bounded normal form -/

/-- The oriented determinant of one numerator atom and one midpoint atom. -/
def monomialMinor (w h : Q') (a m : WeightMonomial) : Q' :=
  determinant (WeightMonomial.eval w a) (WeightMonomial.eval h a)
    (WeightMonomial.eval w m) (WeightMonomial.eval h m)

/-- A mixed component minor as one four-index bounded family. -/
def mixedMinorNormalForm (w h : Q') (s r i j : Nat) : Q' :=
  fsum (fun p => fsum (fun u =>
    fsum (fun q => fsum (fun v =>
      monomialMinor w h (aAtomicMonomial s r i p q)
        (mAtomicMonomial s r j u v))
      (mRightCount s j)) (aRightCount s i))
    (mLeftCount s j)) (aLeftCount s i)

private theorem determinant_eqv_congr
    {a a' ah ah' m m' mh mh' : Q'}
    (ha : a ≈ a') (hah : ah ≈ ah')
    (hm : m ≈ m') (hmh : mh ≈ mh') :
    determinant a ah m mh ≈ determinant a' ah' m' mh' := by
  unfold determinant
  exact Q'.add_eqv_congr'
    (mul_eqv_congr_two ha hmh)
    (Q'.neg_eqv_congr _ _ (mul_eqv_congr_two hm hah))

/-- **Four-index mixed-minor theorem.**  This is the first normal form at the
level where exponent orientation and coefficient mass can be classified. -/
theorem mixedMinorAt_eq_normalForm (w h : Q') (s r i j : Nat) :
    mixedMinorAt w h s r i j ≈ mixedMinorNormalForm w h s r i j := by
  unfold mixedMinorAt
  refine Q'.eqv_trans _ _ _
    (determinant_eqv_congr
      (aComponentAt_eq_normalForm w s r i)
      (aComponentAt_eq_normalForm h s r i)
      (mComponentAt_eq_normalForm w s r j)
      (mComponentAt_eq_normalForm h s r j)) ?_
  unfold aComponentNormalForm mComponentNormalForm mixedMinorNormalForm
  refine Q'.eqv_trans _ _ _
    (determinant_fsum
      (fun p => fsum (fun q => WeightMonomial.eval w
        (aAtomicMonomial s r i p q)) (aRightCount s i))
      (fun p => fsum (fun q => WeightMonomial.eval h
        (aAtomicMonomial s r i p q)) (aRightCount s i))
      (fun u => fsum (fun v => WeightMonomial.eval w
        (mAtomicMonomial s r j u v)) (mRightCount s j))
      (fun u => fsum (fun v => WeightMonomial.eval h
        (mAtomicMonomial s r j u v)) (mRightCount s j))
      (aLeftCount s i) (mLeftCount s j)) ?_
  exact fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _ (fun u =>
    determinant_fsum
      (fun q => WeightMonomial.eval w (aAtomicMonomial s r i p q))
      (fun q => WeightMonomial.eval h (aAtomicMonomial s r i p q))
      (fun v => WeightMonomial.eval w (mAtomicMonomial s r j u v))
      (fun v => WeightMonomial.eval h (mAtomicMonomial s r j u v))
      (aRightCount s i) (mRightCount s j))
    (mLeftCount s j)) (aLeftCount s i)

/-! ## 6. Residual and diagonal cumulative normal forms -/

/-- The eleven structural component families, with no row specialization. -/
def boundaryResidualNormalForm (w h : Q') (s r : Nat) : Q' :=
  mixedMinorNormalForm w h s r 0 1 + mixedMinorNormalForm w h s r 0 2
    + mixedMinorNormalForm w h s r 1 0 + mixedMinorNormalForm w h s r 1 1
    + mixedMinorNormalForm w h s r 1 2 + mixedMinorNormalForm w h s r 2 0
    + mixedMinorNormalForm w h s r 2 1 + mixedMinorNormalForm w h s r 2 2
    + mixedMinorNormalForm w h s r 3 0 + mixedMinorNormalForm w h s r 3 1
    + mixedMinorNormalForm w h s r 3 2

/-- The entire eleven-minor residual is now a bounded monomial family,
uniformly in row and offset. -/
theorem boundaryResidualAt_eq_normalForm (w h : Q') (s r : Nat) :
    boundaryResidualAt w h s r ≈ boundaryResidualNormalForm w h s r := by
  unfold boundaryResidualAt boundaryResidualNormalForm
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr'
                      (mixedMinorAt_eq_normalForm w h s r 0 1)
                      (mixedMinorAt_eq_normalForm w h s r 0 2))
                    (mixedMinorAt_eq_normalForm w h s r 1 0))
                  (mixedMinorAt_eq_normalForm w h s r 1 1))
                (mixedMinorAt_eq_normalForm w h s r 1 2))
              (mixedMinorAt_eq_normalForm w h s r 2 0))
            (mixedMinorAt_eq_normalForm w h s r 2 1))
          (mixedMinorAt_eq_normalForm w h s r 2 2))
        (mixedMinorAt_eq_normalForm w h s r 3 0))
      (mixedMinorAt_eq_normalForm w h s r 3 1))
    (mixedMinorAt_eq_normalForm w h s r 3 2)

/-- Arbitrary-length diagonal accumulation of the bounded residual family. -/
def diagonalCumulativeNormalForm (w h : Q') (s r n : Nat) : Q' :=
  fsum (fun t => boundaryResidualNormalForm w h (s + t) (r + n - 1 - t)) n

/-- **Cumulative bounded-index theorem.**  The complete arbitrary-length
diagonal has a single reusable schema; later coefficient-mass arguments can
quantify over its finite indices without generating any row declarations. -/
theorem cumulativeResidual_eq_monomialNormalForm
    (w h : Q') (s r n : Nat) :
    cumulativeResidual w h s r n ≈
      diagonalCumulativeNormalForm w h s r n := by
  refine Q'.eqv_trans _ _ _
    (CoreBDiagonalCumulative.cumulativeResidual_eq_diagonalResidualSum
      w h s r n) ?_
  unfold CoreBDiagonalCumulative.diagonalResidualSum diagonalCumulativeNormalForm
  exact fsum_eqv_congr _ _ (fun t =>
    boundaryResidualAt_eq_normalForm w h (s + t) (r + n - 1 - t)) n

#print axioms WeightMonomial.eval_mul
#print axioms WeightMonomial.eval_twice
#print axioms coeffW_mul_eq_eval
#print axioms modeWindow_eq_windowNormalForm
#print axioms boundaryTerm_eq_boundaryMonomial
#print axioms aComponentAt_eq_normalForm
#print axioms mComponentAt_eq_normalForm
#print axioms mixedMinorAt_eq_normalForm
#print axioms boundaryResidualAt_eq_normalForm
#print axioms cumulativeResidual_eq_monomialNormalForm

end YMGap.Continuum.CoreBBoundedMonomialNormalForm
