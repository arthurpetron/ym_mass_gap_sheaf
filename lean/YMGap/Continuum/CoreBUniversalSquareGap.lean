/-
# Core-B universal square-gap factorization

The bounded monomial normal form makes every residual a finite family of
oriented determinants between two heat-kernel monomials.  This file proves
once, for arbitrary row and offset, that each such atom has an even exponent
and hence that the whole residual and every diagonal cumulative factor through

  w^2 - h^2.

The resulting quotient is exact algebraic data.  Its nonnegativity is the
subsequent odd/even coefficient-mass problem and is not asserted here.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBBoundedMonomialNormalForm
import YMGap.Continuum.CoreBResidualBaseUniform

namespace YMGap.Continuum.CoreBUniversalSquareGap

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBDiagonalCumulative
open YMGap.Continuum.CoreBBoundedMonomialNormalForm
open YMGap.Continuum.CoreBResidualBaseUniform

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Even exponents for every bounded component atom -/

/-- The SU(2) Casimir exponent has the same parity as its representation
label. -/
theorem c4_mod_two (n : Nat) : c4 n % 2 = n % 2 := by
  unfold c4
  rw [Nat.mul_mod]
  have hshift : (n + 2) % 2 = n % 2 := by omega
  rw [hshift]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [hn]
  · rw [hn]

private theorem c4_sum_four_even (a b c d : Nat)
    (hlabels : (a + b + (c + d)) % 2 = 0) :
    (c4 a + c4 b + (c4 c + c4 d)) % 2 = 0 := by
  have ha := c4_mod_two a
  have hb := c4_mod_two b
  have hc := c4_mod_two c
  have hd := c4_mod_two d
  omega

/-- Every numerator atom occurring inside its declared finite bounds has an
even heat-kernel exponent. -/
theorem aAtomicMonomial_exponent_even (s r i p q : Nat)
    (hp : p < aLeftCount s i) (hq : q < aRightCount s i) :
    (aAtomicMonomial s r i p q).exponent % 2 = 0 := by
  cases i with
  | zero =>
      simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial]
      apply c4_sum_four_even
      simp only [aLeftCount, aRightCount] at hp hq
      omega
  | succ i =>
      cases i with
      | zero =>
          simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            coefficientMonomial]
          apply c4_sum_four_even
          simp only [aLeftCount, aRightCount] at hp hq
          omega
      | succ i =>
          cases i with
          | zero =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                windowMonomial, boundaryMonomial, WeightMonomial.mul,
                coefficientMonomial]
              apply c4_sum_four_even
              simp only [aLeftCount, aRightCount] at hp hq
              omega
          | succ i =>
              simp only [aAtomicMonomial, aLeftMonomial, aRightMonomial,
                boundaryMonomial, WeightMonomial.mul, coefficientMonomial]
              apply c4_sum_four_even
              omega

/-- Every midpoint atom occurring inside its declared finite bounds has an
even heat-kernel exponent. -/
theorem mAtomicMonomial_exponent_even (s r j p q : Nat)
    (hp : p < mLeftCount s j) (hq : q < mRightCount s j) :
    (mAtomicMonomial s r j p q).exponent % 2 = 0 := by
  cases j with
  | zero =>
      simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
        windowMonomial, WeightMonomial.mul, coefficientMonomial]
      apply c4_sum_four_even
      simp only [mLeftCount, mRightCount] at hp hq
      omega
  | succ j =>
      cases j with
      | zero =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            windowMonomial, boundaryMonomial, WeightMonomial.mul,
            WeightMonomial.twice, coefficientMonomial]
          apply c4_sum_four_even
          simp only [mLeftCount, mRightCount] at hp hq
          omega
      | succ j =>
          simp only [mAtomicMonomial, mLeftMonomial, mRightMonomial,
            boundaryMonomial, WeightMonomial.mul, coefficientMonomial]
          apply c4_sum_four_even
          omega

/-! ## 2. Order-uniform divided differences in the squared variables -/

/-- The universal heat-kernel square gap. -/
def squareGap (w h : Q') : Q' := qpow w 2 + -qpow h 2

/-- The signed homogeneous chain which represents `crossPair x y p q` after
division by `x-y`, regardless of the order of `p` and `q`. -/
def orientedHomChain (x y : Q') (p q : Nat) : Q' :=
  if q ≤ p then homChain x y q (p - q)
  else -(homChain x y p (q - p))

theorem crossPair_factor_ordered (x y : Q') (p q : Nat) :
    crossPair x y p q ≈ (x + -y) * orientedHomChain x y p q := by
  by_cases hqp : q ≤ p
  · simp only [orientedHomChain, if_pos hqp]
    have hf := crossPair_factor x y q (p - q)
    rw [show q + (p - q) = p by omega] at hf
    exact hf
  · have hpq : p ≤ q := by omega
    simp only [orientedHomChain, if_neg hqp]
    have hf : crossPair x y p q ≈
        -((x + -y) * homChain x y p (q - p)) := by
      have hfactor := crossPair_factor_neg x y p (q - p)
      rw [show p + (q - p) = q by omega] at hfactor
      exact hfactor
    refine Q'.eqv_trans _ _ _
      hf ?_
    exact Q'.eqv_symm
      (Q'.mul_neg_eqv (x + -y) (homChain x y p (q - p)))

/-- Even powers descend exactly to powers of the squared variable. -/
theorem qpow_eq_squarePow_of_even (w : Q') (n : Nat) (hn : n % 2 = 0) :
    qpow w n ≈ qpow (qpow w 2) (n / 2) := by
  have htwice : 2 * (n / 2) = n := by omega
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq ?_)
    (Q'.eqv_symm (qpow_qpow w 2 (n / 2)))
  exact congrArg (qpow w) htwice.symm

/-! ## 3. Atomic monomial-minor quotient -/

/-- Natural coefficient mass of two monomial atoms, embedded into `Q'`. -/
def monomialPairCoefficient (a m : WeightMonomial) : Q' :=
  Q'.ofNat a.coefficientNat * Q'.ofNat m.coefficientNat

/-- Exact divided square-gap quotient for a pair of even-exponent atoms. -/
def monomialSquareGapQuotient (w h : Q')
    (a m : WeightMonomial) : Q' :=
  monomialPairCoefficient a m *
    orientedHomChain (qpow w 2) (qpow h 2) (a.exponent / 2) (m.exponent / 2)

private def detFactorL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 0) (.var 5))))

private def detFactorR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 2))
    (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 4) (.var 5))))

private theorem detFactor_normal : RingNormaliser.normalize detFactorL =
    RingNormaliser.normalize detFactorR := by decide

private theorem determinant_monomial_factor
    (a m wp hp wq hq : Q') :
    determinant (a * wp) (a * hp) (m * wq) (m * hq) ≈
      (a * m) * (wp * hq + -(wq * hp)) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq detFactorL detFactorR
    detFactor_normal (fun n => match n with
      | 0 => a | 1 => wp | 2 => m | 3 => hq | 4 => wq | _ => hp)
  simpa [determinant, RingNormaliser.eval, detFactorL, detFactorR] using hn

private theorem determinant_eqv_congr
    {a a' ah ah' m m' mh mh' : Q'}
    (ha : a ≈ a') (hah : ah ≈ ah')
    (hm : m ≈ m') (hmh : mh ≈ mh') :
    determinant a ah m mh ≈ determinant a' ah' m' mh' := by
  unfold determinant
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
      (Q'.mul_eqv_congr_left _ _ _ hmh))
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
        (Q'.mul_eqv_congr_left _ _ _ hah)))

private theorem coefficient_factor_swap (c d z : Q') :
    c * (d * z) ≈ d * (c * z) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c d z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ z (Q'.mul_comm_eqv c d)) ?_
  exact Q'.mul_assoc_eqv d c z

/-- An oriented determinant of two even-exponent monomials factors through
the square gap, with its exact signed homogeneous-chain quotient. -/
theorem monomialMinor_squareGap_factor (w h : Q') (a m : WeightMonomial)
    (haeven : a.exponent % 2 = 0) (hmeven : m.exponent % 2 = 0) :
    monomialMinor w h a m ≈
      squareGap w h * monomialSquareGapQuotient w h a m := by
  unfold squareGap
  let ca := Q'.ofNat a.coefficientNat
  let cm := Q'.ofNat m.coefficientNat
  let x := qpow w 2
  let y := qpow h 2
  let pa := a.exponent / 2
  let pm := m.exponent / 2
  have haw : WeightMonomial.eval w a ≈ ca * qpow x pa := by
    unfold WeightMonomial.eval
    exact Q'.mul_eqv_congr_left ca _ _
      (qpow_eq_squarePow_of_even w a.exponent haeven)
  have hah : WeightMonomial.eval h a ≈ ca * qpow y pa := by
    unfold WeightMonomial.eval
    exact Q'.mul_eqv_congr_left ca _ _
      (qpow_eq_squarePow_of_even h a.exponent haeven)
  have hmw : WeightMonomial.eval w m ≈ cm * qpow x pm := by
    unfold WeightMonomial.eval
    exact Q'.mul_eqv_congr_left cm _ _
      (qpow_eq_squarePow_of_even w m.exponent hmeven)
  have hmh : WeightMonomial.eval h m ≈ cm * qpow y pm := by
    unfold WeightMonomial.eval
    exact Q'.mul_eqv_congr_left cm _ _
      (qpow_eq_squarePow_of_even h m.exponent hmeven)
  unfold monomialMinor
  refine Q'.eqv_trans _ _ _
    (determinant_eqv_congr haw hah hmw hmh) ?_
  refine Q'.eqv_trans _ _ _
    (determinant_monomial_factor ca cm (qpow x pa) (qpow y pa)
      (qpow x pm) (qpow y pm)) ?_
  change (ca * cm) * crossPair x y pa pm ≈ _
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ca * cm) _ _
      (crossPair_factor_ordered x y pa pm)) ?_
  exact coefficient_factor_swap (ca * cm) (x + -y)
    (orientedHomChain x y pa pm)

/-! ## 4. Lift through the four bounded monomial indices -/

/-- The exact quotient of one mixed-minor normal form. -/
def mixedMinorSquareGapQuotient
    (w h : Q') (s r i j : Nat) : Q' :=
  fsum (fun p => fsum (fun u =>
    fsum (fun q => fsum (fun v =>
      monomialSquareGapQuotient w h (aAtomicMonomial s r i p q)
        (mAtomicMonomial s r j u v))
      (mRightCount s j)) (aRightCount s i))
    (mLeftCount s j)) (aLeftCount s i)

private theorem fsum_four_const_factor
    (c : Q') (f : Nat → Nat → Nat → Nat → Q')
    (np nu nq nv : Nat) :
    fsum (fun p => fsum (fun u => fsum (fun q =>
      fsum (fun v => c * f p u q v) nv) nq) nu) np ≈
      c * fsum (fun p => fsum (fun u => fsum (fun q =>
        fsum (fun v => f p u q v) nv) nq) nu) np := by
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _ (fun u =>
      fsum_eqv_congr _ _ (fun q =>
        Q'.eqv_symm (fsum_const_mul c (f p u q) nv)) nq) nu) np) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun p => fsum_eqv_congr _ _ (fun u =>
      Q'.eqv_symm (fsum_const_mul c
        (fun q => fsum (f p u q) nv) nq)) nu) np) ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun p =>
      Q'.eqv_symm (fsum_const_mul c
        (fun u => fsum (fun q => fsum (f p u q) nv) nq) nu)) np) ?_
  exact Q'.eqv_symm (fsum_const_mul c
    (fun p => fsum (fun u => fsum (fun q => fsum (f p u q) nv) nq) nu) np)

/-- Every four-index mixed-minor family factors through the same square gap. -/
theorem mixedMinorNormalForm_squareGap_factor
    (w h : Q') (s r i j : Nat) :
    mixedMinorNormalForm w h s r i j ≈
      squareGap w h * mixedMinorSquareGapQuotient w h s r i j := by
  refine Q'.eqv_trans _ _ _ ?_
    (fsum_four_const_factor (squareGap w h)
      (fun p u q v => monomialSquareGapQuotient w h
        (aAtomicMonomial s r i p q) (mAtomicMonomial s r j u v))
      (aLeftCount s i) (mLeftCount s j)
      (aRightCount s i) (mRightCount s j))
  unfold mixedMinorNormalForm
  exact fsum_eqv_congr_lt _ _ (aLeftCount s i) (fun p hp =>
    fsum_eqv_congr_lt _ _ (mLeftCount s j) (fun u hu =>
      fsum_eqv_congr_lt _ _ (aRightCount s i) (fun q hq =>
        fsum_eqv_congr_lt _ _ (mRightCount s j) (fun v hv =>
          monomialMinor_squareGap_factor w h
            (aAtomicMonomial s r i p q) (mAtomicMonomial s r j u v)
            (aAtomicMonomial_exponent_even s r i p q hp hq)
            (mAtomicMonomial_exponent_even s r j u v hu hv)))))

/-- The original component minor, before normal-form rewriting, has the same
universal factor. -/
theorem mixedMinorAt_squareGap_factor (w h : Q') (s r i j : Nat) :
    mixedMinorAt w h s r i j ≈
      squareGap w h * mixedMinorSquareGapQuotient w h s r i j :=
  Q'.eqv_trans _ _ _ (mixedMinorAt_eq_normalForm w h s r i j)
    (mixedMinorNormalForm_squareGap_factor w h s r i j)

/-! ## 5. Eleven-family residual quotient -/

/-- The eleven structural quotient families, in the residual's fixed order. -/
def boundaryResidualSquareGapQuotient (w h : Q') (s r : Nat) : Q' :=
  mixedMinorSquareGapQuotient w h s r 0 1
    + mixedMinorSquareGapQuotient w h s r 0 2
    + mixedMinorSquareGapQuotient w h s r 1 0
    + mixedMinorSquareGapQuotient w h s r 1 1
    + mixedMinorSquareGapQuotient w h s r 1 2
    + mixedMinorSquareGapQuotient w h s r 2 0
    + mixedMinorSquareGapQuotient w h s r 2 1
    + mixedMinorSquareGapQuotient w h s r 2 2
    + mixedMinorSquareGapQuotient w h s r 3 0
    + mixedMinorSquareGapQuotient w h s r 3 1
    + mixedMinorSquareGapQuotient w h s r 3 2

private def addElevenE
    (a b c d e f g h i j k : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.add (.add a b) c) d) e) f) g) h) i) j) k

private def factorElevenL : RingNormaliser.PolyExpr :=
  let c := RingNormaliser.PolyExpr.var 0
  addElevenE (.mul c (.var 1)) (.mul c (.var 2)) (.mul c (.var 3))
    (.mul c (.var 4)) (.mul c (.var 5)) (.mul c (.var 6))
    (.mul c (.var 7)) (.mul c (.var 8)) (.mul c (.var 9))
    (.mul c (.var 10)) (.mul c (.var 11))

private def factorElevenR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (addElevenE (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
      (.var 7) (.var 8) (.var 9) (.var 10) (.var 11))

private theorem factorEleven_normal : RingNormaliser.normalize factorElevenL =
    RingNormaliser.normalize factorElevenR := by decide

private theorem factor_eleven
    (c a b d e f g h i j k l : Q') :
    c * a + c * b + c * d + c * e + c * f + c * g
        + c * h + c * i + c * j + c * k + c * l ≈
      c * (a + b + d + e + f + g + h + i + j + k + l) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq factorElevenL factorElevenR
    factorEleven_normal (fun n => match n with
      | 0 => c | 1 => a | 2 => b | 3 => d | 4 => e | 5 => f
      | 6 => g | 7 => h | 8 => i | 9 => j | 10 => k | _ => l)
  simpa [RingNormaliser.eval, factorElevenL, factorElevenR, addElevenE] using hn

/-- The full bounded normal form of the residual factors through the square
gap, with the sum of its eleven component quotients. -/
theorem boundaryResidualNormalForm_squareGap_factor
    (w h : Q') (s r : Nat) :
    boundaryResidualNormalForm w h s r ≈
      squareGap w h * boundaryResidualSquareGapQuotient w h s r := by
  unfold boundaryResidualNormalForm boundaryResidualSquareGapQuotient
  refine Q'.eqv_trans _ _ _ ?_
    (factor_eleven (squareGap w h)
      (mixedMinorSquareGapQuotient w h s r 0 1)
      (mixedMinorSquareGapQuotient w h s r 0 2)
      (mixedMinorSquareGapQuotient w h s r 1 0)
      (mixedMinorSquareGapQuotient w h s r 1 1)
      (mixedMinorSquareGapQuotient w h s r 1 2)
      (mixedMinorSquareGapQuotient w h s r 2 0)
      (mixedMinorSquareGapQuotient w h s r 2 1)
      (mixedMinorSquareGapQuotient w h s r 2 2)
      (mixedMinorSquareGapQuotient w h s r 3 0)
      (mixedMinorSquareGapQuotient w h s r 3 1)
      (mixedMinorSquareGapQuotient w h s r 3 2))
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
                      (mixedMinorNormalForm_squareGap_factor w h s r 0 1)
                      (mixedMinorNormalForm_squareGap_factor w h s r 0 2))
                    (mixedMinorNormalForm_squareGap_factor w h s r 1 0))
                  (mixedMinorNormalForm_squareGap_factor w h s r 1 1))
                (mixedMinorNormalForm_squareGap_factor w h s r 1 2))
              (mixedMinorNormalForm_squareGap_factor w h s r 2 0))
            (mixedMinorNormalForm_squareGap_factor w h s r 2 1))
          (mixedMinorNormalForm_squareGap_factor w h s r 2 2))
        (mixedMinorNormalForm_squareGap_factor w h s r 3 0))
      (mixedMinorNormalForm_squareGap_factor w h s r 3 1))
    (mixedMinorNormalForm_squareGap_factor w h s r 3 2)

/-- The original eleven-minor residual has the universal factorization. -/
theorem boundaryResidualAt_squareGap_factor (w h : Q') (s r : Nat) :
    boundaryResidualAt w h s r ≈
      squareGap w h * boundaryResidualSquareGapQuotient w h s r :=
  Q'.eqv_trans _ _ _ (boundaryResidualAt_eq_normalForm w h s r)
    (boundaryResidualNormalForm_squareGap_factor w h s r)

/-! ## 6. Arbitrary diagonal cumulative quotient -/

/-- The exact quotient accumulated along an arbitrary finite diagonal. -/
def diagonalCumulativeSquareGapQuotient
    (w h : Q') (s r n : Nat) : Q' :=
  fsum (fun t => boundaryResidualSquareGapQuotient w h
    (s + t) (r + n - 1 - t)) n

theorem diagonalCumulativeNormalForm_squareGap_factor
    (w h : Q') (s r n : Nat) :
    diagonalCumulativeNormalForm w h s r n ≈
      squareGap w h * diagonalCumulativeSquareGapQuotient w h s r n := by
  unfold diagonalCumulativeNormalForm diagonalCumulativeSquareGapQuotient
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun t =>
      boundaryResidualNormalForm_squareGap_factor w h
        (s + t) (r + n - 1 - t)) n) ?_
  exact Q'.eqv_symm (fsum_const_mul (squareGap w h)
    (fun t => boundaryResidualSquareGapQuotient w h
      (s + t) (r + n - 1 - t)) n)

/-- **Universal cumulative square-gap theorem.**  Every row, offset, and
finite diagonal length uses the same exact quotient schema. -/
theorem cumulativeResidual_squareGap_factor
    (w h : Q') (s r n : Nat) :
    cumulativeResidual w h s r n ≈
      squareGap w h * diagonalCumulativeSquareGapQuotient w h s r n :=
  Q'.eqv_trans _ _ _
    (cumulativeResidual_eq_monomialNormalForm w h s r n)
    (diagonalCumulativeNormalForm_squareGap_factor w h s r n)

#print axioms c4_mod_two
#print axioms aAtomicMonomial_exponent_even
#print axioms mAtomicMonomial_exponent_even
#print axioms crossPair_factor_ordered
#print axioms qpow_eq_squarePow_of_even
#print axioms monomialMinor_squareGap_factor
#print axioms mixedMinorNormalForm_squareGap_factor
#print axioms mixedMinorAt_squareGap_factor
#print axioms boundaryResidualNormalForm_squareGap_factor
#print axioms boundaryResidualAt_squareGap_factor
#print axioms diagonalCumulativeNormalForm_squareGap_factor
#print axioms cumulativeResidual_squareGap_factor

end YMGap.Continuum.CoreBUniversalSquareGap
